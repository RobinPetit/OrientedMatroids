/-
Copyright (c) 2026 Jean Cardinal & Robin Petit. All rights reserved.
Released under MIT NON-AI license as described in the file LICENSE.
Authors: Jean Cardinal, Robin Petit
-/

import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Replace

open Lean Lean.Elab.Tactic Lean.Meta

initialize cyclicAttr : TagAttribute ←
  registerTagAttribute `cyclic "Marks results showing invariant under cyclic permutation"

private def rewrite_hyp (mg : MVarId) (decl : LocalDecl) (cyclic_lemma : Name) :
    TacticM (MVarId × LocalDecl) := do
  let type := (← instantiateMVars decl.type).consumeMData  -- compute the param to rw
  let cmd ← mg.rewrite type (← mkConstWithLevelParams cyclic_lemma)  -- create the rw command
  let res := (← mg.replaceLocalDecl decl.fvarId cmd.eNew cmd.eqProof)  -- apply the rw command
  replaceMainGoal [res.mvarId]  -- update the context
  -- return the context and the updated declaration
  return (res.mvarId, (← res.mvarId.withContext getLCtx).get! res.fvarId)

private def get_nb_rws_hyp (_mg : MVarId) (_decl : LocalDecl) (cyclic_lemma : Name) :
    TacticM (MVarId × LocalDecl × Nat) := do
  -- Have a mutable version of mg and decl
  let mut mg := _mg
  let mut decl := _decl
  -- Get the initial expression as a string
  let type := (← instantiateMVars decl.type).consumeMData
  let original_name ← mg.withContext do return (← ppExpr type).pretty
  let mut smallest_name := original_name
  let mut counter : Nat := 0
  let mut obj_counter : Nat := 0
  while true do
    -- Apply rw once
    let ⟨new_mg, new_decl⟩ ← rewrite_hyp mg decl cyclic_lemma
    mg := new_mg; decl := new_decl
    -- Get the new expression as a string
    let new_type := (← instantiateMVars decl.type).consumeMData
    let new_name ← mg.withContext do return (← ppExpr new_type).pretty
    counter := counter + 1
    if new_name < smallest_name then
      -- Find the best one so far
      smallest_name := new_name
      obj_counter := counter
    else if new_name == original_name then
      -- We got back to the starting point, let's stop
      break
  -- Return the obj_counter as well as the updated mg and decl
  return (mg, decl, obj_counter)

private def rewrite_goal (_mg : MVarId) (cyclic_lemma : Name) :
    TacticM MVarId := do
  let mut mg := _mg
  let type := (← instantiateMVars (← mg.getType)).consumeMData
  let cmd ← mg.rewrite type (← mkConstWithLevelParams cyclic_lemma)
  let res := (← mg.replaceTargetEq cmd.eNew cmd.eqProof)
  replaceMainGoal [res]
  return res

private def get_nb_rws_goal (_mg : MVarId) (cyclic_lemma : Name) :
    TacticM (MVarId × Nat) := do
  let mut mg := _mg
  let type := (← instantiateMVars (← mg.getType)).consumeMData
  let original_name ← mg.withContext do return (← ppExpr type).pretty
  let mut smallest_name := original_name
  let mut counter : Nat := 0
  let mut obj_counter : Nat := 0
  while true do
    let new_mg ← rewrite_goal mg cyclic_lemma
    mg := new_mg
    let new_type := (← instantiateMVars (← mg.getType)).consumeMData
    let new_name ← mg.withContext do return (← ppExpr new_type).pretty
    counter := counter + 1
    if new_name < smallest_name then
      smallest_name := new_name
      obj_counter := counter
    else if new_name == original_name then
      break
  return (mg, obj_counter)

syntax "cyclic_nf" ("[" term,* "]")? : tactic

elab_rules : tactic
| `(tactic| cyclic_nf $[[ $args?,* ]]?) => withMainContext do
  let mut mg ← getMainGoal
  let env ← getEnv
  let mut cyclic_lemmas : Array Name := (cyclicAttr.ext.getState env).toArray
  if let some additional_lemmas := args? then
    for id in additional_lemmas.getElems do
      let name ← resolveGlobalConstNoOverload id
      cyclic_lemmas := cyclic_lemmas.push name
  for cyclic_lemma in cyclic_lemmas do
    let ctx ← mg.withContext getLCtx
    let declIds : Array LocalDecl := ctx.foldl Array.push #[]

    for i in [:declIds.size] do
      let ctx ← mg.withContext getLCtx
      let currentDecls := ctx.foldl Array.push #[]

      if i >= currentDecls.size then continue
      let mut decl := currentDecls[i]!
      if decl.isImplementationDetail then continue
      let type := (← instantiateMVars decl.type).consumeMData
      try let _ ← mg.rewrite type (← mkConstWithLevelParams cyclic_lemma)
      catch _e => continue
      let ⟨new_mg, new_decl, obj_counter⟩ ← get_nb_rws_hyp mg decl cyclic_lemma
      decl := new_decl
      mg := new_mg
      for _ in [:obj_counter] do
        let ⟨new_mg, new_decl⟩ ← rewrite_hyp mg decl cyclic_lemma
        mg := new_mg; decl := new_decl
    let type := (← instantiateMVars (← mg.getType)).consumeMData
    try let _ ← mg.rewrite type (← mkConstWithLevelParams cyclic_lemma)
    catch _ => continue
    let ⟨new_mg, obj_counter⟩ ← get_nb_rws_goal mg cyclic_lemma
    mg := new_mg
    for _ in [:obj_counter] do
      mg := (← rewrite_goal mg cyclic_lemma)
  evalTactic (← `(tactic| try assumption))
