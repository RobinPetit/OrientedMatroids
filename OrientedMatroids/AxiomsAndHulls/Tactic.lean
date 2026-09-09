-- import Mathlib
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Assert

import OrientedMatroids.AxiomsAndHulls.Defs

-- namespace AxiomsAndHulls
-- universe u
-- theorem PreCCSystem.cyclic' {α : Type u} {S : PreCCSystem α} {p q r : α} :
--     S.cc p q r → S.cc q r p :=
--   S.cyclic
-- end AxiomsAndHulls

namespace Lean.Elab.Tactic

open Lean Lean.Elab.Tactic Lean.Meta

namespace WIP
open AxiomsAndHulls
universe u
theorem PreCCSystem.cyclic' {α : Type u} {S : PreCCSystem α} {p q r : α} :
    S.cc p q r → S.cc q r p :=
  S.cyclic

elab "cyclicity_v3" : tactic => do
  -- Retrieve the active goal
  let mut mg ← getMainGoal
  -- And the local context (in particular all the local hypotheses)
  let ctx ← mg.withContext getLCtx

  -- For every local declaration
  for (decl : LocalDecl) in ctx do
    -- Only consider the local hypotheses
    if decl.isAuxDecl then continue
    let type : Expr := decl.type
    -- And more precisely the hypotheses of the form `PreCCSystem.cc <α> <S> <p> <q> <r>`
    if !type.isAppOf ``AxiomsAndHulls.PreCCSystem.cc then continue
    -- Get the arity of the application in question (so PreCCSystem.cc)
    let arity := type.getAppNumArgs
    -- hyp_id contains the "free variable ID" of the current last cylic application of the
    -- base hypothesis in `decl`
    let mut hyp_id := decl.fvarId
    -- Now proceed to try all rotations
    for _ in [:arity] do
      -- Needs to be locally wrapped in `mg.withContext` instead of having the whole
      -- monad starting with `withMainContext` because `mg` and `ctx` are modified in the loop
      let (new_hyp_id, new_mg) ← mg.withContext do
        -- Construct an application of cyclic' applied on the last cyclic rotation of `decl`
        let h' ← mkAppM ``PreCCSystem.cyclic' #[(← hyp_id.getDecl).toExpr]
        -- Change the goal target to be h'
        let new_mg ← mg.assert `_ (← inferType h') h'
        -- And use the tactic `intro` to add the implication LHS to the local hypotheses
        let (new_hyp_id, new_mg) ← new_mg.intro `h
        -- Retrieve the id of the newly created hypothesis as well as the updated active goal
        return (new_hyp_id, new_mg)
      -- Finally, update the local variables
      hyp_id := new_hyp_id
      mg := new_mg
      -- Tell Lean that we modified the goal
      replaceMainGoal [mg]
  -- At the end, conclude with invoking `assumption`.
  -- This makes the tactic fail if the goal target cannot be deduced by a sequence of calls to
  -- PreCCSystem.cyclic on any of the local hypotheses
  evalTactic (← `(tactic| assumption))


def getName (arg : Expr) : MetaM Name := do
  return (← arg.fvarId!.getDecl).userName

def get_min_name_idx (args : Array Expr) (i₀ : Nat) : MetaM Nat := do
  let n := args.size
  let mut ret : Nat := i₀
  for i in [i₀+1:n] do
    if Name.lt (← getName args[i]!) (← getName args[ret]!) then
      ret := i
  return ret

elab "cyclic_nf_v1" : tactic => do
  let mut mg ← getMainGoal
  let ctx ← mg.withContext getLCtx
  for (decl : LocalDecl) in ctx do
    let declName := decl.userName
    if decl.isAuxDecl then continue
    let type := (← instantiateMVars decl.type).consumeMData
    let count : Nat ← mg.withContext do (return (← get_min_name_idx type.getAppArgs 2) - 2)
    let mut hyp_id := decl.fvarId
    for _ in [:count] do
      let (new_hyp_id, new_mg) ← mg.withContext do
        let h' ← mkAppM ``PreCCSystem.cyclic' #[(← hyp_id.getDecl).toExpr]
        let new_mg ← mg.assert `_ (← inferType h') h'
        let (new_hyp_id, new_mg) ← new_mg.intro declName
        let new_mg ← new_mg.clear (← hyp_id.getDecl).fvarId
        return (new_hyp_id, new_mg)
      hyp_id := new_hyp_id
      mg := new_mg
      replaceMainGoal [new_mg]
  evalTactic (← `(tactic| try assumption))

elab "cyclic_nf_v2" : tactic => do
  let mut mg ← getMainGoal
  let ctx ← mg.withContext getLCtx
  for (decl : LocalDecl) in ctx do
    let declName := decl.userName
    if decl.isAuxDecl then continue
    let type := (← instantiateMVars decl.type).consumeMData
    let count : Nat ← mg.withContext do (return (← get_min_name_idx type.getAppArgs 2) - 2)
    let mut hyp_id := decl.fvarId
    for _ in [:count] do
      let (new_hyp_id, new_mg) ← mg.withContext do
        let h' ← mkAppM ``PreCCSystem.cyclic' #[(← hyp_id.getDecl).toExpr]
        let new_mg ← mg.assert `_ (← inferType h') h'
        let (new_hyp_id, new_mg) ← new_mg.intro declName
        let new_mg ← new_mg.clear (← hyp_id.getDecl).fvarId
        return (new_hyp_id, new_mg)
      hyp_id := new_hyp_id
      mg := new_mg
      replaceMainGoal [new_mg]
  let target_type := (← instantiateMVars (← mg.getType)).consumeMData
  if target_type.isAppOf ``AxiomsAndHulls.PreCCSystem.cc then
    let arity := target_type.getAppNumArgs
    let count : Nat ← mg.withContext do (return (← get_min_name_idx target_type.getAppArgs 2) - 2)
    for _ in [:(arity-2)-count] do
      let new_mgs ← mg.withContext do
        mg.apply (← mkConstWithFreshMVarLevels ``PreCCSystem.cyclic')
      if new_mgs.length = 1 then
        mg := new_mgs[0]!
        replaceMainGoal [mg]
  evalTactic (← `(tactic| try assumption))

end WIP

-- elab "by_antisymm" : tactic => do withMainContext do
--   sorry

end Lean.Elab.Tactic


-- #min_imports
