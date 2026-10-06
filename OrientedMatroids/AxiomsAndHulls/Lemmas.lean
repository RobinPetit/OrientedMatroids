/-
Copyright (c) 2026 Jean Cardinal & Robin Petit. All rights reserved.
Released under MIT NON-AI license as described in the file LICENSE.
Authors: Jean Cardinal, Robin Petit
-/

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.ByContra

import OrientedMatroids.AxiomsAndHulls.Defs
import OrientedMatroids.Tactic

/-!
DOCSTRING: TODO
-/

namespace AxiomsAndHulls
open CC

universe u
variable {α : Type u}

@[grind .]
lemma ne_of_cc {S : PreCCSystem α} {p q r : α} (h : S.cc p q r) : p ≠ q := by
  exact S.nondegenerate h |>.1

@[grind .]
lemma ne_of_cc' {S : PreCCSystem α} {p q r : α} (h : S.cc p q r) : q ≠ r := by
  exact S.nondegenerate h |>.2.1

@[grind .]
lemma ne_of_cc'' {S : PreCCSystem α} {p q r : α} (h : S.cc p q r) : p ≠ r := by
  exact S.nondegenerate h |>.2.2

@[cyclic]
lemma PreCCSystem.cyclic' {S : PreCCSystem α} {p q r : α} :
    S.cc p q r = S.cc q r p :=
  propext ⟨S.cyclic, S.cyclic2⟩

private lemma dualTransitive_of_transitive_impl {S : PreCCSystem α} {p q r s : α} (t : α)
    (hsner : s ≠ r)
    (hpqt : S.cc p q t) (hpst : S.cc p s t) (hptr : S.cc p t r)
    (htqr : S.cc t q r) (hstr : S.cc s t r) (hstq : S.cc s t q) :
    S.cc s p q → S.cc s r p := by
  intro hspq
  if hpqr : S.cc p q r then
    suffices S.cc p s r by cyclic_nf
    refine S.transitive t q hsner ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf
  else
    by_contra hnotsrp
    have hprq : S.cc p r q := by grind only [ne_of_cc'', ne_of_cc', S.total]
    have hspr : S.cc s p r := by grind only [ne_of_cc'', ne_of_cc, S.total]
    by_cases S.cc r q s
    · case pos hrqs =>
        suffices S.cc q r p by exact hpqr <| by cyclic_nf
        have hrnep : r ≠ p := Ne.symm <| ne_of_cc hprq
        have hpneq : p ≠ q := ne_of_cc hpqt
        have hqner : q ≠ r := Ne.symm <| ne_of_cc hrqs
        refine S.transitive t s hrnep ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf
    · case neg hnotrqs =>
        have hrsq : S.cc r s q := by grind only [ne_of_cc'', ne_of_cc', S.total]
        have hnotrqt : ¬S.cc r q t := S.antisymm (by cyclic_nf)
        have : S.cc r t q := by grind only [ne_of_cc'', ne_of_cc', S.total]
        refine hnotrqt ?_ |>.elim
        have hqnet : q ≠ t := by grind only
        have htner : t ≠ r := by grind only
        refine S.transitive p s hqnet ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf

lemma PreCCSystem.dualTransitive (S : PreCCSystem α) :
    DualTransitive S.cc := by
  intro p q r s t hpner hstp hstq hstr htpq htqr
  by_contra
  have htrp : S.cc t r p := by grind only [ne_of_cc'', ne_of_cc', S.total, S.antisymm]
  have H1 : S.cc s p q → S.cc s r p := by
    refine dualTransitive_of_transitive_impl t (by grind)  ?_ ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf
  have H2 : S.cc s r p → S.cc s q r := by
    refine dualTransitive_of_transitive_impl t (by grind) ?_ ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf
  have H3 : S.cc s q r → S.cc s p q := by
    refine dualTransitive_of_transitive_impl t (by grind) ?_ ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf
  if hspq : S.cc s p q then
    have hsqr : S.cc s q r := H2 <| H1 hspq
    have hspr : S.cc s p r := by refine S.transitive q t (by grind) ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf
    grind [S.total, S.antisymm]
  else
    have hsqp : S.cc s q p := by grind [S.total, S.antisymm]
    have hprs : S.cc s p r := by grind [S.total, S.antisymm]
    suffices S.cc s q r by grind [S.total, S.antisymm]
    refine S.transitive p t (by grind) ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf

def PreCCSystem.toWeakCCSystem (S : PreCCSystem α) : WeakPreCCSystem α :=
  ⟨S.cc, S.antisymm, S.nondegenerate, S.transitive, S.dualTransitive, S.total⟩

instance : Coe (PreCCSystem α) (WeakPreCCSystem α) :=
  ⟨(·.toWeakCCSystem)⟩

namespace WeakPreCCSystem
lemma of_ne_antisymm (S : WeakPreCCSystem α) :
    ∀ {p q r : α}, p ≠ q → p ≠ r → q ≠ r → ¬ S.cc p q r → S.cc p r q :=
  fun hpneq hpner hqner hnot_pqr ↦ S.total hpneq hqner hpner |>.resolve_left hnot_pqr

lemma nondegenerate' {S : WeakPreCCSystem α} {p q : α} :
    ¬S.cc p p q := by grind only [S.nondegenerate]

lemma nondegenerate'' {S : WeakPreCCSystem α} {p q : α} :
    ¬S.cc p q q := by grind only [S.nondegenerate]
end WeakPreCCSystem

namespace PreCCSystem
lemma of_ne_antisymm (S : PreCCSystem α) :
    ∀ {p q r : α}, p ≠ q → p ≠ r → q ≠ r → ¬ S.cc p q r → S.cc p r q :=
  S.toWeakCCSystem.of_ne_antisymm

lemma nondegenerate' {S : PreCCSystem α} {p q : α} :
    ¬S.cc p p q :=
  S.toWeakCCSystem.nondegenerate'

lemma nondegenerate'' {S : PreCCSystem α} {p q : α} :
    ¬S.cc p q q :=
  S.toWeakCCSystem.nondegenerate''
end PreCCSystem

private lemma imp_eq_or {p q : Prop} : (p → q) = (¬p ∨ q) := by
  grind

lemma WeakPreCCSystem.vortexFree (S : WeakPreCCSystem α) :
    S.cc.VortexFree := by
  intro t p q r s hpnes hpner hpnet hqnes hqnet hrnes hrnet hsnet
  have PT := @S.transitive p r t q s hpner
  have DT := @S.dualTransitive p q r s t hpner
  repeat rw [imp_eq_or] at PT DT
  grind [S.of_ne_antisymm]

-- lemma antisymm_of_vortexFree {cc : CC α} (hs : VortexFree cc) : Antisymmetric cc := by
--   intro p q r hpqr hprq
--   simp only [VortexFree] at hs
--   sorry

end AxiomsAndHulls

