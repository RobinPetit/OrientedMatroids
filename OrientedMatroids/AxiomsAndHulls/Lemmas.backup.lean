-- import Mathlib
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.ByContra

import OrientedMatroids.AxiomsAndHulls.Tactic

namespace AxiomsAndHulls

universe u
variable {α : Type u}


lemma PreCCSystem.antisymmetry' (S : PreCCSystem α) :
    ∀ {p q r : α}, p ≠ q → p ≠ r → q ≠ r → ¬ S.cc p q r → S.cc p r q :=
  fun hpneq hpner hqner hnot_pqr ↦ S.total hpneq hqner hpner |>.resolve_left hnot_pqr

-- lemma PreCCSystem.cyclic' (S : PreCCSystem α) {p q r : α} :
--     S.cc p q r ↔ S.cc q r p :=
--   ⟨S.cyclic, fun h ↦ S.cyclic <| S.cyclic h⟩

lemma PreCCSystem.cyclic_eq (S : PreCCSystem α) {p q r : α} :
    S.cc p q r = S.cc q r p :=
  propext ⟨cyclic', (cyclic' <| cyclic' ·)⟩

@[grind .]
lemma ne_of_cc {S : PreCCSystem α} {p q r : α} (h : S.cc p q r) : p ≠ q := by
  exact S.nondegenerate h |>.1

@[grind .]
lemma ne_of_cc' {S : PreCCSystem α} {p q r : α} (h : S.cc p q r) : q ≠ r := by
  exact S.nondegenerate h |>.2.1

@[grind .]
lemma ne_of_cc'' {S : PreCCSystem α} {p q r : α} (h : S.cc p q r) : p ≠ r := by
  exact S.nondegenerate h |>.2.2

lemma PreCCSystem.dualTransitivity (S : PreCCSystem α) :
    DualTransitivy S.cc := by
  intro p q r s t ⟨hstp, hstq, hstr, htpq, htqr⟩
  -- have : ¬S.cc r q p := sorry
  have : S.cc t p s := by cyclicity_v3
  have : S.cc t p s := by cyclic_nf_v2
  cyclic_nf_v2
  sorry
  --have hpneq : p ≠ q := ne_of_cc htpq
  --if hpr : p = r then
  --  subst hpr; cyclic_nf
  --  -- TODO: by_antisymm
  --  sorry
  --  exact S.antisymm htpq (hpr ▸ htqr) |>.elim
  --else
  --  by_contra hnot_tpr
  --  have htrp : S.cc t r p :=
  --    S.total (ne_of_cc' hstr) (Ne.symm hpr) (ne_of_cc htpq) |>.resolve_right hnot_tpr
  --  have : S.cc s p q → S.cc s r p := by
  --    intro hspq
  --    by_cases hpqr : S.cc p q r
  --    · refine S.cyclic ?_
  --      have hpqs := by cyclicity hspq
  --      have hpqt : S.cc p q t := by cyclicity htpq
  --      have hpst : S.cc p s t := by cyclicity hstp
  --      have hptr : S.cc p t r := by cyclicity htrp
  --      refine S.transitive ?_ hpqs hpqt hpqr hpst hptr
  --      exact ne_of_cc'' hstr
  --    · have hprq : S.cc p r q := by
  --        refine S.total hpr ?_ hpneq |>.resolve_right hpqr
  --        exact Ne.symm (ne_of_cc' htqr)
  --      by_cases hspr : S.cc s p r
  --      · have hrqs : S.cc r q s := by
  --          by_contra
  --          have hrsq : S.cc r s q := by
  --            refine S.antisymmetry' ?_ ?_ ?_ this <;> grind only [ne_of_cc'']
  --          have hrsp : S.cc r s p := by cyclicity hspr
  --          have hrqt : S.cc r q t := by
  --            refine S.transitive (ne_of_cc htqr).symm hrsq hrsp ?_ ?_ ?_
  --            · cyclicity hstr
  --            · cyclicity hprq
  --            · refine S.cyclic <| S.antisymmetry' ?_ ?_ ?_ hnot_tpr <;> grind only [ne_of_cc'']
  --          exact S.antisymm hrqt (S.cyclic2 htqr) |>.elim
  --        have :=
  --          have hqsr : S.cc q s r := by cyclicity hrqs
  --          have hqst : S.cc q s t := by cyclicity hstq
  --          have hqsp : S.cc q s p := by cyclicity hspq
  --          have hqrt : S.cc q r t := by cyclicity htqr
  --          have hqtp : S.cc q t p := by cyclicity htpq
  --          S.transitive (Ne.symm hpr) hqsr hqst hqsp hqrt hqtp
  --        exact hpqr (S.cyclic2 this) |>.elim
  --      · refine S.antisymmetry' ?_ ?_ ?_ hspr <;> grind only [ne_of_cc'']
  --  sorry

end AxiomsAndHulls

#min_imports

