-- import Mathlib
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.ByContra

import OrientedMatroids.AxiomsAndHulls.Tactic

namespace AxiomsAndHulls

universe u
variable {α : Type u}


namespace PreCCSystem
lemma antisymmetry' (S : PreCCSystem α) :
    ∀ {p q r : α}, p ≠ q → p ≠ r → q ≠ r → ¬ S.cc p q r → S.cc p r q :=
  fun hpneq hpner hqner hnot_pqr ↦ S.total hpneq hqner hpner |>.resolve_left hnot_pqr

lemma nondegenerate' {S : PreCCSystem α} {p q : α} :
    ¬S.cc p p q := by grind only [S.nondegenerate]

lemma nondegenerate'' {S : PreCCSystem α} {p q : α} :
    ¬S.cc p q q := by grind only [S.nondegenerate]
end PreCCSystem

@[grind .]
lemma ne_of_cc {S : PreCCSystem α} {p q r : α} (h : S.cc p q r) : p ≠ q := by
  exact S.nondegenerate h |>.1

@[grind .]
lemma ne_of_cc' {S : PreCCSystem α} {p q r : α} (h : S.cc p q r) : q ≠ r := by
  exact S.nondegenerate h |>.2.1

@[grind .]
lemma ne_of_cc'' {S : PreCCSystem α} {p q r : α} (h : S.cc p q r) : p ≠ r := by
  exact S.nondegenerate h |>.2.2

private lemma dualTransitivity_of_transitivity_impl {S : PreCCSystem α} {p q r s : α} (t : α)
    (hsner : s ≠ r)
    (hpqt : S.cc p q t) (hpst : S.cc p s t) (hptr : S.cc p t r)
    (htqr : S.cc t q r) (hstr : S.cc s t r) (hstq : S.cc s t q) :
    S.cc s p q → S.cc s r p := by
  intro hspq
  if hpqr : S.cc p q r then
    suffices S.cc p s r by cyclic_nf_v2
    refine S.transitive t q hsner ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf_v2
  else
    by_contra hnotsrp
    have hprq : S.cc p r q := by grind only [ne_of_cc'', ne_of_cc', S.total]
    have hspr : S.cc s p r := by grind only [ne_of_cc'', ne_of_cc, S.total]
    by_cases S.cc r q s
    · case pos hrqs =>
        suffices S.cc q r p by exact hpqr <| by cyclic_nf_v2
        have hrnep : r ≠ p := Ne.symm <| ne_of_cc hprq
        have hpneq : p ≠ q := ne_of_cc hpqt
        have hqner : q ≠ r := Ne.symm <| ne_of_cc hrqs
        refine S.transitive t s hrnep ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf_v2
    · case neg hnotrqs =>
        have hrsq : S.cc r s q := by grind only [ne_of_cc'', ne_of_cc', S.total]
        have hnotrqt : ¬S.cc r q t := S.antisymm (by cyclic_nf_v2)
        have : S.cc r t q := by grind only [ne_of_cc'', ne_of_cc', S.total]
        refine hnotrqt ?_ |>.elim
        have hqnet : q ≠ t := by grind only
        have htner : t ≠ r := by grind only
        refine S.transitive p s hqnet ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf_v2

lemma PreCCSystem.dualTransitivity (S : PreCCSystem α) :
    DualTransitivy S.cc := by
  intro p q r s t ⟨hstp, hstq, hstr, htpq, htqr⟩
  by_contra
  have htrp : S.cc t r p := by grind only [ne_of_cc'', ne_of_cc', S.total, S.antisymm]
  have H1 : S.cc s p q → S.cc s r p := by
    refine dualTransitivity_of_transitivity_impl t (by grind)  ?_ ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf_v2
  have H2 : S.cc s r p → S.cc s q r := by
    refine dualTransitivity_of_transitivity_impl t (by grind) ?_ ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf_v2
  have H3 : S.cc s q r → S.cc s p q := by
    refine dualTransitivity_of_transitivity_impl t (by grind) ?_ ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf_v2
  if hspq : S.cc s p q then
    have hsqr : S.cc s q r := H2 <| H1 hspq
    have hspr : S.cc s p r := by refine S.transitive q t (by grind) ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf_v2
    grind [S.total, S.antisymm]
  else
    have hsqp : S.cc s q p := by grind [S.total, S.antisymm]
    have hprs : S.cc s p r := by grind [S.total, S.antisymm]
    suffices S.cc s q r by grind [S.total, S.antisymm]
    refine S.transitive p t (by grind) ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf_v2

end AxiomsAndHulls

#min_imports

