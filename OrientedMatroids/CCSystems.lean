/-
Copyright (c) 2026 Jean Cardinal & Robin Petit. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Cardinal, Robin Petit
-/

import OrientedMatroids.AxiomsAndHulls.Defs
import OrientedMatroids.Lemmas
import OrientedMatroids.Det

/-!
DOCSTRING: TODO
-/

variable {α : Type*}

open AxiomsAndHulls
open Orientation

def v3 (a b c : α) : Fin 3 → α
  | 0 => a
  | 1 => b
  | 2 => c

private lemma v3_eq {a b c : α} : v3 a b c = c2 (fun _ ↦ a) b c := by
  ext i; fin_cases i <;> simp [v3, c2, append]

lemma v3_eq_expanded {v : Fin 3 → α} : v3 (v 0) (v 1) (v 2) = v := by
  ext i; fin_cases i <;> simp [v3]

lemma v3_injective_of_ne_of_ne_of_ne {p q r : α} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (v3 p q r).Injective := by
  intro i j; simp only [v3]; grind

lemma v3_not_inj_of_eq_01 {p q r : α} (hpq : p = q) : ¬(v3 p q r).Injective := by
  simp only [Function.Injective, not_forall]
  refine ⟨0, 1, by simp [v3, hpq], by simp⟩

lemma v3_not_inj_of_eq_02 {p q r : α} (hpr : p = r) : ¬(v3 p q r).Injective := by
  simp only [Function.Injective, not_forall]
  refine ⟨0, 2, by simp [v3, hpr], by simp⟩

namespace Equiv
private lemma Perm.sign_eq_pos_iff {σ : Equiv.Perm (Fin 3)} :
    σ.sign = 1 ↔
      (σ = 1 ∨ σ = Equiv.swap 0 1 * Equiv.swap 1 2 ∨ σ = Equiv.swap 1 2 * Equiv.swap 0 1) := by
  decide +revert

private lemma Perm.sign_eq_neg_iff {σ : Equiv.Perm (Fin 3)} :
    σ.sign = -1 ↔
      (σ = Equiv.swap 0 1 ∨ σ = Equiv.swap 0 2 ∨ σ = Equiv.swap 1 2) := by
  decide +revert

private lemma Perm.sign_eq_pos_or_neg {σ : Equiv.Perm (Fin 3)} :
    σ.sign = 1 ∨ σ.sign = -1 :=
  Int.units_eq_one_or _
end Equiv

private def cycle : Equiv.Perm (Fin 3) :=
  Equiv.swap 1 2 * Equiv.swap 0 1

lemma Orientation.cyclic {χ : Orientation 3 α} (ha : Alternating χ) {a b c : α} :
    χ (v3 a b c) = χ (v3 b c a) := by
  suffices v3 a b c = (v3 b c a) ∘ cycle by
    rw [this, ha]
    suffices cycle.sign' = 1 by simp [this]
    simp [cycle, Equiv.Perm.sign']
  ext i
  fin_cases i <;> { simp [v3, cycle]; try grind }

lemma Orientation.antisymmetric {χ : Orientation 3 α} (ha : Alternating χ) {a b c : α} :
    χ (v3 a b c) = -χ (v3 a c b) := by
  suffices (v3 a c b) = (v3 a b c) ∘ Equiv.swap 1 2 by
    rw [this, ha]
    simp [Equiv.Perm.sign']
  ext i; fin_cases i <;> { simp [v3]; try grind }

lemma Orientation.antisymmetric' {χ : Orientation 3 α} (ha : Alternating χ) {a b c : α} :
    χ (v3 a b c) = -χ (v3 b a c) := by
  suffices (v3 b a c) = (v3 a b c) ∘ Equiv.swap 0 1 by
    rw [this, ha]
    simp [Equiv.Perm.sign']
  ext i; fin_cases i <;> { simp [v3]; try grind }

lemma Orientation.antisymmetric'' {χ : Orientation 3 α} (ha : Alternating χ) {a b c : α} :
    χ (v3 a b c) = -χ (v3 c b a) := by
  suffices (v3 c b a) = (v3 a b c) ∘ Equiv.swap 0 2 by
    rw [this, ha]
    simp [Equiv.Perm.sign']
  ext i; fin_cases i <;> { simp [v3]; try grind }

private lemma Orientation.zero_of_duplicate {χ : Orientation 3 α} (ha : Alternating χ) {a b : α} :
    χ (v3 a a b) = 0 :=
  SignType.neg_eq_self_iff.mp <| χ.antisymmetric' ha |>.symm

private lemma Orientation.zero_of_duplicate' {χ : Orientation 3 α} (ha : Alternating χ) {a b : α} :
    χ (v3 a b a) = 0 :=
  SignType.neg_eq_self_iff.mp (χ.antisymmetric'' ha).symm

private lemma Orientation.zero_of_duplicate'' {χ : Orientation 3 α} (ha : Alternating χ) {a b : α} :
    χ (v3 b a a) = 0 :=
  SignType.neg_eq_self_iff.mp (χ.antisymmetric ha).symm

instance {α : Type*} : Coe (KOM 3 α) (PreCCSystem α) := by
  refine ⟨fun S ↦ ?_⟩
  refine ⟨fun p q r ↦ S.χ (v3 p q r) > 0, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Cyclic]
    intro p q r hpqr
    exact lt_of_lt_of_eq hpqr (S.χ.cyclic S.alternating)
  · simp only [Antisymmetric, gt_iff_lt, SignType.pos_iff]
    intro p q r hpqr
    rw [Orientation.antisymmetric S.alternating, hpqr]
    simp
  · intro p q r hpqr
    grind [zero_of_duplicate S.alternating, zero_of_duplicate' S.alternating,
      zero_of_duplicate'' S.alternating]
  · intro p r t q s hpner
    simp only [gt_iff_lt, SignType.pos_iff]
    intro htsp htsq htsr htpq htqr
    simp only [v3_eq] at *
    exact S.transitive q s hpner htsp htsq htsr htpq htqr
  · intro p q r hpneq hqner hpner
    simp only [gt_iff_lt, SignType.pos_iff]
    have := S.uniform (v3 p q r) |>.mpr (by intro i j; simp only [v3]; grind)
    cases hpqr : S.χ (v3 p q r)
    · simp_all only [ne_eq, SignType.zero_eq_zero, not_true_eq_false]
    · simp_all only [ne_eq, SignType.neg_eq_neg_one]
      refine Or.inr ?_
      rw [S.χ.antisymmetric S.alternating, hpqr, neg_neg]
    · simp only [SignType.pos_eq_one, true_or]

private lemma nondegenerate01 {S : PreCCSystem α} {p q : α} :
    ¬S.cc p p q := by
  grind [S.nondegenerate]

private lemma nondegenerate02 {S : PreCCSystem α} {p q : α} :
    ¬S.cc p q p := by
  grind [S.nondegenerate]

private lemma nondegenerate12 {S : PreCCSystem α} {p q : α} :
    ¬S.cc p q q:= by
  grind [S.nondegenerate]

private lemma cc_ne_of_swap01 {S : PreCCSystem α} {v : Fin 3 → α}
    (hv : v.Injective) :
    S.cc ((v ∘ Equiv.swap 0 1) 0) ((v ∘ Equiv.swap 0 1) 1) ((v ∘ Equiv.swap 0 1) 2)
      = ¬S.cc (v 0) (v 1) (v 2) := by
  have hvinj' : v 0 ≠ v 1 ∧ v 0 ≠ v 2 ∧ v 1 ≠ v 2 := by grind
  simp only [Equiv.swap, Fin.isValue, Equiv.coe_fn_mk, Function.comp_apply, Equiv.swapCore,
    ↓reduceIte, one_ne_zero, Fin.reduceEq, eq_iff_iff]
  refine ⟨fun h102 h012 ↦ S.antisymm h102 <| S.cyclic h012, ?_⟩
  · refine fun h012 ↦ S.cyclic2 ?_
    have := @S.total (v 0) (v 1) (v 2)
    simpa [hvinj', h012] using this

private lemma cc_ne_of_swap02 {S : PreCCSystem α} {v : Fin 3 → α}
    (hv : v.Injective) :
    S.cc ((v ∘ Equiv.swap 0 2) 0) ((v ∘ Equiv.swap 0 2) 1) ((v ∘ Equiv.swap 0 2) 2)
      = ¬S.cc (v 0) (v 1) (v 2) := by
  have hvinj' : v 0 ≠ v 1 ∧ v 0 ≠ v 2 ∧ v 1 ≠ v 2 := by grind
  simp only [Equiv.swap, Fin.isValue, Equiv.coe_fn_mk, Function.comp_apply, Equiv.swapCore,
    ↓reduceIte, one_ne_zero, Fin.reduceEq, eq_iff_iff]
  refine ⟨fun h210 h012 ↦ S.antisymm h210 <| S.cyclic2 h012, ?_⟩
  · refine fun h012 ↦ S.cyclic ?_
    have := @S.total (v 0) (v 1) (v 2)
    simpa [hvinj', h012] using this


private lemma cc_ne_of_swap12 {S : PreCCSystem α} {v : Fin 3 → α}
    (hv : v.Injective) :
    S.cc ((v ∘ Equiv.swap 1 2) 0) ((v ∘ Equiv.swap 1 2) 1) ((v ∘ Equiv.swap 1 2) 2)
      = ¬S.cc (v 0) (v 1) (v 2) := by
  have hvinj' : v 0 ≠ v 1 ∧ v 0 ≠ v 2 ∧ v 1 ≠ v 2 := by grind
  simp only [Equiv.swap, Fin.isValue, Equiv.coe_fn_mk, Function.comp_apply, Equiv.swapCore,
    zero_ne_one, ↓reduceIte, Fin.reduceEq, eq_iff_iff]
  refine ⟨fun h021 h012 ↦ S.antisymm h021 h012, ?_⟩
  · refine fun h012 ↦ ?_
    have := @S.total (v 0) (v 1) (v 2)
    simpa [hvinj', h012] using this

private lemma cc_eq_of_perm_of_sign_one {S : PreCCSystem α} {σ : Equiv.Perm (Fin 3)}
    (hσsign : σ.sign = 1) {v : Fin 3 → α} :
    S.cc (v 0) (v 1) (v 2) = S.cc ((v ∘ σ) 0) ((v ∘ σ) 1) ((v ∘ σ) 2) := by
  rcases σ.sign_eq_pos_iff.mp hσsign with hσ | hσ | hσ
  all_goals try simp only [Fin.isValue, hσ, Equiv.swap, Equiv.Perm.coe_mul, Equiv.coe_fn_mk,
    Function.comp_apply, Equiv.swapCore, zero_ne_one, ↓reduceIte, Fin.reduceEq, one_ne_zero,
    eq_iff_iff, Equiv.Perm.coe_one, id_eq]
  · exact ⟨S.cyclic, S.cyclic2⟩
  · exact ⟨S.cyclic2, S.cyclic⟩

private lemma not_symm {p q : Prop} : (p = ¬q) ↔ ((¬p) = q) := by grind

private lemma cc_ne_of_perm_of_sign_neg_one {S : PreCCSystem α} {σ : Equiv.Perm (Fin 3)}
    (hσsign : σ.sign = -1) {v : Fin 3 → α} (hv : v.Injective) :
    S.cc (v 0) (v 1) (v 2) = ¬S.cc (v <| σ 0) (v <| σ 1) (v <| σ 2) := by
  rcases σ.sign_eq_neg_iff.mp hσsign with hσ | hσ | hσ
  · rw [hσ, not_symm, ← cc_ne_of_swap01 hv]; simp
  · rw [hσ, not_symm, ← cc_ne_of_swap02 hv]; simp
  · rw [hσ, not_symm, ← cc_ne_of_swap12 hv]; simp

private lemma _c2_eq_v3 {t : Fin (3 - 2) → α} {p q : α} : c2 t p q = v3 (t 0) p q := by
  ext i; simp [c2, append, v3]; grind

private lemma _ite_of_ne {c1 c2 : Prop} [Decidable c1] [Decidable c2] {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) :
    ((if c1 then a else if c2 then b else c) = a) = c1 := by
  simp only [ite_eq_left_iff, eq_iff_iff]
  refine ⟨?_, fun h ↦ by simp [h]⟩
  by_contra
  simp only [Classical.not_imp] at this
  by_cases h2 : c2 <;> simp_all

private lemma _ite_of_ne' {c1 c2 : Prop} [Decidable c1] [Decidable c2] {a b c : α}
    (hab : a ≠ b) (hbc : b ≠ c) :
    ((if c1 then a else if c2 then b else c) = b) = (¬c1 ∧ c2) := by
  grind

noncomputable instance {α : Type*} : Coe (PreCCSystem α) (KOM 3 α) := by
  classical
  refine ⟨fun S ↦ ?_⟩
  refine ⟨fun v ↦ if ¬v.Injective then 0 else if S.cc (v 0) (v 1) (v 2) then 1 else -1, ?_, ?_, ?_⟩
  · intro σ v
    simp only [Fin.isValue, Function.comp_apply, Equiv.Perm.sign', SignType.pos_eq_one,
      SignType.neg_eq_neg_one, mul_ite, mul_one, mul_neg]
    rcases σ.sign_eq_pos_or_neg with hσpos | hσneg
    · simp [cc_eq_of_perm_of_sign_one hσpos, hσpos]
    · if hv : v.Injective then simp [cc_ne_of_perm_of_sign_neg_one hσneg hv, hσneg]
      else simp [hv]
  · intro v
    simp only [Fin.isValue, ite_not, SignType.zero_eq_zero, ne_eq, ite_eq_right_iff,
      Classical.not_imp, and_iff_left_iff_imp]
    intro hv
    by_cases h : S.cc (v 0) (v 1) (v 2) <;> simp [h]
  · intro t p r q s hpner
    simp only [_c2_eq_v3, Fin.isValue]
    if hinj : ¬Function.Injective (v3 (t 0) p r) then
      simp only [Function.Injective, Fin.isValue, not_forall] at hinj
      obtain ⟨i, j, heq, hinej⟩ := hinj
      have : t 0 = p ∨ t 0 = r := by simp [v3] at heq; grind
      rcases this with h | h <;> simp [v3_not_inj_of_eq_01 h, v3_not_inj_of_eq_02 h]
    else
      simp only [Fin.isValue, Decidable.not_not] at hinj
      have H : (0 : SignType) ≠ (1 : SignType) := zero_ne_one' SignType
      have H' : (1 : SignType) ≠ (-1 : SignType) := not_eq_of_beq_eq_false rfl
      repeat rw [_ite_of_ne' H H']
      simp only [Fin.isValue, Decidable.not_not, c2, append, Fin.coe_ofNat_eq_mod, Nat.one_mod,
        Nat.add_one_sub_one, Order.lt_two_iff, Std.le_refl, ↓reduceDIte, lt_self_iff_false,
        Nat.mod_succ, hinj, not_true_eq_false, not_false_eq_true, true_and, and_imp]
      intro _ htsp _ htsq _ htsr _ htpq _ htqr
      exact S.transitive q s hpner htsp htsq htsr htpq htqr

noncomputable def KOM3_eq_PreCCSystem : (KOM 3 α) ≃ (PreCCSystem α) := by
  refine ⟨(·), (·), ?_, ?_⟩
  · intro S
    ext v
    cases hχv : S.χ v
    · simp only [Fin.isValue, gt_iff_lt, SignType.pos_iff, ite_not, SignType.zero_eq_zero,
        ite_eq_right_iff]
      exact (S.uniform v |>.mpr · hχv |>.elim)
    all_goals { have := S.uniform v|>.mp; simp [hχv] at this; simp [this, hχv, v3_eq_expanded]}
  · intro S
    ext p q r
    refine ⟨?_, ?_⟩
    · intro hpqr
      suffices (v3 p q r).Injective by
        by_contra hpqr'
        simp [hpqr', this, v3] at hpqr
      have := PreCCSystem.nondegenerate _ hpqr
      refine v3_injective_of_ne_of_ne_of_ne ?_ ?_ ?_ <;> grind only
    · intro hpqr
      suffices (v3 p q r).Injective by
        simp [hpqr, this, v3]
      have := S.nondegenerate hpqr
      refine v3_injective_of_ne_of_ne_of_ne ?_ ?_ ?_ <;> grind only
