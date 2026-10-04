/-
Copyright (c) 2026 Jean Cardinal & Robin Petit. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Cardinal, Robin Petit
-/

import OrientedMatroids.Basic
import OrientedMatroids.Fin
import OrientedMatroids.Tactic

/-!
DOCSTRING: TODO
-/

lemma Function.injective_iff {α β : Type*} [LinearOrder α] {f : α → β} :
    f.Injective ↔ ∀ i j, i < j → f i ≠ f j := by
  refine ⟨?_, ?_⟩
  · intro hfinj i j hiltj heq
    exact ne_of_lt hiltj <| hfinj heq
  · intro h i j heq
    by_contra
    rcases lt_or_gt_of_ne this with hij | hji
    · exact h i j hij heq
    · exact h j i hji heq.symm

variable {α : Type*} {d : ℕ}

private lemma pos_or_neg_of_ne_zero {x : SignType} (hx : x ≠ 0) :
    x = -1 ∨ x = 1 := by
  cases x <;> simp_all

lemma c2_injective_of_diff_of_ne_of_ne {t : Fin (d - 2) → α} {a b : α}
    (htinj : t.Injective) (h : ∀ i, t i ≠ a ∧ t i ≠ b) (hab : a ≠ b) : (c2 t a b).Injective := by
  intro i j
  simp only [c2, append]
  split_ifs <;> grind

open AtLeast

-- we can move from c2 to c3
lemma c2_eq_c3_of_pref {h : d - 2 ≠ 0} (t : Fin (d - 2) → α) (a b : α) :
    c2 t a b = c3 (pref t) (t ⟨d - 3, by lia⟩) a b := by
  unfold c3 c2 append pref
  ext i
  simp only [Nat.sub_eq, Nat.pred_eq_sub_one]
  split_ifs
  all_goals try rfl
  exact congrArg _ (by grind)

lemma c3_eq_c2_of_append (t : Fin (d - 3) → α) (a b c : α) :
    c3 t a b c = c2 (append t a) b c := by
  ext i; simp [c3, c2, append]; grind

lemma c3_eq {t : Fin (d - 3) → α} {a b c : α} : c3 t a b c = c2 (append t a) b c := by
  unfold c3 c2
  rfl

-- if we take the prefix and append back the last element, then nothing changes
lemma pref_append [AtLeastOne d] {t : Fin d → α} :
    append (pref t) (t ⟨d - 1, sub_one_lt⟩) = t := by
  unfold pref append
  ext i
  split_ifs <;> grind

lemma pref_append' [AtLeastOne d] {t : Fin d → α} {i : Fin d} (hi : i = ⟨d - 1, sub_one_lt⟩) :
    append (pref t) (t i) = t := by
  rw [hi, pref_append]

theorem c2pref2_eq [AtLeastThree d] (t : Fin d → α) :
    c2 (pref2 t) (t ⟨d - 2, sub_two_lt⟩) (t ⟨d - 1, sub_one_lt⟩) = t := by
  ext i
  simp only [c2, append, pref2, Fin.eta, dite_eq_ite]
  split_ifs <;> grind only

theorem pref2_c2_eq (t : Fin (d - 2) → α) {a b : α} :
    pref2 (c2 t a b) = t := by
  ext i
  simp only [pref2, c2, append]
  split_ifs <;> grind

-- if we append an element then take the prefix, nothing changes
lemma append_pref (t : Fin (d - 1) → α) (e : α) :
    pref (append t e) = t := by
  unfold append pref
  simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]

lemma others_pref [AtLeastOne d] {t : Fin d → α} {i : Fin (d - 1)} :
    pref t i = t i := by
  simp only [pref]

section
variable {t : Fin (d - 1) → α} {a : α}

@[simp]
lemma last_append [AtLeastOne d] : append t a ⟨d - 1, sub_one_lt⟩ = a := by
  simp
@[simp]
lemma last_append' [AtLeastOne d] {i : Fin d} (hi : i = ⟨d - 1, sub_one_lt⟩) :
    append t a i = a := by
  grind

@[simp]
lemma others_append {i : Fin d} (hi : i < d - 1) : append t a i = t ⟨i, hi⟩ := by
  simp only [append, hi, ↓reduceDIte]
end

section
variable {t : Fin (d - 2) → α} {a b : α}

@[simp]
lemma others_c2 {i : Fin d} (hi : i < d - 2) : (c2 t a b) i = t ⟨i, hi⟩ := by
  unfold c2 append
  split_ifs <;> grind only

variable [AtLeastTwo d]

@[simp]
lemma last : (c2 t a b) ⟨d - 1, sub_one_lt⟩ = b := by grind
lemma last' {i : Fin d} (hi : i = ⟨d - 1, sub_one_lt⟩) : c2 t a b i = b := by
  rw [hi, last]

@[simp]
lemma penultimate : (c2 t a b) ⟨d - 2, sub_two_lt⟩ = a := by
  simp [c2, append, ← Nat.sub_succ']
lemma penultimate' {i : Fin d} (hi : i = ⟨d - 2, sub_two_lt⟩) : c2 t a b i = a := by
  rw [hi, penultimate]
end

section
variable {t : Fin (d - 3) → α} {a b c : α}

lemma others_c3 {t : Fin (d - 3) → α} {i : Fin d} (hi : i < d - 3) {c : α} :
    (c3 t a b c) i = t ⟨i, hi⟩ := by
  simp only [c3, append]
  split_ifs
  · exact others_c2 _
  · grind

variable [AtLeastThree d]

@[simp]
lemma antepenultimate : c3 t a b c ⟨d - 3, sub_three_lt⟩ = a := by
  simp only [c3, append]
  split_ifs with h
  · rw [penultimate']
    grind only
  · simp only [not_lt, tsub_le_iff_right] at h
    have : d < d := by
      refine lt_of_le_of_lt (le_of_le_of_eq h ?_) sub_two_lt
      exact Eq.symm (Nat.eq_add_of_sub_eq AtLeast.le rfl)
    grind only

lemma antepenultimate' {i : Fin d} (hi : i = ⟨d - 3, sub_three_lt⟩) : c3 t a b c i = a := by
  rw [hi, antepenultimate]

lemma penultimate_c3 {i : Fin d} (hi : i = ⟨d - 2, sub_two_lt⟩) : c3 t a b c i = b := by
  simp [hi]
  grind

lemma last_c3 {i : Fin d} (hi : i = ⟨d - 1, sub_one_lt⟩) : c3 t a b c i = c := by
  simp [hi]
end


section
variable {t : Fin (d - 2) → α} {a b c : α}
variable [inst : AtLeastThree d]
lemma pref_and_last_eq_c2 : c2 t a b = c3 (pref t) (t ⟨d - 3, inst.sub_three_lt_sub_two⟩) a b := by
  ext i
  if hi : i < d - 3 then
    have hi' : i < d - 2 := Nat.lt_of_lt_pred hi
    rw [others_c3 hi, others_c2 hi']
    simp only [pref]
  else if hi' : i < d - 2 then
    have : i = ⟨d - 3, sub_three_lt⟩ := by grind
    rw [others_c2 hi', antepenultimate' this]
    simp_all only [lt_self_iff_false, not_false_eq_true]
  else if i < d - 1 then
    have : i = ⟨d - 2, sub_two_lt⟩ := by grind
    rw [penultimate' this, penultimate_c3 this]
  else
    have : i = ⟨d - 1, sub_one_lt⟩ := by grind
    rw [last' this, last_c3 this]

end

namespace Orientation

variable {α : Type*} {d : ℕ}

lemma c2_uniform (χ : Orientation d α) (hu : Uniformity χ) {x : Fin (d - 2) → α} {p q : α}
    (hxrs : ∀ i, (x i ≠ p ∧ x i ≠ q)) (hrs : p ≠ q) (hx : x.Injective) :
    χ (c2 x p q) ≠ 0 := by
  refine hu _ |>.mpr ?_
  intro i j
  simp only [c2, append]
  split_ifs
  any_goals grind

lemma pref_injective_of_χ_ne_zero (χ : Orientation d α) (hu : Uniformity χ) {x : Fin d → α}
    (hχ : χ x ≠ 0) : (pref x).Injective := by
  intro i j hxij
  simp only [pref] at hxij
  grind [hu _ |>.mp hχ hxij]

lemma pref2_injective_of_χ_ne_zero (χ : Orientation d α) (hu : Uniformity χ) {x : Fin d → α}
    (hχ : χ x ≠ 0) : (pref2 x).Injective := by
  intro i j hxij
  simp only [pref2] at hxij
  grind [hu _ |>.mp hχ hxij]

lemma pref2_of_c2_injective_of_χ_ne_zero (χ : Orientation d α) (hu : Uniformity χ)
    {x : Fin (d - 2) → α} {p q : α} (hχ : χ (c2 x p q) ≠ 0) : x.Injective := by
  have := χ.pref2_injective_of_χ_ne_zero hu hχ
  rw [pref2_c2_eq] at this
  exact this

lemma pref2_of_c2_injective_of_χ_pos (χ : Orientation d α) (hu : Uniformity χ)
    {x : Fin (d - 2) → α} {p q : α} (hχ : χ (c2 x p q) = 1) : x.Injective :=
  χ.pref2_of_c2_injective_of_χ_ne_zero hu (by simp [hχ] : χ (c2 x p q) ≠ 0)

lemma pref2_of_c2_injective_of_χ_neg (χ : Orientation d α) (hu : Uniformity χ)
    {x : Fin (d - 2) → α} {p q : α} (hχ : χ (c2 x p q) = -1) : x.Injective :=
  χ.pref2_of_c2_injective_of_χ_ne_zero hu (by simp [hχ] : χ (c2 x p q) ≠ 0)

lemma pref3_of_c3_injective_of_χ_ne_zero (χ : Orientation d α) (hu : Uniformity χ)
    {x : Fin (d - 3) → α} {p q r : α} (hχ : χ (c3 x p q r) ≠ 0) : x.Injective := by
  intro i j heq
  have : c3 x p q r i = c3 x p q r j := by
    rw [others_c3, others_c3, heq]
    simp only [Fin.is_lt]
  have := hu (c3 x p q r) |>.mp hχ this
  refine Fin.eq_of_val_eq <| by simpa only [Fin.mk.injEq] using this

lemma pref3_of_c3_injective_of_χ_pos (χ : Orientation d α) (hu : Uniformity χ)
    {x : Fin (d - 3) → α} {p q r : α} (hχ : χ (c3 x p q r) = 1) : x.Injective :=
  χ.pref3_of_c3_injective_of_χ_ne_zero hu (ne_zero_of_eq_one hχ)

lemma pref3_of_c3_injective_of_χ_neg (χ : Orientation d α) (hu : Uniformity χ)
    {x : Fin (d - 3) → α} {p q r : α} (hχ : χ (c3 x p q r) = -1) : x.Injective :=
  χ.pref3_of_c3_injective_of_χ_ne_zero hu (by simp [hχ] : χ (c3 x p q r) ≠ 0)

lemma x_eq_tail_of_χ_eq_zero_of_x_injective (χ : Orientation d α)
    (hu : Uniformity χ) {x : Fin (d - 2) → α} {p q : α} (hχ : χ (c2 x p q) = 0) (hx : x.Injective) :
    p = q ∨ ∃ i, (x i = p ∨ x i = q) := by
  by_contra this
  simp only [not_or, not_exists] at this
  obtain ⟨hpq, H⟩ := this
  exact c2_uniform χ hu H hpq hx hχ

variable [AtLeastThree d]

lemma eq_zero_of_non_inj (χ : Orientation d α) (hχ : Uniformity χ) {x : Fin (d - 2) → α} {a : α} :
    χ (c2 x a a) = 0 := by
  have := hχ (c2 x a a) |>.mp |>.mt
  simp only [SignType.zero_eq_zero, ne_eq, Decidable.not_not] at this
  refine this ?_
  simp only [Function.Injective, not_forall]
  refine ⟨⟨d - 2, sub_two_lt⟩, ⟨d - 1, sub_one_lt⟩, ?_⟩
  rw [last, penultimate]
  exact ⟨rfl, by simp⟩

lemma eq_zero_of_non_inj' (χ : Orientation d α) (hχ : Uniformity χ) {x : Fin (d - 2) → α} {a b : α}
    (haeqb : a = b) : χ (c2 x a b) = 0 :=
  haeqb ▸ χ.eq_zero_of_non_inj hχ

lemma ne_of_χ_ne_zero (χ : Orientation d α) (hu : Uniformity χ) {x : Fin (d - 2) → α} {a b : α}
    (hχ : χ (c2 x a b) ≠ 0) : a ≠ b :=
  χ.eq_zero_of_non_inj' hu |>.mt hχ

private lemma lt_castAdd {a b c : ℕ} (h : a < b - c) : a < b :=
  lt_of_lt_of_le h <| b.sub_le c

lemma ne_of_χ_ne_zero' (χ : Orientation d α) (hu : Uniformity χ) {x : Fin (d - 2) → α} {a b : α}
    (hχ : χ (c2 x a b) ≠ 0) : ∀ i, (x i ≠ a ∧ x i ≠ b) := by
  intro i
  have := hu (c2 x a b) |>.mp hχ
  refine ⟨?_, ?_⟩
  · have := this |>.mt (by grind : (⟨i.1, lt_castAdd i.2⟩ : Fin d) ≠ ⟨d - 2, sub_two_lt⟩)
    rw [penultimate, others_c2 (by simp)] at this
    simpa only [ne_eq, Fin.eta] using this
  · have := this |>.mt (by grind : (⟨i.1, lt_castAdd i.2⟩ : Fin d) ≠ ⟨d - 1, sub_one_lt⟩)
    rw [last, others_c2 (by simp)] at this
    simpa only [ne_eq, Fin.eta] using this

end Orientation

open Equiv
open SignType
open AtLeastThree

@[simp] lemma int_unit_ne_neg_unit : -1 ≠ (1 : ℤˣ) := Int.units_ne_iff_eq_neg.mpr rfl

lemma flip_12 [AtLeastThree d] {χ : Orientation d α} (ha : Alternating χ)
    {t : Fin (d - 2) → α} {a b : α} :
    χ (c2 t b a) = - χ (c2 t a b) := by
  classical
  let σ : Perm (Fin d) := swap ⟨d - 2, sub_two_lt⟩ ⟨d - 1, sub_one_lt⟩
  have hl : c2 t b a = (c2 t a b) ∘ σ  := by
    ext i
    simp only [Function.comp_apply, σ, c2, append]
    split_ifs
    any_goals grind
    have : i = ⟨d - 1, sub_one_lt⟩ := Fin.eq_mk_iff_val_eq.mpr <| by lia
    simp_all
  have hr : σ.sign' * χ (c2 t a b) = -χ (c2 t a b) := by
    simp_rw [Perm.sign', σ]
    simp
  rw [hl, ha σ (c2 t a b), hr]

lemma flip_12' [AtLeastThree d] {χ : Orientation d α} (ha : Alternating χ)
    {t : Fin (d - 3) → α} {a b c : α} :
    χ (c3 t a c b) = - χ (c3 t a b c) := by
  rw [c3_eq_c2_of_append, c3_eq_c2_of_append, flip_12 ha]

lemma Orientation.swap [AtLeastThree d] (χ : Orientation d α) (ha : Alternating χ)
    {t : Fin (d - 2) → α} {a b : α} (hχ : χ (c2 t a b) = -1) : χ (c2 t b a) = 1 := by
  rw [flip_12 ha]
  exact neg_eq_iff_eq_neg.mpr <| hχ

lemma Orientation.swap' [AtLeastThree d] (χ : Orientation d α) (ha : Alternating χ)
    {t : Fin (d - 2) → α} {a b : α} (hχ : χ (c2 t a b) = 1) : χ (c2 t b a) = -1 := by
  rw [flip_12 ha]
  simp only [hχ]

lemma KOM.injective_of_pos (S : KOM d α) {v : Fin d → α} (h : S.χ v = 1) : v.Injective := by
  refine S.uniform v |>.mp ?_
  simp [h]

lemma KOM.injective_of_neg (S : KOM d α) {v : Fin d → α} (h : S.χ v = -1) : v.Injective := by
  refine S.uniform v |>.mp ?_
  simp [h]

lemma KOM.swap [AtLeastThree d] (S : KOM d α) {t : Fin (d - 2) → α} {a b : α}
    (hχ : S.χ (c2 t a b) = -1) : S.χ (c2 t b a) = 1 :=
  S.χ.swap S.alternating hχ

lemma KOM.swap' [AtLeastThree d] (S : KOM d α) {t : Fin (d - 2) → α} {a b : α}
    (hχ : S.χ (c2 t a b) = 1) : S.χ (c2 t b a) = -1 :=
  S.χ.swap' S.alternating hχ

lemma KOM.elim [AtLeastThree d] (S : KOM d α) {x : Fin (d - 2) → α} {a b : α}
    (h : S.χ (c2 x a b) = 1) (h' : S.χ (c2 x b a) = 1) {obj : Prop} : obj := by
  rw [flip_12 S.alternating, h] at h'
  simp at h'

lemma KOM.elim' [AtLeastThree d] (S : KOM d α) {x : Fin (d - 3) → α} {a b c : α}
    (h : S.χ (c3 x a b c) = 1) (h' : S.χ (c3 x a c b) = 1) {obj : Prop} : obj := by
  suffices S.χ (c3 x a c b) ≠ 1 by exact this h' |>.elim
  rw [flip_12' S.alternating, h]
  simp

lemma ne_of_c2 [AtLeastThree d] {x : Fin (d - 2) → α} {a b : α} (h : (c2 x a b).Injective) :
    ∀ i, (x i ≠ a ∧ x i ≠ b) := by
  intro i
  have hia := @h i (⟨d - 2, sub_two_lt⟩)
  have hib := @h i (⟨d - 1, sub_one_lt⟩)
  have hi' : i < d - 2 := i.isLt
  simp only [i.isLt, others_c2, Fin.eta, AtLeastTwo.sub_two_lt_sub_one, others_append, Fin.mk.injEq,
    i.ne, imp_false, last_append'] at hia hib
  grind only

lemma transitive_iff [AtLeastThree d] {S : KOM d α} :
    Transitivity S.χ ↔
    (∀ (x : Fin (d - 3) → α) (t s p q r : α),
      p ≠ r → S.χ (c3 x t s p) = 1 → S.χ (c3 x t s q) = 1 → S.χ (c3 x t s r) = 1 →
      S.χ (c3 x t p q) = 1 → S.χ (c3 x t q r) = 1 → S.χ (c3 x t p r) = 1) := by
  refine ⟨?_, ?_⟩
  · intro h x t s p q r hpner htsp htsq htsr htpq htqr
    rw [c3_eq_c2_of_append] at *
    exact h q s hpner htsp htsq htsr htpq htqr
  · intro h x p r q s hpner hsp hsq hsr hpq hqr
    have := h (pref x) (x ⟨d - 3, sub_three_lt_sub_two⟩) s p q r hpner
    repeat rw [c3_eq_c2_of_append, @pref_append' _ (d - 2) _ x _ (by grind)] at this
    exact this hsp hsq hsr hpq hqr

lemma dualTransitive_iff [AtLeastThree d] {S : KOM d α} :
    DualTransitivity S.χ ↔
    (∀ (x : Fin (d - 3) → α) (t s p q r : α),
      p ≠ r → S.χ (c3 x t p s) = 1 → S.χ (c3 x t q s) = 1 → S.χ (c3 x t r s) = 1 →
      S.χ (c3 x t p q) = 1 → S.χ (c3 x t q r) = 1 → S.χ (c3 x t p r) = 1) := by
  refine ⟨?_, ?_⟩
  · intro h x t s p q r hpner htps htqs htrs htpq htqr
    rw [c3_eq_c2_of_append] at *
    simp only [DualTransitivity] at h
    exact h q s hpner htps htqs htrs htpq htqr
  · intro h t p r q s hpner htps htqs htrs htpq htqr
    have := h (pref t) (t ⟨d - 3, sub_three_lt_sub_two⟩) s p q r hpner
    repeat rw [c3_eq_c2_of_append, @pref_append' _ (d - 2) _ t _ (by grind)] at this
    exact this htps htqs htrs htpq htqr

private lemma swap_compose [DecidableEq α] {i j k : α} (hik : i = k) : Equiv.swap j k i = j := by
  rw [hik]
  exact swap_apply_right j k

@[cyclic]
private lemma KOM.cyclic3_last [AtLeastThree d] {S : KOM d α} {v : Fin (d - 3) → α} {p q r : α} :
    S.χ (c3 v p q r) = S.χ (c3 v q r p) := by
  let τ23 := Equiv.swap (Fin.minus_two d) (Fin.minus_three d)
  let τ12 := Equiv.swap (Fin.minus_one d) (Fin.minus_two d)
  let σ := τ23 * τ12
  have := S.alternating σ (c3 v p q r)
  have hσsign : σ.sign' = 1 := by simp [Perm.sign', σ, τ12, τ23]
  simp only [hσsign, one_mul] at this
  rw [← this]
  refine congrArg _ ?_
  ext i
  simp only [Function.comp_apply]
  if hi : i < d - 3 then
    have hσi : i = σ i := by
      simp only [Perm.coe_mul, Function.comp_apply, σ, τ23, τ12]
      have : Equiv.swap (Fin.minus_one d) (Fin.minus_two d) i = i := by
        rw [swap_apply_of_ne_of_ne]
        <;> grind [Fin.minus_one, Fin.minus_two, AtLeastThree.sub_three_lt_sub_one]
      rw [this, swap_apply_of_ne_of_ne]
      <;> grind [Fin.minus_one, Fin.minus_two, Fin.minus_three, AtLeastThree.sub_three_lt_sub_one]
    rw [others_c3 hi, others_c3 (hσi ▸ hi)]
    refine congrArg _ (by simp only [← hσi])
  else if hidm3 : i = ⟨d - 3, sub_three_lt⟩ then
    rw [penultimate_c3, antepenultimate' hidm3]
    simp only [Fin.minus_two, Fin.minus_three, Fin.minus_one, hidm3, Perm.coe_mul,
      Function.comp_apply, σ, τ23, τ12]
    rw [swap_compose]
    rw [swap_apply_of_ne_of_ne] <;> grind
  else if hidm2 : i = ⟨d - 2, sub_two_lt⟩ then
    rw [last_c3, penultimate_c3 hidm2]
    simp only [Fin.minus_two, Fin.minus_three, Fin.minus_one, hidm2, Perm.coe_mul,
      Function.comp_apply, swap_apply_right, σ, τ23, τ12]
    rw [swap_apply_of_ne_of_ne] <;> grind
  else
    have : i = ⟨d - 1, sub_one_lt⟩ := by grind
    rw [antepenultimate', last_c3 this]
    simp [σ, τ12, τ23, Fin.minus_one, Fin.minus_two, Fin.minus_three, this]

lemma pref3_inj_of_inj {x : Fin (d - 3) → α} {p q r : α} (h : (c3 x p q r).Injective) :
    x.Injective := by
  intro i j heq
  have := @h i j
  grind

lemma pref3_inj_of_χ_ne_zero {x : Fin (d - 3) → α} {p q r : α} {S : KOM d α}
    (h : S.χ (c3 x p q r) ≠ 0) : x.Injective :=
  pref3_inj_of_inj <| S.uniform _ |>.mp h

lemma pref3_inj_of_χ_pos {x : Fin (d - 3) → α} {p q r : α} {S : KOM d α}
    (h : S.χ (c3 x p q r) = 1) : x.Injective :=
  pref3_inj_of_χ_ne_zero (ne_zero_of_eq_one h)

lemma pref3_inj_of_χ_neg {x : Fin (d - 3) → α} {p q r : α} {S : KOM d α}
    (h : S.χ (c3 x p q r) = -1) : x.Injective :=
  pref3_inj_of_χ_ne_zero (by simp [h] : S.χ (c3 x p q r) ≠ 0)

lemma tail_ne_of_χ_ne_zero [AtLeastThree d] {x : Fin (d - 3) → α} {p q r : α} {S : KOM d α}
    (h : S.χ (c3 x p q r) ≠ 0) :
    x.Injective ∧ (∀ i, (x i ≠ p ∧ x i ≠ q ∧ x i ≠ r)) ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r := by
  have : (c3 x p q r).Injective := S.uniform _ |>.mp h
  simp only [Function.Injective] at this
  have H : ∀ ⦃i j : Fin d⦄, i ≠ j → c3 x p q r i ≠ c3 x p q r j := by grind only
  have h1 := H Fin.minus_three_ne_minus_two
  have h2 := H Fin.minus_three_ne_minus_one
  have h3 := H Fin.minus_two_ne_minus_one
  simp only [Fin.minus_one, Fin.minus_two, Fin.minus_three, antepenultimate, penultimate_c3,
    last_c3] at h1 h2 h3
  suffices ∀ i, (x i ≠ p ∧ x i ≠ q ∧ x i ≠ r) by
    grind [pref3_inj_of_χ_ne_zero h]
  intro i
  have hi3 : (i : Fin d) ≠ ⟨d - 3, sub_three_lt⟩ := by grind
  have hi2 : (i : Fin d) ≠ ⟨d - 2, sub_two_lt⟩ := by grind
  have hi1 : (i : Fin d) ≠ ⟨d - 1, sub_one_lt⟩ := by grind
  grind [H hi1, H hi2, H hi3]

lemma tail_ne_of_χ_pos [AtLeastThree d] {x : Fin (d - 3) → α} {p q r : α} {S : KOM d α}
    (h : S.χ (c3 x p q r) = 1) :
    x.Injective ∧ (∀ i, (x i ≠ p ∧ x i ≠ q ∧ x i ≠ r)) ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r :=
  tail_ne_of_χ_ne_zero (ne_zero_of_eq_one h)

lemma c3_inj_iff [AtLeastThree d] {x : Fin (d - 3) → α} {p q r : α} :
    (c3 x p q r).Injective ↔
      (x.Injective ∧ (∀ i, x i ≠ p ∧ x i ≠ q ∧ x i ≠ r) ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r) := by
  refine ⟨fun hxpqrinj ↦ ?_, ?_⟩
  · have inj' (i j) := @hxpqrinj i j
    refine ⟨fun i j heq ↦ ?_, fun i ↦ ?_, ?_, ?_, ?_⟩
    · have := inj' i j
      rw [others_c3 i.2, others_c3 j.2] at this
      simp only [Fin.eta, heq, Fin.mk.injEq, forall_const] at this
      exact Fin.eq_of_val_eq this
    · have H3 := inj' i ⟨d - 3, sub_three_lt⟩
      have H2 := inj' i ⟨d - 2, sub_two_lt⟩
      have H1 := inj' i ⟨d - 1, sub_one_lt⟩
      rw [others_c3 i.2, antepenultimate] at H3
      rw [others_c3 i.2, penultimate_c3 rfl] at H2
      rw [others_c3 i.2, last_c3 rfl] at H1
      grind
    · have := inj' ⟨d - 3, sub_three_lt⟩ ⟨d - 2, sub_two_lt⟩
      rw [antepenultimate, penultimate_c3 rfl] at this
      exact this.mt Fin.minus_three_ne_minus_two
    · have := inj' ⟨d - 3, sub_three_lt⟩ ⟨d - 1, sub_one_lt⟩
      rw [antepenultimate, last_c3 rfl] at this
      exact this.mt Fin.minus_three_ne_minus_one
    · have := inj' ⟨d - 2, sub_two_lt⟩ ⟨d - 1, sub_one_lt⟩
      rw [penultimate_c3 rfl, last_c3 rfl] at this
      exact this.mt Fin.minus_two_ne_minus_one
  · exact fun ⟨hxinj, hipqr, hpneq, hpner, hqner⟩ ↦ Function.injective_iff.mpr <| by grind

lemma swap_c3 [AtLeastThree d] {x : Fin (d - 3) → α} {p q r : α} {S : KOM d α}
    (hpqr : S.χ (c3 x p q r) ≠ 1) (hv : (c3 x p r q).Injective) : S.χ (c3 x p r q) = 1 := by
  cases hxprq : S.χ (c3 x p r q)
  · have := S.uniform (c3 x p r q) |>.mpr.mt <| by simp [hxprq]
    contradiction
  · refine hpqr ?_ |>.elim
    rw [c3_eq_c2_of_append] at hxprq ⊢
    exact S.χ.swap S.alternating hxprq
  · exact pos_eq_one

lemma swap_c3' [AtLeastThree d] {x : Fin (d - 3) → α} {p q r : α} {S : KOM d α}
    (hpqr : S.χ (c3 x p q r) ≠ 1) (hxinj : x.Injective) (hipqr : ∀ i, (x i ≠ p ∧ x i ≠ q ∧ x i ≠ r))
    (hne : p ≠ q ∧ p ≠ r ∧ q ≠ r) :
    S.χ (c3 x p r q) = 1 := by
  refine swap_c3 hpqr <| c3_inj_iff.mpr <| by grind

private lemma KOM.dualTransitive_of_transitive_impl [AtLeastThree d] {S : KOM d α} {p q r s : α}
    (t : α) (x : Fin (d - 3) → α) (hsner : s ≠ r)
    (hpqt : S.χ (c3 x p q t) = 1) (hpst : S.χ (c3 x p s t) = 1) (hptr : S.χ (c3 x p t r) = 1)
    (htqr : S.χ (c3 x t q r) = 1) (hstr : S.χ (c3 x s t r) = 1) (hstq : S.χ (c3 x s t q) = 1) :
    S.χ (c3 x s p q) = 1 → S.χ (c3 x s r p) = 1 := by
  intro hspq
  if hpqr : S.χ (c3 x p q r) = 1 then
    suffices S.χ (c3 x p s r) = 1 by cyclic_nf
    refine transitive_iff.mp S.transitive x p q s t r ?_ ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf
  else
    obtain ⟨hxinj, hipqt, Hpqt⟩ := tail_ne_of_χ_pos hpqt
    obtain ⟨hxinj, hitqr, Htqr⟩ := tail_ne_of_χ_pos htqr
    obtain ⟨hxinj, hiptr, Hptr⟩ := tail_ne_of_χ_pos hptr
    obtain ⟨hxinj, histr, Hstr⟩ := tail_ne_of_χ_pos hstr
    obtain ⟨hxinj, hispq, Hspq⟩ := tail_ne_of_χ_pos hspq
    clear hxinj; clear hxinj; clear hxinj
    by_contra hnotsrp
    have hprq : S.χ (c3 x p r q) = 1 := by refine swap_c3' hpqr ?_ ?_ ?_ <;> grind only
    have hspr : S.χ (c3 x s p r) = 1 := by refine swap_c3' hnotsrp ?_ ?_ ?_ <;> grind only
    rcases hrqs : S.χ (c3 x r q s)
    · exact (S.uniform (c3 x r q s) |>.mpr.mt <| by simp [hrqs]) <| c3_inj_iff.mpr <| by grind
    · cyclic_nf
      have hrsq : S.χ (c3 x r s q) = 1 := by
        have H : S.χ (c3 x r q s) ≠ 1 := by
          cyclic_nf
          simp only [hrqs, neg_eq_neg_one, ne_eq, neg_eq_self_iff, one_ne_zero, not_false_eq_true]
        refine swap_c3' H ?_ ?_ ?_ <;> grind only
      have hnotrqt : S.χ (c3 x r q t) ≠ 1 := (S.elim' · (by cyclic_nf))
      refine hnotrqt ?_ |>.elim
      have hqnet : q ≠ t := by grind only
      refine transitive_iff.mp S.transitive x r s q p t hqnet hrsq ?_ hstr ?_ ?_ <;> cyclic_nf
    · suffices S.χ (c3 x q r p) = 1 by exact hpqr <| by cyclic_nf
      have hrnep : r ≠ p := by grind
      refine transitive_iff.mp S.transitive x q s r t p hrnep ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf

lemma KOM.dualTransitive [AtLeastThree d] (S : KOM d α) : DualTransitivity S.χ := by
  refine dualTransitive_iff.mpr ?_
  intro x t s p q r hpner htps htqs htrs htpq htqr-- hprq hpsq hptq hprs hpst
  by_contra hnotprt
  obtain ⟨hxinj, hitps, Htps⟩ := tail_ne_of_χ_pos htps
  obtain ⟨hxinj, hitqs, Htqs⟩ := tail_ne_of_χ_pos htqs
  obtain ⟨hxinj, hitrs, Htrs⟩ := tail_ne_of_χ_pos htrs
  obtain ⟨hxinj, hitpq, Htpq⟩ := tail_ne_of_χ_pos htpq
  obtain ⟨hxinj, hitqr, Htqr⟩ := tail_ne_of_χ_pos htqr
  clear hxinj; clear hxinj; clear hxinj
  have htrp : S.χ (c3 x t r p) = 1 := by refine swap_c3' (by cyclic_nf) hxinj ?_ ?_ <;> grind only
  have H1 : S.χ (c3 x s p q) = 1 → S.χ (c3 x s r p) = 1 := by
    refine dualTransitive_of_transitive_impl t x (by grind)  ?_ ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf
  have H2 : S.χ (c3 x s r p) = 1 → S.χ (c3 x s q r) = 1 := by
    refine dualTransitive_of_transitive_impl t x (by grind) ?_ ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf
  have H3 : S.χ (c3 x s q r) = 1 → S.χ (c3 x s p q) = 1 := by
    refine dualTransitive_of_transitive_impl t x (by grind) ?_ ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf
  if hspq : S.χ (c3 x s p q) = 1 then
    have hsqr : S.χ (c3 x s q r) = 1 := H2 <| H1 hspq
    refine S.elim' (H1 hspq) ?_
    refine transitive_iff.mp S.transitive x s t p q r (by grind) ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf
  else
    have hsqp : S.χ (c3 x s q p) = 1 := by refine swap_c3' hspq hxinj ?_ ?_ <;> grind
    have hprs : S.χ (c3 x s p r) = 1 := by
      refine swap_c3' (H2.mt <| H3.mt hspq) hxinj ?_ ?_ <;> grind
    suffices S.χ (c3 x s q r) = 1 by refine S.elim' hsqp (H3 this)
    refine transitive_iff.mp S.transitive x s t q p r (by grind) ?_ ?_ ?_ ?_ ?_ <;> cyclic_nf

theorem UOM.transitivity [AtLeastThree d] (S : UOM d α) : Transitivity S.χ := by
  intro x p r q s hdistinctpr hsp hsq hsr hpq hqr
  have ht1p : S.χ (c2 x s r) * S.χ (c2 x p q) ≥ 0 := by simp [hsr, hpq]
  have ht2p : S.χ (c2 x s p) * S.χ (c2 x q r) ≥ 0 := by simp [hsp, hqr]
  have ht3p : S.χ (c2 x s q) * S.χ (c2 x p r) ≥ 0 := S.GP3 x s p q r ht1p ht2p
  rw [hsq] at ht3p
  -- get the implications from uniformity
  have hip := S.uniform (c2 x p q) |>.mp <| by simp [hpq]
  have hir := S.uniform (c2 x s r) |>.mp <| by simp [hsr]
  simp only [Function.Injective] at hip hir
  ---------------------------------------
  -- hence x i is distinct from p
  ---------------------------------------
  have hdistinctxip : ∀ i : Fin (d - 2), x i ≠ p := by
    intro i
    have hobj := @hip ⟨i.1, by lia⟩ ⟨d - 2, sub_two_lt⟩ |>.mt
    simpa only [ne_eq, Fin.mk.injEq, ne_of_lt i.2, not_false_eq_true, Fin.is_lt, others_c2, Fin.eta,
      penultimate, forall_const] using hobj
  ---------------------------------------
  -- x i is distinct from r / same proof
  ---------------------------------------
  have hdistinctxir : ∀ i : Fin (d - 2), x i ≠ r := by
    intro i
    have hobj := @hir ⟨i.1, by lia⟩ ⟨d - 1, sub_one_lt⟩ |>.mt
    have H : i ≠ d - 1 := by grind
    simpa only [ne_eq, Fin.mk.injEq, H, not_false_eq_true, Fin.is_lt, others_c2, Fin.eta, last,
      forall_const] using hobj
  ---------------------------------------
  -- and all i j less than d - 2 are all distinct as well
  ---------------------------------------
  have hdistinctxij : ∀ i j : Fin (d - 2), i ≠ j → x i ≠ x j := by
    intro i j h
    -- apply uniformity with s r (could be any other)
    have hobj := @hir ⟨i, by lia⟩ ⟨j, by lia⟩ |>.mt <| by grind
    simpa only [Fin.is_lt, others_c2, Fin.eta] using hobj
  ---------------------------------------
  -- so all in x p r are distinct
  ---------------------------------------
  have hdistinctall : (∀ i j : Fin d, i ≠ j → (c2 x p r) i ≠ (c2 x p r) j) := by
    intro i j hij
    have Hlt {i : Fin d} (hi : i < d - 2) : c2 x p r i = x ⟨i, by lia⟩ := by
      rw [others_c2]
    have H1 {i : Fin d} (hi : i = d - 1) : c2 x p r i = r := by
      rw [(by grind : i = ⟨d - 1, _⟩), last]
    have H2 {i : Fin d} (hi : i = d - 2) : c2 x p r i = p := by
      rw [(by grind : i = ⟨d - 2, _⟩), penultimate]
    grind only
  ---------------------------------------
  -- therefore pr is nonzero from uniformity
  ---------------------------------------
  have hnonz : S.χ (c2 x p r) ≠ zero := by
    refine (S.uniform (c2 x p r)).mpr ?_
    intro i j hij
    have := hdistinctall i j |>.mt
    simpa [hij] using! this
  ---------------------------------------
  -- hence it must be positive
  ---------------------------------------
  cases heq : S.χ (c2 x p r) with
  | zero => exact absurd heq hnonz
  | neg  => rw [heq] at ht3p; contradiction
  | pos  => exact pos_eq_one

theorem KOM.GP3 (d : ℕ) [AtLeastThree d] (S : KOM d α) : GP3 S.χ := by
  intro x s p q r hxsrxpq hxspxqr
  by_contra hxsqxpr
  simp only [ge_iff_le, not_le, neg_iff] at hxsqxpr
  have hsneq : s ≠ q := by
    intro hseqq
    have : S.χ (c2 x s q) = 0 := S.χ.eq_zero_of_non_inj' S.uniform hseqq
    simp_all only [ge_iff_le, zero_mul, reduceCtorEq]
  have hpner : p ≠ r := by
    intro hpeqr
    have : S.χ (c2 x p r) = 0 := S.χ.eq_zero_of_non_inj' S.uniform hpeqr
    simp_all
  have Hχ : (S.χ (c2 x s q) = -1 ∧ S.χ (c2 x p r) = 1)
      ∨ (S.χ (c2 x s q) = 1 ∧ S.χ (c2 x p r) = -1) := by
    cases hχxsq : S.χ (c2 x s q) <;> simp_all
  have hpnes : p ≠ s := by
    intro h; subst h
    rcases Hχ with ⟨hxsq, hxpr⟩ | ⟨hxsq, hxpr⟩ <;> simp_all
  have hpneq : p ≠ q := by
    intro h; subst h
    rcases Hχ with ⟨hxsq, hxpr⟩ | ⟨hxsq, hxpr⟩ <;> simp_all
  have hqner : q ≠ r := by
    intro h; subst h
    rcases Hχ with ⟨hxsq, hxpr⟩ | ⟨hxsq, hxpr⟩ <;> simp_all
  have hrnes : r ≠ s := by
    intro h; subst h
    rcases Hχ with ⟨hxsq, hxpr⟩ | ⟨hxsq, hxpr⟩
    · have hxqr : S.χ (c2 x q r) = 1 := by rw [flip_12 S.alternating, hxsq, InvolutiveNeg.neg_neg]
      have hxrp : S.χ (c2 x r p) = -1 := by rw [flip_12 S.alternating, hxpr]
      simp_all
    · have hxqr : S.χ (c2 x q r) = -1 := by rw [flip_12 S.alternating, hxsq]
      have hxrp : S.χ (c2 x r p) = 1 := by rw [flip_12 S.alternating, hxpr, InvolutiveNeg.neg_neg]
      simp_all
  have hχxsq : S.χ (c2 x s q) ≠ 0 := by
    rcases Hχ with ⟨h, _⟩ | ⟨h, _⟩
    <;> simp only [h, ne_eq, neg_eq_zero_iff, one_ne_zero, not_false_eq_true]
  have hχxpr : S.χ (c2 x p r) ≠ 0 := by
    rcases Hχ with ⟨_, h⟩ | ⟨_, h⟩
    <;> simp only [h, ne_eq, neg_eq_zero_iff, one_ne_zero, not_false_eq_true]
  have hxinj : x.Injective := S.χ.pref2_of_c2_injective_of_χ_ne_zero S.uniform hχxsq
  have hxpqrs : ∀ i, (x i ≠ p ∧ x i ≠ q ∧ x i ≠ r ∧ x i ≠ s) := by
    intro i
    have := S.χ.ne_of_χ_ne_zero' S.uniform hχxsq
    have := S.χ.ne_of_χ_ne_zero' S.uniform hχxpr
    grind
  have hχxsr : S.χ (c2 x s r) ≠ 0 := S.χ.c2_uniform S.uniform (by grind) hrnes.symm hxinj
  have hχxpq : S.χ (c2 x p q) ≠ 0 := S.χ.c2_uniform S.uniform (by grind) hpneq hxinj
  have hχxsp : S.χ (c2 x s p) ≠ 0 := S.χ.c2_uniform S.uniform (by grind) hpnes.symm hxinj
  have hχxqr : S.χ (c2 x q r) ≠ 0 := S.χ.c2_uniform S.uniform (by grind) hqner hxinj
  have hxsreqxpq : S.χ (c2 x s r) = S.χ (c2 x p q) := by
    cases Hxsr : S.χ (c2 x s r) <;> cases Hxpq : S.χ (c2 x p q) <;> simp_all
  have hxspeqxqr : S.χ (c2 x s p) = S.χ (c2 x q r) := by
    cases Hxsp : S.χ (c2 x s p) <;> cases Hxqr : S.χ (c2 x q r) <;> simp_all
  clear hxsrxpq hxspxqr hxpqrs
  -- Horrendous case analysis
  match pos_or_neg_of_ne_zero hχxsr, pos_or_neg_of_ne_zero hχxsp with
  | Or.inl Hxrs, Or.inl Hxps =>
      rw [Hxrs] at hxsreqxpq
      rw [Hxps] at hxspeqxqr
      rw [flip_12 S.alternating] at Hxrs Hxps hxsreqxpq hxspeqxqr
      simp only [neg_inj] at Hxrs Hxps hxsreqxpq hxspeqxqr
      refine S.elim ?_ hxsreqxpq.symm
      rcases Hχ with ⟨Hxqs, Hxrp⟩ | ⟨Hxqs, Hxrp⟩
      · rw [flip_12 S.alternating] at Hxqs
        simp only [neg_inj] at Hxqs
        exact S.dualTransitive r s hpneq Hxps Hxrs Hxqs Hxrp hxspeqxqr.symm
      · rw [flip_12 S.alternating] at Hxrp
        simp only [neg_inj] at Hxrp
        exact S.transitive s r hpneq Hxrp Hxrs hxspeqxqr.symm Hxps Hxqs
  | Or.inl Hxrs, Or.inr Hxsp =>
      rw [Hxsp] at hxspeqxqr
      rw [Hxrs] at hxsreqxpq
      rw [flip_12 S.alternating] at Hxrs hxsreqxpq
      simp only [neg_inj] at Hxrs hxsreqxpq
      rcases Hχ with ⟨Hxqs, Hxrp⟩ | ⟨Hxqs, Hxrp⟩
      · refine S.elim Hxsp ?_
        exact S.transitive r q hpnes hxsreqxpq.symm hxspeqxqr.symm (S.swap Hxqs) Hxrp Hxrs
      · rw [flip_12 S.alternating] at Hxrp
        simp only [neg_inj] at Hxrp
        refine S.elim ?_ Hxqs
        exact S.dualTransitive r p hsneq.symm hxsreqxpq.symm Hxrp Hxsp hxspeqxqr.symm Hxrs
  | Or.inr Hxsr, Or.inl Hxps =>
      rw [Hxsr] at hxsreqxpq
      rw [Hxps] at hxspeqxqr
      rw [flip_12 S.alternating] at hxspeqxqr Hxps
      simp only [neg_inj] at hxspeqxqr Hxps
      rcases Hχ with ⟨Hxqs, Hxrp⟩ | ⟨Hxqs, Hxrp⟩
      · refine S.elim ?_ (S.swap Hxqs)
        exact S.transitive r p hsneq Hxps Hxrp hxsreqxpq.symm Hxsr hxspeqxqr.symm
      · refine S.elim ?_ (S.swap Hxrp)
        exact S.dualTransitive s q hpner hxsreqxpq.symm Hxqs hxspeqxqr.symm Hxps Hxsr
  | Or.inr Hxsr, Or.inr Hxsp =>
      rw [Hxsr] at hxsreqxpq
      rw [Hxsp] at hxspeqxqr
      rcases Hχ with ⟨Hxqs, Hxrp⟩ | ⟨Hxqs, Hxrp⟩
      · rw [flip_12 S.alternating] at Hxqs
        simp only [neg_inj] at Hxqs
        refine S.elim ?_ Hxqs
        exact S.dualTransitive p r hsneq Hxsr Hxrp hxspeqxqr.symm Hxsp hxsreqxpq.symm
      · refine S.elim ?_ (S.swap Hxrp)
        exact S.transitive q s hpner Hxsp Hxqs Hxsr hxsreqxpq.symm hxspeqxqr.symm

instance (d : ℕ) [AtLeastThree d] : Coe (UOM d α) (KOM d α) :=
  ⟨fun S ↦ ⟨S.χ, S.alternating, S.uniform, S.transitivity⟩⟩

instance (d : ℕ) [AtLeastThree d] : Coe (KOM d α) (UOM d α) :=
  ⟨fun S ↦ ⟨S.χ, S.alternating, S.uniform, S.GP3⟩⟩

lemma uom_kom_eq {d : ℕ} [AtLeastThree d] (S : UOM d α) : ((S : KOM d α) : UOM d α) = S :=
  rfl
lemma kom_uom_eq {d : ℕ} [AtLeastThree d] (S : KOM d α) : ((S : UOM d α) : KOM d α) = S :=
  rfl

def kom_eq_uom (d : ℕ) [AtLeastThree d] : KOM d α ≃ UOM d α :=
  ⟨(·), (·), kom_uom_eq, uom_kom_eq⟩
