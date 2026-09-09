/-
Copyright (c) 2026 Jean Cardinal & Robin Petit. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Cardinal, Robin Petit
-/

import OrientedMatroids.Basic

/-!
DOCSTRING: TODO
-/

variable {α : Type*}
-- the rank (dimension) is at least three
variable {d : ℕ}

-- we can move from c2 to c3
lemma c2_eq_c3_of_pref {h : d - 2 ≠ 0} (t : Fin (d - 2) → α) (a b : α) :
    c2 t a b = c3 (pref t) (t ⟨d - 3, by lia⟩) a b := by
  unfold c3 c2 append pref
  ext i
  simp only [Nat.sub_eq, Nat.pred_eq_sub_one]
  split_ifs
  · rfl
  · exact congrArg _ (by grind)
  · rfl
  · rfl

-- if we take the prefix and append back the last element, then nothing changes
lemma pref_append (hdge3 : d ≥ 3) (t : Fin d → α) :
    append (pref t) (t ⟨d - 1, Nat.sub_one_lt_of_lt hdge3⟩) = t := by
  unfold pref append
  ext i
  split_ifs
  · rfl
  · rename_i h
    simp only [not_lt, tsub_le_iff_right] at h
    refine congrArg _ <| Fin.eq_of_val_eq ?_
    exact le_antisymm (Nat.sub_le_of_le_add h) (Nat.le_sub_one_of_lt i.2)

-- if we append an element then take the prefix, nothing changes
lemma append_pref (t : Fin (d - 1) → α) (e : α) :
    pref (append t e) = t := by
  unfold append pref
  simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]

section
variable {t : Fin (d - 2) → α} {a b : α} (hdge3 : d ≥ 3)

@[simp] lemma last : (c2 t a b) ⟨d - 1, by lia⟩ = b := by grind
@[simp] lemma penultimate : (c2 t a b) ⟨d - 2, by lia⟩ = a := by grind
@[simp] lemma others {i : Fin d} (hi : i < d - 2) : (c2 t a b) i = t ⟨i, hi⟩ := by
  unfold c2 append
  split_ifs <;> grind

end

open Equiv
open SignType

@[simp] lemma int_unit_ne_neg_unit : -1 ≠ (1 : ℤˣ) := Int.units_ne_iff_eq_neg.mpr rfl

namespace Utils
protected lemma nat_ne_32 {n : ℕ} (hn : n ≥ 3) : n - 3 ≠ n - 2 := by lia
protected lemma nat_ne_31 {n : ℕ} (hn : n ≥ 3) : n - 3 ≠ n - 1 := by lia
protected lemma nat_ne_21 {n : ℕ} (hn : n ≥ 3) : n - 2 ≠ n - 1 := by lia
end Utils

lemma flip_v1 (hdge3 : d ≥ 3) (χ : Orientation d α) (ha : Alternating χ)
    (t : Fin (d - 2) → α) (a b : α) :
    χ (c2 t b a) = - χ (c2 t a b) := by
  classical
  let σ : Perm (Fin d) := swap ⟨d - 2, by lia⟩ ⟨d - 1, by lia⟩
  have hl : c2 t b a = (c2 t a b) ∘ σ  := by
    ext i
    simp only [Function.comp_apply, σ, c2, append]
    split_ifs <;> grind
  have hr : σ.sign' * χ (c2 t a b) = -χ (c2 t a b) := by
    simp_rw [Perm.sign', σ]
    simp [Utils.nat_ne_21 hdge3]
  rw [hl, ha σ (c2 t a b), hr]

-- the same with c3
lemma flip23 (hdge3 : d ≥ 3) (χ : Orientation d α) (ha : Alternating χ)
    (t : Fin (d - 3) → α) (a b c : α) :
    χ (c3 t c b a) = - χ (c3 t c a b) := by
  let σ : Perm (Fin d) := swap ⟨d - 2, by lia⟩ ⟨d - 1, by lia⟩
  have hl : c3 t c b a = (c3 t c a b) ∘ σ := by
    ext i
    simp only [Function.comp_apply, σ, c3, c2, append]
    split_ifs <;> grind
  have hr : σ.sign' * χ (c3 t c a b) = -χ (c3 t c a b) := by
    simp_rw [Perm.sign', σ]
    simp [Utils.nat_ne_21 hdge3]
  rw [hl, ha σ (c3 t c a b), hr]

-- swap the first two of the last three
lemma flip12 (hdge3 : d ≥ 3) (χ : Orientation d α) (ha : Alternating χ)
    {t : Fin (d - 3) → α} {a b c : α} :
    χ (c3 t a b c) = - χ (c3 t b a c) := by
  let σ : Perm (Fin d) := swap ⟨d - 3, by lia⟩ ⟨d - 2, by lia⟩
  have hl : c3 t b a c = (c3 t a b c) ∘ σ := by
    ext i
    simp only [c3, append, c2, Function.comp_apply, σ]
    split_ifs <;> grind
  have hr : σ.sign' * χ (c3 t a b c) = -χ (c3 t a b c) := by
    simp_rw [Perm.sign', σ]
    simp [Utils.nat_ne_32 hdge3]
  rw [hl, ha σ (c3 t a b c), hr, neg_neg]

-- now cylicity is easier
lemma cyclic (hdge3 : d ≥ 3) (χ : Orientation d α) (ha : Alternating χ)
    {t : Fin (d - 3) → α} {a b c : α} :
    χ (c3 t a b c) = χ (c3 t b c a) := by
  rw [flip12 hdge3 χ ha, flip23 hdge3 χ ha, neg_neg]

-- the other direction
lemma cyclic2 (hdge3 : d ≥ 3) (χ : Orientation d α) (ha : Alternating χ)
    {t : Fin (d - 3) → α} {a b c : α} :
    χ (c3 t a b c) = χ (c3 t c a b) := by
  repeat rw [cyclic hdge3 χ ha]

lemma ne_of_ne_of_eq_of_eq {a b c d : α} (h : a ≠ b) (hac : a = c) (hbd : b = d) :
    c ≠ d := by
  simpa only [hac, hbd] using h

theorem UOM_satisfy_transitivity (hdge3 : d ≥ 3) (S : UOM d α) : Transitivity S.χ := by
  intro x s p q r hdistinctpr hsp hsq hsr hpq hqr
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
    have hobj := @hip ⟨i.1, by lia⟩ ⟨d - 2, by lia⟩ |>.mt
    simpa only [Fin.mk.injEq, ne_of_lt i.2, not_false_eq_true, Fin.is_lt, others, Fin.eta,
      forall_const, penultimate hdge3] using hobj
  ---------------------------------------
  -- x i is distinct from r / same proof
  ---------------------------------------
  have hdistinctxir : ∀ i : Fin (d - 2), x i ≠ r := by
    intro i
    have hobj := @hir ⟨i.1, by lia⟩ ⟨d - 1, by lia⟩ |>.mt
    have H : i ≠ d - 1 := by grind
    simpa only [ne_eq, Fin.mk.injEq, H, not_false_eq_true, Fin.is_lt, others, Fin.eta, last hdge3,
      forall_const] using hobj
  ---------------------------------------
  -- and all i j less than d - 2 are all distinct as well
  ---------------------------------------
  have hdistinctxij : ∀ i j : Fin (d - 2), i ≠ j → x i ≠ x j := by
    intro i j h
    -- apply uniformity with s r (could be any other)
    have hobj := @hir ⟨i, by lia⟩ ⟨j, by lia⟩ |>.mt <| by grind
    simpa only [Fin.is_lt, others, Fin.eta] using hobj
  ---------------------------------------
  -- so all in x p r are distinct / ridiculous case analysis
  ---------------------------------------
  have hdistinctall : (∀ i j : Fin d, i ≠ j → (c2 x p r) i ≠ (c2 x p r) j) := by
    intro i j hij
    have Hlt {i : Fin d} (hi : i < d - 2) : c2 x p r i = x ⟨i, by lia⟩ := by
      rw [others]
    have H1 {i : Fin d} (hi : i = d - 1) : c2 x p r i = r := by
      rw [(by grind : i = ⟨d - 1, _⟩), last hdge3]
    have H2 {i : Fin d} (hi : i = d - 2) : c2 x p r i = p := by
      rw [(by grind : i = ⟨d - 2, _⟩), penultimate hdge3]
    have Hi : i < d - 2 ∨ i = d - 2 ∨ i = d - 1 := by grind
    have Hj : j < d - 2 ∨ j = d - 2 ∨ j = d - 1 := by grind
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
  | pos  => exact heq

theorem KOM_satisfy_GP3 (hdge3 : d ≥ 3) (S : KOM d α) : GP3 S.χ := by
  sorry

def NatAtLeast3 := {n : ℕ // 3 ≤ n}

instance : Coe NatAtLeast3 ℕ :=
  ⟨fun n ↦ n.val⟩

instance (d : NatAtLeast3) : Coe (UOM d α) (KOM d α) :=
  ⟨fun S ↦ ⟨S.χ, S.alternating, S.uniform, UOM_satisfy_transitivity d.prop S⟩⟩

instance (d : NatAtLeast3) : Coe (KOM d α) (UOM d α) :=
  ⟨fun S ↦ ⟨S.χ, S.alternating, S.uniform, KOM_satisfy_GP3 d.prop S⟩⟩

lemma uom_kom_eq (d : NatAtLeast3) (S : UOM d α) : ((S : KOM d α) : UOM d α) = S :=
  rfl
lemma kom_uom_eq (d : NatAtLeast3) (S : KOM d α) : ((S : UOM d α) : KOM d α) = S :=
  rfl
