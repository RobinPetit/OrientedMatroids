/-
Copyright (c) 2026 Jean Cardinal & Robin Petit. All rights reserved.
Released under MIT NON-AI license as described in the file LICENSE.
Authors: Jean Cardinal, Robin Petit
-/

import Mathlib.Algebra.BigOperators.Fin

import OrientedMatroids.AtLeast

/-!
DOCSTRING: TODO
-/

lemma Fin1_sum {M : Type*} [AddCommMonoid M] {f : Fin 1 → M} :
    ∑ i, f i = f 0 := by
  simp

lemma Fin2_sum {M : Type*} [AddCommMonoid M] {f : Fin 2 → M} :
    ∑ i, f i = f 0 + f 1 := by
  simp

lemma Fin3_sum {M : Type*} [AddCommMonoid M] {f : Fin 3 → M} :
    ∑ i, f i = f 0 + f 1 + f 2 := by
  simp only [Finset.sum, Fin.univ_val_map, List.ofFn_succ, Fin.isValue, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, List.ofFn_zero, Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]
  grind only

lemma Fin4_sum {M : Type*} [AddCommMonoid M] {f : Fin 4 → M} :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  simp only [Finset.sum, Fin.univ_val_map, List.ofFn_succ, Fin.isValue, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, List.ofFn_zero, Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]
  grind only

lemma zero_ne_two {n : ℕ} [inst : AtLeastThree n] : (0 : Fin n) ≠ (2 : Fin n) := by
  refine Fin.ne_of_val_ne ?_
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, ne_eq]
  rw [Nat.mod_eq_of_lt inst.two_lt]
  simp

lemma one_ne_two {n : ℕ} [AtLeastThree n] : (1 : Fin n) ≠ (2 : Fin n) := by
  refine Fin.ne_of_val_ne ?_
  simp only [Fin.coe_ofNat_eq_mod, ne_eq]
  rw [Nat.mod_eq_of_lt AtLeastTwo.one_lt, Nat.mod_eq_of_lt AtLeastThree.two_lt]
  simp

def Fin.castUp {m n : ℕ} (hmn : m < n) (i : Fin m) : Fin n :=
  ⟨i, lt_trans i.2 hmn⟩

instance {m n : ℕ} : CoeOut (Fin (m - n)) (Fin m) := by
  refine ⟨fun i ↦ ⟨i, lt_of_lt_of_le i.2 (Nat.sub_le ..)⟩⟩

lemma Fin.ne {n : ℕ} (i : Fin n) : i ≠ n := ne_of_lt i.2

def Fin.minus_one (n : ℕ) [AtLeastOne n] : Fin n := ⟨n - 1, AtLeast.sub_one_lt⟩
def Fin.minus_two (n : ℕ) [AtLeastTwo n] : Fin n := ⟨n - 2, AtLeast.sub_two_lt⟩
def Fin.minus_three (n : ℕ) [AtLeastThree n] : Fin n := ⟨n - 3, AtLeast.sub_three_lt⟩

section
variable {n : ℕ}

@[simp, grind .]
lemma Fin.minus_one_ne_minus_two [AtLeastTwo n] : Fin.minus_one n ≠ Fin.minus_two n := by
  simp [Fin.minus_one, Fin.minus_two, Ne.symm <| ne_of_lt AtLeastTwo.sub_two_lt_sub_one]
@[simp, grind .]
lemma Fin.minus_two_ne_minus_one [AtLeastTwo n] : Fin.minus_two n ≠ Fin.minus_one n := by
  exact Ne.symm Fin.minus_one_ne_minus_two

@[simp, grind .]
lemma Fin.minus_one_ne_minus_three [AtLeastThree n] : Fin.minus_one n ≠ Fin.minus_three n := by
  simp [Fin.minus_one, Fin.minus_three, Ne.symm <| ne_of_lt AtLeastThree.sub_three_lt_sub_one]
@[simp, grind .]
lemma Fin.minus_three_ne_minus_one [AtLeastThree n] : Fin.minus_three n ≠ Fin.minus_one n := by
  exact Ne.symm <| Fin.minus_one_ne_minus_three

@[simp, grind .]
lemma Fin.minus_two_ne_minus_three [AtLeastThree n] : Fin.minus_two n ≠ Fin.minus_three n := by
  simp [Fin.minus_two, Fin.minus_three, Ne.symm <| ne_of_lt AtLeastThree.sub_three_lt_sub_two]
@[simp, grind .]
lemma Fin.minus_three_ne_minus_two [AtLeastThree n] : Fin.minus_three n ≠ Fin.minus_two n := by
  exact Ne.symm <| Fin.minus_two_ne_minus_three

end
