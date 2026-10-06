/-
Copyright (c) 2026 Jean Cardinal & Robin Petit. All rights reserved.
Released under MIT NON-AI license as described in the file LICENSE.
Authors: Jean Cardinal, Robin Petit
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import OrientedMatroids.Fin

/-!
DOCSTRING
-/

private lemma sum_eq_of_eq_of_eq {α : Type*} [Add α] {a b x y : α} (h : a = x) (h' : b = y) :
    a + b = x + y := by
  rw [h, h']

private lemma mul_eq_of_eq_left {α : Type*} [Mul α] {x y z : α} (h : y = z) : x * y = x * z := by
  rw [h]

variable {R : Type*} [CommRing R]

lemma laplace_4x4_last_col
    {a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 : R}
    :
    !![a11, a12, a13, a14;
      a21, a22, a23, a24;
      a31, a32, a33, a34;
      a41, a42, a43, a44].det =
    - !![a21, a22, a23; a31, a32, a33; a41, a42, a43].det * a14
      + !![a11, a12, a13; a31, a32, a33; a41, a42, a43].det * a24
      - !![a11, a12, a13; a21, a22, a23; a41, a42, a43].det * a34
      + !![a11, a12, a13; a21, a22, a23; a31, a32, a33].det * a44 := by
  rw [@Matrix.det_succ_column _ _ 3 _ 3, Fin4_sum]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    Nat.mod_succ, zero_add, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val,
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, Fin.succAbove_zero, Nat.one_mod,
    Matrix.cons_val_one, Nat.reduceMod, sub_eq_add_neg]
  repeat refine sum_eq_of_eq_of_eq ?_ ?_
  all_goals {
    ring_nf
    try simp only [Fin.isValue, neg_inj]
    refine mul_eq_of_eq_left ?_
    refine congrArg _ ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Fin.succAbove]
  }

lemma det_updateRow_eq_of_linear_combination {m n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    {j : Fin n} (c : Fin m → R) (f : Fin m → Fin n → R) (r : Fin n → R)
    (hr : r = ∑ i : Fin m, (c i) • (f i)) :
    (M.updateRow j r).det = ∑ i, (c i) * (M.updateRow j (f i)).det := by
  induction m generalizing r with
  | zero =>
      simp_all only [Finset.univ_eq_empty, Finset.sum_empty]
      refine Matrix.det_eq_zero_of_row_eq_zero j ?_
      intro i
      simp only [Matrix.updateRow, Matrix.of_apply, Function.update, ↓reduceDIte, Pi.zero_apply]
  | succ m ih => ?_
  rw [hr, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc (fun i ↦ (c i) * (M.updateRow j (f i)).det)]
  simp only [Matrix.det_updateRow_add, Matrix.det_updateRow_smul, add_left_inj]
  have H := by
    refine ih (c ·.castSucc) (fun i j ↦ f i.castSucc j) (r - (c (Fin.last m)) • (f (Fin.last m))) ?_
    refine eq_sub_of_add_eq ?_.symm |>.symm
    rw [← Fin.sum_univ_castSucc (fun i ↦ (c i) • (f i)), hr]
  rw [← H]
  refine congrArg _ ?_
  ext a b
  simp only [Matrix.updateRow, Matrix.of_apply, Function.update, eq_rec_constant, dite_eq_ite]
  if ha : a = j then
    simp only [ha, ↓reduceIte, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hr, Pi.sub_apply]
    rw [Fin.sum_univ_castSucc, add_sub_cancel_right]
  else
    simp only [ha, ↓reduceIte]
