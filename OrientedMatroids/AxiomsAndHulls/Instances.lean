/-
Copyright (c) 2026 Jean Cardinal & Robin Petit. All rights reserved.
Released under MIT NON-AI license as described in the file LICENSE.
Authors: Jean Cardinal, Robin Petit
-/

import Architect

import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith

import OrientedMatroids.Det
import OrientedMatroids.AxiomsAndHulls.Defs

/-!
DOSCTRING: TODO
-/

open AxiomsAndHulls
open CC

abbrev PointR2 := ℝ × ℝ

def matrix_of_points (p q r : PointR2) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![p.1, p.2, 1;
     q.1, q.2, 1;
     r.1, r.2, 1]

def Set.Tripletwise {α : Type*} (s : Set α) (pred : α → α → α → Prop) :=
    ∀ (x y z : s), pred x y z

def Noncolinear (s : Set PointR2) := s.Tripletwise <| fun p q r ↦ (matrix_of_points p q r).det ≠ 0

private lemma minus_sign_det_of_swap {p q r : PointR2} :
    (matrix_of_points p q r).det = -(matrix_of_points p r q).det := by
  let σ : (Fin 3) ≃ (Fin 3) := Equiv.swap 1 2
  suffices (matrix_of_points p q r).submatrix σ id = (matrix_of_points p r q) by
    rw [← this]
    simp only [Matrix.det_permute]
    suffices (Equiv.Perm.sign σ) = -1 by simp [this, Units.val_one, Int.cast_one, one_mul]
    simp only [σ]
    refine Equiv.Perm.sign_swap <| by grind only
  ext i j
  simp only [matrix_of_points, Matrix.submatrix, σ]
  fin_cases i <;> simp [Equiv.swap, Equiv.swapCore]

private lemma det_eq_of_rotation {p q r : PointR2} :
    (matrix_of_points p q r).det = (matrix_of_points q r p).det := by
  let σ : (Fin 3) ≃ (Fin 3) := {
    toFun := fun | 0 => 1 | 1 => 2 | 2 => 0,
    invFun := fun | 0 => 2 | 1 => 0 | 2 => 1
    left_inv := by grind
    right_inv := by grind
  }
  suffices (matrix_of_points p q r).submatrix σ id = (matrix_of_points q r p) by
    rw [← this]
    rw [Matrix.det_permute]
    suffices (Equiv.Perm.sign σ) = 1 by simp only [this, Units.val_one, Int.cast_one, one_mul]
    exact Equiv.Perm.IsThreeCycle.sign rfl
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix_of_points, σ]

variable (X : Set PointR2)

private abbrev det (p q r : PointR2) : ℝ := (matrix_of_points p q r).det

private def _vec_of_point (p : PointR2) (c : ℝ) : Fin 3 → ℝ
| 0 => p.1
| 1 => p.2
| 2 => c

private lemma _vec_of_points_linear {n : ℕ} (c : Fin n → ℝ) (f : Fin n → PointR2) :
    _vec_of_point (∑ i, (c i) • (f i)) (∑ i, c i) = ∑ i, (c i) • (_vec_of_point (f i) 1) := by
  induction n with
  | zero =>
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      ext i
      simp [_vec_of_point]
      grind only
  | succ n ih =>
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc c, Fin.sum_univ_castSucc]
      have := ih (fun i ↦ c i.castSucc) (fun i ↦ f i.castSucc)
      ext j
      fin_cases j <;>
      simp only [_vec_of_point, Prod.fst_add, Prod.snd_add, Prod.snd_sum, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, mul_one,
        Fin.isValue, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Prod.fst_sum]

private lemma _det_linear {n : ℕ} {p q r : PointR2} (c : Fin n → ℝ) (f : Fin n → PointR2)
    (hc : ∑ i, c i = 1)
    (hr : r = ∑ i, (c i) • (f i)) :
    det p q r = ∑ i, (c i) * (det p q (f i)) := by
  simp only [det]
  have : (matrix_of_points p q r) = (matrix_of_points p q r).updateRow 2 (_vec_of_point r 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> all_goals simp [matrix_of_points, _vec_of_point]
  nth_rw 3 [hr] at this
  rw [this]
  refine det_updateRow_eq_of_linear_combination c (fun i ↦ _vec_of_point (f i) 1) _ ?_
  ext j
  simp only [_vec_of_point, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases j <;> {
    simp only [Prod.fst_sum, Prod.smul_fst, Prod.snd_sum, Prod.smul_snd, smul_eq_mul, mul_one, hc]
  }

lemma det_eq_0_of_first_eq_last {p q : PointR2} :
    det p q p = 0 := by
  simp only [det, matrix_of_points]
  refine Matrix.det_zero_of_row_eq (by grind : (0 : Fin 3) ≠ 2) ?_
  ext j; fin_cases j <;> simp

private lemma cramer_rule (p q r t : PointR2) :
    (det p q r) • t = (det t q r) • p + (det p t r) • q + (det p q t) • r := by
  simp only [det, matrix_of_points, Matrix.det_fin_three]
  ext <;> { simp; ring }

private abbrev R2cc : CC X :=
  fun p q r ↦ det p q r > 0

private lemma is_nondegenerate : Nondegenerate <| R2cc X := by
  intro p q r hpqr
  simp only [R2cc, det, matrix_of_points] at hpqr
  refine ⟨?_, ?_, ?_⟩
  · intro hpeqq; subst hpeqq
    refine Std.ne_of_lt hpqr (Eq.symm ?_)
    refine Matrix.det_zero_of_row_eq Fin.zero_ne_one ?_
    ext; simp
  · intro hqeqr; subst hqeqr
    refine Std.ne_of_lt hpqr (Eq.symm ?_)
    have : (1 : Fin 3) ≠ 2 := by grind
    refine Matrix.det_zero_of_row_eq this ?_
    ext; simp
  · intro hpeqr; subst hpeqr
    refine Std.ne_of_lt hpqr (Eq.symm ?_)
    have : (0 : Fin 3) ≠ 2 := by grind
    refine Matrix.det_zero_of_row_eq this ?_
    ext; simp

private lemma is_cyclic : Cyclic <| R2cc X := by
  intro p q r hpqr
  simp only [R2cc, det] at hpqr ⊢
  suffices (matrix_of_points p q r).det = (matrix_of_points q r p).det by
    exact this ▸ hpqr
  exact det_eq_of_rotation

private lemma is_antisymm : Antisymmetric <| R2cc X := by
  intro p q r hpqr
  simp only [R2cc] at hpqr ⊢
  suffices (matrix_of_points p r q).det < 0 by exact Std.not_gt_of_lt this
  exact minus_sign_det_of_swap ▸ neg_neg_iff_pos.mpr hpqr

private lemma is_total (hX : Noncolinear X) : Total <| R2cc X := by
  intro p q r hpneq hqner hpner
  rw [R2cc, R2cc, det, minus_sign_det_of_swap]
  simp [hX p r q]

private lemma det_interior_rule {p q r t : PointR2} :
    det p q r = det t q r + det p t r + det p q t := by
  let M := !![p.1, p.2, 1, 1; q.1, q.2, 1, 1; r.1, r.2, 1, 1; t.1, t.2, 1, 1]
  have : M.det = 0 := by
    rw [← Matrix.det_transpose]
    refine Matrix.det_zero_of_row_eq (by grind : (2 : Fin 4) ≠ 3) ?_
    ext; simp [M]
  simp only [M, laplace_4x4_last_col, mul_one] at this
  repeat rw [← matrix_of_points] at this
  rw [@minus_sign_det_of_swap p q r] at this
  simp only [det]
  rw [minus_sign_det_of_swap]
  rw [@det_eq_of_rotation t q r]
  rw [@minus_sign_det_of_swap p t r]
  grind

private lemma is_interior : Interior <| R2cc X := by
  intro ⟨p, hp⟩ ⟨q, hq⟩ ⟨r, hr⟩ ⟨t, ht⟩ htsp htsq htsr
  let M := !![p.1, p.2, 1, 1; q.1, q.2, 1, 1; r.1, r.2, 1, 1; t.1, t.2, 1, 1]
  have : M.det = 0 := by
    rw [← Matrix.det_transpose]
    refine Matrix.det_zero_of_row_eq (by grind : (2 : Fin 4) ≠ 3) ?_
    ext; simp [M]
  simp_all only[R2cc, det]
  simp only [M, laplace_4x4_last_col, mul_one] at this
  repeat rw [← matrix_of_points] at this
  rw [@minus_sign_det_of_swap p q r] at this
  have : (matrix_of_points p r t).det
      = (matrix_of_points q r t).det + (matrix_of_points p q t).det
        + (matrix_of_points p r q).det := by grind
  grind

private lemma is_transitive (hX : Noncolinear X) : Transitive <| R2cc X := by
  intro ⟨p, hp⟩ ⟨r, hr⟩ ⟨t, ht⟩ ⟨q, hq⟩ ⟨s, hs⟩ hpner htsp htsq htsr htpq htqr
  have htnep : (⟨t, ht⟩ : X) ≠ ⟨p, hp⟩ := by grind [is_nondegenerate X htsp]
  have htner : (⟨t, ht⟩ : X) ≠ ⟨r, hr⟩ := by grind [is_nondegenerate X htqr]
  refine (is_total X hX htnep hpner htner).elim (·) (fun htrp ↦ ?_)
  have hcramer := cramer_rule p q r t
  have hpqr : R2cc X ⟨p, hp⟩ ⟨q, hq⟩ ⟨r, hr⟩ :=
    is_interior X htqr (is_cyclic X <| is_cyclic X htrp) (is_cyclic X htpq)
  have : t = ((det t q r) / (det p q r)) • p + ((det p t r) / (det p q r)) • q
      + ((det p q t) / (det p q r)) • r := by
    have hpqrne0 : det p q r ≠ 0 := Ne.symm <| Std.ne_of_lt hpqr
    have : (det p q r)⁻¹ • (det p q r • t)
        = (det p q r)⁻¹ • (det t q r • p + det p t r • q + det p q t • r) := by
      simp only [hcramer, smul_add, smul_smul]
    simp only [smul_smul, inv_mul_cancel₀ hpqrne0, smul_add, one_smul] at this
    repeat rw [inv_mul_eq_div] at this
    exact this
  suffices (det t s t) > 0 by
    simp only [det_eq_0_of_first_eq_last, gt_iff_lt, lt_self_iff_false] at this
  let c : Fin 3 → ℝ
  | 0 => (det t q r / det p q r)
  | 1 => (det p t r / det p q r)
  | 2 => (det p q t / det p q r)
  let f : Fin 3 → PointR2
  | 0 => p
  | 1 => q
  | 2 => r
  have : t = ∑ i, (c i) • (f i) := by
    rw [this]
    simp only [Fin.sum_univ_castSucc, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton, Fin.castSucc_zero, Fin.reduceLast, Fin.castSucc_one, c, f]
  nth_rw 2 [this]
  rw [_det_linear c f ?_ rfl]
  · simp only [Fin.sum_univ_castSucc, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton, Fin.castSucc_zero, Fin.reduceLast, Fin.castSucc_one, gt_iff_lt, c, f]
    unfold R2cc at *
    suffices 0 < (det t q r * det t s p + det p t r * det t s q + det p q t * det t s r)
        / (det p q r) by
      grind only
    refine div_pos ?_ hpqr
    repeat refine Right.add_pos' ?_ ?_
    · exact Left.mul_pos htqr htsp
    · exact Left.mul_pos (lt_of_lt_of_eq htrp <| det_eq_of_rotation.symm) htsq
    · exact Left.mul_pos (lt_of_lt_of_eq htpq <| det_eq_of_rotation) htsr
  · simp only [Fin.sum_univ_castSucc, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton, Fin.castSucc_zero, Fin.reduceLast, Fin.castSucc_one, c]
    repeat rw [← add_div]
    rw [← det_interior_rule]
    refine (div_eq_one_iff_eq ?_).mpr rfl
    exact hX ⟨p, hp⟩ ⟨q, hq⟩ ⟨r, hr⟩

@[blueprint "def-CCSystem-ofR2"
  (statement := /-- Construct A CC system from a set of noncolinear points in $\mathbb{R}^2$. -/)]
def CCSystem.of_R2_set (X : Set PointR2) (hX : Noncolinear X) : CCSystem X where
  cc := R2cc X
  cyclic := is_cyclic X
  antisymm := is_antisymm X
  nondegenerate := is_nondegenerate X
  transitive := is_transitive X hX
  total := is_total X hX
  interiority := is_interior X
