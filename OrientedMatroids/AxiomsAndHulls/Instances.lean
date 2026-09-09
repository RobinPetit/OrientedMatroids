import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith

import OrientedMatroids.AxiomsAndHulls.Defs

open AxiomsAndHulls
-- open Matrix

private lemma Fin1_sum {M : Type*} [AddCommMonoid M] {f : Fin 1 → M} :
    ∑ i, f i = f 0 := by
  simp

private lemma Fin2_sum {M : Type*} [AddCommMonoid M] {f : Fin 2 → M} :
    ∑ i, f i = f 0 + f 1 := by
  simp

private lemma Fin3_sum {M : Type*} [AddCommMonoid M] {f : Fin 3 → M} :
    ∑ i, f i = f 0 + f 1 + f 2 := by
  simp only [Finset.sum, Fin.univ_val_map, List.ofFn_succ, Fin.isValue, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, List.ofFn_zero, Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]
  grind only

private lemma Fin4_sum {M : Type*} [AddCommMonoid M] {f : Fin 4 → M} :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  simp only [Finset.sum, Fin.univ_val_map, List.ofFn_succ, Fin.isValue, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, List.ofFn_zero, Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]
  grind only

private lemma laplace_4x4_last_col {M : Type*} [CommRing M]
    {a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 : M}
    :
    !![a11, a12, a13, a14;
      a21, a22, a23, a24;
      a31, a32, a33, a34;
      a41, a42, a43, a44].det =
    !![a21, a22, a23; a31, a32, a33; a41, a42, a43].det * a14
      - !![a11, a12, a13; a31, a32, a33; a41, a42, a43].det * a24
      + !![a11, a12, a13; a21, a22, a23; a41, a42, a43].det * a34
      - !![a11, a12, a13; a21, a22, a23; a31, a32, a33].det * a44 := by
  sorry

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
  sorry
  -- induction n with
  -- | zero =>
  --     simp only [Finset.univ_eq_empty, Finset.sum_empty]
  --     ext i
  --     simp [_vec_of_point]
  --     grind only
  -- | succ n ih =>
  --     --
  --     rw [Fin.sum_univ_castSucc]
  --     rw [Fin.sum_univ_castSucc c]
  --     rw [Fin.sum_univ_castSucc]
  --     have := ih (fun i ↦ c i.castSucc) (fun i ↦ f i.castSucc)
  --     ext j
  --     fin_cases j
  --     · simp
  --       sorry
  --     · sorry
  --     · sorry

private lemma TMP {n : ℕ} {p q r : PointR2} (c : Fin n → ℝ) (f : Fin n → PointR2)
    (hc : ∑ i, c i = 1) (hr : r = ∑ i, (c i) • (f i)) :
    det p q r = ∑ i, (c i) * (det p q (f i)) := by
  simp only [det]
  have : (matrix_of_points p q r) = (matrix_of_points p q r).updateRow 2 (_vec_of_point r 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> all_goals simp [matrix_of_points, _vec_of_point]
  nth_rw 3 [hr] at this
  rw [← hc, _vec_of_points_linear] at this
  simp? [Matrix.det_updateRow_add, Matrix.det_updateRow_smul] at this
  induction n with
  | zero =>
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hr hc ⊢
      exact eq_zero_of_zero_eq_one hc (det p q r)
  | succ n => ?_
  sorry

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

private lemma is_nondegenerate : Nondegeneracy <| R2cc X := by
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

private lemma is_cyclic : Cyclicity <| R2cc X := by
  intro p q r hpqr
  simp only [R2cc, det] at hpqr ⊢
  suffices (matrix_of_points p q r).det = (matrix_of_points q r p).det by
    exact this ▸ hpqr
  exact det_eq_of_rotation

private lemma is_antisymm : Antisymmetry <| R2cc X := by
  intro p q r hpqr
  simp only [R2cc] at hpqr ⊢
  suffices (matrix_of_points p r q).det < 0 by exact Std.not_gt_of_lt this
  exact minus_sign_det_of_swap ▸ neg_neg_iff_pos.mpr hpqr

private lemma is_total (hX : Noncolinear X) : Totality <| R2cc X := by
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
  simp only [sub_neg_eq_add] at this
  simp only [det]
  rw [minus_sign_det_of_swap]
  rw [@det_eq_of_rotation t q r]
  rw [@minus_sign_det_of_swap p t r]
  grind

private lemma is_interior : Interiority <| R2cc X := by
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

private lemma is_transitive (hX : Noncolinear X) : Transitivity <| R2cc X := by
  intro ⟨p, hp⟩ ⟨r, hr⟩ ⟨t, ht⟩ ⟨q, hq⟩ ⟨s, hs⟩ hpner htsp htsq htsr htpq htqr
  have htnep : (⟨t, ht⟩ : X) ≠ ⟨p, hp⟩ := by grind [is_nondegenerate X htsp]
  have htner : (⟨t, ht⟩ : X) ≠ ⟨r, hr⟩ := by grind [is_nondegenerate X htqr]
  refine (is_total X hX htnep hpner htner).elim (·) (fun htrp ↦ ?_)
  -- have := @det_interior_rule p q r t
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
    grind => ring
  suffices (det t s t) > 0 by
    simp only [det_eq_0_of_first_eq_last, gt_iff_lt, lt_self_iff_false] at this
  nth_rw 2 [this]
  simp only [det, matrix_of_points]
  simp?
  calc (det t s t)
    _ = (det t s ()) := by
      sorry
    _ > 0 :=
    sorry

def CCSystem_of_R2_set (X : Set PointR2) (hX : Noncolinear X) : CCSystem X where
  cc := R2cc X
  cyclic := is_cyclic X
  antisymm := is_antisymm X
  nondegenerate := is_nondegenerate X
  transitive := is_transitive X hX
  total := is_total X hX
  interiority := is_interior X
