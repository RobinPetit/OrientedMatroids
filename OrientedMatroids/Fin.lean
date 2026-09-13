import Mathlib.Algebra.BigOperators.Fin

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

