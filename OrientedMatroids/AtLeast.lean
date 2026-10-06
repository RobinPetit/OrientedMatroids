/-
Copyright (c) 2026 Jean Cardinal & Robin Petit. All rights reserved.
Released under MIT NON-AI license as described in the file LICENSE.
Authors: Jean Cardinal, Robin Petit
-/

import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Ring.Nat

/-!
DOCSTRING: TODO
-/

class AtLeast (m n : ℕ) where
  le : m ≤ n

abbrev AtLeastOne (n : ℕ) := AtLeast 1 n
abbrev AtLeastTwo (n : ℕ) := AtLeast 2 n
abbrev AtLeastThree (n : ℕ) := AtLeast 3 n

instance (n : ℕ) [NeZero n] : AtLeastOne n := ⟨Nat.one_le_iff_ne_zero.mpr <| NeZero.ne n⟩
instance (n : ℕ) [inst : AtLeastOne n] : NeZero n := ⟨Nat.ne_zero_of_lt inst.le⟩
instance (n : ℕ) [inst : AtLeastTwo n] : AtLeastOne n := ⟨le_trans one_le_two inst.le⟩
instance (n : ℕ) [inst : AtLeastThree n] : AtLeastTwo n := ⟨le_trans (by lia) inst.le⟩

namespace AtLeastOne
variable {n : ℕ} [AtLeastOne n]
@[simp] lemma pos : 0 < n := Nat.zero_lt_of_ne_zero <| NeZero.ne n
@[simp] lemma one_le : 1 ≤ n := AtLeast.le
end AtLeastOne

namespace AtLeast
open AtLeastOne

variable {n : ℕ}
@[simp] lemma sub_nonzero_le (k : ℕ) : n - k ≤ n := Nat.sub_le ..
@[simp] lemma sub_one_le : n - 1 ≤ n := sub_nonzero_le _
@[simp] lemma sub_two_le : n - 2 ≤ n := sub_nonzero_le _
@[simp] lemma sub_three_le : n - 3 ≤ n := sub_nonzero_le _

variable [AtLeastOne n]
@[simp] lemma sub_nonzero_lt (k : ℕ) [NeZero k] : n - k < n := Nat.sub_lt pos pos
@[simp] lemma sub_one_lt : n - 1 < n := sub_nonzero_lt _
@[simp] lemma sub_two_lt : n - 2 < n := sub_nonzero_lt _
@[simp] lemma sub_three_lt : n - 3 < n := sub_nonzero_lt _
end AtLeast

namespace AtLeastTwo
variable {n : ℕ} [AtLeastTwo n]
@[simp] lemma one_lt : 1 < n := lt_of_lt_of_le (0 : ℕ).one_lt_succ_succ AtLeast.le
@[simp] lemma two_le : 2 ≤ n := AtLeast.le
@[simp] lemma sub_two_lt_sub_one : n - 2 < n - 1 := Nat.sub_succ_lt_self _ _ one_lt
@[simp] lemma sub_two_ne_sub_one : n - 2 ≠ n - 1 := ne_of_lt AtLeastTwo.sub_two_lt_sub_one

instance (n : ℕ) [AtLeastTwo n] : NeZero (n - 1) := NeZero.of_pos <| Nat.zero_lt_sub_of_lt one_lt
instance (n : ℕ) [AtLeastTwo n] : AtLeastOne (n - 1) := by infer_instance
end AtLeastTwo

namespace AtLeastThree
variable {n : ℕ} [AtLeastThree n]
@[simp] lemma two_lt : 2 < n := Nat.lt_of_succ_le AtLeast.le
@[simp] lemma three_le : 3 ≤ n := AtLeast.le

@[simp] lemma sub_three_lt_sub_two : n - 3 < n - 2 := Nat.sub_succ_lt_self n 2 two_lt
@[simp] lemma sub_three_lt_sub_one : n - 3 < n - 1 :=
  lt_trans sub_three_lt_sub_two AtLeastTwo.sub_two_lt_sub_one

instance (n : ℕ) [AtLeastThree n] : NeZero (n - 2) := NeZero.of_pos <| Nat.sub_pos_of_lt two_lt
instance (n : ℕ) [AtLeastThree n] : AtLeastTwo (n - 1) := ⟨Nat.le_sub_one_of_lt two_lt⟩
instance (n : ℕ) [AtLeastThree n] : AtLeastOne (n - 2) := by infer_instance
end AtLeastThree

instance : AtLeastOne 1 := ⟨le_rfl⟩
instance : AtLeastTwo 2 := ⟨le_rfl⟩
instance : AtLeastThree 3 := ⟨le_rfl⟩
