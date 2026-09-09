/-
Copyright (c) 2026 Jean Cardinal & Robin Petit. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Cardinal, Robin Petit
-/

import Mathlib.Data.Sign.Defs
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Combinatorics.Matroid.Rank.ENat

/-!
DOCSTRING: TODO
-/

open Equiv
open SignType

variable {α : Type*}
-- the rank (dimension) is at least three
variable {d : ℕ} {hdge3 : d ≥ 3}

-- predicate now gives a sign for each d-tuple we choose to allow duplicates
abbrev Orientation (d : ℕ) (α : Type*) :=
  (Fin d → α) → SignType

-- appends an element to a m-1 vector to yield an m vector
abbrev append (v : Fin (d - 1) → α) (e : α) : Fin d → α :=
  fun i ↦ if h : (i.val < d - 1) then v ⟨i.val, h⟩ else e

-- append twice or thrice - should be useful
abbrev c2 (t : Fin (d - 2) → α) (a b : α) : Fin d → α :=
  append (append t a) b
abbrev c3 (t : Fin (d - 3) → α) (a b c : α) : Fin d → α :=
  append (c2 t a b) c

def pref (t : Fin d → α) : Fin (d - 1) → α :=
  fun i ↦ t ⟨i, Nat.lt_of_lt_pred i.2⟩

namespace Equiv
namespace Perm
-- the sign of a permutation
def sign' {d : ℕ} (σ : Perm (Fin d)) : SignType :=
  if σ.sign = 1 then pos else neg
end Perm
end Equiv

-- Alternating : permuting the components multiplies by the sign of the permutation
def Alternating (χ : Orientation d α) : Prop :=
  ∀ (σ : Perm (Fin d)) (v : Fin d → α), χ (v ∘ σ) = σ.sign' * χ v

-- Uniformity : + or - iff distinct elements
def Uniformity (χ : Orientation d α) : Prop :=
  ∀ f, (χ f ≠ zero) ↔ f.Injective

def GP3 (χ : Orientation d α) : Prop :=
  ∀ x : Fin (d - 2) → α, ∀ s p q r : α,
    let t1 := (χ (c2 x s r)) * (χ (c2 x p q))
    let t2 := (χ (c2 x s p)) * (χ (c2 x q r))
    let t3 := (χ (c2 x s q)) * (χ (c2 x p r))
    (t1 ≥ 0 → t2 ≥ 0 → t3 ≥ 0)

-- definition of a uniform oriented matroid
structure UOM (d : ℕ) (α : Type*) where
  χ : Orientation d α
  alternating : Alternating χ
  uniform : Uniformity χ
  GP3 : GP3 χ

structure OM (α : Type*) where
  M : Matroid α
  finite : M.E.Finite
  χ : Orientation M.eRank.toNat α
  alternating : Alternating χ
  GP3 : GP3 χ
  basesNonZero : ∀ f, χ f ≠ zero ↔ Matroid.IsBasis M (Set.range f) M.E

namespace Orientation

abbrev IsArc (χ : Orientation d α) (t : Fin (d - 2) → α) (a b : α) : Prop :=
  χ (c2 t a b) = pos

end Orientation

abbrev arc (χ : Orientation d α) (t : Fin (d - 2) → α) (a b : α) : Prop :=
  χ.IsArc t a b


-- Knuth's transitivity axiom in terms of arcs of a tournament
-- this is simply forbidding a vortex with a source
def Transitivity (χ : Orientation d α) : Prop :=
  ∀ t : Fin (d - 2) → α, ∀ s p q r : α,
    p ≠ r → arc χ t s p → arc χ t s q → arc χ t s r → arc χ t p q → arc χ t q r → arc χ t p r

-- we define Knuth's oriented matroids!
structure KOM (d : ℕ) (α : Type*) where
  χ : Orientation d α
  alternating : Alternating χ
  uniform : Uniformity χ
  transitive : Transitivity χ

-- generalized dual transitivity -- forbids a vortex with a sink
def DualTransitivity (χ : Orientation d α) : Prop :=
  ∀ t s p q r,
    p ≠ r → arc χ t p s → arc χ t q s → arc χ t r s → arc χ t p q → arc χ t q r → arc χ t p r

instance (α : Type*) : Coe (OM α) (Matroid α) :=
  ⟨(·.M)⟩
