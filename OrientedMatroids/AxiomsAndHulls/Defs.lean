namespace AxiomsAndHulls

universe u

-- Knuth's CC-systems (counter-clockwise systems)
abbrev CC (α : Type u) := α → α → α → Prop

section

variable {α : Type u} (cc : CC α)

-- Require that {p q r} contains 3 distinct elements, unnamed in Knuth's textbook
def Nondegenerate : Prop :=
  ∀ {p q r : α}, cc p q r → p ≠ q ∧ q ≠ r ∧ p ≠ r

-- Knuth's axiom 1
def Cyclic : Prop :=
  ∀ {p q r : α}, cc p q r → cc q r p

-- Knuth's axiom 2
def Antisymmetric : Prop :=
  ∀ {p q r : α}, cc p q r → ¬ cc p r q

-- Knuth's axiom 3 (called nondegeneracy in the textbook)
def Total : Prop :=
  ∀ {p q r : α}, p ≠ q → q ≠ r → p ≠ r → cc p q r ∨ cc p r q

-- Jnuth's axiom 4
def Interior : Prop :=
  ∀ {p t q r : α}, cc t q r → cc p t r → cc p q t → cc p q r

-- Knuth's axiom 5
def Transitive  : Prop :=
  ∀ {p r t : α} (q s : α), p ≠ r → cc t s p → cc t s q → cc t s r → cc t p q → cc t q r → cc t p r

-- Knuth's axiom 5'
def DualTransitive : Prop :=
  ∀ {p q r s t : α}, p ≠ r → cc s t p → cc s t q → cc s t r → cc t p q → cc t q r → cc t p r

def VortexFree : Prop :=
  ∀ {t p q r s : α}, p ≠ s → p ≠ r → p ≠ t → q ≠ s → q ≠ t → r ≠ s → r ≠ t → s ≠ t →
    (cc t p s ∨ cc t q s ∨ cc t r s ∨ (cc t q p ∨ cc t r q ∨ cc t p r)) ∧
    (cc s p t ∨ cc s q t ∨ cc s r t ∨ (cc t q p ∨ cc t r q ∨ cc t p r))

end

@[ext]
structure WeakPreCCSystem (α : Type u) where
  cc : CC α
  antisymm : Antisymmetric cc
  nondegenerate : Nondegenerate cc
  transitive : Transitive cc
  dualTransitive : DualTransitive cc
  total : Total cc

@[ext]
structure PreCCSystem (α : Type u) where
  cc : CC α
  cyclic : Cyclic cc
  antisymm : Antisymmetric cc
  nondegenerate : Nondegenerate cc
  transitive : Transitive cc
  total : Total cc

theorem PreCCSystem.cyclic2 {α : Type u} {S : PreCCSystem α} {p q r : α} :
    S.cc p q r → S.cc r p q :=
  (S.cyclic <| S.cyclic ·)

structure CCSystem (α : Type u) extends PreCCSystem α where
  interiority : Interior cc

end AxiomsAndHulls
