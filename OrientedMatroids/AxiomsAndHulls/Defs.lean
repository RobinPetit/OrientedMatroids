namespace AxiomsAndHulls

universe u

-- Knuth's CC-systems (counter-clockwise systems)
def CC (α : Type u) := α → α → α → Prop

section

variable {α : Type u} (cc : CC α)

-- Require that {p q r} contains 3 distinct elements, unnamed in Knuth's textbook
def Nondegeneracy : Prop :=
  ∀ {p q r : α}, cc p q r → p ≠ q ∧ q ≠ r ∧ p ≠ r

-- Knuth's axiom 1
def Cyclicity : Prop :=
  ∀ {p q r : α}, cc p q r → cc q r p

-- Knuth's axiom 2
def Antisymmetry : Prop :=
  ∀ {p q r : α}, cc p q r → ¬ cc p r q

-- Knuth's axiom 3 (called nondegeneracy in the textbook)
def Totality : Prop :=
  ∀ {p q r : α}, p ≠ q → q ≠ r → p ≠ r → cc p q r ∨ cc p r q

-- Jnuth's axiom 4
def Interiority : Prop :=
  ∀ {p t q r : α}, cc t q r → cc p t r → cc p q t → cc p q r

-- Knuth's axiom 5
def Transitivity  : Prop :=
  ∀ {p r t : α} (q s : α), p ≠ r → cc t s p → cc t s q → cc t s r → cc t p q → cc t q r → cc t p r

-- Knuth's axiom 5'
def DualTransitivy : Prop :=
  ∀ {p q r s t : α}, (cc s t p ∧ cc s t q ∧ cc s t r ∧ cc t p q ∧ cc t q r) → cc t p r

end

structure PreCCSystem (α : Type u) where
  cc : CC α
  cyclic : Cyclicity cc
  antisymm : Antisymmetry cc
  nondegenerate : Nondegeneracy cc
  transitive : Transitivity cc
  total : Totality cc

structure CCSystem (α : Type u) extends PreCCSystem α where
  interiority : Interiority cc

end AxiomsAndHulls
