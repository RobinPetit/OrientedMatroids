/-
Copyright (c) 2026 Jean Cardinal & Robin Petit. All rights reserved.
Released under MIT NON-AI license as described in the file LICENSE.
Authors: Jean Cardinal, Robin Petit
-/

import Architect

namespace AxiomsAndHulls

universe u

-- Knuth's CC-systems (counter-clockwise systems)
@[blueprint "def-CC"
  (statement := /-- A \emph{CC} is a triplet predicate.
    If the CC is unambiguous, its evaluation on the triplet $(p, q, r)$ is typically denoted
    by $pqr$. -/)]
abbrev CC (α : Type u) := α → α → α → Prop

namespace CC

variable {α : Type u} (cc : CC α)

-- Require that {p q r} contains 3 distinct elements, unnamed in Knuth's textbook
@[blueprint "def-CC-Nondegenerate"
  (statement := /-- A CC is \emph{nondegenerate} if it evaluated to true only if its arguments
    are pairwsie distinct. -/)]
def Nondegenerate : Prop :=
  ∀ {p q r : α}, cc p q r → p ≠ q ∧ q ≠ r ∧ p ≠ r

-- Knuth's axiom 1
@[blueprint "def-CC-Cyclic"
  (statement := /-- A CC is \emph{cyclic} if it is invariant under a cyclic permutation of
    its arguments. -/)]
def Cyclic : Prop :=
  ∀ {p q r : α}, cc p q r → cc q r p

-- Knuth's axiom 2
@[blueprint "def-CC-Antisymmetric"
  (statement := /-- A CC is \emph{antisymmetric} if $pqr$ and $prq$ cannot be true
    simultaneously. -/)]
def Antisymmetric : Prop :=
  ∀ {p q r : α}, cc p q r → ¬ cc p r q

-- Knuth's axiom 3 (called nondegeneracy in the textbook)
@[blueprint "def-CC-Total"
  (statement := /-- A CC is \emph{total} if every triplet $(p, q, r)$ satisfies either $pqr$
    or $prq$. -/)]
def Total : Prop :=
  ∀ {p q r : α}, p ≠ q → q ≠ r → p ≠ r → cc p q r ∨ cc p r q

-- Knuth's axiom 4
@[blueprint "def-CC-Interior"
  (statement := /-- A CC satisfies the \emph{interiority property} if every triplet $(p, q, r)$ satisfies either $pqr$
    or $prq$. -/)]
def Interior : Prop :=
  ∀ {p t q r : α}, cc t q r → cc p t r → cc p q t → cc p q r

-- Knuth's axiom 5
@[blueprint "def-CC-Transitive"
  (statement := /-- A CC is \emph{transitive} whenever for every $p, q, r, s, t \in X$ with
    $p \ne r \land tsp \land tsq \land tsr \land tpq \land tqr$, we have $tpr$. -/)]
def Transitive  : Prop :=
  ∀ {p r t : α} (q s : α), p ≠ r → cc t s p → cc t s q → cc t s r → cc t p q → cc t q r → cc t p r

-- Knuth's axiom 5'
def DualTransitive : Prop :=
  ∀ {p q r s t : α}, p ≠ r → cc s t p → cc s t q → cc s t r → cc t p q → cc t q r → cc t p r

def VortexFree : Prop :=
  ∀ {t p q r s : α}, p ≠ s → p ≠ r → p ≠ t → q ≠ s → q ≠ t → r ≠ s → r ≠ t → s ≠ t →
    (cc t p s ∨ cc t q s ∨ cc t r s ∨ (cc t q p ∨ cc t r q ∨ cc t p r)) ∧
    (cc s p t ∨ cc s q t ∨ cc s r t ∨ (cc t q p ∨ cc t r q ∨ cc t p r))

end CC

@[ext]
structure WeakPreCCSystem (α : Type u) where
  cc : CC α
  antisymm : cc.Antisymmetric
  nondegenerate : cc.Nondegenerate
  transitive : cc.Transitive
  dualTransitive : cc.DualTransitive
  total : cc.Total

@[ext, blueprint "def-PreCCSystem" (statement := /--
    A \emph{pre CC-system} is a CC (see Definition~\ref{def-CC}) that is nondegenerate, cyclic,
    antisymmetric, total and transitive
    (see Definitions~\ref{def-CC-Nondegenerate},~\ref{def-CC-Cyclic},~\ref{def-CC-Antisymmetric},
    \ref{def-CC-Total}~and~\ref{def-CC-Transitive}). -/)]
structure PreCCSystem (α : Type u) where
  cc : CC α
  cyclic : cc.Cyclic
  antisymm : cc.Antisymmetric
  nondegenerate : cc.Nondegenerate
  transitive : cc.Transitive
  total : cc.Total

theorem PreCCSystem.cyclic2 {α : Type u} {S : PreCCSystem α} {p q r : α} :
    S.cc p q r → S.cc r p q :=
  (S.cyclic <| S.cyclic ·)

@[blueprint "def-CCSystem" (statement := /-- A \emph{CC-system} is a pre CC-system that satisfies
    the interiority property (see Definition~\ref{def-CC-Interior}). -/)]
structure CCSystem (α : Type u) extends PreCCSystem α where
  interiority : cc.Interior

end AxiomsAndHulls
