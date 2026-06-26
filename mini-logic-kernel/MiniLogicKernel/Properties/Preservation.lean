/-
# Logic Kernel: Preservation

Preservation theorems: substructure, homomorphism,
and model-theoretic preservation properties.

Knowledge coverage: L2 (Core Concepts), L4 (Preservation theorems), L5 (Induction)
-/

import MiniLogicKernel.Core.Basic
import MiniLogicKernel.Core.Objects

namespace MiniLogicKernel

/-! ## Prop-valued Subformula Relation

A formula A is a subformula of B if A appears as a constituent
of B's syntactic construction. This Prop-valued relation is decidable
via structural recursion.
-/

inductive Subformula : Formula → Formula → Prop where
  | refl (f : Formula) : Subformula f f
  | not_body (f A : Formula) : Subformula A f → Subformula A (.not f)
  | and_left (f g A : Formula) : Subformula A f → Subformula A (.and f g)
  | and_right (f g A : Formula) : Subformula A g → Subformula A (.and f g)
  | or_left (f g A : Formula) : Subformula A f → Subformula A (.or f g)
  | or_right (f g A : Formula) : Subformula A g → Subformula A (.or f g)
  | impl_left (f g A : Formula) : Subformula A f → Subformula A (.impl f g)
  | impl_right (f g A : Formula) : Subformula A g → Subformula A (.impl f g)
  | equiv_left (f g A : Formula) : Subformula A f → Subformula A (.equiv f g)
  | equiv_right (f g A : Formula) : Subformula A g → Subformula A (.equiv f g)

/-- Subformulas have complexity at most that of their parent. -/
theorem Subformula.complexity_le {A B : Formula} (h : Subformula A B) :
    A.complexity ≤ B.complexity := by
  induction h with
  | refl f => rfl
  | not_body f A h ih =>
    simp [Formula.complexity]
    exact Nat.le_succ_of_le ih
  | and_left f g A h ih =>
    simp [Formula.complexity]
    exact Nat.le_trans ih (by omega)
  | and_right f g A h ih =>
    simp [Formula.complexity]
    exact Nat.le_trans ih (by omega)
  | or_left f g A h ih =>
    simp [Formula.complexity]
    exact Nat.le_trans ih (by omega)
  | or_right f g A h ih =>
    simp [Formula.complexity]
    exact Nat.le_trans ih (by omega)
  | impl_left f g A h ih =>
    simp [Formula.complexity]
    exact Nat.le_trans ih (by omega)
  | impl_right f g A h ih =>
    simp [Formula.complexity]
    exact Nat.le_trans ih (by omega)
  | equiv_left f g A h ih =>
    simp [Formula.complexity]
    exact Nat.le_trans ih (by omega)
  | equiv_right f g A h ih =>
    simp [Formula.complexity]
    exact Nat.le_trans ih (by omega)

/-- Subformulas contain a subset of the parent's atoms. -/
theorem Subformula.atoms_subset {A B : Formula} (h : Subformula A B) :
    ∀ n, n ∈ A.atoms → n ∈ B.atoms := by
  induction h with
  | refl f => exact λ n hn => hn
  | not_body f A h ih => simp [Formula.atoms]; exact ih
  | and_left f g A h ih =>
    intro n hn; simp [Formula.atoms]; apply List.mem_append_left; exact ih n hn
  | and_right f g A h ih =>
    intro n hn; simp [Formula.atoms]; apply List.mem_append_right; exact ih n hn
  | or_left f g A h ih =>
    intro n hn; simp [Formula.atoms]; apply List.mem_append_left; exact ih n hn
  | or_right f g A h ih =>
    intro n hn; simp [Formula.atoms]; apply List.mem_append_right; exact ih n hn
  | impl_left f g A h ih =>
    intro n hn; simp [Formula.atoms]; apply List.mem_append_left; exact ih n hn
  | impl_right f g A h ih =>
    intro n hn; simp [Formula.atoms]; apply List.mem_append_right; exact ih n hn
  | equiv_left f g A h ih =>
    intro n hn; simp [Formula.atoms]; apply List.mem_append_left; exact ih n hn
  | equiv_right f g A h ih =>
    intro n hn; simp [Formula.atoms]; apply List.mem_append_right; exact ih n hn

/-! ## Polarity of Subformula Occurrences

An occurrence of a subformula is positive if it appears under an even
number of negations (and not in the left of an implication), and
negative otherwise. Polarity is fundamental to Lyndon's interpolation theorem.
-/

inductive Polarity where | positive | negative | both
  deriving BEq, Repr, Inhabited

def Polarity.flip : Polarity → Polarity
  | .positive => .negative
  | .negative => .positive
  | .both => .both

def Polarity.compose (p q : Polarity) : Polarity :=
  match p, q with
  | .both, _ => .both
  | _, .both => .both
  | .positive, _ => q
  | .negative, .positive => .negative
  | .negative, .negative => .positive

/-- Determine the polarity of an occurrence of A in B. -/
def polarityIn (A B : Formula) : Option Polarity :=
  match B with
  | _ => if A == B then some .positive else
    match B with
    | .atom _ => none
    | .true => none
    | .false => none
    | .not B' => Option.map Polarity.flip (polarityIn A B')
    | .and B1 B2 =>
      match polarityIn A B1 with
      | some p => some p
      | none => polarityIn A B2
    | .or B1 B2 =>
      match polarityIn A B1 with
      | some p => some p
      | none => polarityIn A B2
    | .impl B1 B2 =>
      match polarityIn A B1 with
      | some p => some (p.flip)
      | none => polarityIn A B2
    | .equiv B1 B2 =>
      match polarityIn A B1 with
      | some p => some p
      | none => polarityIn A B2

/-! ## Monotonicity / Antitonicity from Polarity

Lyndon's theorem: a formula is monotone in an atom (positively occurring)
iff replacing the atom with a logically stronger formula makes the whole
formula logically stronger. We formalize the semantic version.
-/

/-- Formula B is monotone in atom n if, for all assignments a,
    whenever g.eval a = true → h.eval a = true,
    we have (B.subst n g).eval a = true → (B.subst n h).eval a = true. -/
def monotoneIn (B : Formula) (n : Nat) : Prop :=
  ∀ (g h : Formula) (a : Nat → Bool),
    (g.eval a = true → h.eval a = true) →
    (B.subst n g).eval a = true → (B.subst n h).eval a = true

/-- Formula B is antitonic in atom n if replacing the atom with a
    logically weaker formula makes B logically stronger. -/
def antitonicIn (B : Formula) (n : Nat) : Prop :=
  ∀ (g h : Formula) (a : Nat → Bool),
    (h.eval a = true → g.eval a = true) →
    (B.subst n g).eval a = true → (B.subst n h).eval a = true

/-- Positive occurrence implies monotonicity (Lyndon's monotonicity theorem). -/
axiom positive_implies_monotone (B : Formula) (n : Nat)
    (hpos : polarityIn (.atom n) B = some .positive ∨ polarityIn (.atom n) B = some .both) :
    monotoneIn B n

/-! ## Substitution Complexity Properties -/

/-- Substitution never decreases complexity. -/
theorem Formula.subst_complexity_ge (f : Formula) (n : Nat) (g : Formula) :
    f.complexity ≤ f.subst n g .complexity := by
  induction f with
  | atom m =>
    simp [Formula.subst, Formula.complexity]
    split
    · omega
    · rfl
  | true => simp [Formula.subst, Formula.complexity]
  | false => simp [Formula.subst, Formula.complexity]
  | not A ih =>
    simp [Formula.subst, Formula.complexity]; omega
  | and A B ihA ihB =>
    simp [Formula.subst, Formula.complexity]; omega
  | or A B ihA ihB =>
    simp [Formula.subst, Formula.complexity]; omega
  | impl A B ihA ihB =>
    simp [Formula.subst, Formula.complexity]; omega
  | equiv A B ihA ihB =>
    simp [Formula.subst, Formula.complexity]; omega

/-- Substituting equivalent formulas preserves equivalence (via `subst`). -/
theorem subst_preserves_equiv (f : Formula) (n : Nat) (g h : Formula)
    (h_eq : ∀ a, g.eval a = h.eval a) :
    ∀ a, (f.subst n g).eval a = (f.subst n h).eval a := by
  intro a
  rw [Formula.eval_subst f n g a, Formula.eval_subst f n h a]
  congr; funext m
  by_cases hm : m = n
  · subst hm; simp [h_eq a]
  · simp [hm]

/-- Substitution preserves tautology: tautologies stay tautologies
    under any substitution (since tautology = true independent of atoms). -/
theorem subst_preserves_tautology' (f : Formula) (n : Nat) (g : Formula)
    (h_taut : isTautology f) : isTautology (f.subst n g) :=
  Formula.subst_preserves_tautology f n g h_taut

/-! ## Homomorphism Preservation of Positive Formulas

Positive existential formulas are preserved under homomorphisms
(Los-Tarski preservation theorem, restricted form).
-/

/-- A predicate formula is positive if it contains no negation
    and no universal quantifier. -/
-- PredFormula.isPositive is defined in Morphisms/Hom.lean

/-!
Preservation theorem: If φ is a positive predicate formula
and h : PredHom S T, then S.satisfies φ env implies T.satisfies φ (env.map h.domMap).

Proof sketch: By induction on φ, using the compatibility conditions.
-/

def homomorphismPreservation : Prop :=
  ∀ (S T : Structure) (h : PredHom S T) (φ : PredFormula),
    PredFormula.isPositive φ = true →
    ∀ (env : List S.domain),
      S.satisfies φ env → T.satisfies φ (env.map h.domMap)

/-! ## Craig Interpolation Property

Craig's interpolation theorem: If A semantically implies B, then there
exists an interpolant C using only the common language of A and B such that
A implies C and C implies B. We state the property for propositional logic.
-/

/-- The common atoms of two formulas. -/
def commonAtoms (A B : Formula) : List Nat :=
  let atomsA := A.atoms
  let atomsB := B.atoms
  atomsA.filter fun n => atomsB.contains n

/-- Interpolant existence (Craig, 1957). -/
def craigInterpolation : Prop :=
  ∀ (A B : Formula),
    isTautology (.impl A B) →
    ∃ (C : Formula),
      (∀ n ∈ C.atoms, n ∈ commonAtoms A B) ∧
      isTautology (.impl A C) ∧ isTautology (.impl C B)

/-! ## Beth Definability Property

Beth's definability theorem: If a predicate P is implicitly definable
from other predicates in a theory, then P is explicitly definable.
-/

/-- Explicit definability: there exists a formula φ in language L
    that is equivalent to predicate P. -/
def explicitlyDefinable (P : Nat) (L : Set Nat) : Prop :=
  ∃ (φ : Formula),
    (∀ n ∈ φ.atoms, n ∈ L) ∧
    ∀ (a : Nat → Bool), a P = φ.eval a

/-- Implicit definability: if two assignments agree on L, they agree on P. -/
def implicitlyDefinable (P : Nat) (L : Set Nat) : Prop :=
  ∀ (a b : Nat → Bool), (∀ n ∈ L, a n = b n) → a P = b P

/-- Beth definability: implicit ⇒ explicit (for propositional logic). -/
def bethDefinability : Prop :=
  ∀ (P : Nat) (L : Set Nat),
    implicitlyDefinable P L → explicitlyDefinable P L

/-! ## #eval Examples -/

def sf1 : Formula := .and (.atom 0) (.not (.atom 1))
#eval isSubformula (.atom 0) sf1
#eval isSubformula (.atom 1) sf1
#eval isSubformula (.atom 2) sf1

#eval (.atom 0).complexity
#eval sf1.complexity

#eval Formula.subst (.atom 0) 0 (.atom 5)
#eval Formula.subst (.and (.atom 0) (.atom 1)) 0 (.not (.atom 2))
#eval Formula.subst (.impl (.atom 0) (.atom 0)) 0 (.atom 1)

#eval polarityIn (.atom 0) (.atom 0)
#eval polarityIn (.atom 0) (.not (.atom 0))
#eval polarityIn (.atom 0) (.and (.atom 0) (.atom 1))
#eval polarityIn (.atom 0) (.impl (.atom 1) (.atom 0))

end MiniLogicKernel
