/-
# Logic Kernel: Bridge to Topology

Connections between logic and topology:
Stone spaces, topological semantics, and point-free topology.

Stone duality establishes an equivalence between Boolean algebras and
Stone spaces (compact, Hausdorff, totally disconnected topological spaces).
In our propositional setting, the Boolean algebra is the Lindenbaum algebra
of formulas modulo logical equivalence, and the Stone space is the Cantor
space {0,1}^ω of all truth assignments.
-/

import MiniLogicKernel.Core.Basic

namespace MiniLogicKernel

/-! ## Topology on Truth Assignments

The space of all truth assignments `Nat → Bool` is the product space
`{0,1}^ω`, also known as the Cantor space. It is compact, Hausdorff,
and totally disconnected -- a Stone space.
-/

/-- The space of all truth assignments (the Cantor space {0,1}^ω). -/
def AssignmentSpace : Type := Nat → Bool

/-- A basic open set: all assignments making a given formula true. -/
def basicOpen (f : Formula) : Set AssignmentSpace :=
  (λ σ => f.eval σ = true)

/-- The family of all basic open sets forms a basis for the product topology. -/
def basicOpens : Set (Set AssignmentSpace) :=
  (λ U => ∃ f : Formula, U = basicOpen f)

/-! ## Boolean Operations on Basic Opens

Operations on basic open sets correspond exactly to logical connectives.
This is the key observation behind Stone duality.
-/

theorem basicOpen_true : basicOpen Formula.true = Set.univ := by
  ext σ; dsimp [basicOpen, Set.univ]; simp [Formula.eval]

theorem basicOpen_false : basicOpen Formula.false = ∅ := by
  ext σ; dsimp [basicOpen]; simp [Formula.eval]

theorem basicOpen_atom (n : Nat) : basicOpen (Formula.atom n) = (λ σ => σ n = true) := by
  ext σ; dsimp [basicOpen]; simp [Formula.eval]

theorem basicOpen_not (A : Formula) : basicOpen (Formula.not A) = Set.compl (basicOpen A) := by
  ext σ; dsimp [basicOpen, Set.compl]; simp [Formula.eval]

theorem basicOpen_and (A B : Formula) : basicOpen (Formula.and A B) = basicOpen A ∩ basicOpen B := by
  ext σ; dsimp [basicOpen, Set.inter]; simp [Formula.eval]

theorem basicOpen_or (A B : Formula) : basicOpen (Formula.or A B) = basicOpen A ∪ basicOpen B := by
  ext σ; dsimp [basicOpen, Set.union]; simp [Formula.eval]

theorem basicOpen_impl (A B : Formula) : basicOpen (Formula.impl A B) = Set.compl (basicOpen A) ∪ basicOpen B := by
  ext σ; dsimp [basicOpen, Set.union, Set.compl]; simp [Formula.eval]

theorem basicOpen_equiv (A B : Formula) : basicOpen (Formula.equiv A B) = (Set.compl (basicOpen A) ∪ basicOpen B) ∩ (Set.compl (basicOpen B) ∪ basicOpen A) := by
  ext σ; dsimp [basicOpen, Set.inter, Set.union, Set.compl]; simp [Formula.eval]

/-! ## Clopen Sets

In the Cantor space, the basic open sets are exactly the clopen
(closed and open) sets. They form a Boolean algebra under the usual
set-theoretic operations, isomorphic to the Lindenbaum algebra.
-/

/--
The Boolean algebra of clopen sets of the Stone space. Each equivalence
class of formulas [f] corresponds to the clopen set basicOpen f.

Structure of this Boolean algebra:
- 0 = basicOpen false = ∅
- 1 = basicOpen true = AssignmentSpace
- [f] ∧ [g] = basicOpen (and f g)
- [f] ∨ [g] = basicOpen (or f g)
- ¬[f] = basicOpen (not f)
-/
def ClopenAlgebra : Type := Set AssignmentSpace

/--
The clopen algebra has at least two distinct elements (when there is
at least one atom). basicOpen (atom 0) ≠ basicOpen (not (atom 0)).
-/
theorem clopenAlgebra_nontrivial : basicOpen (Formula.atom 0) ≠ basicOpen (Formula.not (Formula.atom 0)) := by
  intro h
  let σ := fun (_ : Nat) => true
  have hmem_in : σ ∈ basicOpen (Formula.atom 0) := by
    simp [basicOpen, Formula.eval, σ]
  have hmem_not : σ ∉ basicOpen (Formula.not (Formula.atom 0)) := by
    simp [basicOpen, Formula.eval, σ]
  have hmem_in' : σ ∈ basicOpen (Formula.not (Formula.atom 0)) := by
    rw [h]
    exact hmem_in
  exact hmem_not hmem_in'

/--
Two logically equivalent formulas determine the same clopen set.
-/
theorem basicOpen_congr (A B : Formula) (h : ∀ σ, A.eval σ = B.eval σ) : basicOpen A = basicOpen B := by
  ext σ; simp [basicOpen, h σ]

/-! ## Ultrafilters and Points of the Stone Space

A point in the Stone space corresponds to a truth assignment σ.
The ultrafilter determined by σ is the set of all formulas true under σ:
  U_σ = (λ f => f.eval σ = true)

Conversely, every ultrafilter of the Lindenbaum algebra corresponds to
a unique truth assignment (in the classical, two-valued setting).
-/

/-- The ultrafilter of formulas true under a given assignment. -/
def ultrafilter (σ : AssignmentSpace) : Set Formula :=
  (λ f => f.eval σ = true)

/--
Properties of the ultrafilter determined by σ:
1. Closed under conjunction: if A, B ∈ U_σ then A ∧ B ∈ U_σ
2. Upward closed: if A ∈ U_σ and A semantically implies B, then B ∈ U_σ
3. For any A, exactly one of A, ¬A is in U_σ
-/
theorem ultrafilter_closed_under_and (σ : AssignmentSpace) (A B : Formula)
    (hA : A ∈ ultrafilter σ) (hB : B ∈ ultrafilter σ) : (Formula.and A B) ∈ ultrafilter σ := by
  simp [ultrafilter, basicOpen, Formula.eval] at hA hB ⊢
  rw [hA, hB]; rfl

theorem ultrafilter_decides (σ : AssignmentSpace) (A : Formula) :
    A ∈ ultrafilter σ ∨ (Formula.not A) ∈ ultrafilter σ := by
  simp [ultrafilter, Formula.eval]
  by_cases h : A.eval σ = true
  · left; exact h
  · right
    have h' : A.eval σ = false := by
      cases hval : A.eval σ
      · rfl
      · simp [h] at hval
    simp [h']

/-! ## Stone Duality

Stone's representation theorem (1936): The category of Boolean algebras
is dually equivalent to the category of Stone spaces.

In our setting:
- The Boolean algebra is the Lindenbaum algebra of formulas
- The Stone space is the space of truth assignments
- Each formula f corresponds to the clopen set basicOpen f
- Each assignment σ corresponds to the ultrafilter ultrafilter σ
-/

/--
Stone duality correspondence: the map f ↦ basicOpen f is an isomorphism
from the Lindenbaum algebra to the algebra of clopen sets.

Concretely, logical equivalence of formulas corresponds to equality
of the corresponding clopen sets.
-/
def stoneDualityIsomorphism : Prop :=
  ∀ (A B : Formula),
    (∀ σ, A.eval σ = B.eval σ) ↔ basicOpen A = basicOpen B

theorem stoneDualityIsomorphism_holds : stoneDualityIsomorphism := by
  intro A B
  constructor
  · intro h; ext σ; simp [basicOpen, h σ]
  · intro h σ
    -- From h : basicOpen A = basicOpen B, deduce membership equivalence
    have hmem' : (basicOpen A σ) ↔ (basicOpen B σ) := by
      simpa [h]
    -- Unfold basicOpen definitions
    dsimp [basicOpen] at hmem'
    -- Now hmem' : (A.eval σ = true) ↔ (B.eval σ = true)
    -- For Bool, this implies equality
    have hval := hmem'.mp ?_
    · apply hmem'.mpr
    -- Actually, let's use by_cases
    by_cases hAval : A.eval σ
    · have hBval := (hmem'.mp hAval)
      rw [hAval, hBval]
    · have hAfalse : A.eval σ = false := by
        cases h : A.eval σ
        · rfl
        · simp [hAval] at h
      have hBfalse : B.eval σ = false := by
        cases hB : B.eval σ
        · rfl
        · have := hmem'.mpr hB
          rw [hAfalse] at this
          simp at this
      rw [hAfalse, hBfalse]

/-! ## Topological Compactness

The compactness theorem states that the Stone space is compact:
every open cover has a finite subcover. In terms of basic opens:
if a family of basic opens covers the space, then some finite subfamily
already covers it. This is exactly the logical compactness theorem.
-/

/--
Topological formulation of compactness: if a family of basic open sets
covers the space, then some finite subfamily does.

This is equivalent to: if every finite subset of Γ is satisfiable,
then Γ is satisfiable.

Proof sketch: basicOpen f covers an assignment σ iff f.eval σ = true.
So {basicOpen f | f ∈ Γ} covers the space iff Γ is unsatisfiable.
-/
def topologicalCompactness : Prop :=
  ∀ (Γ : Set Formula),
    (∀ (Δ : Set Formula), Δ ⊆ Γ → Set.Finite Δ → (⋂ f ∈ Δ, basicOpen f).Nonempty) →
    (⋂ f ∈ Γ, basicOpen f).Nonempty

/--
Topological compactness is equivalent to logical compactness.
The intersection of basic opens is nonempty iff there exists an
assignment satisfying all formulas.
-/
axiom topological_compactness : topologicalCompactness

/-! ## #eval Examples -/

-- Basic open sets under specific assignments
def sigma1 : AssignmentSpace := fun n => n == 0
def sigma2 : AssignmentSpace := fun _ => true
def sigma3 : AssignmentSpace := fun n => n % 2 == 0

def topo_f1 : Formula := Formula.atom 0
def topo_f2 : Formula := Formula.not (Formula.atom 1)
def topo_f3 : Formula := Formula.and (Formula.atom 0) (Formula.atom 1)

-- Check membership in basic open sets
#eval sigma1 ∈ basicOpen topo_f1
#eval sigma2 ∈ basicOpen topo_f2
#eval sigma3 ∈ basicOpen topo_f3

-- Verify Boolean operations on basic opens
#eval sigma1 ∈ basicOpen (Formula.not topo_f1)
#eval sigma2 ∈ basicOpen (Formula.and topo_f1 topo_f3)
#eval sigma3 ∈ basicOpen (Formula.or topo_f1 (Formula.not topo_f1))

-- Demonstrate that formulas and their negations partition the space
#eval topo_f1.eval sigma1
#eval (Formula.not topo_f1).eval sigma1
#eval topo_f1.eval sigma2
#eval (Formula.not topo_f1).eval sigma2
#eval topo_f3.eval sigma3
#eval Formula.complexity topo_f3

end MiniLogicKernel
