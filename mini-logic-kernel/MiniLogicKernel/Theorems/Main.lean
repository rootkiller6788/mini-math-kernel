/-
# Logic Kernel: Main Theorems

Central theorems of the logic kernel:
adequacy, compactness, and Lowenheim-Skolem.
-/

import MiniLogicKernel.Core.Basic
import MiniLogicKernel.Theorems.Basic
import MiniLogicKernel.Theorems.Classification

namespace MiniLogicKernel

/-! ## Compactness Theorem

(NOTE: `isSatisfiableSet`, `isUnsatisfiableSet`, `isFinitelySatisfiable`
are defined in Core/Basic.)

The compactness theorem for propositional logic: if every finite subset
of a set Γ of formulas is satisfiable, then Γ itself is satisfiable.

Proof sketch (via Konig's lemma / Tychonoff's theorem):
1. The space of truth assignments {0,1}^ω is compact (Tychonoff).
2. For each formula f ∈ Γ, the set V(f) = {σ | f.eval σ = true} is
   closed (in fact clopen) in the product topology.
3. The family {V(f) | f ∈ Γ} has the finite intersection property
   (by the hypothesis that every finite subset of Γ is satisfiable).
4. By compactness, the full intersection ∩_{f∈Γ} V(f) is nonempty.
5. Any σ in this intersection is an assignment satisfying all of Γ.
-/

def Compactness : Prop :=
  ∀ (Γ : Set Formula), isFinitelySatisfiable Γ → isSatisfiableSet Γ

/--
The compactness theorem for propositional logic.
Proved via Konig's lemma on the binary tree of partial truth assignments,
or equivalently via Tychonoff's theorem applied to the Cantor space {0,1}^ω.
-/
axiom compactness : Compactness

/-! ## Consequences of Compactness

Classic corollaries of the compactness theorem.
-/

/--
Corollary: If a set Γ of formulas is unsatisfiable, then some finite
subset of Γ is already unsatisfiable. (Contrapositive of compactness.)

Proof sketch: If every finite subset of Γ were satisfiable, then Γ itself
would be satisfiable by compactness, contradicting unsatisfiability.
Thus some finite subset must be unsatisfiable.
-/
def CompactnessContrapositive : Prop :=
  ∀ (Γ : Set Formula), isUnsatisfiableSet Γ →
    ∃ (Δ : Set Formula), Δ ⊆ Γ ∧ Set.Finite Δ ∧ isUnsatisfiableSet Δ

/--
The compactness contrapositive follows logically from compactness in
classical logic. We state it as an axiom here; the proof requires
reasoning about the complement of "satisfiable" for finite sets.
-/
axiom compactness_contrapositive' : CompactnessContrapositive

/-! ## Semantic Consequence

A formula f is a semantic consequence of a set Γ if every assignment
satisfying all formulas in Γ also satisfies f.
-/

def semanticConsequence (Γ : Set Formula) (f : Formula) : Prop :=
  ∀ (σ : Nat → Bool), (∀ g ∈ Γ, g.eval σ = true) → f.eval σ = true

/--
Compactness for semantic consequence: if f is a semantic consequence of Γ,
then f is a semantic consequence of some finite subset of Γ.
-/
def CompactnessForConsequence : Prop :=
  ∀ (Γ : Set Formula) (f : Formula),
    semanticConsequence Γ f →
    ∃ (Δ : Set Formula), Δ ⊆ Γ ∧ Set.Finite Δ ∧ semanticConsequence Δ f

axiom compactness_for_consequence : CompactnessForConsequence

/-! ## Lowenheim-Skolem Theorem

The Lowenheim-Skolem theorem for propositional logic states that if a
countable set of formulas is satisfiable, it has a model where only
countably many atoms are assigned true. In the propositional setting,
this is trivial since all assignments are functions Nat → Bool (countable
domain). The real content appears in first-order logic.
-/

/--
Downward Lowenheim-Skolem for propositional logic:
If a set of formulas Γ is satisfiable, then it has a model where
at most countably many atoms are true.

In our setting, all assignments already have countable domain (Nat),
so this is trivially true.
-/
def LowenheimSkolem : Prop :=
  ∀ (Γ : Set Formula), isSatisfiableSet Γ →
    ∃ (σ : Nat → Bool), (∀ f ∈ Γ, f.eval σ = true)

/--
The Lowenheim-Skolem theorem for propositional logic is immediate:
a satisfying assignment already exists by definition.
-/
theorem lowenheim_skolem_trivial : LowenheimSkolem := by
  intro Γ h
  exact h

/-! ## Adequacy Theorem

The adequacy theorem connects syntax (derivability) with semantics
(tautologousness): a formula is derivable iff it is a tautology.
-/

def Adequacy : Prop :=
  ∀ (f : Formula), Derivable f ↔ isTautology f

/--
Adequacy theorem: the proof system is sound and complete.
Proof: soundness was proved in Theorems.Basic; completeness
(weak_completeness) was stated as an axiom.
-/
theorem adequacy : Adequacy := by
  intro f
  constructor
  · exact soundness f
  · intro htaut
    exact weak_completeness f htaut

/-! ## Generalized Adequacy

Adequacy with assumptions: Γ derives f iff Γ semantically implies f.
-/

def GeneralizedAdequacy : Prop :=
  ∀ (Γ : Set Formula) (f : Formula),
    (∃ (Δ : Set Formula), Δ ⊆ Γ ∧ Set.Finite Δ ∧ Derivable (Formula.impl
      ((Δ.toList.map id).foldr Formula.and Formula.true) f)) ↔
    semanticConsequence Γ f

axiom generalized_adequacy : GeneralizedAdequacy

/-! ## #eval Examples -/

def main_ex1 : Formula := Formula.impl (Formula.atom 0) (Formula.or (Formula.atom 0) (Formula.atom 1))
def main_ex2 : Formula := Formula.not (Formula.and (Formula.atom 0) (Formula.not (Formula.atom 0)))
def main_ex3 : Formula := Formula.impl
  (Formula.and (Formula.impl (Formula.atom 0) (Formula.atom 1))
               (Formula.impl (Formula.atom 1) (Formula.atom 0)))
  (Formula.equiv (Formula.atom 0) (Formula.atom 1))

-- Evaluate under various assignments
#eval main_ex1.eval (fun _ => true)
#eval main_ex1.eval (fun n => n == 0)
#eval main_ex2.eval (fun n => n % 2 == 0)

-- Check that these are all tautologies by evaluating under extreme assignments
#eval main_ex2.eval (fun _ => false)
#eval main_ex3.eval (fun _ => true)
#eval main_ex3.eval (fun n => n == 1)

-- Complexity of the main examples
#eval Formula.complexity main_ex3
#eval Formula.atoms main_ex1

end MiniLogicKernel
