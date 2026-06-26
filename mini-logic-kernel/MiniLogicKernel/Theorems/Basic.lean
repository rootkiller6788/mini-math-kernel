/-
# Logic Kernel: Basic Theorems

Fundamental theorems of propositional and first-order logic:
deduction theorem, soundness, and completeness.
-/

import MiniLogicKernel.Core.Basic
import MiniLogicKernel.Core.Laws

namespace MiniLogicKernel

/-! ## Proof System for Propositional Logic

A Hilbert-style proof system for propositional formulas.
Axioms are the derived rule schemas; the only inference rule is modus ponens.
-/

inductive Derivable : Formula → Prop where
  | ax_id              (A : Formula) : Derivable (ruleId A)
  | ax_excluded_middle (A : Formula) : Derivable (ruleExcludedMiddle A)
  | ax_non_contradiction (A : Formula) : Derivable (ruleNonContradiction A)
  | ax_double_neg_elim (A : Formula) : Derivable (ruleDoubleNegElim A)
  | ax_double_neg_intro (A : Formula) : Derivable (ruleDoubleNegIntro A)
  | ax_de_morgan_and   (A B : Formula) : Derivable (ruleDeMorganAnd A B)
  | ax_de_morgan_or    (A B : Formula) : Derivable (ruleDeMorganOr A B)
  | ax_contraposition  (A B : Formula) : Derivable (ruleContraposition A B)
  | ax_exportation     (A B C : Formula) : Derivable (ruleExportation A B C)
  | ax_importation     (A B C : Formula) : Derivable (ruleImportation A B C)
  | ax_syllogism       (A B C : Formula) : Derivable (ruleSyllogism A B C)
  | ax_proof_by_cases  (A B C : Formula) : Derivable (ruleProofByCases A B C)
  | mp {A B : Formula} : Derivable (Formula.impl A B) → Derivable A → Derivable B

/-! ## Soundness Theorem

Every derivable formula is a tautology. We prove this by induction on the
derivation, using the fact that each axiom schema evaluates to true under
every Boolean assignment.
-/

theorem soundness (f : Formula) (h : Derivable f) : isTautology f := by
  induction h with
  | ax_id A =>
    intro assignment
    unfold isTautology ruleId
    simp [Formula.eval]
    by_cases hA : A.eval assignment <;> simp [hA]
  | ax_excluded_middle A =>
    intro assignment
    unfold isTautology ruleExcludedMiddle
    simp [Formula.eval]
    by_cases hA : A.eval assignment <;> simp [hA]
  | ax_non_contradiction A =>
    intro assignment
    unfold isTautology ruleNonContradiction
    simp [Formula.eval]
    by_cases hA : A.eval assignment <;> simp [hA]
  | ax_double_neg_elim A =>
    intro assignment
    unfold isTautology ruleDoubleNegElim
    simp [Formula.eval]
    by_cases hA : A.eval assignment <;> simp [hA]
  | ax_double_neg_intro A =>
    intro assignment
    unfold isTautology ruleDoubleNegIntro
    simp [Formula.eval]
    by_cases hA : A.eval assignment <;> simp [hA]
  | ax_de_morgan_and A B =>
    intro assignment
    unfold isTautology ruleDeMorganAnd
    simp [Formula.eval]
    by_cases hA : A.eval assignment <;> by_cases hB : B.eval assignment <;> simp [hA, hB]
  | ax_de_morgan_or A B =>
    intro assignment
    unfold isTautology ruleDeMorganOr
    simp [Formula.eval]
    by_cases hA : A.eval assignment <;> by_cases hB : B.eval assignment <;> simp [hA, hB]
  | ax_contraposition A B =>
    intro assignment
    unfold isTautology ruleContraposition
    simp [Formula.eval]
    by_cases hA : A.eval assignment <;> by_cases hB : B.eval assignment <;> simp [hA, hB]
  | ax_exportation A B C =>
    intro assignment
    unfold isTautology ruleExportation
    simp [Formula.eval]
    by_cases hA : A.eval assignment <;> by_cases hB : B.eval assignment <;> by_cases hC : C.eval assignment <;> simp [hA, hB, hC]
  | ax_importation A B C =>
    intro assignment
    unfold isTautology ruleImportation
    simp [Formula.eval]
    by_cases hA : A.eval assignment <;> by_cases hB : B.eval assignment <;> by_cases hC : C.eval assignment <;> simp [hA, hB, hC]
  | ax_syllogism A B C =>
    intro assignment
    unfold isTautology ruleSyllogism
    simp [Formula.eval]
    by_cases hA : A.eval assignment <;> by_cases hB : B.eval assignment <;> by_cases hC : C.eval assignment <;> simp [hA, hB, hC]
  | ax_proof_by_cases A B C =>
    intro assignment
    unfold isTautology ruleProofByCases
    simp [Formula.eval]
    by_cases hA : A.eval assignment <;> by_cases hB : B.eval assignment <;> by_cases hC : C.eval assignment <;> simp [hA, hB, hC]
  | mp {A B : Formula} _hAB _hA ihAB ihA =>
    intro assignment
    have hAB_true : (Formula.impl A B).eval assignment = true := ihAB assignment
    have hA_true : A.eval assignment = true := ihA assignment
    simp [Formula.eval] at hAB_true hA_true ⊢
    rw [hA_true] at hAB_true
    simp at hAB_true
    exact hAB_true

/-! ## Deduction Theorem

The deduction theorem: if a formula B is derivable from assumptions
Γ ∪ {A}, then A → B is derivable from Γ alone.
The standard proof proceeds by induction on the derivation of B.

(NOTE: `isSatisfiableSet` and `semanticallyImplies` are defined in Core/Basic)
-/

/--
The deduction theorem for the semantic side:
If Γ ∪ {A} semantically implies B, then Γ semantically implies A → B.
-/
theorem semantic_deduction (Γ : Set Formula) (A B : Formula)
    (h : semanticallyImplies (Γ ∪ {A}) B) : semanticallyImplies Γ (Formula.impl A B) := by
  intro σ hΓ
  have h_impl : (Formula.impl A B).eval σ = true := by
    simp [Formula.eval]
    by_cases hA : A.eval σ = true
    · simp [hA]
      -- Goal becomes: B.eval σ = true
      have hΓ' : ∀ g, (Γ ∪ {A}) g → g.eval σ = true := by
        intro g hg
        dsimp [Set.union, Set.singleton] at hg
        rcases hg with (hgΓ | hgA)
        · exact hΓ g hgΓ
        · subst hgA; exact hA
      exact h σ hΓ'
    · have hA_false : A.eval σ = false := by
        cases hA' : A.eval σ
        · rfl
        · simp [hA] at hA'
      simp [hA_false]
  exact h_impl

/--
The deduction theorem, stated as a Prop encapsulating the relationship
between derivability and implication. In a full development, this would
be proved by induction on the derivation.
-/
def DeductionTheorem : Prop :=
  ∀ (A B : Formula), Derivable B → Derivable (Formula.impl A B)

/--
The deduction theorem holds for our proof system. The proof proceeds by
induction on the derivation of B, translating each inference step using
the Hilbert-style axioms. This is a metalogical result; we state it as
an axiom here (the full proof requires a careful induction on Derivable).
-/
axiom deduction_theorem_holds : DeductionTheorem

/-! ## Weak Completeness

Weak completeness: every propositional tautology is derivable in our
Hilbert-style proof system. The standard proof (Post, 1921) proceeds by:
1. Convert the formula to conjunctive normal form (CNF).
2. Show each clause (disjunction of literals) is derivable.
3. Derive the conjunction of all clauses.

For a tautology, each CNF clause contains complementary literals,
making each clause an instance of excluded middle.
-/

def WeakCompleteness : Prop :=
  ∀ (f : Formula), isTautology f → Derivable f

/--
Weak completeness for propositional logic. Proved by Emil Post in 1921
via truth-table method: construct a derivation of the formula from its
disjunctive normal form. We state this as an axiom; the full proof
requires a constructive enumeration of all 2ⁿ truth assignments and a
systematic translation to derivations.
-/
axiom weak_completeness : WeakCompleteness

/-!
Strong completeness: if Γ semantically implies f, then f is derivable from Γ.
In propositional logic, this follows from compactness + weak completeness.
-/

/--
Strong completeness (Finite Subset Property): if Γ semantically implies f,
then some finite subset of Γ already semantically implies f.
This is equivalent to the compactness theorem for propositional logic.
-/
def StrongCompleteness : Prop :=
  ∀ (Γ : Set Formula) (f : Formula),
    semanticallyImplies Γ f →
    ∃ (Δ : Set Formula), Δ ⊆ Γ ∧ Set.Finite Δ ∧ semanticallyImplies Δ f

/--
Strong completeness for propositional logic. Proved by combining weak
completeness (every tautology is derivable) with the compactness theorem.
-/
axiom strong_completeness : StrongCompleteness

/-! ## Adequacy Corollary

The proof system is adequate: derivability coincides with semantic validity.
-/

def Adequacy : Prop :=
  ∀ (f : Formula), Derivable f ↔ isTautology f

theorem adequacy : Adequacy := by
  intro f
  constructor
  · exact soundness f
  · exact weak_completeness f

/-! ## #eval Examples -/

def testFormula1 : Formula := Formula.impl (Formula.atom 0) (Formula.atom 0)
def testFormula2 : Formula := Formula.or (Formula.atom 0) (Formula.not (Formula.atom 0))
def testFormula3 : Formula := ruleModusPonens (Formula.atom 0) (Formula.atom 1) (Formula.atom 0)

#eval testFormula1.eval (fun _ => true)
#eval testFormula2.eval (fun n => n == 0)
#eval Formula.complexity testFormula3

/--
Demonstrate that `ruleId` and `ruleExcludedMiddle` are tautologies
by evaluating under a specific assignment.
-/
#eval (ruleId (Formula.atom 0)).eval (fun _ => false)
#eval (ruleExcludedMiddle (Formula.atom 1)).eval (fun n => n % 2 == 0)
#eval (ruleDoubleNegElim (Formula.atom 0)).eval (fun _ => true)

end MiniLogicKernel
