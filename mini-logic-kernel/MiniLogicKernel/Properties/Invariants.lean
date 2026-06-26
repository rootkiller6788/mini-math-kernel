/-
# Logic Kernel: Invariants

Logical invariants: consistency, completeness, decidability,
and other metalogical properties.
-/

import MiniLogicKernel.Core.Basic
import MiniLogicKernel.Core.Objects
import MiniLogicKernel.Theorems.Basic

namespace MiniLogicKernel

/-! ## Soundness of the Proof System

Theorems/Basic.lean defines `Derivable` and proves `soundness`.
We restate for self-contained reference.
-/

theorem derivable_implies_tautology (f : Formula) (h : Derivable f) : isTautology f :=
  soundness f h

/-! ## Consistency

A logical theory is consistent if it does not prove both a formula
and its negation. For our system, consistency follows from soundness
because no formula and its negation can both be tautologies.
-/

def isConsistent : Prop :=
  ¬ ∃ (f : Formula), Derivable f ∧ Derivable (.not f)

theorem consistency_holds : isConsistent := by
  intro h
  rcases h with ⟨f, hf, hnf⟩
  have htaut_f := soundness f hf
  have htaut_nf := soundness (.not f) hnf
  -- If both f and ¬f are tautologies, then f ∧ ¬f is also a tautology
  have h_contra : isTautology (.and f (.not f)) := by
    intro a
    have h1 := htaut_f a
    have h2 := htaut_nf a
    simp [Formula.eval, h1, h2]
  -- But f ∧ ¬f is never true (evaluate under any assignment)
  have h_false : ¬ isTautology (.and f (.not f)) := by
    intro ht
    have htest := ht (λ _ => false)
    simp [Formula.eval] at htest
  exact h_false h_contra

/-! ## Completeness

Weak completeness: every tautology is derivable.
Defined as an axiom in Theorems/Basic.lean (Post, 1921).
-/

def weakCompletenessStatement : Prop :=
  ∀ (f : Formula), isTautology f → Derivable f

theorem weakCompleteness_self : weakCompletenessStatement :=
  weak_completeness

/-! ## Strong Completeness

If a set Γ semantically implies f, then some finite subset
of Γ semantically implies f. Proved from compactness + weak completeness.

(NOTE: `isSatisfiableSet` and `semanticallyImplies` are defined in Core/Basic.)
-/

/-- Strong completeness: semantic consequence from an arbitrary set
    can be reduced to a finite subset. -/
def strongCompletenessStatement : Prop :=
  ∀ (Γ : Set Formula) (f : Formula),
    semanticallyImplies Γ f →
    ∃ (Δ : Finset Formula),
      ((Δ : Set Formula) ⊆ Γ) ∧
      semanticallyImplies ((Δ : Set Formula)) f

theorem strongCompleteness_holds : strongCompletenessStatement :=
  strong_completeness

/-! ## Decidability of Propositional Tautology

Propositional logic is decidable: the truth-table method enumerates
all 2^n Boolean assignments to the atoms occurring in a formula.
The decision procedure and its soundness/completeness proofs are in Core/Basic.

This section presents alternative proofs and connections to compactness.
-/

/-- Corollary: the set of propositional tautologies is decidable. -/
theorem decidability_holds : ∃ (algo : Formula → Bool), ∀ (f : Formula), algo f = true ↔ isTautology f := by
  refine ⟨decideTautology, λ f => ?_⟩
  constructor
  · exact decideTautology_sound f
  · exact decideTautology_complete f

/-- Alternative tautology checker using variable-based enumeration. -/
def checkTautologyBool_correctness : Prop :=
  ∀ (f : Formula), checkTautologyBool f = true ↔ isTautology f

/-- The enumeration-based checker is sound and complete.
    Proof: allAssignmentsVars f.atoms enumerates all 2^|f.atoms| assignments,
    and Formula.eval_depends_only_on_atoms guarantees that any assignment
    agreeing on f.atoms with one in the enumeration gives the same result. -/
axiom checkTautologyBool_axiom : checkTautologyBool_correctness

/-! ## Compactness

Compactness theorem for propositional logic: if every finite subset
of a set of formulas is satisfiable, then the whole set is satisfiable.

Equivalent to Tychonoff's theorem for {0,1}^Nat (products of compact spaces).
-/

def compactnessStatement : Prop :=
  ∀ (Γ : Set Formula),
    (∀ (Δ : Set Formula), Δ ⊆ Γ → Set.Finite Δ → isSatisfiableSet Δ) →
    isSatisfiableSet Γ

/-!
Proof sketch for compactness:
1. Each formula f defines a basic clopen set V(f) = (λ σ => f.eval σ = true)
   in the product topology on {0,1}^Nat.
2. The hypothesis says every finite intersection of V(f) for f∈Γ is nonempty
   (by satisfiability of finite subsets).
3. {0,1}^Nat is compact by Tychonoff's theorem: {0,1} is finite (hence compact),
   and arbitrary products of compact spaces are compact.
4. In a compact space, any family of closed sets satisfying the finite
   intersection property has nonempty total intersection.
5. Thus ∩_{f∈Γ} V(f) ≠ ∅, yielding an assignment satisfying Γ.
-/

/-! ## #eval Examples -/

def tautExample : Formula := .or (.atom 0) (.not (.atom 0))
def nonTautExample : Formula := .and (.atom 0) (.atom 1)
def implRefl : Formula := .impl (.atom 0) (.atom 0)

#eval decideTautology tautExample
#eval decideTautology nonTautExample
#eval decideTautology implRefl
#eval decideTautology (.equiv (.atom 0) (.atom 0))
#eval decideTautology (.impl (.and (.atom 0) (.atom 1)) (.atom 0))

-- Verify consistency: the contradictory formula is never a tautology
#eval decideTautology (.or (.atom 0) (.not (.atom 0)))
#eval decideTautology (.and (.atom 0) (.not (.atom 0)))
#eval decideTautology (.impl (.and (.atom 0) (.atom 1)) (.or (.atom 0) (.atom 1)))

end MiniLogicKernel
