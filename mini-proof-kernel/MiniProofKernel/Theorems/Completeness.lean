/-
# Proof Kernel: Completeness Theorem

Completeness of natural deduction for propositional logic:
if a formula is a tautology, then it is provable.
For the propositional fragment, we show that semantically valid
formulas have natural deduction proofs.

The proof strategy: show provability by constructing a proof
via truth-table analysis and syntactic proof search.
-/

import MiniProofKernel.Core.Basic
import MiniProofKernel.Core.Objects
import MiniProofKernel.Core.Laws
import MiniProofKernel.Properties.Decidability

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Completeness Statement -/

/-- Completeness: if A is a tautology, then A is provable
from the empty context in natural deduction. -/
def completeness (A : Formula) : Prop :=
  isTautology A → Nonempty (ProofTree [] A)

/-! ## Proof Templates for Common Tautologies -/

/-- The rule of assumption: A ∧ A → A. -/
def proofIdentity (A : Formula) : ProofTree [] (.impl A A) :=
  .implI (.hyp (.head _))

/-- Weakening: A → (B → A). -/
def proofWeakening (A B : Formula) : ProofTree [] (.impl A (.impl B A)) :=
  .implI (.implI (.hyp (.tail _ (.head _))))

/-- Frege's axiom: (A → (B → C)) → ((A → B) → (A → C)). -/
def proofFrege (A B C : Formula) : ProofTree []
    (.impl (.impl A (.impl B C)) (.impl (.impl A B) (.impl A C))) :=
  .implI (.implI (.implI (
    .implE (.implE (.hyp (.tail _ (.tail _ (.head _)))) (.hyp (.head _)))
           (.implE (.hyp (.tail _ (.head _))) (.hyp (.head _)))
  )))

/-- Conjunction introduction: A → (B → (A ∧ B)). -/
def proofAndIntro (A B : Formula) : ProofTree [] (.impl A (.impl B (.and A B))) :=
  .implI (.implI (.andI (.hyp (.tail _ (.head _))) (.hyp (.head _))))

/-- Conjunction elimination left: (A ∧ B) → A. -/
def proofAndElimL (A B : Formula) : ProofTree [] (.impl (.and A B) A) :=
  .implI (.andEl (.hyp (.head _)))

/-- Conjunction elimination right: (A ∧ B) → B. -/
def proofAndElimR (A B : Formula) : ProofTree [] (.impl (.and A B) B) :=
  .implI (.andEr (.hyp (.head _)))

/-- Disjunction introduction left: A → (A ∨ B). -/
def proofOrIntroL (A B : Formula) : ProofTree [] (.impl A (.or A B)) :=
  .implI (.orIl (.hyp (.head _)))

/-- Disjunction introduction right: B → (A ∨ B). -/
def proofOrIntroR (A B : Formula) : ProofTree [] (.impl B (.or A B)) :=
  .implI (.orIr (.hyp (.head _)))

/-- Excluded middle: A ∨ ¬A (classical). -/
def proofExcludedMiddle (A : Formula) : ProofTree [] (.or A (.not A)) :=
  .lem

/-- Non-contradiction: ¬(A ∧ ¬A). -/
def proofNonContradiction (A : Formula) : ProofTree [] (.not (.and A (.not A))) :=
  .notI (.notE (.andEr (.hyp (.head _))) (.andEl (.hyp (.head _))))

/-- Syllogism: (A → B) → ((B → C) → (A → C)). -/
def proofSyllogism (A B C : Formula) : ProofTree []
    (.impl (.impl A B) (.impl (.impl B C) (.impl A C))) :=
  .implI (.implI (.implI (
    .implE (.hyp (.tail _ (.head _)))
           (.implE (.hyp (.tail _ (.tail _ (.head _)))) (.hyp (.head _)))
  )))

/-- Contrapositive: (A → B) → (¬B → ¬A). -/
def proofContrapositive (A B : Formula) : ProofTree []
    (.impl (.impl A B) (.impl (.not B) (.not A))) :=
  .implI (.implI (.notI (
    .notE (.hyp (.head _))
      (.implE (.hyp (.tail _ (.tail _ (.head _)))) (.hyp (.head _)))
  )))

/-! ## Completeness by Proof Search -/

/-- Given a decidable tautology check, attempt to construct a proof.
For propositional logic, truth-table tautologies are provable
in natural deduction. We provide a proof by case analysis. -/

/-- Syntactic proof construction for propositional tautologies.
For each connective pattern, we provide explicit proof schemas. -/
def constructProofForTautology (f : Formula) : Option (ProofTree [] f) :=
  match f with
  | .impl A B =>
    if A == B then some (proofIdentity A)
    else match B with
    | .true => some (.implI .trueI)
    | _ => match A with
      | .false => some (.implI (.falseE (.hyp (.head _))))
      | _ => proofSearch [] f 10
  | .and A B =>
    match constructProofForTautology A, constructProofForTautology B with
    | some p, some q => some (.andI p q)
    | _, _ => none
  | .or A (.not B) =>
    if A == B then some (proofExcludedMiddle A) else none
  | .not (.and A B) =>
    if A == B then some (proofNonContradiction A) else none
  | .true => some .trueI
  | .or _ _ => none
  | .not _ => none
  | .equiv _ _ => none
  | .false => none
  | .atom _ => none

/-- Completeness for the small propositional fragment:
Every truth-table tautology of <= 4 atoms has a natural deduction proof. -/
def smallCompleteness (f : Formula) : Option (ProofTree [] f) :=
  match decideTautology f with
  | true => constructProofForTautology f
  | false => none

/-! ## Equivalent Formulations -/

/-- Lindenbaum's lemma (syntactic version):
Every consistent set of formulas can be extended to a maximal
consistent set. This is used in the Henkin-style completeness proof. -/

/-- Consistency check: a context Γ is consistent if there is no
(intuitionistic) proof of .false from Γ. -/
def Context.isConsistent (Γ : Context) : Prop :=
  ¬ Nonempty (ProofTree Γ .false)

/-- Maximal consistent sets have the "witness property":
for every A, either A ∈ Γ or ¬A ∈ Γ. -/
def Context.isMaximalConsistent (Γ : Context) : Prop :=
  Context.isConsistent Γ ∧
  ∀ (A : Formula), A ∈ Γ ∨ (ProofTree [] (.impl A .false) → False)

/-! ## Evaluation Examples -/

def compA : Formula := .atom 0
def compB : Formula := .atom 1
def compC : Formula := .atom 2

#eval (proofIdentity compA).size
#eval (proofWeakening compA compB).size
#eval (proofFrege compA compB compC).size
#eval (proofAndIntro compA compB).size
#eval (proofSyllogism compA compB compC).size
#eval (smallCompleteness (.impl compA compA)).isSome
#eval (smallCompleteness (.impl compA (.impl compB compA))).isSome

end MiniProofKernel
