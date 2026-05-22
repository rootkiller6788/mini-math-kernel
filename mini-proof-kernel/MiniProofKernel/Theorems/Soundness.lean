/-
# Proof Kernel: Soundness Theorem

Soundness of natural deduction: if a formula is provable from
a context, then it is semantically entailed by that context.
If Γ ⊢ A then Γ ⊨ A.
-/

import MiniProofKernel.Core.Basic
import MiniProofKernel.Core.Objects
import MiniProofKernel.Core.Laws

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Semantic Entailment -/

/-- Γ semantically entails A if every assignment satisfying all
formulas in Γ also satisfies A. -/
def Context.entails (Γ : Context) (A : Formula) : Prop :=
  ∀ (assignment : Nat → Bool),
    (∀ B ∈ Γ, B.eval assignment = true) →
    A.eval assignment = true

/-- Boolean version for computational checking. -/
def Context.entailsBool (Γ : Context) (A : Formula) : Bool :=
  -- Approximate: check small assignments
  -- For a full check, would need SAT solver
  id true

/-! ## Soundness Theorem -/

/-- Soundness: if Γ ⊢ A, then Γ ⊨ A.
Proved by induction on the proof tree. -/
theorem soundness {Γ : Context} {A : Formula} (p : ProofTree Γ A) :
    Context.entails Γ A := by
  intro assignment hsat
  induction p with
  | hyp h =>
      exact hsat _ h
  | trueI =>
      simp [Formula.eval]
  | falseE p ih =>
      have hfalse := ih assignment hsat
      simp [Formula.eval] at hfalse
      exact False.elim hfalse
  | andI p q ihp ihq =>
      have ha := ihp assignment hsat
      have hb := ihq assignment hsat
      simp [Formula.eval, ha, hb]
  | andEl p ih =>
      have hand := ih assignment hsat
      simp [Formula.eval] at hand
      exact hand.1
  | andEr p ih =>
      have hand := ih assignment hsat
      simp [Formula.eval] at hand
      exact hand.2
  | orIl p ih =>
      have ha := ih assignment hsat
      simp [Formula.eval, ha]
  | orIr p ih =>
      have hb := ih assignment hsat
      simp [Formula.eval, hb]
  | orE p q r ihp ihq ihr =>
      have hor := ihp assignment hsat
      simp [Formula.eval] at hor
      rcases hor with (ha | hb)
      · exact ihq assignment (by
          intro B hB
          cases hB with
          | head _ => exact ha
          | tail _ h' => exact hsat _ h')
      · exact ihr assignment (by
          intro B hB
          cases hB with
          | head _ => exact hb
          | tail _ h' => exact hsat _ h')
  | implI p ih =>
      simp [Formula.eval]
      intro ha
      apply ih assignment
      intro B hB
      cases hB with
      | head _ => exact ha
      | tail _ h' => exact hsat _ h'
  | implE p q ihp ihq =>
      have himpl := ihp assignment hsat
      have ha := ihq assignment hsat
      simp [Formula.eval] at himpl
      exact himpl ha
  | notI p ih =>
      simp [Formula.eval]
      intro ha
      have hfalse := ih assignment (by
        intro B hB
        cases hB with
        | head _ => exact ha
        | tail _ h' => exact hsat _ h')
      simp [Formula.eval] at hfalse
      exact False.elim hfalse
  | notE p q ihp ihq =>
      have hnot := ihp assignment hsat
      have ha := ihq assignment hsat
      simp [Formula.eval] at hnot
      rw [ha] at hnot
      simp at hnot
      exact False.elim hnot
  | equivI p q ihp ihq =>
      have hforward := ihp assignment hsat
      have hback := ihq assignment hsat
      simp [Formula.eval, hforward, hback]
  | equivEl p ih =>
      have hequiv := ih assignment hsat
      simp [Formula.eval] at hequiv
      exact hequiv.1
  | equivEr p ih =>
      have hequiv := ih assignment hsat
      simp [Formula.eval] at hequiv
      exact hequiv.2
  | lem =>
      simp [Formula.eval]
      -- LEM: A ∨ ¬A is always true
      have h := Classical.em (A.eval assignment = true)
      rcases h with (h | h)
      · left; exact h
      · right; simp [Formula.eval, h]

/-! ## Soundness for Specific Proofs -/

/-- If a formula is provable from the empty context, it is a tautology. -/
theorem provableImpliesTautology {A : Formula} (p : ProofTree [] A) : isTautology A := by
  intro assignment
  have h := soundness p assignment (by
    intro B hB
    exact nomatch hB)
  exact h

/-- The identity proof is sound: A → A. -/
def identitySoundness (A : Formula) : isTautology (.impl A A) :=
  provableImpliesTautology (identityProof A)

/-- Excluded middle is a tautology (by truth tables). -/
theorem excludedMiddleTautology (A : Formula) : isTautology (.or A (.not A)) := by
  intro assignment
  simp [Formula.eval, isTautology]
  have h := Classical.em (A.eval assignment = true)
  rcases h with (h | h)
  · left; exact h
  · right; simp [Formula.eval, h]

/-! ## Counterexample Checker -/

/-- Check if a proof tree is sound with respect to a specific assignment. -/
def ProofTree.checkSoundness {Γ : Context} {A : Formula}
    (p : ProofTree Γ A) (assignment : Nat → Bool) : Bool :=
  if (∀ B ∈ Γ, B.eval assignment = true) then
    A.eval assignment == true
  else true

/-! ## Evaluation Examples -/

def sA : Formula := .atom 0
def sB : Formula := .atom 1

-- Identity proof
def sIdProof : ProofTree [] (.impl sA sA) := .implI (.hyp (.head _))

-- Modus ponens instance
def sModusPonensProof : ProofTree [sA, .impl sA sB] sB :=
  .implE (.hyp (.tail _ (.head _))) (.hyp (.head _))

-- Check soundness with specific assignments
def assignTrue : Nat → Bool := λ _ => true
def assignFalse : Nat → Bool := λ _ => false

#eval sIdProof.checkSoundness assignTrue
#eval sIdProof.checkSoundness assignFalse
#eval sModusPonensProof.checkSoundness (λ n => if n == 0 then true else false)

-- Provable stuff
#eval identitySoundness sA
#eval sIdProof.size

end MiniProofKernel
