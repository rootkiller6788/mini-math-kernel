/-
# Proof Kernel: Objects

Sequent calculus representation and proof objects beyond
natural deduction trees. Defines sequent proofs, cut rules,
and transformation objects.
-/

import MiniProofKernel.Core.Basic

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Sequent Calculus Representation -/

/-- A sequent: `lhs ⊢ rhs` where both sides are lists of formulas.
Multi-succedent for classical flexibility. -/
structure Sequent where
  lhs : Context
  rhs : Context
  deriving Repr, Inhabited

/-- Sequent calculus proof rules (one-sided, Gentzen-style). -/
inductive SequentProof : Sequent → Type where
  | ax  (A : Formula) : SequentProof ⟨[A], [A]⟩
  | cut (A : Formula) (p : SequentProof ⟨Γ, A::Δ⟩) (q : SequentProof ⟨A::Γ', Δ'⟩) :
      SequentProof ⟨Γ ++ Γ', Δ ++ Δ'⟩
  | trueR  : SequentProof ⟨Γ, .true :: Δ⟩
  | falseL : SequentProof ⟨.false :: Γ, Δ⟩
  | notL (A : Formula) (p : SequentProof ⟨Γ, A :: Δ⟩) : SequentProof ⟨.not A :: Γ, Δ⟩
  | notR (A : Formula) (p : SequentProof ⟨A :: Γ, Δ⟩) : SequentProof ⟨Γ, .not A :: Δ⟩
  | andL (A B : Formula) (p : SequentProof ⟨A :: B :: Γ, Δ⟩) : SequentProof ⟨.and A B :: Γ, Δ⟩
  | andR (A B : Formula) (p : SequentProof ⟨Γ, A :: Δ⟩) (q : SequentProof ⟨Γ, B :: Δ⟩) :
      SequentProof ⟨Γ, .and A B :: Δ⟩
  | orL (A B : Formula) (p : SequentProof ⟨A :: Γ, Δ⟩) (q : SequentProof ⟨B :: Γ, Δ⟩) :
      SequentProof ⟨.or A B :: Γ, Δ⟩
  | orR (A B : Formula) (p : SequentProof ⟨Γ, A :: B :: Δ⟩) : SequentProof ⟨Γ, .or A B :: Δ⟩
  | implL (A B : Formula) (p : SequentProof ⟨Γ, A :: Δ⟩) (q : SequentProof ⟨B :: Γ, Δ⟩) :
      SequentProof ⟨.impl A B :: Γ, Δ⟩
  | implR (A B : Formula) (p : SequentProof ⟨A :: Γ, B :: Δ⟩) : SequentProof ⟨Γ, .impl A B :: Δ⟩
  deriving Repr

/-- Weakening for sequent proofs — add formulas to both sides. -/
def SequentProof.size : SequentProof σ → Nat
  | .ax _ => 1
  | .cut _ p q => 1 + size p + size q
  | .trueR => 1
  | .falseL => 1
  | .notL _ p => 1 + size p
  | .notR _ p => 1 + size p
  | .andL _ _ p => 1 + size p
  | .andR _ _ p q => 1 + size p + size q
  | .orL _ _ p q => 1 + size p + size q
  | .orR _ _ p => 1 + size p
  | .implL _ _ p q => 1 + size p + size q
  | .implR _ _ p => 1 + size p

/-! ## Dummy Objects — Return Type Carriers -/

/-- A normalized proof (beta-normal, eta-long). Wraps a proof tree. -/
structure NormalProof (Γ : Context) (A : Formula) where
  tree : ProofTree Γ A
  deriving Repr, Inhabited

/-- An annotated proof with explicit rule names for display. -/
inductive AnnotatedRule : Type where
  | hyp | trueI | falseE | andI | andEl | andEr
  | orIl | orIr | orE | implI | implE
  | notI | notE | equivI | equivEl | equivEr | lem
  deriving Repr, DecidableEq

/-- A derivation history recording each step. -/
structure DerivationStep where
  rule : AnnotatedRule
  context : Context
  conclusion : Formula
  deriving Repr, Inhabited

/-- A linearized proof trace (list of derivation steps). -/
abbrev ProofTrace := List DerivationStep

/-! ## Proof Utilities -/

/-- Count the number of hypothesis uses in a proof. -/
def ProofTree.hypCount {Γ : Context} {A : Formula} : ProofTree Γ A → Nat
  | .hyp _ => 1
  | .trueI => 0
  | .falseE p => hypCount p
  | .andI p q => hypCount p + hypCount q
  | .andEl p => hypCount p
  | .andEr p => hypCount p
  | .orIl p => hypCount p
  | .orIr p => hypCount p
  | .orE p q r => hypCount p + hypCount q + hypCount r
  | .implI p => hypCount p
  | .implE p q => hypCount p + hypCount q
  | .notI p => hypCount p
  | .notE p q => hypCount p + hypCount q
  | .equivI p q => hypCount p + hypCount q
  | .equivEl p => hypCount p
  | .equivEr p => hypCount p
  | .lem => 0

/-- Count the number of connectives introduced in a proof. -/
def ProofTree.connectiveCount {Γ : Context} {A : Formula} : ProofTree Γ A → Nat
  | .hyp _ => 0
  | .trueI => 1
  | .falseE p => 1 + connectiveCount p
  | .andI p q => 1 + connectiveCount p + connectiveCount q
  | .andEl p => connectiveCount p
  | .andEr p => connectiveCount p
  | .orIl p => connectiveCount p
  | .orIr p => connectiveCount p
  | .orE p q r => connectiveCount p + connectiveCount q + connectiveCount r
  | .implI p => 1 + connectiveCount p
  | .implE p q => connectiveCount p + connectiveCount q
  | .notI p => 1 + connectiveCount p
  | .notE p q => connectiveCount p + connectiveCount q
  | .equivI p q => 2 + connectiveCount p + connectiveCount q
  | .equivEl p => connectiveCount p
  | .equivEr p => connectiveCount p
  | .lem => 1

/-! ## Examples -/

def exampleA : Formula := .atom 0
def exampleB : Formula := .atom 1

-- A simple identity proof: A → A
def idProof : ProofTree [] (.impl exampleA exampleA) :=
  .implI (.hyp (.head _))

-- A sequent calculus proof of A ⊢ A
def axProof : SequentProof ⟨[exampleA], [exampleA]⟩ := .ax exampleA

#eval idProof.size
#eval idProof.connectiveCount
#eval Formula.complexity (.impl exampleA (.and exampleB exampleA))
#eval axProof.size
#eval idProof.isValid

end MiniProofKernel
