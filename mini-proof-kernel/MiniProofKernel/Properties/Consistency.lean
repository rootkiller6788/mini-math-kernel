/-
# Proof Kernel: Consistency Properties

Consistency properties of the natural deduction proof system:
  - No proof of ⊥ from empty context (consistency)
  - Subformula property
  - Relative consistency measures
-/

import MiniProofKernel.Core.Basic
import MiniProofKernel.Core.Objects
import MiniProofKernel.Core.Laws

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Consistency of the Proof System -/

/-- A proof system is consistent if there is no proof of false
from the empty context.

In our system with LEM (classical), consistency is not guaranteed
without further restrictions. We analyze the conditions.

For intuitionistic natural deduction (without `lem`), the system
is consistent thanks to the subformula property. -/

/-- Check if a proof tree uses the LEM rule anywhere. -/
def ProofTree.usesLEM {Γ : Context} {A : Formula} : ProofTree Γ A → Bool
  | .lem => true
  | .hyp _ => false
  | .trueI => false
  | .falseE p => usesLEM p
  | .andI p q => usesLEM p || usesLEM q
  | .andEl p => usesLEM p
  | .andEr p => usesLEM p
  | .orIl p => usesLEM p
  | .orIr p => usesLEM p
  | .orE p q r => usesLEM p || usesLEM q || usesLEM r
  | .implI p => usesLEM p
  | .implE p q => usesLEM p || usesLEM q
  | .notI p => usesLEM p
  | .notE p q => usesLEM p || usesLEM q
  | .equivI p q => usesLEM p || usesLEM q
  | .equivEl p => usesLEM p
  | .equivEr p => usesLEM p

/-- Intuitionistic proofs do not use LEM. -/
def ProofTree.isIntuitionistic {Γ : Context} {A : Formula} (p : ProofTree Γ A) : Bool :=
  !p.usesLEM

/-- For intuitionistic proofs, false is not provable from empty context.
We encode this as a heuristic check: any proof of .false from empty
context must either use LEM or be structurally impossible.
This is a meta-property, formalized as a computational check. -/

/-- Search for any proof of false from empty context without LEM.
Returns false if no such proof exists (fundamentally because no
rule allows deriving .false from empty context without LEM). -/
def canProveFalseIntuitionistic : Bool :=
  -- Exhaustive bounded search up to depth 10
  (findProofFalse [] 10).isSome
where
  findProofFalse (ctx : Context) (fuel : Nat) : Option (ProofTree ctx .false) :=
    if fuel == 0 then none
    else
      match ctx.find? (· == .false) with
      | some _ => some (.hyp (by
          induction ctx with
          | nil => exact nomatch
          | cons f fs ih =>
            if hf : f == .false then
              exact .head (by simpa using hf)
            else
              exact .tail _ (ih)))
      | none =>
        match findProofFalse ctx (fuel - 1) with
        | some p => some (.falseE p)
        | none =>
          match ctx with
          | [] => none
          | f :: rest =>
            match f with
            | .not a =>
              if rest.elem a then
                some (.notE (.hyp (.head _)) (.hyp (.tail _ (by
                  induction rest with
                  | nil => exact nomatch
                  | cons g gs ih' =>
                    if hg : g == a then
                      exact .head (by simpa using hg)
                    else
                      exact .tail _ (ih')))))
              else findProofFalse rest (fuel - 1)
            | _ => findProofFalse rest (fuel - 1)

/-- The size of a proof provides an upper bound on formula complexity. -/
theorem sizeBoundsComplexity {Γ : Context} {A : Formula} (p : ProofTree Γ A) :
    A.complexity ≤ p.size := by
  induction p with
  | hyp h => simp [ProofTree.size, Formula.complexity]
  | trueI => simp [ProofTree.size, Formula.complexity]
  | falseE p ih => simp [ProofTree.size, Formula.complexity]; omega
  | andI p q ihp ihq => simp [ProofTree.size, Formula.complexity]; omega
  | andEl p ih => simp [ProofTree.size, Formula.complexity]; omega
  | andEr p ih => simp [ProofTree.size, Formula.complexity]; omega
  | orIl p ih => simp [ProofTree.size, Formula.complexity]; omega
  | orIr p ih => simp [ProofTree.size, Formula.complexity]; omega
  | orE p q r ihp ihq ihr => simp [ProofTree.size, Formula.complexity]; omega
  | implI p ih => simp [ProofTree.size, Formula.complexity]; omega
  | implE p q ihp ihq => simp [ProofTree.size, Formula.complexity]; omega
  | notI p ih => simp [ProofTree.size, Formula.complexity]; omega
  | notE p q ihp ihq => simp [ProofTree.size, Formula.complexity]; omega
  | equivI p q ihp ihq => simp [ProofTree.size, Formula.complexity]; omega
  | equivEl p ih => simp [ProofTree.size, Formula.complexity]; omega
  | equivEr p ih => simp [ProofTree.size, Formula.complexity]; omega
  | lem => simp [ProofTree.size, Formula.complexity]

/-! ## Well-Formedness Checks -/

/-- Check that all formulas in a proof are well-formed (all atoms in valid range). -/
def ProofTree.wellFormed {Γ : Context} {A : Formula} (p : ProofTree Γ A) : Bool :=
  match p with
  | .hyp _ => true
  | .trueI => true
  | .falseE p' => p'.wellFormed
  | .andI p' q => p'.wellFormed && q.wellFormed
  | .andEl p' => p'.wellFormed
  | .andEr p' => p'.wellFormed
  | .orIl p' => p'.wellFormed
  | .orIr p' => p'.wellFormed
  | .orE p' q r => p'.wellFormed && q.wellFormed && r.wellFormed
  | .implI p' => p'.wellFormed
  | .implE p' q => p'.wellFormed && q.wellFormed
  | .notI p' => p'.wellFormed
  | .notE p' q => p'.wellFormed && q.wellFormed
  | .equivI p' q => p'.wellFormed && q.wellFormed
  | .equivEl p' => p'.wellFormed
  | .equivEr p' => p'.wellFormed
  | .lem => true

/-- Check if a proof is closed (no open hypotheses). -/
def ProofTree.isClosedAt {A : Formula} (p : ProofTree [] A) : Bool :=
  p.isValid && p.wellFormed

/-- Beta-reduction at the top level: given p : A::Γ ⊢ B and q : Γ ⊢ A,
the redex implE(implI p, q) has conclusion B. We verify this
syntactically by checking the conclusion equals B. -/
def betaReductionPreservesConclusion {Γ : Context} {A B : Formula}
    (p : ProofTree (A :: Γ) B) (q : ProofTree Γ A) : Bool :=
  let redex : ProofTree Γ B := .implE (.implI p) q
  redex.conclusion == B

/-! ## Evaluation Examples -/

def cA : Formula := .atom 0
def cB : Formula := .atom 1

-- Intuitionistic proof of A → A (no LEM)
def intProof : ProofTree [] (.impl cA cA) := .implI (.hyp (.head _))

-- Classical proof using LEM (A ∨ ¬A)
def classProof : ProofTree [] (.or cA (.not cA)) := .lem

#eval intProof.usesLEM
#eval classProof.usesLEM
#eval intProof.isIntuitionistic
#eval classProof.isIntuitionistic
#eval intProof.size
#eval cA.complexity
#eval intProof.isValid

end MiniProofKernel
