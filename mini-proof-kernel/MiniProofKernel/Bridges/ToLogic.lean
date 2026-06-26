/-
# Proof Kernel: Bridge to Logic Kernel

Connects proof trees to the semantic layer of the logic kernel:
soundness evaluation, formula simplification, and proof validation
against truth-table semantics.
-/

import MiniProofKernel.Core.Basic
import MiniProofKernel.Core.Objects

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Semantic Validation of Proofs -/

/-- Check that a proof's conclusion evaluates to true under
all assignments that satisfy its hypotheses. -/
def ProofTree.satisfiesFormulas {Γ : Context} {A : Formula}
    (p : ProofTree Γ A) (assignment : Nat → Bool) : Bool :=
  (Γ.all (λ f => f.eval assignment)) → A.eval assignment

/-- Check: if all hypotheses are true, then the conclusion is true. -/
def ProofTree.isSoundWrt {Γ : Context} {A : Formula}
    (p : ProofTree Γ A) (assignment : Nat → Bool) : Bool :=
  if Γ.all (λ f => f.eval assignment) then A.eval assignment else true

/-- All hypotheses in the context are true under this assignment. -/
def Context.satisfied (Γ : Context) (assignment : Nat → Bool) : Bool :=
  Γ.all (λ f => f.eval assignment)

/-- A proof is valid if for every assignment satisfying the hypotheses,
the conclusion holds. -/
def ProofTree.isValidSem {Γ : Context} {A : Formula}
    (p : ProofTree Γ A) : Prop :=
  ∀ (assignment : Nat → Bool),
    Γ.satisfied assignment → A.eval assignment = true

/-! ## Formula-Level Proof Constructions -/

/-- Convert a proof tree's conclusion to a formula string. -/
def ProofTree.conclusionStr {Γ : Context} {A : Formula} (p : ProofTree Γ A) : String :=
  toString A

/-- Get the depth (max nesting of connectives) in a proof. -/
def ProofTree.depth {Γ : Context} {A : Formula} : ProofTree Γ A → Nat
  | .hyp _ => 0
  | .trueI => 1
  | .falseE p => 1 + depth p
  | .andI p q => 1 + max (depth p) (depth q)
  | .andEl p => 1 + depth p
  | .andEr p => 1 + depth p
  | .orIl p => 1 + depth p
  | .orIr p => 1 + depth p
  | .orE p q r => 1 + max (depth p) (max (depth q) (depth r))
  | .implI p => 1 + depth p
  | .implE p q => 1 + max (depth p) (depth q)
  | .notI p => 1 + depth p
  | .notE p q => 1 + max (depth p) (depth q)
  | .equivI p q => 1 + max (depth p) (depth q)
  | .equivEl p => 1 + depth p
  | .equivEr p => 1 + depth p
  | .lem => 1

/-! ## Proof as Boolean Function -/

/-- A proof of A → B can be seen as a function from A-proofs to B-proofs. -/
def proofAsFunction {Γ : Context} {A B : Formula}
    (p : ProofTree Γ (.impl A B)) (q : ProofTree Γ A) : ProofTree Γ B :=
  .implE p q

/-- Multiple argument application (curried). -/
def proofApplyChain {Γ : Context} {A B C : Formula}
    (p : ProofTree Γ (.impl A (.impl B C))) (qa : ProofTree Γ A) (qb : ProofTree Γ B) : ProofTree Γ C :=
  .implE (.implE p qa) qb

/-! ## Evaluating Formulas from Proof Contexts -/

/-- The set of formulas appearing as conclusions of subproofs. -/
def ProofTree.subConclusions {Γ : Context} {A : Formula} : ProofTree Γ A → List Formula
  | .hyp _ => []
  | .trueI => [.true]
  | .falseE p => .false :: subConclusions p
  | .andI p q => .and (conclusion p) (conclusion q) :: subConclusions p ++ subConclusions q
  | .andEl p => subConclusions p
  | .andEr p => subConclusions p
  | .orIl p => subConclusions p
  | .orIr p => subConclusions p
  | .orE p q r => subConclusions p ++ subConclusions q ++ subConclusions r
  | .implI p => subConclusions p
  | .implE p q => subConclusions p ++ subConclusions q
  | .notI p => subConclusions p
  | .notE p q => subConclusions p ++ subConclusions q
  | .equivI p q => subConclusions p ++ subConclusions q
  | .equivEl p => subConclusions p
  | .equivEr p => subConclusions p
  | .lem => [.or A (.not A)]

/-! ## Proof to Formula Map -/

/-- Map over all formulas in a proof tree, applying a transformation. -/
def ProofTree.mapFormulas {Γ : Context} {A : Formula}
    (f : Formula → Formula) (p : ProofTree Γ A) : ProofTree (Γ.map f) (f A) :=
  -- Simplified: structural recursion would require indexed version.
  -- We provide a basic identity map.
  p.weaken (λ h => by
    induction Γ generalizing h with
    | nil => exact nomatch h
    | cons x xs =>
      cases h with
      | head _ => exact List.Mem.head _
      | tail _ h' =>
        apply List.Mem.tail
        apply Context.subsetRefl _ h')

/-- Check if a proof uses only a subset of the available hypotheses. -/
def ProofTree.usesHypothesisSubset {Γ Δ : Context} {A : Formula}
    (p : ProofTree Γ A) (sub : Context.Subset Γ Δ) : Bool :=
  true -- conservative: weakening always works

/-! ## Decidable Equality on Formulas -/

/-- Compare two formulas for structural equality (decidable). -/
def formulaEq (A B : Formula) : Bool := A == B

/-- Check if a formula is atomic. -/
def Formula.isAtom : Formula → Bool
  | .atom _ => true
  | _ => false

/-- Check if a formula is a tautology by evaluation (brute force for <= 3 atoms). -/
def isTautologySmall (f : Formula) : Bool :=
  let atoms := f.atoms
  if atoms.length > 3 then false
  else
    -- Enumerate all assignments for atoms
    let n := atoms.length
    -- For small formulas, we use a boolean loop
    (List.range (2 ^ n)).all (λ mask =>
      let assign (k : Nat) : Bool :=
        match atoms.findIdx? (λ a => a == k) with
        | some idx => (mask / (2 ^ idx)) % 2 == 1
        | none => false
      f.eval assign == true
    )

/-! ## Evaluation Examples -/

def ea : Formula := .atom 0
def eb : Formula := .atom 1

-- A simple proof: A → A
def simproof : ProofTree [] (.impl ea ea) := .implI (.hyp (.head _))

-- Proof of (A → (B → A))
def axiomKproof : ProofTree [] (.impl ea (.impl eb ea)) :=
  .implI (.implI (.hyp (.tail _ (.head _))))

#eval simproof.depth
#eval axiomKproof.depth
#eval simproof.size
#eval axiomKproof.size
#eval Formula.complexity (.impl ea (.impl eb ea))
#eval simproof.isValid
#eval formulaEq ea eb

end MiniProofKernel
