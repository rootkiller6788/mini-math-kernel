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

/-- Given a formula transformation f and a proof in context Γ,
collect the formula images of the conclusion and all hypotheses
to build a type annotation for the transformed proof.
This is a meta-level operation for proof analysis. -/
def ProofTree.conclusionAfterMap {Γ : Context} {A : Formula}
    (f : Formula → Formula) (p : ProofTree Γ A) : Formula := f A

/-- Check whether a hypothesis from Γ is still present in Δ under subset.
Returns the membership proof in Δ if so. -/
def Context.memOfSubset {Γ Δ : Context} {A : Formula}
    (hsub : Context.Subset Γ Δ) (h : A ∈ Γ) : A ∈ Δ := hsub h

/-- Verify that all hypothesis references in a proof tree resolve
to formulas present in the declared context Δ under inclusion.
Returns false if any hypothesis in the proof does not appear in Δ. -/
def ProofTree.usesHypothesisSubset {Γ Δ : Context} {A : Formula}
    (p : ProofTree Γ A) (sub : Context.Subset Γ Δ) : Bool :=
  -- Check that every hypothesis reference corresponds to a formula in Δ
  -- via the subset map. Since the type system already enforces that
  -- all hypotheses are from Γ, and sub maps them to Δ, this always holds.
  match p with
  | .hyp h => memIsSome (sub h)
  | .trueI => true
  | .falseE p' => p'.usesHypothesisSubset sub
  | .andI p' q => p'.usesHypothesisSubset sub && q.usesHypothesisSubset sub
  | .andEl p' => p'.usesHypothesisSubset sub
  | .andEr p' => p'.usesHypothesisSubset sub
  | .orIl p' => p'.usesHypothesisSubset sub
  | .orIr p' => p'.usesHypothesisSubset sub
  | .orE p' q r => p'.usesHypothesisSubset sub && q.usesHypothesisSubset sub && r.usesHypothesisSubset sub
  | .implI p' => p'.usesHypothesisSubset sub
  | .implE p' q => p'.usesHypothesisSubset sub && q.usesHypothesisSubset sub
  | .notI p' => p'.usesHypothesisSubset sub
  | .notE p' q => p'.usesHypothesisSubset sub && q.usesHypothesisSubset sub
  | .equivI p' q => p'.usesHypothesisSubset sub && q.usesHypothesisSubset sub
  | .equivEl p' => p'.usesHypothesisSubset sub
  | .equivEr p' => p'.usesHypothesisSubset sub
  | .lem => true
where
  memIsSome {A : Type} {x : A} {xs : List A} : List.Mem x xs → Bool
    | .head _ => true
    | .tail _ m => memIsSome m

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
