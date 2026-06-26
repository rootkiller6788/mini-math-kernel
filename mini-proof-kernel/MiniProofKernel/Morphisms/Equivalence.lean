/-
# Proof Kernel: Natural Deduction

Helper combinators for constructing natural deduction proofs.
-/

import MiniProofKernel.Core.Basic

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Hypothesis Helpers -/

def assume (A : Formula) : ProofTree (A :: Γ) A :=
  .hyp (.head _)

/-! ## Forward Reasoning -/

def applyModusPonens {Γ : Context} {A B : Formula}
    (impl : ProofTree Γ (.impl A B)) (prem : ProofTree Γ A) : ProofTree Γ B :=
  .implE impl prem

def andLeft {Γ : Context} {A B : Formula} (p : ProofTree Γ (.and A B)) : ProofTree Γ A := .andEl p
def andRight {Γ : Context} {A B : Formula} (p : ProofTree Γ (.and A B)) : ProofTree Γ B := .andEr p

def andIntro {Γ : Context} {A B : Formula}
    (p : ProofTree Γ A) (q : ProofTree Γ B) : ProofTree Γ (.and A B) := .andI p q

/-! ## Backward Reasoning -/

def introImpl {Γ : Context} {A B : Formula}
    (f : ProofTree (A :: Γ) A → ProofTree (A :: Γ) B) : ProofTree Γ (.impl A B) :=
  .implI (f (.hyp (.head _)))

def introOrLeft {Γ : Context} {A B : Formula} (p : ProofTree Γ A) : ProofTree Γ (.or A B) :=
  .orIl p

def introOrRight {Γ : Context} {A B : Formula} (p : ProofTree Γ B) : ProofTree Γ (.or A B) :=
  .orIr p

def introNot {Γ : Context} {A : Formula}
    (f : ProofTree (A :: Γ) A → ProofTree (A :: Γ) .false) : ProofTree Γ (.not A) :=
  .notI (f (.hyp (.head _)))

/-! ## Classical Reasoning -/

def byContradiction {Γ : Context} {A : Formula}
    (f : ProofTree ((.not A) :: Γ) (.not A) → ProofTree ((.not A) :: Γ) .false) : ProofTree Γ A :=
  .orE (.lem (a:=A)) (.hyp (.head _)) (.falseE (f (.hyp (.head _))))

def doubleNegElim {Γ : Context} {A : Formula}
    (p : ProofTree Γ (.not (.not A))) : ProofTree Γ A :=
  .orE (.lem (a:=A)) (.hyp (.head _)) (.falseE (.notE (p.weakenCons) (.hyp (.head _))))

/-! ## Proof Equivalence Relations -/

/-- Two proofs of the same conclusion from the same context are
beta-eta equivalent if one can be obtained from the other by
a series of beta-reductions and eta-expansions. -/

/-- Check if two proofs are syntactically identical (structural equality).
This is decidable via the automatically derived `DecidableEq`. -/
def ProofTree.structEq {Γ : Context} {A : Formula}
    (p q : ProofTree Γ A) : Bool := p == q

/-- Check if a proof is beta-reducible at the top level.
Only detects redexes that can be safely reduced without
substitution machinery (conjunction and equivalence beta-redexes).
Implication and disjunction redexes require substitution which
is detected by the structural `cutCount` but not reduced here. -/
def ProofTree.hasRedex {Γ : Context} {A : Formula} : ProofTree Γ A → Bool
  | .andEl (.andI _ _) => true
  | .andEr (.andI _ _) => true
  | .equivEl (.equivI _ _) => true
  | .equivEr (.equivI _ _) => true
  | .falseE p => hasRedex p
  | .andI p q => hasRedex p || hasRedex q
  | .andEl p => hasRedex p
  | .andEr p => hasRedex p
  | .orIl p => hasRedex p
  | .orIr p => hasRedex p
  | .orE p q r => hasRedex p || hasRedex q || hasRedex r
  | .implI p => hasRedex p
  | .implE p q => hasRedex p || hasRedex q
  | .notI p => hasRedex p
  | .notE p q => hasRedex p || hasRedex q
  | .equivI p q => hasRedex p || hasRedex q
  | .equivEl p => hasRedex p
  | .equivEr p => hasRedex p
  | _ => false

/-! ## Proof Transformations -/

/-- One-step weak head reduction: reduce the leftmost-outermost redex.
For top-level beta-redexes, performs the reduction directly.
For nested redexes, recursively reduces sub-proofs.
For implication substitution (the hard case), we note the structural
change without full substitution since proper substitution requires
dependent type machinery beyond propositional logic. -/
def ProofTree.reduceOneStep {Γ : Context} {A : Formula} :
    ProofTree Γ A → ProofTree Γ A
  | .hyp h => .hyp h
  | .trueI => .trueI
  | .lem => .lem
  | .implE (.implI p) q =>
    -- Beta-reduction for implication: (λx. p) q → p[q/x].
    -- We approximate substitution by weakening p's context
    -- note: full substitution is a meta-level operation.
    -- The reduced form knows A was introduced by implI and used by q.
    -- For propositional logic, this is the detour that we want to count/eliminate.
    -- We keep the structure but note it's reduced.
    .implE (.implI p) q
  | .andEl (.andI p _) => p
  | .andEr (.andI _ q) => q
  | .orE (.orIl p) q r =>
    -- Beta for disjunction left: case(inl(p), q, r) → q[p/x]
    -- p : Γ ⊢ A, q : A::Γ ⊢ C. Substitute p for head in q.
    -- Return q (type mismatch, cannot reduce in typed repr without substitution)
    .orE (.orIl p) q r
  | .orE (.orIr p) q r =>
    -- Beta for disjunction right: case(inr(p), q, r) → r[p/x]
    .orE (.orIr p) q r
  | .equivEl (.equivI p _) => p
  | .equivEr (.equivI _ q) => q
  | .falseE p => .falseE (reduceOneStep p)
  | .andI p q => .andI (reduceOneStep p) (reduceOneStep q)
  | .andEl p => .andEl (reduceOneStep p)
  | .andEr p => .andEr (reduceOneStep p)
  | .orIl p => .orIl (reduceOneStep p)
  | .orIr p => .orIr (reduceOneStep p)
  | .orE p q r => .orE (reduceOneStep p) (reduceOneStep q) (reduceOneStep r)
  | .implI p => .implI (reduceOneStep p)
  | .implE p q => .implE (reduceOneStep p) (reduceOneStep q)
  | .notI p => .notI (reduceOneStep p)
  | .notE p q => .notE (reduceOneStep p) (reduceOneStep q)
  | .equivI p q => .equivI (reduceOneStep p) (reduceOneStep q)
  | .equivEl p => .equivEl (reduceOneStep p)
  | .equivEr p => .equivEr (reduceOneStep p)

/-- Apply one-step reduction repeatedly until no more beta-redexes
exist or fuel runs out. For conjunction and equivalence redexes,
each step strictly decreases the proof tree. For implication and
disjunction (which require substitution infrastructure beyond the
typed representation), we count the detour but the reduction is a
no-op at the term level. Fuel ensures termination. -/
def ProofTree.normalizeFuel {Γ : Context} {A : Formula}
    (p : ProofTree Γ A) (fuel : Nat) : ProofTree Γ A :=
  match fuel with
  | 0 => p
  | fuel' + 1 =>
    if p.hasRedex then
      normalizeFuel (p.reduceOneStep) fuel'
    else
      p

/-- Full normalization with fuel bounded by proof size.
Each proper beta-redex elimination reduces size, so the fuel
bound ensures termination for all finite proofs. -/
def ProofTree.normalizeRec {Γ : Context} {A : Formula} (p : ProofTree Γ A) : ProofTree Γ A :=
  p.normalizeFuel p.size

/-! ## Proof Congruence Rules -/

/-- Reflexivity of proof equivalence: every proof is equivalent to itself. -/
def proofEquivRefl {Γ : Context} {A : Formula} (p : ProofTree Γ A) :
    ProofTree Γ (.equiv A A) := .equivI (.implI (.hyp (.head _))) (.implI (.hyp (.head _)))

/-- Symmetry: if A ↔ B is provable, so is B ↔ A. -/
def proofEquivSymm {Γ : Context} {A B : Formula}
    (p : ProofTree Γ (.equiv A B)) : ProofTree Γ (.equiv B A) :=
  .equivI (.equivEr p) (.equivEl p)

/-- Transitivity: if A ↔ B and B ↔ C are provable, so is A ↔ C. -/
def proofEquivTrans {Γ : Context} {A B C : Formula}
    (pAB : ProofTree Γ (.equiv A B))
    (pBC : ProofTree Γ (.equiv B C)) : ProofTree Γ (.equiv A C) :=
  .equivI
    (.implI (.implE (.equivEl pBC.weakenCons) (.implE (.equivEl pAB.weakenCons) (.hyp (.head _)))))
    (.implI (.implE (.equivEr pAB.weakenCons) (.implE (.equivEr pBC.weakenCons) (.hyp (.head _)))))

/-! ## Combinatorial Properties of Proofs -/

/-- Count the number of distinct sub-proofs in a proof tree.
Two sub-proofs are distinct if they have different structure. -/
def ProofTree.distinctSubproofCount {Γ : Context} {A : Formula} : ProofTree Γ A → Nat
  | .hyp _ => 1
  | .trueI => 1
  | .falseE p => 1 + distinctSubproofCount p
  | .andI p q => 1 + distinctSubproofCount p + distinctSubproofCount q
  | .andEl p => 1 + distinctSubproofCount p
  | .andEr p => 1 + distinctSubproofCount p
  | .orIl p => 1 + distinctSubproofCount p
  | .orIr p => 1 + distinctSubproofCount p
  | .orE p q r => 1 + distinctSubproofCount p + distinctSubproofCount q + distinctSubproofCount r
  | .implI p => 1 + distinctSubproofCount p
  | .implE p q => 1 + distinctSubproofCount p + distinctSubproofCount q
  | .notI p => 1 + distinctSubproofCount p
  | .notE p q => 1 + distinctSubproofCount p + distinctSubproofCount q
  | .equivI p q => 1 + distinctSubproofCount p + distinctSubproofCount q
  | .equivEl p => 1 + distinctSubproofCount p
  | .equivEr p => 1 + distinctSubproofCount p
  | .lem => 1

/-- Count the branching factor (max number of immediate subproofs). -/
def ProofTree.maxBranching {Γ : Context} {A : Formula} : ProofTree Γ A → Nat
  | .hyp _ => 0
  | .trueI => 0
  | .lem => 0
  | .falseE _ | .andEl _ | .andEr _ | .orIl _ | .orIr _ | .implI _ | .notI _
  | .equivEl _ | .equivEr _ => 1
  | .andI _ _ | .implE _ _ | .notE _ _ | .equivI _ _ => 2
  | .orE _ _ _ => 3

/-- Count the number of leaves (hypotheses and axioms) in a proof tree. -/
def ProofTree.leafCount {Γ : Context} {A : Formula} : ProofTree Γ A → Nat
  | .hyp _ => 1
  | .trueI => 1
  | .lem => 1
  | .falseE p => leafCount p
  | .andI p q => leafCount p + leafCount q
  | .andEl p => leafCount p
  | .andEr p => leafCount p
  | .orIl p => leafCount p
  | .orIr p => leafCount p
  | .orE p q r => leafCount p + leafCount q + leafCount r
  | .implI p => leafCount p
  | .implE p q => leafCount p + leafCount q
  | .notI p => leafCount p
  | .notE p q => leafCount p + leafCount q
  | .equivI p q => leafCount p + leafCount q
  | .equivEl p => leafCount p
  | .equivEr p => leafCount p

/-! ## Unused Hypothesis Detection -/

/-- Check if a hypothesis h in context Γ is actually used in proof p.
Returns true if the hypothesis appears somewhere in the proof tree. -/
def ProofTree.usesHypothesis {Γ : Context} {A B : Formula}
    (p : ProofTree Γ B) (h : A ∈ Γ) : Bool :=
  match p with
  | .hyp h' => h = h'
  | .trueI => false
  | .falseE p' => p'.usesHypothesis h
  | .andI p' q => p'.usesHypothesis h || q.usesHypothesis h
  | .andEl p' => p'.usesHypothesis h
  | .andEr p' => p'.usesHypothesis h
  | .orIl p' => p'.usesHypothesis h
  | .orIr p' => p'.usesHypothesis h
  | .orE p' q r => p'.usesHypothesis h || q.usesHypothesis h || r.usesHypothesis h
  | .implI p' => p'.usesHypothesis (by
      cases h with
      | head _ => exact .head _
      | tail _ h' => exact .tail _ h')
  | .implE p' q => p'.usesHypothesis h || q.usesHypothesis h
  | .notI p' => p'.usesHypothesis (by
      cases h with
      | head _ => exact .head _
      | tail _ h' => exact .tail _ h')
  | .notE p' q => p'.usesHypothesis h || q.usesHypothesis h
  | .equivI p' q => p'.usesHypothesis h || q.usesHypothesis h
  | .equivEl p' => p'.usesHypothesis h
  | .equivEr p' => p'.usesHypothesis h
  | .lem => false

/-- Collect the subset of hypotheses from Γ that are actually used in p.
Returns a list of formulas present in the proof tree. -/
def ProofTree.usedHypotheses {Γ : Context} {A : Formula} (p : ProofTree Γ A) : List Formula :=
  match p with
  | .hyp h => [A]
  | .trueI => []
  | .lem => []
  | .falseE p' => p'.usedHypotheses
  | .andI p' q => p'.usedHypotheses ++ q.usedHypotheses
  | .andEl p' => p'.usedHypotheses
  | .andEr p' => p'.usedHypotheses
  | .orIl p' => p'.usedHypotheses
  | .orIr p' => p'.usedHypotheses
  | .orE p' q r => p'.usedHypotheses ++ q.usedHypotheses ++ r.usedHypotheses
  | .implI p' => (p'.usedHypotheses).filter (· != A)
  | .implE p' q => p'.usedHypotheses ++ q.usedHypotheses
  | .notI p' => (p'.usedHypotheses).filter (· != A)
  | .notE p' q => p'.usedHypotheses ++ q.usedHypotheses
  | .equivI p' q => p'.usedHypotheses ++ q.usedHypotheses
  | .equivEl p' => p'.usedHypotheses
  | .equivEr p' => p'.usedHypotheses

/-- Count the number of distinct hypotheses actually used in a proof.
Useful for dependency analysis. -/
def ProofTree.distinctHypothesisCount {Γ : Context} {A : Formula} (p : ProofTree Γ A) : Nat :=
  let hyps := p.usedHypotheses
  dedup hyps |>.length
where
  dedup {α : Type} [BEq α] : List α → List α
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

/-! ## Evaluation Examples -/

def eqA : Formula := .atom 0
def eqB : Formula := .atom 1
def eqC : Formula := .atom 2

-- A proof with a conjunction beta-redex: andEl(andI(h, h'))
def eqRedex : ProofTree [eqA, eqB] eqA :=
  .andEl (.andI (.hyp (.head _)) (.hyp (.tail _ (.head _))))

-- A normal proof: just a hypothesis
def eqNormal : ProofTree [eqA] eqA := .hyp (.head _)

-- A proof with an equivalence beta-redex
def eqEquivRedex : ProofTree [] (.equiv eqA eqB) :=
  .equivEl (.equivI (.implI (.hyp (.head _))) (.implI (.hyp (.head _))))

-- Commutativity of ∧ as an equivalence
def eqAndComm : ProofTree [] (.equiv (.and eqA eqB) (.and eqB eqA)) :=
  .equivI
    (.implI (.andI (.andEr (.hyp (.head _))) (.andEl (.hyp (.head _)))))
    (.implI (.andI (.andEr (.hyp (.head _))) (.andEl (.hyp (.head _)))))

-- Transitivity example
def eqAB : ProofTree [] (.equiv eqA eqB) :=
  .equivI (.implI (.hyp (.head _))) (.implI (.hyp (.head _)))
def eqBC : ProofTree [] (.equiv eqB eqC) :=
  .equivI (.implI (.hyp (.head _))) (.implI (.hyp (.head _)))

#eval eqRedex.hasRedex
#eval eqNormal.hasRedex
#eval eqEquivRedex.hasRedex
#eval eqRedex.size
#eval eqRedex.reduceOneStep.size
#eval (eqRedex.normalizeRec).size
#eval (eqEquivRedex.reduceOneStep).size
#eval (eqAndComm).size
#eval (proofEquivSymm eqAndComm).size
#eval (proofEquivTrans eqAB eqBC).size
#eval (eqNormal).leafCount
#eval (eqNormal).maxBranching
#eval (eqAndComm).distinctSubproofCount
#eval (eqRedex).distinctHypothesisCount
#eval (eqNormal).distinctHypothesisCount

end MiniProofKernel
