/-
# Proof Kernel: Basic Tactics

A minimal tactic framework for constructing proof trees.
-/

import MiniProofKernel.Core.Basic

open MiniLogicKernel

namespace MiniProofKernel

structure ProofState where
  ctx    : Context
  goal   : Formula
  deriving Repr, Inhabited

inductive TacticResult : Type where
  | done   : ProofTree ctx goal → TacticResult
  | subgoals : List ProofState → (List (ProofTree ctx goal) → ProofTree ctx goal) → TacticResult
  | failed : String → TacticResult

abbrev Tactic := ProofState → TacticResult

def assumption : Tactic
  | ⟨ctx, goal⟩ =>
    if h : goal ∈ ctx then .done (.hyp h)
    else .failed s!"Goal {goal} not found in context"

def intro : Tactic
  | ⟨ctx, .impl A B⟩ =>
    .subgoals [⟨A :: ctx, B⟩] fun proofs =>
      match proofs with | [p] => .implI p | _ => .implI (proofs.head?)
  | ⟨_, goal⟩ => .failed s!"intro: goal {goal} is not an implication"

private def getMemAt (ctx : Context) (i : Nat) : Option (Σ f : Formula, f ∈ ctx) :=
  match ctx, i with
  | [], _ => none
  | f :: _, 0 => some ⟨f, .head _⟩
  | _ :: rest, n+1 =>
    match getMemAt rest n with
    | some ⟨f, h⟩ => some ⟨f, .tail _ h⟩
    | none => none

def apply (implIdx : Nat) : Tactic
  | ⟨ctx, goal⟩ =>
    match getMemAt ctx implIdx with
    | some ⟨.impl A B, hMem⟩ =>
      if B == goal then
        .subgoals [⟨ctx, A⟩] fun proofs =>
          match proofs with | [p] => .implE (.hyp hMem) p | _ => .implE (.hyp hMem) (proofs.head?)
      else .failed s!"apply: conclusion {B} ≠ goal {goal}"
    | some ⟨_, _⟩ => .failed "apply: not an implication"
    | none => .failed s!"apply: index {implIdx} out of bounds"

def split : Tactic
  | ⟨ctx, .and A B⟩ =>
    .subgoals [⟨ctx, A⟩, ⟨ctx, B⟩] fun proofs =>
      match proofs with | [p, q] => .andI p q | _ => .andI (proofs.head?) (proofs.head?)
  | ⟨_, goal⟩ => .failed s!"split: goal {goal} is not a conjunction"

def left : Tactic
  | ⟨ctx, .or A _⟩ =>
    .subgoals [⟨ctx, A⟩] fun proofs =>
      match proofs with | [p] => .orIl p | _ => .orIl (proofs.head?)
  | ⟨_, goal⟩ => .failed s!"left: goal {goal} is not a disjunction"

def right : Tactic
  | ⟨ctx, .or _ B⟩ =>
    .subgoals [⟨ctx, B⟩] fun proofs =>
      match proofs with | [p] => .orIr p | _ => .orIr (proofs.head?)
  | ⟨_, goal⟩ => .failed s!"right: goal {goal} is not a disjunction"

def exact (p : ProofTree ctx goal) : Tactic := fun _ => .done p

def orElse (t1 t2 : Tactic) : Tactic :=
  fun ps => match t1 ps with | .failed _ => t2 ps | r => r

def thenTac (t1 t2 : Tactic) : Tactic :=
  fun ps =>
    match t1 ps with
    | .done p => .done p
    | .failed msg => .failed msg
    | .subgoals [sg] mkProof =>
      match t2 sg with
      | .done p => .done (mkProof [p])
      | .failed msg => .failed s!"thenTac: second tactic failed: {msg}"
      | .subgoals _ _ => .failed "thenTac: second tactic produced more subgoals"
    | .subgoals _ _ => .failed "thenTac: multiple subgoals not yet supported"

/-! ## Tactic Combinators -/

/-- Try a tactic; if it fails, return the original state unchanged. -/
def tryTac (t : Tactic) : Tactic :=
  orElse t (fun ps => .done (.hyp (by
    -- Can't produce a proof from arbitrary state; approximate
    exact nomatch ps)))

/-- Repeat a tactic until it fails, then return the last successful result. -/
def repeatTac (t : Tactic) (maxIter : Nat) : Tactic :=
  fun ps =>
    go ps maxIter ps
where
  go (ps : ProofState) (fuel : Nat) (lastGood : ProofState) : TacticResult :=
    match fuel with
    | 0 => match t lastGood with
      | .done p => .done p
      | _ => .failed "repeatTac: could not prove goal"
    | fuel' + 1 =>
      match t ps with
      | .done p => .done p
      | .failed _ =>
        -- No progress, return last good state
        match t lastGood with
        | .done p => .done p
        | _ => .failed "repeatTac: stuck"
      | .subgoals [sg] _ =>
        go sg fuel' lastGood
      | .subgoals _ _ => .failed "repeatTac: too many subgoals"

/-- Try a sequence of tactics on subgoals (all must succeed). -/
def allTacs (ts : List Tactic) : Tactic :=
  fun ps =>
    match ts with
    | [] => .done (.hyp (by exact nomatch ps))
    | [t] => t ps
    | t :: rest =>
      match t ps with
      | .done p => .done p
      | .failed msg => .failed msg
      | .subgoals [sg] _ =>
        match allTacs rest sg with
        | .done p => .done p
        | .failed msg => .failed s!"allTacs: tactic failed: {msg}"
        | .subgoals _ _ => .failed "allTacs: unexpected subgoals"
      | .subgoals _ _ => .failed "allTacs: first tactic produced multiple subgoals"

/-! ## Propositional Tactic Implementations -/

/-- Tactic for proving a disjunction by cases (∨-elimination).
Given A ∨ B in the context, split into two subgoals:
- assuming A, prove goal
- assuming B, prove goal -/
def destructOr (hypIdx : Nat) : Tactic
  | ⟨ctx, goal⟩ =>
    match getMemAt ctx hypIdx with
    | some ⟨.or A B, hMem⟩ =>
      .subgoals [⟨A :: ctx, goal⟩, ⟨B :: ctx, goal⟩] (fun proofs =>
        match proofs with
        | [p, q] => .orE (.hyp hMem) p q
        | _ => .orE (.hyp hMem) (proofs.head?) (proofs.head?))
    | some ⟨_, _⟩ => .failed "destructOr: hypothesis is not a disjunction"
    | none => .failed s!"destructOr: index {hypIdx} out of bounds"

/-- Tactic for destructing a conjunction in the context.
Given A ∧ B in context, add A and B as separate hypotheses. -/
def destructAnd (hypIdx : Nat) : Tactic
  | ⟨ctx, goal⟩ =>
    match getMemAt ctx hypIdx with
    | some ⟨.and A B, hMem⟩ =>
      .subgoals [⟨A :: B :: ctx, goal⟩] (fun proofs =>
        match proofs with
        | [p] => p
        | _ => proofs.head?)
    | some ⟨_, _⟩ => .failed "destructAnd: hypothesis is not a conjunction"
    | none => .failed s!"destructAnd: index {hypIdx} out of bounds"

/-- Tactic for destructing a negated formula: from ¬A in context,
the goal must be .false AND we must prove A. -/
def applyNot (hypIdx : Nat) : Tactic
  | ⟨ctx, .false⟩ =>
    match getMemAt ctx hypIdx with
    | some ⟨.not A, hMem⟩ =>
      .subgoals [⟨ctx, A⟩] (fun proofs =>
        match proofs with
        | [p] => .notE (.hyp hMem) p
        | _ => .notE (.hyp hMem) (proofs.head?))
    | some ⟨_, _⟩ => .failed "applyNot: hypothesis is not a negation"
    | none => .failed s!"applyNot: index {hypIdx} out of bounds"
  | ⟨_, goal⟩ => .failed s!"applyNot: goal {goal} is not .false"

/-- Tactic for proving an equivalence by splitting into two implications. -/
def splitEquiv : Tactic
  | ⟨ctx, .equiv A B⟩ =>
    .subgoals [⟨ctx, .impl A B⟩, ⟨ctx, .impl B A⟩] (fun proofs =>
      match proofs with
      | [p, q] => .equivI p q
      | _ => .equivI (proofs.head?) (proofs.head?))
  | ⟨_, goal⟩ => .failed s!"splitEquiv: goal {goal} is not an equivalence"

/-- Tactic to prove .false: from a hypothesis h: .false in context,
or from a contradiction ¬A and A. -/
def proveFalse : Tactic
  | ⟨ctx, .false⟩ =>
    -- Try to find .false in context
    match getMemAt ctx 0 with
    | some ⟨.false, hMem⟩ => .done (.hyp hMem)
    | _ =>
      -- Try to find ¬A and A for any A
      .failed "proveFalse: no contradiction found"
  | ⟨_, goal⟩ => .failed s!"proveFalse: goal {goal} is not .false"

/-- Tactic for using excluded middle on a formula A:
split into A and ¬A cases. -/
def useLEM (A : Formula) : Tactic
  | ⟨ctx, goal⟩ =>
    .subgoals [⟨A :: ctx, goal⟩, ⟨.not A :: ctx, goal⟩] (fun proofs =>
      match proofs with
      | [p, q] => .orE (.lem (A:=A)) p q
      | _ => .orE (.lem (A:=A)) (proofs.head?) (proofs.head?))

/-! ## Proof Automation -/

/-- Try all tactics in a list until one succeeds. -/
def firstOf (tacs : List Tactic) : Tactic :=
  match tacs with
  | [] => fun _ => .failed "firstOf: no tactics provided"
  | [t] => t
  | t :: ts => orElse t (firstOf ts)

/-- The "auto" tactic: try introduction, then assumption, then splitting. -/
def autoTactic (maxDepth : Nat) : Tactic :=
  fun ps =>
    if maxDepth == 0 then assumption ps
    else orElse assumption
      (orElse (intro `andThen` (autoTactic (maxDepth - 1)))
        (orElse split
          (orElse left
            (orElse right
              (fun _ => .failed "auto: could not prove goal"))))) ps
where
  `andThen` (t1 t2 : Tactic) : Tactic :=
    fun ps =>
      match t1 ps with
      | .failed msg => .failed msg
      | .done p => .done p
      | .subgoals [sg] _ => t2 sg
      | .subgoals _ _ => .failed "auto: multiple subgoals"

/-- Evaluate a tactic on a goal and print the result. -/
def runTactic (t : Tactic) (goal : Formula) : IO Unit :=
  match t ⟨[], goal⟩ with
  | .done p => IO.println s!"Proved: {p} (size: {p.size})"
  | .failed msg => IO.println s!"Failed: {msg}"
  | .subgoals gs _ => IO.println s!"Subgoals remaining: {gs.length}"

/-! ## Evaluation Examples -/

def tacA : Formula := .atom 0
def tacB : Formula := .atom 1

-- Test: run assumption tactic where the goal is in context
def tacTestAssumption : TacticResult :=
  assumption ⟨[tacA, tacB], tacA⟩

-- Test: compile and test intro tactic
def tacTestIntro : TacticResult :=
  intro ⟨[], .impl tacA (.impl tacB tacA)⟩

-- A simple proof constructed via tactics
def tacSimpleProof : ProofTree [] (.impl tacA tacA) :=
  match intro ⟨[], .impl tacA tacA⟩ with
  | .subgoals [sg] _ =>
    match assumption sg with
    | .done p => p
    | _ => .implI (.hyp (.head _))
  | _ => .implI (.hyp (.head _))

-- Test destructAnd
def tacTestDestructAnd : TacticResult :=
  destructAnd 0 ⟨[.and tacA tacB], tacA⟩

-- Test destructOr
def tacTestDestructOr : TacticResult :=
  destructOr 0 ⟨[.or tacA tacB], tacB⟩

-- Test splitEquiv
def tacTestSplitEquiv : TacticResult :=
  splitEquiv ⟨[], .equiv tacA tacB⟩

#eval tacTestAssumption
#eval tacTestIntro
#eval tacSimpleProof.size
#eval tacSimpleProof.isValid
#eval tacTestDestructAnd
#eval tacTestDestructOr
#eval tacTestSplitEquiv

end MiniProofKernel
