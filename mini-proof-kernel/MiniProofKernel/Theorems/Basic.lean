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

end MiniProofKernel
