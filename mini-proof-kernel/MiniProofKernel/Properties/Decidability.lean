/-
# Proof Kernel: Decidability

Decision procedures for propositional logic: truth-table evaluation
of tautologies, satisfiability checking, and proof search for
constructing evidence of provability.
-/

import MiniProofKernel.Core.Basic
import MiniProofKernel.Core.Laws

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Truth-Table Decision Procedure -/

/-- Collect all atom indices used in a formula. -/
def Formula.collectAtoms : Formula → List Nat
  | .atom n => [n]
  | .true => []
  | .false => []
  | .not A => collectAtoms A
  | .and A B => collectAtoms A ++ collectAtoms B
  | .or A B => collectAtoms A ++ collectAtoms B
  | .impl A B => collectAtoms A ++ collectAtoms B
  | .equiv A B => collectAtoms A ++ collectAtoms B

/-- Remove duplicates from a list of atoms. -/
def dedupAtoms : List Nat → List Nat
  | [] => []
  | n :: ns => n :: dedupAtoms (ns.filter (· != n))

/-- The list of unique atoms in a formula, in order of first appearance. -/
def Formula.uniqueAtoms (f : Formula) : List Nat :=
  dedupAtoms f.collectAtoms

/-- Generate all boolean assignments for the given list of atom indices. -/
def allAssignments : List Nat → List (Nat → Bool)
  | [] => [λ _ => false]
  | n :: ns =>
    let rest := allAssignments ns
    (rest.map λ asgn => λ m => if m == n then true else asgn m) ++
    (rest.map λ asgn => λ m => if m == n then false else asgn m)

/-- Decide if a formula is a tautology using truth tables.
Evaluates the formula under all 2^n assignments (where n = number of atoms). -/
def decideTautology (f : Formula) : Bool :=
  let atoms := f.uniqueAtoms
  let assignments := allAssignments atoms
  assignments.all λ asgn => f.eval asgn

/-- Decide if a formula is satisfiable. -/
def decideSat (f : Formula) : Bool :=
  let atoms := f.uniqueAtoms
  let assignments := allAssignments atoms
  assignments.any λ asgn => f.eval asgn

/-- Decide if a formula is a contradiction (unsatisfiable). -/
def decideUnsat (f : Formula) : Bool :=
  !decideSat f

/-! ## Propositional Proof Search -/

/-- Simple backward proof search for propositional logic.
Attempts to find a proof tree for goal A under context Γ.
Uses a depth limit to guarantee termination. -/
partial def proofSearch (Γ : Context) (goal : Formula) (depth : Nat) : Option (ProofTree Γ goal) :=
  if depth == 0 then none
  else
    -- Try hypothesis
    match Γ.find? (· == goal) with
    | some _ =>
      match goal with
      | _ =>
        -- Search for membership proof using List.Mem
        searchHyp Γ goal
    | none =>
      match goal with
      | .true => some .trueI
      | .and A B =>
        match proofSearch Γ A (depth-1), proofSearch Γ B (depth-1) with
        | some p, some q => some (.andI p q)
        | _, _ => none
      | .impl A B =>
        match proofSearch (A :: Γ) B (depth-1) with
        | some p => some (.implI p)
        | none => none
      | .or A B =>
        match proofSearch Γ A (depth-1) with
        | some p => some (.orIl p)
        | none =>
          match proofSearch Γ B (depth-1) with
          | some p => some (.orIr p)
          | none => none
      | .not A =>
        match proofSearch (A :: Γ) .false (depth-1) with
        | some p => some (.notI p)
        | none => none
      | .equiv A B =>
        match proofSearch Γ (.impl A B) (depth-1),
              proofSearch Γ (.impl B A) (depth-1) with
        | some p, some q => some (.equivI p q)
        | _, _ => none
      | .false => none
      | .atom _ => none
where
  searchHyp (ctx : Context) (g : Formula) : Option (ProofTree ctx g) :=
    match ctx with
    | [] => none
    | a :: rest =>
      if a == g then
        some (.hyp (.head _))
      else
        match searchHyp rest g with
        | some (.hyp h) => some (.hyp (.tail _ h))
        | _ => none

/-- Auto-prove a tautology. Given a formula that is a tautology
(by truth-table check), attempt to construct a proof via search. -/
def autoProve (f : Formula) (maxDepth : Nat := 20) : Option (ProofTree [] f) :=
  if decideTautology f then
    proofSearch [] f maxDepth
  else none

/-! ## Small Tautology Prover -/

/-- Prove simple tautologies with direct construction.
Handles: identity, true introduction, simple implications. -/
def proveSimple (f : Formula) : Option (ProofTree [] f) :=
  match f with
  | .impl A B =>
    if A == B then some (.implI (.hyp (.head _)))
    else match A, B with
    | _, .true => some (.implI .trueI)
    | .false, _ => some (.implI (.falseE (.hyp (.head _))))
    | _, _ => proofSearch [] f 10
  | .and A B =>
    match proveSimple A, proveSimple B with
    | some p, some q => some (.andI p q)
    | _, _ => none
  | .true => some .trueI
  | _ => none

/-! ## Evaluation Examples -/

def decA : Formula := .atom 0
def decB : Formula := .atom 1

-- Identity is a tautology
def decIdFormula : Formula := .impl decA decA

-- Excluded middle is a tautology (by truth table)
def decLemFormula : Formula := .or decA (.not decA)

-- Non-contradiction: ¬(A ∧ ¬A)
def decNCFormula : Formula := .not (.and decA (.not decA))

-- de Morgan: ¬(A ∧ B) → (¬A ∨ ¬B) (classical tautology)
def decDMFormula : Formula :=
  .impl (.not (.and decA decB)) (.or (.not decA) (.not decB))

#eval decideTautology decIdFormula
#eval decideTautology decLemFormula
#eval decideTautology decNCFormula
#eval decideTautology decDMFormula
#eval decideSat (.and decA (.not decA))
#eval (proveSimple decIdFormula |>.getOrElse .trueI).size
#eval decDMFormula.complexity

end MiniProofKernel
