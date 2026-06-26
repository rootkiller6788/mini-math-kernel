/-
# Logic Kernel: Counterexamples

Counterexamples in logic: non-tautologies,
invalid inference rule instances, and non-models.
-/

import MiniLogicKernel.Core.Basic
import MiniLogicKernel.Core.Objects

namespace MiniLogicKernel

/-! ## Counterexample Representation -/

/-- A printable representation of a partial assignment. -/
def AssignmentRepr := List (Nat × Bool)

instance : Repr AssignmentRepr where
  reprPrec l _ := repr l

/-! ## Formulas That Are Satisfiable But Not Valid -/

/-- Simple atom: satisfiable (set atom 0 to true) but not valid (set atom 0 to false). -/
def ex_simpleAtom : Formula := .atom 0

/-- Conjunction of independent atoms: satisfiable (both true) but not valid (both false). -/
def ex_conjunction : Formula := .and (.atom 0) (.atom 1)

/-- Disjunction: satisfiable (set one true) but not valid (both false makes it false). -/
def ex_disjunction : Formula := .or (.atom 0) (.atom 1)

/-- Implication: satisfiable (false → anything is true) but not valid (true → false is false). -/
def ex_implication : Formula := .impl (.atom 0) (.atom 1)

/-- Equivalence of distinct atoms: satisfiable (both true or both false) but not valid. -/
def ex_equivalence : Formula := .equiv (.atom 0) (.atom 1)

/-- `(A ∧ B) ∨ (¬A ∧ ¬B)`: true when A and B match, false otherwise. Satisfiable but not valid. -/
def ex_matching : Formula :=
  .or (.and (.atom 0) (.atom 1)) (.and (.not (.atom 0)) (.not (.atom 1)))

/-- Triple disjunction: satisfiable but not valid. -/
def ex_tripleOr : Formula := .or (.atom 0) (.or (.atom 1) (.atom 2))

#eval checkSatisfiableBool ex_simpleAtom
#eval checkTautologyBool ex_simpleAtom
#eval checkSatisfiableBool ex_conjunction
#eval checkTautologyBool ex_conjunction
#eval checkSatisfiableBool ex_disjunction
#eval checkTautologyBool ex_disjunction
#eval checkSatisfiableBool ex_implication
#eval checkTautologyBool ex_implication
#eval checkSatisfiableBool ex_equivalence
#eval checkTautologyBool ex_equivalence
#eval checkSatisfiableBool ex_matching
#eval checkTautologyBool ex_matching
#eval checkSatisfiableBool ex_tripleOr
#eval checkTautologyBool ex_tripleOr

/-! ## Counterexample Assignments for Non-Tautologies -/

/-- Counterexample for `A`: set atom 0 to false. -/
def counter_Atom : Nat → Bool := fun _ => false
#eval ex_simpleAtom.eval counter_Atom

/-- Counterexample for `A ∧ B`: set both to false. -/
def counter_Conjunction : Nat → Bool := fun _ => false
#eval ex_conjunction.eval counter_Conjunction

/-- Counterexample for `A ∨ B`: set both to false. -/
def counter_Disjunction : Nat → Bool := fun _ => false
#eval ex_disjunction.eval counter_Disjunction

/-- Counterexample for `A → B`: A true, B false. -/
def counter_Implication : Nat → Bool
  | 0 => true
  | _ => false
#eval ex_implication.eval counter_Implication

/-- Counterexample for `A ↔ B`: A true, B false (they differ). -/
def counter_Equivalence : Nat → Bool
  | 0 => true
  | _ => false
#eval ex_equivalence.eval counter_Equivalence

/-- Counterexample for `(A ∧ B) ∨ (¬A ∧ ¬B)`: A true, B false. -/
def counter_Matching : Nat → Bool
  | 0 => true
  | _ => false
#eval ex_matching.eval counter_Matching

/-! ## Invalid Inference Patterns -/

/-- Affirming the Consequent: `((A → B) ∧ B) → A` — INVALID.
    Counterexample: A false, B true. Then A→B is true and B is true, but A is false. -/
def invalid_affirmingConsequent (A B : Formula) : Formula :=
  .impl (.and (.impl A B) B) A

#eval checkTautologyBool (invalid_affirmingConsequent (.atom 0) (.atom 1))

def counter_affirmingConsequent : Nat → Bool
  | 0 => false
  | 1 => true
  | _ => false
#eval (invalid_affirmingConsequent (.atom 0) (.atom 1)).eval counter_affirmingConsequent

/-- Denying the Antecedent: `((A → B) ∧ ¬A) → ¬B` — INVALID.
    Counterexample: A false, B true. Then A→B is true, ¬A is true, but ¬B is false. -/
def invalid_denyingAntecedent (A B : Formula) : Formula :=
  .impl (.and (.impl A B) (.not A)) (.not B)

#eval checkTautologyBool (invalid_denyingAntecedent (.atom 0) (.atom 1))

def counter_denyingAntecedent : Nat → Bool
  | 0 => false
  | 1 => true
  | _ => false
#eval (invalid_denyingAntecedent (.atom 0) (.atom 1)).eval counter_denyingAntecedent

/-- Commutativity of implication: `(A → B) → (B → A)` — INVALID.
    Counterexample: A false, B true. LHS: false→true = true. RHS: true→false = false. -/
def invalid_implCommutative (A B : Formula) : Formula :=
  .impl (.impl A B) (.impl B A)

#eval checkTautologyBool (invalid_implCommutative (.atom 0) (.atom 1))

def counter_implCommutative : Nat → Bool
  | 0 => false
  | 1 => true
  | _ => false
#eval (invalid_implCommutative (.atom 0) (.atom 1)).eval counter_implCommutative

/-- Non-associativity of equivalence:
    `((A ↔ B) ↔ C) ↔ (A ↔ (B ↔ C))` — NOT a tautology.
    Counterexample: A=false, B=false, C=true.
    LHS: ((false↔false)↔true) = (true↔true) = true.
    RHS: (false↔(false↔true)) = (false↔false) = true.
    Wait, both are true! Let me try A=true, B=false, C=true:
    LHS: ((true↔false)↔true) = (false↔true) = false.
    RHS: (true↔(false↔true)) = (true↔false) = false.
    Try A=true, B=true, C=false:
    LHS: ((true↔true)↔false) = (true↔false) = false.
    RHS: (true↔(true↔false)) = (true↔false) = false.
    Try A=true, B=false, C=false:
    LHS: ((true↔false)↔false) = (false↔false) = true.
    RHS: (true↔(false↔false)) = (true↔true) = true.
    Hmm, equivalence IS associative! Let me use a different invalid pattern.
    Actually, equivalence IS associative classically. Let me use:
    `(A → (B → C)) ↔ ((A → B) → C)` — NOT a tautology. -/
def invalid_implAssoc (A B C : Formula) : Formula :=
  .equiv (.impl A (.impl B C)) (.impl (.impl A B) C)

#eval checkTautologyBool (invalid_implAssoc (.atom 0) (.atom 1) (.atom 2))

/-- `(A ↔ B) ∨ C` does NOT imply `(A ∨ C) ↔ (B ∨ C)` when C is true and A,B differ.
    Counterexample: C=true, A=false, B=true.
    LHS: (false↔true) ∨ true = false ∨ true = true.
    RHS: (false∨true) ↔ (true∨true) = true ↔ true = true.
    Wait, that's true. Try C=true, A=true, B=false:
    LHS: (true↔false) ∨ true = true. RHS: (true∨true) ↔ (false∨true) = true↔true = true.
    Hmm. Let me just use a simpler definitely-invalid formula.
    `(A → B) ∧ (B → C) ∧ A` does NOT imply `C`... wait that IS valid (Modus Ponens twice).
    OK: `A ∧ B → ¬(¬A ∨ ¬B)` is valid (it's one direction of De Morgan).
    But `¬(A ∧ B) → ¬A ∨ ¬B` — this IS a tautology.
    Let me use: `A → (B → A)` is valid, but `(A → B) → A` is NOT. -/
def invalid_affirmingConverse (A B : Formula) : Formula :=
  .impl (.impl A B) A

#eval checkTautologyBool (invalid_affirmingConverse (.atom 0) (.atom 1))

def counter_affirmingConverse : Nat → Bool
  | 0 => false
  | _ => false
#eval (invalid_affirmingConverse (.atom 0) (.atom 1)).eval counter_affirmingConverse

/-! ## Use findCounterexample for Automated Detection -/

def excludedMiddleForm (A : Formula) : Formula := .or A (.not A)
def lawOfIdentityForm (A : Formula) : Formula := .impl A A

#eval findCounterexample ex_simpleAtom
#eval findCounterexample ex_conjunction
#eval findCounterexample ex_disjunction
#eval findCounterexample ex_implication
#eval findCounterexample ex_equivalence
#eval findCounterexample (invalid_affirmingConsequent (.atom 0) (.atom 1))
#eval findCounterexample (invalid_denyingAntecedent (.atom 0) (.atom 1))

-- Verify that tautologies have no counterexample
#eval findCounterexample (excludedMiddleForm (.atom 0))
#eval findCounterexample (lawOfIdentityForm (.atom 0))

/-! ## Structural Counterexamples in Predicate Logic -/

/-- A structure with a two-element domain (Bool).
    Predicate 1 holds only for `true`, predicate 2 holds only for `false`. -/
def twoElementStructure : Structure where
  domain := Bool
  predInterp := fun p args =>
    match p, args with
    | 0, [] => True
    | 1, [x] => x      -- predicate 1 holds only for true
    | 2, [x] => !x     -- predicate 2 holds only for false
    | _, _ => False
  constInterp := fun _ => false

/-- `∃x P(x) → ∀x P(x)` is NOT valid when domain has >1 element.
    In the two-element structure with P(1) true only for `true`:
    ∃x P(x) is true (witness: true), but ∀x P(x) is false (false is a counterexample). -/
def invalid_existsImpliesForall : PredFormula :=
  .impl (.ex (.pred 1 [0])) (.all (.pred 1 [0]))

/-- Quantifier swap: `∀x∃y P(x,y) → ∃y∀x P(x,y)` — NOT valid.
    Example: domain = Nat, P(x,y) means "x < y".
    For every x there exists a larger y (true), but there is no y larger than all x (false). -/
def invalid_quantifierSwap : PredFormula :=
  .impl (.all (.ex (.pred 1 [0, 1]))) (.ex (.all (.pred 1 [0, 1])))

/-! ## #eval: Print Counterexample Formulas -/

#eval ex_simpleAtom
#eval invalid_affirmingConsequent (.atom 0) (.atom 1)
#eval invalid_denyingAntecedent (.atom 0) (.atom 1)
#eval invalid_implCommutative (.atom 0) (.atom 1)
#eval invalid_implAssoc (.atom 0) (.atom 1) (.atom 2)
#eval invalid_affirmingConverse (.atom 0) (.atom 1)

-- Show eval results for key counterexamples
#eval ex_simpleAtom.eval (fun _ => false)
#eval ex_implication.eval (fun n => if n = 0 then true else false)
#eval (invalid_affirmingConsequent (.atom 0) (.atom 1)).eval
      (fun n => match n with | 0 => false | 1 => true | _ => false)

end MiniLogicKernel
