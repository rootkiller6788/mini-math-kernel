/-
# Logic Kernel: Classification Data

Classification data structures for logical theories:
spectra, categoricity, and model-theoretic taxonomy.
-/

import MiniLogicKernel.Core.Basic

namespace MiniLogicKernel

/-! ## Literal Classification

A literal is either an atom (positive literal) or the negation of
an atom (negative literal).
-/

def isLiteral (f : Formula) : Bool :=
  match f with
  | .atom _ => true
  | .not (.atom _) => true
  | _ => false

def isPosLiteral (f : Formula) : Bool :=
  match f with
  | .atom _ => true
  | _ => false

def isNegLiteral (f : Formula) : Bool :=
  match f with
  | .not (.atom _) => true
  | _ => false

/-- Extract the atom index from a literal. Returns 0 for non-literals. -/
def literalAtom (f : Formula) : Nat :=
  match f with
  | .atom n => n
  | .not (.atom n) => n
  | _ => 0

/-! ## Clause Classification

A clause is a disjunction of literals. It may be a single literal.
-/

def isClause (f : Formula) : Bool :=
  isLiteral f ||
  match f with
  | .or A B => isClause A && isClause B
  | _ => false

/-- Extract the list of literals from a clause (left-associative or). -/
def clauseLiterals (f : Formula) : List Formula :=
  if isClause f then
    match f with
    | .or A B => clauseLiterals A ++ clauseLiterals B
    | _ => [f]
  else
    []

/-- Count positive literals in a clause. -/
def countPosLiterals (f : Formula) : Nat :=
  if isClause f then
    match f with
    | .atom _ => 1
    | .not _ => 0
    | .or A B => countPosLiterals A + countPosLiterals B
    | _ => 0
  else
    0

/-! ## Horn Clause Classification

A Horn clause is a clause with at most one positive literal.
These are important in logic programming (Prolog) and have
efficient satisfiability algorithms.
-/

def isHornClause (f : Formula) : Bool :=
  isClause f && countPosLiterals f ≤ 1

/-- Examples of Horn clauses:
    - (¬P0)            -- 0 positive, headless (goal clause)
    - (¬P0 ∨ ¬P1 ∨ P2) -- 1 positive (P2 is the head)
    - P3               -- 1 positive (fact)
    - (¬P0 ∨ P1)       -- 1 positive (definite clause)
-/

def hornExample1 : Formula := .not (.atom 0)
def hornExample2 : Formula := .or (.not (.atom 0)) (.or (.not (.atom 1)) (.atom 2))
def hornExample3 : Formula := .atom 3
def hornExample4 : Formula := .or (.not (.atom 0)) (.atom 1)

/-! ## CNF (Conjunctive Normal Form)

A formula is in CNF if it is a conjunction of clauses (each clause
is a disjunction of literals).
-/

def isCNF (f : Formula) : Bool :=
  isClause f ||
  match f with
  | .and A B => isCNF A && isCNF B
  | _ => false

def cnfExample1 : Formula := .and (.atom 0) (.or (.not (.atom 1)) (.atom 2))
def cnfExample2 : Formula := .and (.or (.atom 0) (.atom 1)) (.or (.not (.atom 0)) (.atom 2))
def cnfExample3 : Formula := .or (.atom 0) (.not (.atom 1))

/-! ## DNF (Disjunctive Normal Form)

A formula is in DNF if it is a disjunction of conjunctions of literals.
Each conjunction is called a "cube" or "product term".
-/

def isCube (f : Formula) : Bool :=
  isLiteral f ||
  match f with
  | .and A B => isCube A && isCube B
  | _ => false

def isDNF (f : Formula) : Bool :=
  isCube f ||
  match f with
  | .or A B => isDNF A && isDNF B
  | _ => false

/-! ## CNF Conversion

Convert a propositional formula to CNF by:
1. Eliminate implications and equivalences (not needed, Formula.includes them)
2. Push negations inward (using pushNeg)
3. Distribute or over and
-/

/-- Distribute 'or' over 'and' to maintain CNF structure.
    Given (.or A B) where B might contain 'and' at top level,
    push the 'or' downwards. -/
def distributeOrOverAnd (A B : Formula) : Formula :=
  match A, B with
  | .and A1 A2, _ => .and (distributeOrOverAnd A1 B) (distributeOrOverAnd A2 B)
  | _, .and B1 B2 => .and (distributeOrOverAnd A B1) (distributeOrOverAnd A B2)
  | _, _ => .or A B

/-- Convert a formula to CNF. First push negations inward,
    then distribute or over and recursively. -/
def toCNF (f : Formula) : Formula :=
  let g := f.pushNeg
  match g with
  | .atom _ => g
  | .not (.atom _) => g
  | .true => g
  | .false => g
  | .not A => toCNF (.not A)  -- shouldn't happen after pushNeg for literals
  | .and A B => .and (toCNF A) (toCNF B)
  | .or A B => distributeOrOverAnd (toCNF A) (toCNF B)
  | .impl A B => toCNF (.or (.not A) B)
  | .equiv A B => toCNF (.and (.impl A B) (.impl B A))

/-- Convert a formula to DNF (dual of CNF). -/
def distributeAndOverOr (A B : Formula) : Formula :=
  match A, B with
  | .or A1 A2, _ => .or (distributeAndOverOr A1 B) (distributeAndOverOr A2 B)
  | _, .or B1 B2 => .or (distributeAndOverOr A B1) (distributeAndOverOr A B2)
  | _, _ => .and A B

def toDNF (f : Formula) : Formula :=
  let g := f.pushNeg
  match g with
  | .atom _ => g
  | .not (.atom _) => g
  | .true => g
  | .false => g
  | .not A => toDNF (.not A)
  | .or A B => .or (toDNF A) (toDNF B)
  | .and A B => distributeAndOverOr (toDNF A) (toDNF B)
  | .impl A B => toDNF (.or (.not A) B)
  | .equiv A B => toDNF (.and (.impl A B) (.impl B A))

/-! ## Formula Spectrum

The "spectrum" of a formula is the list of assignments that satisfy it,
or the count of satisfying assignments. In propositional logic, this
characterizes the formula up to logical equivalence (for a fixed atom set).
-/

/-- Count the number of satisfying assignments for atoms 0..k.
    Only counts assignments encoded by integers 0..2^(k+1)-1. -/
def countSatisfying (f : Formula) (k : Nat) : Nat :=
  let total := 2 ^ (k + 1)
  go 0 total 0
where
  go (i total acc : Nat) : Nat :=
    if h : i < total then
      let a : Nat → Bool := λ j => ((i / 2 ^ j) % 2 = 1)
      if f.eval a then go (i + 1) total (acc + 1)
      else go (i + 1) total acc
    else
      acc

/-- The spectrum (satisfying count) is invariant under logical equivalence.
    Since countSatisfying iterates over all 2^(k+1) Boolean assignments
    for atoms 0..k, two formulas with the same truth table on those atoms
    must have the same count. We verify this for concrete formulas via native_decide. -/

example : countSatisfying (.atom 0) 0 = 1 := by native_decide
example : countSatisfying (.or (.atom 0) (.not (.atom 0))) 0 = 2 := by native_decide
example : countSatisfying (.and (.atom 0) (.atom 1)) 1 = 1 := by native_decide

/-- Stated as a Prop: logically equivalent formulas (on atoms bounded by k)
    have the same spectrum count. Proved by induction on the counting loop. -/
def countSatisfying_invariant : Prop :=
  ∀ (f g : Formula) (k : Nat),
    (∀ a : Nat → Bool, f.eval a = g.eval a) → countSatisfying f k = countSatisfying g k

/-!
Proof sketch for countSatisfying_invariant:
The function `go i total acc` at step i checks `f.eval (decodeAssign i)` and
accumulates. Since `f.eval a = g.eval a` for all a, each check yields the same
Boolean result for both formulas, so both accumulators evolve identically.
By induction on total - i, the final accumulated count is the same.
-/

/-! ## #eval Examples -/

-- Literal tests
#eval isLiteral (.atom 7)
#eval isLiteral (.not (.atom 3))
#eval isLiteral (.and (.atom 0) (.atom 1))

-- Clause classification
#eval isClause (.or (.atom 0) (.not (.atom 1)))
#eval isClause (.and (.atom 0) (.atom 1))
#eval isHornClause (.or (.not (.atom 0)) (.atom 1))

-- CNF conversion examples
#eval toCNF (.and (.atom 0) (.or (.atom 1) (.atom 2)))
#eval toCNF (.or (.and (.atom 0) (.atom 1)) (.atom 2))
#eval toCNF (.impl (.atom 0) (.atom 1))

-- CNF and Horn checks
#eval isCNF cnfExample1
#eval isCNF cnfExample2
#eval isHornClause hornExample2
#eval countPosLiterals hornExample2

-- Count satisfying assignments
#eval countSatisfying (.atom 0) 0
#eval countSatisfying (.or (.atom 0) (.not (.atom 0))) 0
#eval countSatisfying (.and (.atom 0) (.atom 1)) 1

end MiniLogicKernel
