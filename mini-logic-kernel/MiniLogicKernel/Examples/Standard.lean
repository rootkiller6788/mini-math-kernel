/-
# Logic Kernel: Standard Examples

Standard examples: propositional tautologies, predicate
formulas, and first-order structures.
-/

import MiniLogicKernel.Core.Basic
import MiniLogicKernel.Core.Objects

namespace MiniLogicKernel

/-! ## Helper: List Operations -/

/-- Check if all elements of a list satisfy a predicate. -/
def listAll {α : Type} (l : List α) (p : α → Bool) : Bool :=
  match l with
  | [] => true
  | x :: xs => p x && listAll xs p

/-- Check if any element of a list satisfies a predicate. -/
def listAny {α : Type} (l : List α) (p : α → Bool) : Bool :=
  match l with
  | [] => false
  | x :: xs => p x || listAny xs p

/-- Enumerate all 2^n assignments for a list of n distinct atom variables. -/
def allAssignments : List Nat → List (Nat → Bool)
  | []      => [fun _ => false]
  | v :: vs =>
    let rest := allAssignments vs
    let setTrue := rest.map fun σ n => if n = v then true else σ n
    let setFalse := rest.map fun σ n => if n = v then false else σ n
    setTrue ++ setFalse

/-- Check if a formula is a tautology by enumerating all assignments
    for the atoms that appear in it. -/
def checkTautologyBool (f : Formula) : Bool :=
  let vars := f.atoms
  listAll (allAssignments vars) fun σ => f.eval σ == true

/-- Check if a formula is satisfiable by searching all assignments. -/
def checkSatisfiableBool (f : Formula) : Bool :=
  let vars := f.atoms
  listAny (allAssignments vars) fun σ => f.eval σ == true

/-! ## Standard Propositional Tautologies -/

/-- Law of Identity: `A → A` -/
def lawOfIdentity (A : Formula) : Formula := .impl A A

/-- Modus Ponens form: `(A ∧ (A → B)) → B` -/
def modusPonensForm (A B : Formula) : Formula :=
  .impl (.and A (.impl A B)) B

/-- Hypothetical Syllogism: `((A → B) ∧ (B → C)) → (A → C)` -/
def hypotheticalSyllogism (A B C : Formula) : Formula :=
  .impl (.and (.impl A B) (.impl B C)) (.impl A C)

/-- Contraposition: `(A → B) → (¬B → ¬A)` -/
def contrapositionForm (A B : Formula) : Formula :=
  .impl (.impl A B) (.impl (.not B) (.not A))

/-- Excluded Middle: `A ∨ ¬A` -/
def excludedMiddleForm (A : Formula) : Formula := .or A (.not A)

/-- Non-Contradiction: `¬(A ∧ ¬A)` -/
def nonContradictionForm (A : Formula) : Formula := .not (.and A (.not A))

/-- Double Negation Introduction: `A → ¬¬A` -/
def doubleNegIntroForm (A : Formula) : Formula :=
  .impl A (.not (.not A))

/-- Double Negation Elimination: `¬¬A → A` -/
def doubleNegElimForm (A : Formula) : Formula :=
  .impl (.not (.not A)) A

/-- De Morgan (AND): `¬(A ∧ B) → (¬A ∨ ¬B)` -/
def deMorganAndForm (A B : Formula) : Formula :=
  .impl (.not (.and A B)) (.or (.not A) (.not B))

/-- De Morgan (OR): `¬(A ∨ B) → (¬A ∧ ¬B)` -/
def deMorganOrForm (A B : Formula) : Formula :=
  .impl (.not (.or A B)) (.and (.not A) (.not B))

/-- Proof by Cases: `((A → C) ∧ (B → C)) → ((A ∨ B) → C)` -/
def proofByCasesForm (A B C : Formula) : Formula :=
  .impl (.and (.impl A C) (.impl B C)) (.impl (.or A B) C)

/-- Exportation: `((A ∧ B) → C) → (A → (B → C))` -/
def exportationForm (A B C : Formula) : Formula :=
  .impl (.impl (.and A B) C) (.impl A (.impl B C))

/-- Importation: `(A → (B → C)) → ((A ∧ B) → C)` -/
def importationForm (A B C : Formula) : Formula :=
  .impl (.impl A (.impl B C)) (.impl (.and A B) C)

/-- Distributivity of AND over OR: `(A ∧ (B ∨ C)) ↔ ((A ∧ B) ∨ (A ∧ C))` -/
def distribAndOverOr (A B C : Formula) : Formula :=
  .equiv (.and A (.or B C)) (.or (.and A B) (.and A C))

/-- Distributivity of OR over AND: `(A ∨ (B ∧ C)) ↔ ((A ∨ B) ∧ (A ∨ C))` -/
def distribOrOverAnd (A B C : Formula) : Formula :=
  .equiv (.or A (.and B C)) (.and (.or A B) (.or A C))

/-- Pierce's Law: `((A → B) → A) → A` -/
def pierceLaw (A B : Formula) : Formula :=
  .impl (.impl (.impl A B) A) A

/-! ## #eval: Verify Propositional Tautologies -/

def p0 := Formula.atom 0
def p1 := Formula.atom 1
def p2 := Formula.atom 2

#eval checkTautologyBool (lawOfIdentity p0)
#eval checkTautologyBool (modusPonensForm p0 p1)
#eval checkTautologyBool (hypotheticalSyllogism p0 p1 p2)
#eval checkTautologyBool (contrapositionForm p0 p1)
#eval checkTautologyBool (excludedMiddleForm p0)
#eval checkTautologyBool (nonContradictionForm p0)
#eval checkTautologyBool (doubleNegIntroForm p0)
#eval checkTautologyBool (doubleNegElimForm p0)
#eval checkTautologyBool (deMorganAndForm p0 p1)
#eval checkTautologyBool (deMorganOrForm p0 p1)
#eval checkTautologyBool (proofByCasesForm p0 p1 p2)
#eval checkTautologyBool (exportationForm p0 p1 p2)
#eval checkTautologyBool (importationForm p0 p1 p2)
#eval checkTautologyBool (distribAndOverOr p0 p1 p2)
#eval checkTautologyBool (distribOrOverAnd p0 p1 p2)
#eval checkTautologyBool (pierceLaw p0 p1)

/-! ## Peano Axioms as Predicate Formulas -/

/-- The natural numbers as a first-order structure. -/
def natStructure : Structure where
  domain := Nat
  predInterp := fun p args =>
    match p, args with
    | 0, [] => True          -- always-true predicate
    | 1, [x] => x = 0        -- isZero(x)
    | 2, [x, y] => y = x + 1 -- successor(x, y)
    | _, _ => False
  constInterp := fun n => n

/-- Peano Axiom 1: 0 is a natural number (always true in our structure). -/
def peanoAx1 : PredFormula := .pred 0 []

/-- Peano Axiom 2: Every natural number has a successor.
    `∀x ∃y S(x,y)` where S is the binary successor predicate 2. -/
def peanoAx2 : PredFormula :=
  .all (.ex (.pred 2 [0, 1]))

/-- Peano Axiom 3: 0 is not the successor of any number.
    `∀x ¬S(x,0)` — "0 has no predecessor". -/
def peanoAx3 : PredFormula :=
  .all (.not (.pred 2 [0, 0]))

/-- Peano Axiom 4: If numbers have the same successor, they are equal.
    `∀x∀y∀z (S(x,z) ∧ S(y,z) → x=y)` — injectivity of successor. -/
def peanoAx4 : PredFormula :=
  .all (.all (.all (.impl (.and (.pred 2 [0, 2]) (.pred 2 [1, 2])) (.eq 0 1))))

/-- Peano Axiom 5 (Induction Schema): For any property P (predicate 3),
    if P(0) and ∀x∀y (P(x) ∧ S(x,y) → P(y)), then ∀x P(x).
    This is a simplified instance of the full second-order induction axiom. -/
def peanoAx5_instance : PredFormula :=
  .impl (.and (.pred 3 [0]) (.all (.all (.impl (.and (.pred 3 [0]) (.pred 2 [0, 1])) (.pred 3 [1])))))
        (.all (.pred 3 [0]))

/-! ## Dense Linear Order Structure -/

/-- The rational numbers as a dense linear order without endpoints.
    Represented as a first-order structure with order relation `<`.
    We use Nat × Nat with cross-multiplication for rational comparison
    (a1/a2 < b1/b2 iff a1*b2 < b1*a2, restricted to positive denominators). -/
def denseOrderStructure : Structure where
  domain := Nat × Nat
  predInterp := fun p args =>
    match p, args with
    | 0, [] => True
    | 1, [a, b] => a.1 * b.2 < b.1 * a.2  -- rational comparison a1/a2 < b1/b2
    | _, _ => False
  constInterp := fun n => (n, 1)

/-- Irreflexivity: `∀x ¬(x < x)` -/
def orderIrreflexive : PredFormula :=
  .all (.not (.pred 1 [0, 0]))

/-- Transitivity: `∀x∀y∀z (x < y ∧ y < z) → x < z` -/
def orderTransitive : PredFormula :=
  .all (.all (.all (.impl (.and (.pred 1 [0, 1]) (.pred 1 [1, 2])) (.pred 1 [0, 2]))))

/-- Totality: `∀x∀y (x < y ∨ x = y ∨ y < x)` -/
def orderTotal : PredFormula :=
  .all (.all (.or (.pred 1 [0, 1]) (.or (.eq 0 1) (.pred 1 [1, 0]))))

/-- Density: `∀x∀y (x < y → ∃z (x < z ∧ z < y))` -/
def orderDense : PredFormula :=
  .all (.all (.impl (.pred 1 [0, 1]) (.ex (.and (.pred 1 [0, 1]) (.pred 1 [1, 2])))))

/-- No endpoints: `∀x ∃y (x < y) ∧ ∀x ∃y (y < x)` -/
def orderNoEndpoints : PredFormula :=
  .and (.all (.ex (.pred 1 [0, 1]))) (.all (.ex (.pred 1 [1, 0])))

/-! ## #eval: Print and Verify -/

-- Print tautology formulas
#eval lawOfIdentity p0
#eval modusPonensForm p0 p1
#eval modusPonensForm p0 p1 |>.eval (fun n => match n with | 0 => true | _ => false)
#eval excludedMiddleForm p0 |>.eval (fun _ => false)
#eval excludedMiddleForm p0 |>.eval (fun _ => true)

-- Satisfiability checks
#eval checkSatisfiableBool (modusPonensForm p0 p1)
#eval checkSatisfiableBool (.and p0 (.not p0))
#eval checkSatisfiableBool (pierceLaw p0 p1)

-- Test tautologies with larger atom sets
#eval checkTautologyBool (.impl (.and p0 p1) p0)
#eval checkTautologyBool (.impl p0 (.or p0 p1))
#eval checkTautologyBool (.equiv (.not (.and p0 p1)) (.or (.not p0) (.not p1)))

-- Print predicate formulas
#eval peanoAx1
#eval peanoAx2
#eval peanoAx3
#eval peanoAx2.quantifierDepth
#eval peanoAx3.freeTermVars

-- Print order formulas
#eval orderIrreflexive
#eval orderDense
#eval orderDense.quantifierDepth
#eval orderNoEndpoints.quantifierDepth

end MiniLogicKernel
