/-
# Axioms Kernel: Peano Arithmetic

Defines Peano arithmetic as an AxiomSystem with the standard 7 axioms,
encoded in propositional logic with atoms representing relations.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws

open MiniLogicKernel

namespace MiniAxiomKernel

/-! ## Peano Axioms (Propositional Encoding) -/

/-- We encode Peano arithmetic axioms using a finite domain.
    Atom encoding:
    - Atom 0: "0 exists" (there is a zero element)
    - Atom 1: "every number has a successor"
    - Atom 2: "0 is not a successor"
    - Atom 3: "successor is injective"
    - Atom 4: "induction schema (for one predicate)"
    - Atom 5: "addition exists"
    - Atom 6: "multiplication exists" -/

/-- Axiom 1: 0 is a natural number. -/
def peanoAx1 : Axiom := Axiom.simple "PA1-zero" (.atom 0)

/-- Axiom 2: Every natural number has a successor. -/
def peanoAx2 : Axiom := Axiom.simple "PA2-succ" (.impl (.atom 0) (.atom 1))

/-- Axiom 3: 0 is not the successor of any natural number. -/
def peanoAx3 : Axiom := Axiom.simple "PA3-zero-not-succ" (.impl (.atom 1) (.not (.atom 2)))

/-- Axiom 4: If two numbers have the same successor, they are equal.
    Encoded as: successor property implies unique predecessor. -/
def peanoAx4 : Axiom := Axiom.simple "PA4-succ-inj" (.impl (.atom 3) (.atom 1))

/-- Axiom 5: Induction schema (finite approximation for one predicate P).
    If P(0) and P(n) → P(S(n)) for all n, then P holds for all n. -/
def peanoAx5 : Axiom := Axiom.simple "PA5-induction"
  (.impl (.and (.atom 0) (.impl (.atom 0) (.atom 1))) (.atom 4))

/-- Axiom 6: Addition exists and satisfies a + 0 = a. -/
def peanoAx6 : Axiom := Axiom.simple "PA6-add-zero" (.impl (.atom 0) (.atom 5))

/-- Axiom 7: Multiplication exists and satisfies a * 0 = 0. -/
def peanoAx7 : Axiom := Axiom.simple "PA7-mul-zero" (.impl (.atom 0) (.atom 6))

/-! ## Peano Axiom System -/

/-- The full Peano axiom system (finite propositional fragment). -/
def peanoSystem : AxiomSystem :=
  AxiomSystem.empty "Peano" "1.0"
    |>.addAxiom peanoAx1
    |>.addAxiom peanoAx2
    |>.addAxiom peanoAx3
    |>.addAxiom peanoAx4
    |>.addAxiom peanoAx5
    |>.addAxiom peanoAx6
    |>.addAxiom peanoAx7

/-- The list of all Peano axioms for inspection. -/
def peanoAxioms : List Axiom :=
  [peanoAx1, peanoAx2, peanoAx3, peanoAx4, peanoAx5, peanoAx6, peanoAx7]

/-! ## Consistency Analysis -/

/-- Check consistency of the Peano system on the full set of atoms. -/
def checkPeanoConsistency : Bool := peanoSystem.checkConsistent

/-- Check if any Peano axiom is independent of the others. -/
def checkPeanoIndependence (axName : String) : Option Bool :=
  peanoSystem.isIndependent axName

/-- Count models of the Peano system. -/
def countPeanoModels : Option Nat :=
  let allAtoms := peanoSystem.axioms.statements.bind Formula.atoms
  let atoms := dedup allAtoms
  let n := atoms.length
  if n > 16 then none
  else some (countM atoms 0 (2 ^ n) peanoSystem 0)
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  countM (atoms : List Nat) (k : Nat) (remaining : Nat) (sys : AxiomSystem) (acc : Nat) : Nat :=
    if remaining == 0 then acc
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then
        countM atoms (k + 1) (remaining - 1) sys (acc + 1)
      else countM atoms (k + 1) (remaining - 1) sys acc

/-! ## Small Domain Models -/

/-- Check if the Peano axioms have any model on a domain with exactly 1
    element (atom 0 true, all others set accordingly). -/
def checkPeanoOneElementModel : Bool :=
  let assign (_ : Nat) : Bool := true
  isModel assign peanoSystem

/-- Check if there is a model where the only true atom is atom 0. -/
def checkPeanoMinimalModel : Bool :=
  let assign (n : Nat) : Bool := n == 0
  isModel assign peanoSystem

/-! ## #eval Examples -/

#eval peanoSystem.name
#eval peanoSystem.axioms.size
#eval checkPeanoConsistency
#eval peanoAx1.statement
#eval peanoAx5.statement
#eval checkPeanoIndependence "PA1-zero"
#eval countPeanoModels
#eval checkPeanoMinimalModel

end MiniAxiomKernel
