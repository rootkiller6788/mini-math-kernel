/-
# Axioms Kernel: Consistency Properties

Defines and analyzes consistency strength, relative consistency,
and equiconsistency of axiom systems.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Constructions.Quotients

namespace MiniAxiomKernel

/-! ## Consistency Classification -/

/-- A consistency classification for an axiom system. -/
inductive ConsistencyClass
  | consistent
  | inconsistent
  | unknown  -- too many atoms to decide
  deriving Repr, DecidableEq

instance : ToString ConsistencyClass where
  toString
    | .consistent => "consistent"
    | .inconsistent => "inconsistent"
    | .unknown => "unknown"

/-- Classify the consistency of an axiom system by brute-force search
    (up to 16 atoms). -/
def classifyConsistency (sys : AxiomSystem) : ConsistencyClass :=
  let atoms := dedup (sys.axioms.statements.bind Formula.atoms)
  let n := atoms.length
  if n > 16 then .unknown
  else if sys.checkConsistent then .consistent
  else .inconsistent
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

/-! ## Consistency Strength Ordering -/

/-- System A has at most the consistency strength of system B if the
    consistency of B implies the consistency of A. This is a relative
    consistency notion. -/
structure HasConsistencyLE (sysA sysB : AxiomSystem) where
  relativeConsistency : isConsistent sysB → isConsistent sysA
  deriving Repr

/-- Compute a finite approximation: if every model of B is also a model
    of A (up to the shared atoms), then A has at most the strength of B.
    This is the interpretation ordering. -/
def checkConsistencyLE (sysA sysB : AxiomSystem) : Bool :=
  let sharedAtoms := dedup (
    (sysA.axioms.statements.bind Formula.atoms) ++
    (sysB.axioms.statements.bind Formula.atoms))
  let n := sharedAtoms.length
  if n > 16 then false
  else search sharedAtoms 0 (2 ^ n) sysA sysB
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  search (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sysA sysB : AxiomSystem) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      -- If B has a model, A must also have a model
      if isModel assign sysB then
        if isModel assign sysA then
          search atoms (k + 1) (remaining - 1) sysA sysB
        else false
      else search atoms (k + 1) (remaining - 1) sysA sysB

/-! ## Equiconsistency -/

/-- Two systems are equiconsistent if each is consistent relative to
    the other. -/
def areEquiconsistent (sysA sysB : AxiomSystem) : Bool :=
  checkConsistencyLE sysA sysB && checkConsistencyLE sysB sysA

/-- Compute the consistency strength as a natural number: the number
    of models over the shared atoms. More models = weaker system. -/
def consistencyStrength (sys : AxiomSystem) : Option Nat :=
  let atoms := dedup (sys.axioms.statements.bind Formula.atoms)
  let n := atoms.length
  if n > 16 then none
  else some (countModels atoms 0 (2 ^ n) sys 0)
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  countModels (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sys : AxiomSystem) (acc : Nat) : Nat :=
    if remaining == 0 then acc
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then
        countModels atoms (k + 1) (remaining - 1) sys (acc + 1)
      else countModels atoms (k + 1) (remaining - 1) sys acc

/-! ## Minimal Inconsistent Subsystem -/

/-- Find a minimal subset of axioms that is already inconsistent.
    Uses a simple greedy algorithm: try removing each axiom. -/
def findMinimalInconsistentSubset (sys : AxiomSystem) : List Axiom :=
  if sys.checkConsistent then []
  else greedyMinimize sys.axioms.axioms [] sys.axioms.axioms
where
  greedyMinimize (remaining candidates current : List Axiom) : List Axiom :=
    match remaining with
    | [] => current
    | ax :: rest =>
      let withoutAx := current.filter (·.name != ax.name)
      let testSys := AxiomSystem.empty "test" "1.0" |>.addAxioms withoutAx
      if testSys.checkConsistent then
        greedyMinimize rest candidates current
      else greedyMinimize rest candidates withoutAx

/-! ## Relative Consistency via Translation -/

/-- Interpret system A in system B: if B is consistent then A is
    consistent. This checks via a translation. -/
def checkRelativeConsistency (sysA sysB : AxiomSystem) (t : FormulaTranslation) : Bool :=
  let atoms := dedup (
    (sysA.axioms.statements.bind Formula.atoms) ++
    (sysB.axioms.statements.bind Formula.atoms) ++
    (sysA.axioms.statements.map (t.apply ·)).bind Formula.atoms)
  let n := atoms.length
  if n > 16 then false
  else search atoms 0 (2 ^ n) sysA sysB t
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  search (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sysA sysB : AxiomSystem) (t : FormulaTranslation) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sysB then
        let translatedOk := sysA.axioms.axioms.all fun ax =>
          (t.apply ax.statement).eval assign == true
        if translatedOk then
          search atoms (k + 1) (remaining - 1) sysA sysB t
        else false
      else search atoms (k + 1) (remaining - 1) sysA sysB t

/-! ## #eval Examples -/

def consSys : AxiomSystem :=
  AxiomSystem.empty "cons" "1.0"
    |>.addAxiom (Axiom.simple "ax1" (.impl (.atom 0) (.atom 1)))
    |>.addAxiom (Axiom.simple "ax2" (.atom 0))

#eval classifyConsistency consSys
#eval consistencyStrength consSys
#eval checkConsistencyLE emptySystem consSys
#eval areEquiconsistent consSys consSys
#eval (findMinimalInconsistentSubset (makeInconsistent consSys (.atom 1))).length

end MiniAxiomKernel
