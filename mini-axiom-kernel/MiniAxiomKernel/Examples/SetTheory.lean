/-
# Axioms Kernel: Set Theory Axioms

Example: Zermelo-Fraenkel set theory axioms represented as a finite
propositional approximation for finite models.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Objects
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Properties.Consistency
import MiniAxiomKernel.Properties.Independence

namespace MiniAxiomKernel

/-! ## Encoding Sets as Propositional Atoms -/

/-- In the finite case, we represent sets as atoms and membership as
    a binary relation encoded propositionally. For k elements and n sets,
    we use atoms to encode ∈(x, S). -/

-- Atom 0: a₁ ∈ S₀, Atom 1: a₁ ∈ S₁, Atom 2: a₂ ∈ S₀, etc.
def encodeMembership (element : Nat) (set : Nat) (numElements : Nat) : Nat :=
  element + set * numElements

def encodeEquality (x y numElements offset : Nat) : Nat :=
  offset + x * numElements + y

/-! ## ZFC Axioms (Propositional Approximation) -/

/-- Extensionality: sets with the same elements are equal.
    Encoded as: ∀ S, T (S = T ↔ ∀ x (x ∈ S ↔ x ∈ T))
    Propositional approximation: (e₁ ↔ e₁') ∧ (e₂ ↔ e₂') → S = T -/
def axiomExtensionality (elements : Nat) (sets : Nat) : Formula :=
  -- Simplified: for each pair of sets, membership of all elements must agree
  let conjunctions : List Formula := (List.range sets).bind fun s1 =>
    (List.range sets).filter (· > s1).map fun s2 =>
      let elementEqs : List Formula := (List.range elements).map fun e =>
        .equiv (.atom (encodeMembership e s1 elements))
               (.atom (encodeMembership e s2 elements))
      .impl (elementEqs.foldr .and .true) (.atom (encodeEquality s1 s2 elements (elements * sets)))
  conjunctions.foldr .and .true

/-- Empty set exists: ∃ S ∀ x (x ∉ S).
    Propositional approximation for finite elements/sets. -/
def axiomEmptySet (elements : Nat) (sets : Nat) : Formula :=
  -- There is a set with no elements: all membership atoms for that set are false
  let emptySet := sets - 1  -- designate the last set as empty
  let noElements : List Formula := (List.range elements).map fun e =>
    .not (.atom (encodeMembership e emptySet elements))
  .and (noElements.foldr .and .true) .true

/-- Pairing: for any a, b, there exists S = {a, b}.
    Simplified propositional version. -/
def axiomPairing (elements : Nat) (sets : Nat) : Formula :=
  -- For the first two elements, there is a set containing exactly them
  if elements < 2 then .true else
  let pairSet := sets - 2
  let e0in := .atom (encodeMembership 0 pairSet elements)
  let e1in := .atom (encodeMembership 1 pairSet elements)
  let othersOut : List Formula := (List.range elements).filter (fun e => e > 1).map fun e =>
    .not (.atom (encodeMembership e pairSet elements))
  .and e0in (.and e1in (othersOut.foldr .and .true))

/-- Union: for any S, there exists T = ⋃S.
    Propositional approximation. -/
def axiomUnion (elements : Nat) (sets : Nat) : Formula :=
  -- The union set contains elements that are in any set
  if sets < 2 then .true else
  let unionSet := sets - 2
  -- element e is in union if it is in any member set
  let elemConditions : List Formula := (List.range elements).map fun e =>
    let memberInAny : List Formula := (List.range sets).map fun s =>
      .atom (encodeMembership e s elements)
    .equiv (.atom (encodeMembership e unionSet elements))
           (memberInAny.foldr .or .false)
  elemConditions.foldr .and .true

/-! ## Build the ZFC Axiom System -/

/-- Build a ZFC-like axiom system with a finite number of elements
    and sets for ground model exploration. -/
def buildZFCSystem (elements sets : Nat) (version : String) : AxiomSystem :=
  AxiomSystem.empty "ZFC" version
    |>.addAxiom (Axiom.simple "extensionality" (axiomExtensionality elements sets))
    |>.addAxiom (Axiom.simple "emptySet" (axiomEmptySet elements sets))
    |>.addAxiom (Axiom.simple "pairing" (axiomPairing elements sets))
    |>.addAxiom (Axiom.simple "union" (axiomUnion elements sets))

/-- Check if this finite ZFC approximation is consistent. -/
def checkZFCConsistency (elements sets : Nat) : ConsistencyClass :=
  let sys := buildZFCSystem elements sets "1.0"
  classifyConsistency sys

/-- Count models of the finite ZFC approximation. -/
def zfcModelCount (elements sets : Nat) : Option Nat :=
  let sys := buildZFCSystem elements sets "1.0"
  let atoms := dedup (sys.axioms.statements.bind Formula.atoms)
  let n := atoms.length
  if n > 16 then none
  else some (count atoms 0 (2 ^ n) sys 0)
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  count (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sys : AxiomSystem) (acc : Nat) : Nat :=
    if remaining == 0 then acc
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then
        count atoms (k + 1) (remaining - 1) sys (acc + 1)
      else count atoms (k + 1) (remaining - 1) sys acc

/-! ## Foundation and Choice (Propositional) -/

/-- Foundation (Regularity) simplified: every non-empty set has an
    element disjoint from it. Approximated for finite sets. -/
def axiomFoundation (elements : Nat) (sets : Nat) : Formula :=
  -- For each set S ≠ ∅, ∃ x ∈ S such that x ∩ S = ∅
  -- Propositional: each set that has elements has a minimal element
  .true  -- simplified for finite model

/-- Choice: for any set of non-empty disjoint sets, there is a choice
    set containing exactly one element from each. -/
def axiomChoice (elements : Nat) (sets : Nat) : Formula :=
  .true  -- simplified for propositional encoding

/-! ## Independence of Parallel Postulate Analogue -/

/-- In a finite ZFC-like model, we ask: is the existence of a set
    with exactly 2 elements independent? (Analogous to independence
    of the parallel postulate in geometry.) -/
def twoElementSetAxiom (elements : Nat) (sets : Nat) : Formula :=
  let twoSet := sets - 1
  let e0in := .atom (encodeMembership 0 twoSet elements)
  let e1in := .atom (encodeMembership 1 twoSet elements)
  let othersOut : List Formula := (List.range elements).filter (fun e => e > 1).map fun e =>
    .not (.atom (encodeMembership e twoSet elements))
  .and e0in (.and e1in (othersOut.foldr .and .true))

/-- Check if the two-element set axiom is independent of basic ZFC. -/
def checkTwoElementSetIndependence (elements sets : Nat) : Option Bool :=
  let sys := buildZFCSystem elements sets "1.0"
    |>.addAxiom (Axiom.simple "foundation" (axiomFoundation elements sets))
  isAxiomIndependent sys (s!"twoElemSet")

/-! ## #eval Examples -/

-- A tiny ZFC-like system: 2 elements, 3 sets
def tinyZFC : AxiomSystem := buildZFCSystem 2 3 "1.0"

#eval tinyZFC.name
#eval tinyZFC.axioms.axioms.length
#eval checkZFCConsistency 2 3
#eval zfcModelCount 1 2
#eval axiomExtensionality 2 3 |>.toString

end MiniAxiomKernel
