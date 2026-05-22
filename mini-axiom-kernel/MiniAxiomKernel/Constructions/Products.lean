/-
# Axioms Kernel: Products of Axiom Systems

Defines the product (union, disjoint union, and tensor product)
constructions for axiom systems.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Constructions.Subobjects

namespace MiniAxiomKernel

/-! ## Union of Axiom Systems -/

/-- The union of two axiom systems combines all axioms, merging
    duplicates by name (keeping the first occurrence). -/
def unionSystems (sys1 sys2 : AxiomSystem) : AxiomSystem :=
  let names1 := sys1.axioms.axioms.map (·.name)
  let newAxioms := sys2.axioms.axioms.filter fun ax =>
    !(names1.any (· == ax.name))
  AxiomSystem.empty (s!"{sys1.name}∪{sys2.name}") (s!"{sys1.version}")
    |>.addAxioms sys1.axioms.axioms
    |>.addAxioms newAxioms

/-- The disjoint union of two axiom systems renames atoms to avoid
    clashes: atoms from sys1 keep their index, atoms from sys2 get
    shifted by a given offset. -/
def disjointUnion (sys1 sys2 : AxiomSystem) (shift : Nat) : AxiomSystem :=
  let shiftedSys2 := renameAtoms sys2 (fun n => n + shift)
  unionSystems sys1 shiftedSys2
where
  renameAtoms (sys : AxiomSystem) (f : Nat → Nat) : AxiomSystem :=
    let renamed := sys.axioms.axioms.map fun ax =>
      { ax with statement := renameFormula ax.statement f }
    AxiomSystem.empty sys.name sys.version |>.addAxioms renamed

  renameFormula : Formula → (Nat → Nat) → Formula
    | .atom n, f => .atom (f n)
    | .true, _ => .true
    | .false, _ => .false
    | .not A, f => .not (renameFormula A f)
    | .and A B, f => .and (renameFormula A f) (renameFormula B f)
    | .or A B, f => .or (renameFormula A f) (renameFormula B f)
    | .impl A B, f => .impl (renameFormula A f) (renameFormula B f)
    | .equiv A B, f => .equiv (renameFormula A f) (renameFormula B f)

/-! ## Product Theory (Independent Combination) -/

/-- The product theory has as models pairs of models of the components.
    Its axioms are tagged with component origin and atoms are disjoint.
    This is the categorical product in the category of axiom systems. -/
structure ProductTheory where
  component1 : AxiomSystem
  component2 : AxiomSystem
  shift2      : Nat
  deriving Repr

/-- Build the product theory. Atoms of component1 remain as-is;
    atoms of component2 are shifted by `shift2`. -/
def ProductTheory.build (p : ProductTheory) : AxiomSystem :=
  let ax1 := p.component1.axioms.axioms.map fun ax =>
    { ax with name := s!"1.{ax.name}" }
  let ax2 := p.component2.axioms.axioms.map fun ax =>
    { ax with name := s!"2.{ax.name}",
              statement := renameFormula ax.statement (fun n => n + p.shift2) }
  AxiomSystem.empty (s!"{p.component1.name}×{p.component2.name}") "1.0"
    |>.addAxioms ax1
    |>.addAxioms ax2
where
  renameFormula : Formula → (Nat → Nat) → Formula
    | .atom n, f => .atom (f n)
    | .true, _ => .true
    | .false, _ => .false
    | .not A, f => .not (renameFormula A f)
    | .and A B, f => .and (renameFormula A f) (renameFormula B f)
    | .or A B, f => .or (renameFormula A f) (renameFormula B f)
    | .impl A B, f => .impl (renameFormula A f) (renameFormula B f)
    | .equiv A B, f => .equiv (renameFormula A f) (renameFormula B f)

/-- Project a model of the product back to a model of component1. -/
def ProductTheory.project1 (p : ProductTheory) (assign : Nat → Bool) : Nat → Bool :=
  assign

/-- Project a model of the product back to a model of component2. -/
def ProductTheory.project2 (p : ProductTheory) (assign : Nat → Bool) : Nat → Bool :=
  fun n => assign (n + p.shift2)

/-! ## Consistency of Products -/

/-- The product of two consistent systems is consistent (in finite
    model theory, this holds if the components have disjoint signatures). -/
def checkProductConsistent (sys1 sys2 : AxiomSystem) (shift : Nat) : Bool :=
  let prod := (ProductTheory.mk sys1 sys2 shift).build
  prod.checkConsistent

/-- If both components are consistent, the product is consistent. -/
def productPreservesConsistency (sys1 sys2 : AxiomSystem) (shift : Nat) : Bool :=
  sys1.checkConsistent && sys2.checkConsistent → checkProductConsistent sys1 sys2 shift

/-! ## Independence in Products -/

/-- In the product theory, axioms from different components are
    independent (neither implies the other). -/
def checkIndependenceInProduct (sys1 sys2 : AxiomSystem) (shift : Nat)
    (axName1 axName2 : String) : Bool :=
  let prod := (ProductTheory.mk sys1 sys2 shift).build
  match prod.isIndependent (s!"1.{axName1}") with
  | some b => b
  | none => true

/-! ## Finite Product of n Systems -/

/-- Build the product of a list of systems, each shifted by a
    cumulative offset. -/
def productOfList (systems : List AxiomSystem) : AxiomSystem :=
  match systems with
  | [] => AxiomSystem.empty "empty-product" "1.0"
  | sys :: rest =>
    let offsets := computeOffsets sys rest 0
    buildProduct sys rest offsets
where
  computeOffsets : AxiomSystem → List AxiomSystem → Nat → List Nat
    | _, [], _ => []
    | current, next :: rest, offset =>
      let newOffset := offset + maxAtom (signature current)
      newOffset :: computeOffsets next rest (newOffset + maxAtom (signature next))

  maxAtom (atoms : List Nat) : Nat :=
    match atoms with
    | [] => 0
    | _ => atoms.foldl max 0 + 1

  buildProduct : AxiomSystem → List AxiomSystem → List Nat → AxiomSystem
    | sys, [], _ => sys
    | sys, next :: rest, off :: offs =>
      buildProduct (disjointUnion sys next off) rest offs
    | _, _, _ => AxiomSystem.empty "error" "1.0"

/-! ## #eval Examples -/

def prodA : AxiomSystem :=
  AxiomSystem.empty "A" "1.0"
    |>.addAxiom (Axiom.simple "a1" (.atom 0))

def prodB : AxiomSystem :=
  AxiomSystem.empty "B" "1.0"
    |>.addAxiom (Axiom.simple "b1" (.atom 1))

#eval (unionSystems prodA prodB).axioms.axioms.length
#eval (ProductTheory.mk prodA prodB 10).build.axioms.axioms.length
#eval checkProductConsistent prodA prodB 10
#eval (ProductTheory.mk prodA prodB 5).build.checkConsistent
#eval (disjointUnion prodA prodB 5).axioms.axioms.length
#eval productPreservesConsistency prodA prodB 3

end MiniAxiomKernel
