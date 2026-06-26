/-
# Axioms Kernel: Subobjects of Axiom Systems

Defines sub-axiom-system relations: subtheory, reduct, and restriction.
A subtheory is a subset of axioms; a reduct restricts the language
(signature) of the system.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws

namespace MiniAxiomKernel

/-! ## Subtheory (Subset of Axioms) -/

/-- A subtheory is an axiom system whose axioms are a subset of the
    parent system's axioms. -/
structure Subtheory (parent sub : AxiomSystem) where
  subsetAxioms : ∀ (ax : Axiom), ax ∈ sub.axioms.axioms → ax ∈ parent.axioms.axioms
  deriving Repr

/-- Check if `sub` is a subtheory of `parent` by name comparison. -/
def isSubtheoryOf (parent sub : AxiomSystem) : Bool :=
  sub.axioms.axioms.all fun ax =>
    parent.axioms.axioms.any fun pax => pax.name == ax.name

/-- Create a subtheory by filtering axioms by a predicate. -/
def filterAxioms (sys : AxiomSystem) (p : Axiom → Bool) : AxiomSystem :=
  { sys with axioms := { axioms := sys.axioms.axioms.filter p } }

/-- Create a subtheory by keeping only axioms with names in a list. -/
def restrictToNames (sys : AxiomSystem) (names : List String) : AxiomSystem :=
  filterAxioms sys (fun ax => names.any (· == ax.name))

/-- Remove a single axiom by name, returning the smaller system. -/
def removeAxiom (sys : AxiomSystem) (name : String) : AxiomSystem :=
  filterAxioms sys (fun ax => ax.name != name)

/-! ## Language Reduct (Restricting Atoms) -/

/-- The language (signature) of an axiom system is the set of atoms
    that appear in its axioms. -/
def signature (sys : AxiomSystem) : List Nat :=
  dedup (sys.axioms.statements.bind Formula.atoms)
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

/-- Check if system `small` is a reduct of system `large`, meaning
    its signature is a subset and every model of `large` restricts to
    a model of `small`. -/
def isReductOf (small large : AxiomSystem) : Bool :=
  let sigSmall := signature small
  let sigLarge := signature large
  let sigSubset := sigSmall.all fun a => sigLarge.any (· == a)
  if !sigSubset then false
  else
    let atoms := dedupAll
    let n := atoms.length
    if n > 16 then false
    else search atoms 0 (2 ^ n) small large
where
  dedupAll : List Nat :=
    let raw := (small.axioms.statements.bind Formula.atoms) ++ (large.axioms.statements.bind Formula.atoms)
    dedup' raw

  dedup' : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup' (xs.filter (· != x))

  search (atoms : List Nat) (k : Nat) (remaining : Nat)
      (small large : AxiomSystem) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign large then
        if isModel assign small then
          search atoms (k + 1) (remaining - 1) small large
        else false
      else search atoms (k + 1) (remaining - 1) small large

/-! ## Finite Axiomatizability -/

/-- A system is finitely axiomatizable if it has a finite number of
    axioms (always true for our representation, but we can check if
    the theory generated is finitely axiomatizable). -/
def isFinitelyAxiomatizable (sys : AxiomSystem) : Bool :=
  sys.axioms.axioms.length > 0

/-- The number of axioms. -/
def axiomCount (sys : AxiomSystem) : Nat := sys.axioms.axioms.length

/-- The signature size (number of distinct atoms). -/
def signatureSize (sys : AxiomSystem) : Nat := (signature sys).length

/-! ## Subtheory Lattice Operations -/

/-- Intersection of two subtheories (keep only common axioms by name). -/
def intersectTheories (sys1 sys2 : AxiomSystem) : AxiomSystem :=
  let commonNames := sys1.axioms.axioms.filterMap fun ax =>
    if sys2.axioms.axioms.any (·.name == ax.name) then some ax.name else none
  restrictToNames sys1 commonNames

/-- Union of two subtheories (unique axioms by name). -/
def unionTheories (sys1 sys2 : AxiomSystem) : AxiomSystem :=
  let names2 := sys2.axioms.axioms.map (·.name)
  let filteredFromSys1 := sys1.axioms.axioms.filter fun ax =>
    !(names2.any (· == ax.name))
  AxiomSystem.empty "union" "1.0"
    |>.addAxioms filteredFromSys1
    |>.addAxioms sys2.axioms.axioms

/-! ## #eval Examples -/

def parentSys : AxiomSystem :=
  AxiomSystem.empty "parent" "1.0"
    |>.addAxiom (Axiom.simple "ax1" (.impl (.atom 0) (.atom 1)))
    |>.addAxiom (Axiom.simple "ax2" (.atom 0))
    |>.addAxiom (Axiom.simple "ax3" (.impl (.atom 1) (.atom 2)))

def childSys : AxiomSystem :=
  AxiomSystem.empty "child" "1.0"
    |>.addAxiom (Axiom.simple "ax1" (.impl (.atom 0) (.atom 1)))
    |>.addAxiom (Axiom.simple "ax2" (.atom 0))

#eval isSubtheoryOf parentSys childSys
#eval axiomCount parentSys
#eval signatureSize parentSys
#eval (removeAxiom parentSys "ax2").axioms.axioms.length
#eval isReductOf childSys parentSys
#eval (intersectTheories parentSys childSys).axioms.axioms.length

end MiniAxiomKernel
