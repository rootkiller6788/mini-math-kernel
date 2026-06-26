/-
# Axioms Kernel: Independence Properties

Defines and checks axiom independence within axiom systems.
An axiom is independent if it is not provable from the others.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Constructions.Subobjects

namespace MiniAxiomKernel

/-! ## Axiom Independence -/

/-- An axiom is independent of the other axioms in the system if there
    exists a model of all other axioms that falsifies this axiom.
    Computed by finite model search (up to 16 atoms). -/
def isAxiomIndependent (sys : AxiomSystem) (axName : String) : Option Bool :=
  match sys.axioms.findByName axName with
  | none => none
  | some target =>
    let others := sys.axioms.axioms.filter (·.name != axName)
    let atoms := dedup (others.bind (·.statement.atoms) ++ target.statement.atoms)
    let n := atoms.length
    if n > 16 then none
    else some (searchCounterModel atoms 0 (2 ^ n) others target)
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  searchCounterModel (atoms : List Nat) (k : Nat) (remaining : Nat)
      (others : List Axiom) (target : Axiom) : Bool :=
    if remaining == 0 then false
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      let othersOk := others.all fun ax => ax.statement.eval assign == true
      let targetFalse := target.statement.eval assign == false
      if othersOk && targetFalse then true
      else searchCounterModel atoms (k + 1) (remaining - 1) others target

/-! ## Independence Classification -/

/-- The independence status of an axiom in a system. -/
inductive IndependenceStatus
  | independent  -- has a countermodel
  | dependent    -- implied by the others
  | unknown      -- cannot determine (too many atoms)
  | notFound     -- axiom not in system
  deriving Repr, DecidableEq

instance : ToString IndependenceStatus where
  toString
    | .independent => "independent"
    | .dependent => "dependent"
    | .unknown => "unknown"
    | .notFound => "not found"

/-- Classify the independence of an axiom. -/
def classifyIndependence (sys : AxiomSystem) (axName : String) : IndependenceStatus :=
  match isAxiomIndependent sys axName with
  | none => .notFound
  | some true => .independent
  | some false => .dependent

/-- Get the independence status of all axioms in a system. -/
def allIndependenceStatuses (sys : AxiomSystem) : List (String × IndependenceStatus) :=
  sys.axioms.axioms.map fun ax =>
    (ax.name, classifyIndependence sys ax.name)

/-! ## Independence Basis -/

/-- An independence basis is a set of mutually independent axioms.
    Check if a subset of axioms is an independent basis. -/
def isIndependentBasis (sys : AxiomSystem) (basisNames : List String) : Bool :=
  basisNames.all fun name =>
    match classifyIndependence sys name with
    | .independent => true
    | .dependent => false
    | _ => false

/-- Get all independent axioms in the system. -/
def getIndependentAxioms (sys : AxiomSystem) : List Axiom :=
  sys.axioms.axioms.filter fun ax =>
    match classifyIndependence sys ax.name with
    | .independent => true
    | _ => false

/-- Count how many axioms are independent. -/
def countIndependentAxioms (sys : AxiomSystem) : Nat :=
  (getIndependentAxioms sys).length

/-! ## Independence Witness -/

/-- Find a countermodel assignment that witnesses the independence
    of an axiom. -/
def findIndependenceWitness (sys : AxiomSystem) (axName : String) : Option (Nat → Bool) :=
  match sys.axioms.findByName axName with
  | none => none
  | some target =>
    let others := sys.axioms.axioms.filter (·.name != axName)
    let atoms := dedup (others.bind (·.statement.atoms) ++ target.statement.atoms)
    let n := atoms.length
    if n > 16 then none
    else search atoms 0 (2 ^ n) others target
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  search (atoms : List Nat) (k : Nat) (remaining : Nat)
      (others : List Axiom) (target : Axiom) : Option (Nat → Bool) :=
    if remaining == 0 then none
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      let othersOk := others.all fun ax => ax.statement.eval assign == true
      let targetFalse := target.statement.eval assign == false
      if othersOk && targetFalse then some assign
      else search atoms (k + 1) (remaining - 1) others target

/-! ## Independence Preserving Extensions -/

/-- Check if adding an axiom preserves the independence of existing
    axioms. -/
def preservesIndependence (sys : AxiomSystem) (newAx : Axiom) (existingName : String) : Bool :=
  let extended := sys.addAxiom newAx
  match isAxiomIndependent sys existingName with
  | some true => isAxiomIndependent extended existingName == some true
  | _ => true

/-- An axiom system is irredundant (no redundant axioms) if every
    axiom is independent. -/
def isIrredundant (sys : AxiomSystem) : Bool :=
  sys.axioms.axioms.all fun ax =>
    match classifyIndependence sys ax.name with
    | .independent => true
    | _ => false

/-! ## #eval Examples -/

def indSys : AxiomSystem :=
  AxiomSystem.empty "indTest" "1.0"
    |>.addAxiom (Axiom.simple "ax1" (.impl (.atom 0) (.atom 1)))
    |>.addAxiom (Axiom.simple "ax2" (.atom 0))
    |>.addAxiom (Axiom.simple "ax3" (.atom 1))

#eval classifyIndependence indSys "ax1"
#eval classifyIndependence indSys "ax2"
#eval classifyIndependence indSys "ax3"
#eval isIrredundant indSys
#eval countIndependentAxioms indSys
#eval allIndependenceStatuses indSys
#eval (getIndependentAxioms indSys).length

end MiniAxiomKernel
