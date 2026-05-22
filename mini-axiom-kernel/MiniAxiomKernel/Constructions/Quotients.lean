/-
# Axioms Kernel: Quotients of Axiom Systems

Defines quotient constructions for axiom systems: adding axioms to
strengthen a theory, forming the quotient system.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Constructions.Subobjects

namespace MiniAxiomKernel

/-! ## Quotient by Adding Axioms -/

/-- A quotient system is formed by adding extra axioms to an existing
    system. The new axioms restrict the models to a smaller class. -/
structure QuotientSystem where
  base   : AxiomSystem
  extras : AxiomSet
  name   : String
  deriving Repr, Inhabited

instance : ToString QuotientSystem where
  toString q := s!"Quotient {q.name} ({q.base.name} + {q.extras.axioms.length} axioms)"

/-- Create a quotient system by adding axioms. -/
def QuotientSystem.mk (base : AxiomSystem) (extras : List Axiom) (name : String) : QuotientSystem :=
  { base, extras := AxiomSet.empty.addAll extras, name }

/-- The underlying axiom system of a quotient. -/
def QuotientSystem.toSystem (q : QuotientSystem) : AxiomSystem :=
  { q.base with axioms := q.base.axioms.addAll q.extras.axioms }
    |>.withName q.name
where
  withName (sys : AxiomSystem) (n : String) : AxiomSystem :=
    { sys with name := n }

/-- A quotient is conservative if it adds only redundant axioms. -/
def QuotientSystem.isConservative (q : QuotientSystem) : Bool :=
  let allAtoms := (q.base.axioms.statements.bind Formula.atoms)
    ++ (q.extras.statements.bind Formula.atoms)
  let atoms := dedup allAtoms
  let n := atoms.length
  if n > 16 then false
  else search atoms 0 (2 ^ n) q.base q.extras
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  search (atoms : List Nat) (k : Nat) (remaining : Nat)
      (base : AxiomSystem) (extras : AxiomSet) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign base then
        if isModel assign (AxiomSystem.empty "" "1.0" |>.addAxioms extras.axioms) then
          search atoms (k + 1) (remaining - 1) base extras
        else false
      else search atoms (k + 1) (remaining - 1) base extras

/-! ## Forcing a Contradiction (Inconsistent Quotient) -/

/-- Adding an axiom and its negation forces inconsistency. -/
def makeInconsistent (sys : AxiomSystem) (f : Formula) : AxiomSystem :=
  sys.addAxiom (Axiom.simple "contra-f" f)
    |>.addAxiom (Axiom.simple "contra-notf" (.not f))

/-- Check if a quotient renders the system inconsistent. -/
def QuotientSystem.isInconsistent (q : QuotientSystem) : Bool :=
  not (q.toSystem.checkConsistent)

/-! ## Completing an Axiom System -/

/-- For each formula over the signature, add either it or its negation
    to attempt to form a complete extension. This finite version only
    considers atomic formulas. -/
def completeOverAtoms (sys : AxiomSystem) : AxiomSystem :=
  let sig := signature sys
  let atmAxioms : List Axiom := sig.map fun a =>
    Axiom.simple s!"atom-{a}" (.atom a)
  sys.addAxioms atmAxioms

/-- Check if a system is complete for its signature atoms: for each
    atom, either its truth or its negation is forced. -/
def isCompleteOverAtoms (sys : AxiomSystem) : Bool :=
  let sig := signature sys
  let allAtoms := sig ++ (sys.axioms.statements.bind Formula.atoms)
  let atoms := dedup allAtoms
  let n := atoms.length
  if n > 16 then false
  else sig.all fun a => atomFixed atoms 0 (2 ^ n) sys a
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  atomFixed (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sys : AxiomSystem) (a : Nat) : Bool :=
    if remaining == 0 then false
    else
      let assign (x : Nat) : Bool :=
        match atoms.findIdx? (· == x) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then true
      else
        let assignNeg := fun (x : Nat) => if x == a then !(assign x) else assign x
        if isModel assignNeg sys then true
        else atomFixed atoms (k + 1) (remaining - 1) sys a

/-! ## Adding a Schema (Axiom Scheme Instantiation) -/

/-- Apply an axiom schema: a function from a formula parameter to an
    axiom. This adds all instances of the schema over a finite set of
    formulas derived from atoms. -/
def instantiateSchema (sys : AxiomSystem) (schema : Formula → Axiom) (formulas : List Formula) : AxiomSystem :=
  let newAxioms := formulas.map schema
  sys.addAxioms newAxioms

/-- Generate all atomic and negated-atomic formulas over a signature. -/
def atomicFormulas (atoms : List Nat) : List Formula :=
  atoms.map (.atom ·) ++ atoms.map (.not <| .atom ·)

/-- Add the excluded middle schema for all atoms in the signature. -/
def addExcludedMiddleSchema (sys : AxiomSystem) : AxiomSystem :=
  let sig := signature sys
  let formulas := sig.map (.atom ·)
  instantiateSchema sys (fun f => Axiom.simple s!"LEM-{f}" (.or f (.not f))) formulas

/-! ## #eval Examples -/

def baseSys : AxiomSystem :=
  AxiomSystem.empty "base" "1.0"
    |>.addAxiom (Axiom.simple "ax1" (.impl (.atom 0) (.atom 1)))

#eval baseSys.checkConsistent

def quotientSys : QuotientSystem :=
  QuotientSystem.mk baseSys
    [Axiom.simple "ax2" (.atom 0)]
    "strengthened"

#eval quotientSys.toSystem.checkConsistent
#eval QuotientSystem.isConservative quotientSys
#eval (makeInconsistent baseSys (.atom 0)).checkConsistent
#eval signature baseSys
#eval (addExcludedMiddleSchema baseSys).axioms.axioms.length

end MiniAxiomKernel
