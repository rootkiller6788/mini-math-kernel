/-
# Axioms Kernel: Axiom Homomorphisms

Defines structure-preserving maps (homomorphisms) between axiom systems.
A homomorphism translates formulas from one system to another while
preserving logical structure and axiom validity.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Objects
import MiniAxiomKernel.Core.Laws

namespace MiniAxiomKernel

/-! ## Formula Translation Maps -/

/-- A translation map is a function from formulas to formulas. It is
    defined by an atom-to-formula map extended homomorphically. -/
structure FormulaTranslation where
  atomMap : Nat → Formula
  name    : String
  description : Option String
  deriving Repr, Inhabited

instance : ToString FormulaTranslation where
  toString t := s!"translation {t.name}"

/-- Apply a translation recursively to a formula. -/
def FormulaTranslation.apply (t : FormulaTranslation) : Formula → Formula
  | .atom n => t.atomMap n
  | .true => .true
  | .false => .false
  | .not A => .not (apply t A)
  | .and A B => .and (apply t A) (apply t B)
  | .or A B => .or (apply t A) (apply t B)
  | .impl A B => .impl (apply t A) (apply t B)
  | .equiv A B => .equiv (apply t A) (apply t B)

/-- The identity translation. -/
def FormulaTranslation.id : FormulaTranslation :=
  { atomMap := .atom, name := "id", description := some "identity translation" }

/-- Compose two translations. -/
def FormulaTranslation.comp (t1 t2 : FormulaTranslation) : FormulaTranslation :=
  { atomMap := fun n => t2.apply (t1.atomMap n)
    name := s!"{t1.name}∘{t2.name}"
    description := some s!"composition of {t1.name} and {t2.name}" }

/-- A translation that shifts all atom indices by a constant. -/
def FormulaTranslation.shift (k : Nat) : FormulaTranslation :=
  { atomMap := fun n => .atom (n + k)
    name := s!"shift+{k}"
    description := some s!"shift all atoms by {k}" }

/-- A translation that maps every atom to a fixed formula. -/
def FormulaTranslation.const (f : Formula) : FormulaTranslation :=
  { atomMap := fun _ => f
    name := s!"const({f})"
    description := some "constant translation" }

/-! ## Finite Model Check for Homomorphism Preservation -/

/-- Given two axiom systems and a translation, check (by exhaustive
    search up to 16 atoms) that the translation preserves axiom validity:
    every model of target system makes each translated source axiom true. -/
def checkHomPreservation (source target : AxiomSystem) (t : FormulaTranslation) : Bool :=
  let allAtoms := (source.axioms.statements.bind Formula.atoms)
    ++ (target.axioms.statements.bind Formula.atoms)
    ++ (source.axioms.statements.map (t.apply ·)).bind Formula.atoms
  let atoms := dedup allAtoms
  let n := atoms.length
  if n > 16 then false
  else search atoms 0 (2 ^ n) source target t
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  search (atoms : List Nat) (k : Nat) (remaining : Nat)
      (source target : AxiomSystem) (t : FormulaTranslation) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign target then
        let translatedOk := source.axioms.axioms.all fun ax =>
          (t.apply ax.statement).eval assign == true
        if translatedOk then search atoms (k + 1) (remaining - 1) source target t
        else false
      else search atoms (k + 1) (remaining - 1) source target t

/-! ## Axiom System Homomorphism (Computable) -/

/-- A computable homomorphism record bundles a translation with a
    verification flag indicating that the finite check passed. -/
structure CheckedHom (source target : AxiomSystem) where
  translation : FormulaTranslation
  verified : Bool := true
  deriving Repr

/-- Create a checked hom from a translation, running the verification.
    Returns `none` if the check fails. -/
def CheckedHom.mk (source target : AxiomSystem) (t : FormulaTranslation) : Option (CheckedHom source target) :=
  if checkHomPreservation source target t then
    some { translation := t, verified := true }
  else none

/-- Identity checked hom. Always valid since the identity trivially
    preserves all axioms. -/
def CheckedHom.id (sys : AxiomSystem) : CheckedHom sys sys :=
  { translation := FormulaTranslation.id, verified := true }

/-- Compose two checked homs. Re-verifies the composition. -/
def CheckedHom.comp {sys1 sys2 sys3 : AxiomSystem}
    (h1 : CheckedHom sys1 sys2) (h2 : CheckedHom sys2 sys3) : Option (CheckedHom sys1 sys3) :=
  let t := FormulaTranslation.comp h1.translation h2.translation
  CheckedHom.mk sys1 sys3 t

/-- Check that a translation preserves axioms without constructing
    a CheckedHom. Convenience wrapper. -/
def verifyHom (source target : AxiomSystem) (t : FormulaTranslation) : Bool :=
  checkHomPreservation source target t

/-- The trivial (constant true) hom from any system to any satisfiable
    system. Use with caution: may not preserve structure. -/
def trivialHom (source target : AxiomSystem) : CheckedHom source target :=
  { translation := FormulaTranslation.const .true, verified := false }

/-! ## Conservative Extension Check -/

/-- A new axiom is a conservative extension of a system if every model
    of the original system can be extended to a model of the system with
    the new axiom, without changing the truth of any original formula.
    This performs a finite check (up to 16 atoms). -/
def checkConservativeExtension (sys : AxiomSystem) (newAx : Axiom) : Bool :=
  let allAtoms := (sys.axioms.statements.bind Formula.atoms) ++ newAx.statement.atoms
  let atoms := dedup allAtoms
  let n := atoms.length
  if n > 16 then false
  else search atoms 0 (2 ^ n) sys newAx
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  search (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sys : AxiomSystem) (newAx : Axiom) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then
        if newAx.statement.eval assign == true then
          search atoms (k + 1) (remaining - 1) sys newAx
        else false
      else search atoms (k + 1) (remaining - 1) sys newAx

/-! ## Definitional Extension -/

/-- A definitional extension adds a new axiom of the form `P ↔ φ`
    where `P` is a new atom not appearing in the original system. -/
def isDefinitional (sys : AxiomSystem) (newAx : Axiom) : Bool :=
  let existingAtoms := dedup (sys.axioms.statements.bind Formula.atoms)
  let newAtoms := dedup newAx.statement.atoms
  let freshAtoms := newAtoms.filter (fun a => !(existingAtoms.any (· == a)))
  freshAtoms.length == 1 && checkConservativeExtension sys newAx
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

/-! ## #eval Examples -/

def homExampleSource : AxiomSystem :=
  AxiomSystem.empty "source" "1.0"
    |>.addAxiom (Axiom.simple "A1" (.impl (.atom 0) (.atom 1)))
    |>.addAxiom (Axiom.simple "A2" (.atom 0))

def homExampleTarget : AxiomSystem :=
  AxiomSystem.empty "target" "1.0"
    |>.addAxiom (Axiom.simple "B1" (.impl (.atom 0) (.atom 1)))
    |>.addAxiom (Axiom.simple "B2" (.atom 0))
    |>.addAxiom (Axiom.simple "B3" (.atom 1))

#eval FormulaTranslation.id.name
#eval (FormulaTranslation.id.apply (.impl (.atom 0) (.atom 1))).toString
#eval (FormulaTranslation.shift 2).name
#eval checkHomPreservation homExampleSource homExampleTarget FormulaTranslation.id
#eval (CheckedHom.mk homExampleSource homExampleTarget FormulaTranslation.id).isSome
#eval verifyHom homExampleSource homExampleTarget FormulaTranslation.id

end MiniAxiomKernel
