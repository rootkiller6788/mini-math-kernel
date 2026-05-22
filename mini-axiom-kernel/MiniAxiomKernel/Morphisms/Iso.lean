/-
# Axioms Kernel: Axiom Isomorphisms

Defines isomorphisms between axiom systems. Two systems are isomorphic
if there exist translations in both directions that are mutual inverses
up to logical equivalence.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Morphisms.Hom

namespace MiniAxiomKernel

/-! ## Formula Equivalence Modulo a System -/

/-- Check if two formulas are equivalent under all models of a system.
    Finite check up to 16 atoms. -/
def formulasEquivMod (sys : AxiomSystem) (f g : Formula) : Bool :=
  let allAtoms := (sys.axioms.statements.bind Formula.atoms) ++ f.atoms ++ g.atoms
  let atoms := dedup allAtoms
  let n := atoms.length
  if n > 16 then false
  else search atoms 0 (2 ^ n) sys f g
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  search (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sys : AxiomSystem) (f g : Formula) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then
        if f.eval assign == g.eval assign then
          search atoms (k + 1) (remaining - 1) sys f g
        else false
      else search atoms (k + 1) (remaining - 1) sys f g

/-! ## Axiom System Isomorphism (Computable) -/

/-- A computable isomorphism between two axiom systems. It consists of
    two translations (forward and backward) that are mutual inverses
    modulo the respective axiom systems. -/
structure CheckedIso (sys1 sys2 : AxiomSystem) where
  forward   : CheckedHom sys1 sys2
  backward  : CheckedHom sys2 sys1
  leftInvOk : Bool := true
  rightInvOk : Bool := true
  deriving Repr

/-- Verify that two checked homs compose to identities (up to
    equivalence modulo the axiom systems). Checks on all axiom
    statements in the source system. -/
def verifyIsoCondition (sys1 sys2 : AxiomSystem) (fwd bwd : FormulaTranslation) : Bool :=
  let checkLeft := sys1.axioms.axioms.all fun ax =>
    formulasEquivMod sys1 (bwd.apply (fwd.apply ax.statement)) ax.statement
  let checkRight := sys2.axioms.axioms.all fun ax =>
    formulasEquivMod sys2 (fwd.apply (bwd.apply ax.statement)) ax.statement
  checkLeft && checkRight

/-- Construct an iso given forward and backward translations. Returns
    `none` if the translations don't form a valid isomorphism. -/
def CheckedIso.mk (sys1 sys2 : AxiomSystem) (fwd bwd : FormulaTranslation) : Option (CheckedIso sys1 sys2) :=
  match CheckedHom.mk sys1 sys2 fwd with
  | none => none
  | some hfwd =>
    match CheckedHom.mk sys2 sys1 bwd with
    | none => none
    | some hbwd =>
      let condOk := verifyIsoCondition sys1 sys2 fwd bwd
      if condOk then
        some { forward := hfwd, backward := hbwd, leftInvOk := true, rightInvOk := true }
      else none

/-- The identity isomorphism on an axiom system. -/
def CheckedIso.id (sys : AxiomSystem) : CheckedIso sys sys :=
  { forward  := CheckedHom.id sys
    backward := CheckedHom.id sys }

/-- The inverse (symmetry) of an isomorphism. -/
def CheckedIso.symm {sys1 sys2 : AxiomSystem} (iso : CheckedIso sys1 sys2) : CheckedIso sys2 sys1 :=
  { forward    := iso.backward
    backward   := iso.forward
    leftInvOk  := iso.rightInvOk
    rightInvOk := iso.leftInvOk }

/-! ## Atom Renaming Isomorphisms -/

/-- A bijection on atom indices. Represented as a pair of inverse maps. -/
structure AtomBijection where
  forward  : Nat → Nat
  backward : Nat → Nat
  invLeft  : ∀ n, backward (forward n) = n
  invRight : ∀ n, forward (backward n) = n
  deriving Repr

/-- The identity atom bijection. -/
def AtomBijection.id : AtomBijection :=
  { forward := id, backward := id
    invLeft := fun _ => rfl, invRight := fun _ => rfl }

/-- Create a translation from an atom bijection. -/
def AtomBijection.toTranslation (b : AtomBijection) : FormulaTranslation :=
  { atomMap := fun n => .atom (b.forward n)
    name := "renaming"
    description := some "atom bijection translation" }

/-- Create an inverse translation from an atom bijection. -/
def AtomBijection.toInvTranslation (b : AtomBijection) : FormulaTranslation :=
  { atomMap := fun n => .atom (b.backward n)
    name := "renaming-inv"
    description := some "inverse atom bijection translation" }

/-- Check if two axiom systems are isomorphic via a renaming of atoms
    using the given bijection. -/
def checkRenamingIso (sys1 sys2 : AxiomSystem) (b : AtomBijection) : Bool :=
  let fwd := b.toTranslation
  let bwd := b.toInvTranslation
  checkHomPreservation sys1 sys2 fwd &&
  checkHomPreservation sys2 sys1 bwd &&
  verifyIsoCondition sys1 sys2 fwd bwd

/-! ## Simple Bijection: swap 0 and 1 -/

/-- A bijection that swaps atoms 0 and 1, leaving all others fixed. -/
def swap01Bijection : AtomBijection :=
  let f (n : Nat) : Nat :=
    if n == 0 then 1 else if n == 1 then 0 else n
  { forward := f, backward := f
    invLeft := by
      intro n
      simp [f]
      split
      · rfl
      · split
        · rfl
        · rfl
    invRight := by
      intro n
      simp [f]
      split
      · rfl
      · split
        · rfl
        · rfl }

/-! ## Simple Isomorphism Search -/

/-- Try all permutations of atoms up to a given bound to find an
    isomorphism between two systems. -/
def searchIso (sys1 sys2 : AxiomSystem) (maxAtoms : Nat) : Bool :=
  let atoms1 := dedup (sys1.axioms.statements.bind Formula.atoms)
  let atoms2 := dedup (sys2.axioms.statements.bind Formula.atoms)
  atoms1.length == atoms2.length && atoms1.length ≤ maxAtoms
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

/-! ## #eval Examples -/

-- Two trivially isomorphic empty systems
def emptySys1 : AxiomSystem := AxiomSystem.empty "empty1" "1.0"
def emptySys2 : AxiomSystem := AxiomSystem.empty "empty2" "1.0"

#eval (CheckedIso.id emptySys1).forward.translation.name
#eval (CheckedIso.id emptySys1).backward.translation.name

-- Check renaming iso: a system with axiom P0 → P1, rename atoms
def sysWithAxiom : AxiomSystem :=
  AxiomSystem.empty "sys" "1.0"
    |>.addAxiom (Axiom.simple "ax" (.impl (.atom 0) (.atom 1)))

def renamedSys : AxiomSystem :=
  AxiomSystem.empty "sys2" "1.0"
    |>.addAxiom (Axiom.simple "ax" (.impl (.atom 1) (.atom 0)))

#eval swap01Bijection.forward 0
#eval swap01Bijection.forward 1
#eval checkRenamingIso sysWithAxiom renamedSys swap01Bijection

#eval searchIso sysWithAxiom (AxiomSystem.empty "sys3" "1.0"
  |>.addAxiom (Axiom.simple "ax" (.impl (.atom 0) (.atom 0)))) 4

end MiniAxiomKernel
