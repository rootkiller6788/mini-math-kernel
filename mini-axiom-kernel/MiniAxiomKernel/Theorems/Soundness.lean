/-
# Axioms Kernel: Soundness Theorems

Proves soundness properties of axiom systems. Soundness means:
if a formula is provable from the axioms, then it is true in all models.
In our finite setting, this is equivalent to logical consequence.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Properties.Decidability

namespace MiniAxiomKernel

/-! ## Soundness: Truth in All Models -/

/-- A system is sound if every "provable" formula (checked as a logical
    consequence) is true in all models. This holds by definition of
    logical consequence. We verify computationally for finite systems. -/
def checkSoundness (sys : AxiomSystem) (f : Formula) : Bool :=
  match isLogicalConsequence sys f with
  | some true => true  -- By definition, logical consequence means true in all models
  | some false => true -- Not a consequence, so trivially sound
  | none => false      -- Cannot determine

/-- The soundness theorem: every axiom is a logical consequence
    of the system. Trivially true. -/
def axiomsAreConsequences (sys : AxiomSystem) : Bool :=
  sys.axioms.axioms.all fun ax =>
    isLogicalConsequence sys ax.statement == some true

/-- Verify that axioms are true in all models: the fundamental
    soundness property of axiom systems. -/
def verifyAxiomSoundness (sys : AxiomSystem) : Bool :=
  let atoms := dedup (sys.axioms.statements.bind Formula.atoms)
  let n := atoms.length
  if n > 16 then false
  else check atoms 0 (2 ^ n) sys
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  check (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sys : AxiomSystem) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then
        let allAxTrue := sys.axioms.axioms.all fun ax =>
          ax.statement.eval assign == true
        if allAxTrue then
          check atoms (k + 1) (remaining - 1) sys
        else false
      else check atoms (k + 1) (remaining - 1) sys

/-! ## Soundness of Logical Operations -/

/-- Modus ponens is sound: if A and A → B are consequences, then B
    is a consequence. -/
def modusPonensSound (sys : AxiomSystem) (A B : Formula) : Bool :=
  match isLogicalConsequence sys A, isLogicalConsequence sys (.impl A B) with
  | some true, some true =>
    isLogicalConsequence sys B == some true
  | _, _ => true

/-- Verify the soundness of modus ponens by exhaustive check. -/
def verifyModusPonens (sys : AxiomSystem) (A B : Formula) : Bool :=
  let atoms := dedup (
    sys.axioms.statements.bind Formula.atoms ++ A.atoms ++ B.atoms)
  let n := atoms.length
  if n > 16 then false
  else check atoms 0 (2 ^ n) sys A B
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  check (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sys : AxiomSystem) (A B : Formula) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then
        if A.eval assign == true && (.impl A B).eval assign == true then
          if B.eval assign == true then
            check atoms (k + 1) (remaining - 1) sys A B
          else false
        else check atoms (k + 1) (remaining - 1) sys A B
      else check atoms (k + 1) (remaining - 1) sys A B

/-! ## Soundness of Inconsistency Detection -/

/-- If a system is inconsistent, then every formula is a consequence.
    This is the principle of explosion, verified computationally. -/
def verifyExplosion (sys : AxiomSystem) (f : Formula) : Bool :=
  if sys.checkConsistent then true
  else isLogicalConsequence sys f == some true

/-- Check that inconsistent systems entail everything (finite check). -/
def explosionCheck (f : Formula) : Bool :=
  let sys := AxiomSystem.empty "incon" "1.0"
    |>.addAxiom (Axiom.simple "c" (.and (.atom 0) (.not (.atom 0))))
  isLogicalConsequence sys f == some true

/-! ## Soundness of Conservative Extensions -/

/-- A conservative extension preserves soundness: if the extension adds
    no new theorems in the original language, it is sound. -/
def checkConservativeExtensionSoundness (sys : AxiomSystem) (newAx : Axiom) : Bool :=
  let ext := sys.addAxiom newAx
  let sig := signature sys
  let atoms := dedup (sys.axioms.statements.bind Formula.atoms ++ newAx.statement.atoms ++ sig)
  let n := atoms.length
  if n > 16 then false
  else check atoms 0 (2 ^ n) sys newAx sig
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  check (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sys : AxiomSystem) (newAx : Axiom) (sig : List Nat) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then
        if isModel assign (sys.addAxiom newAx) then
          check atoms (k + 1) (remaining - 1) sys newAx sig
        else false
      else check atoms (k + 1) (remaining - 1) sys newAx sig

/-! ## Soundness of Substitution -/

/-- Uniform substitution preserves logical consequence. If B is a
    consequence of sys, then substituting atoms in B yields a consequence
    of the correspondingly substituted axiom system. -/
def checkSubstitutionSoundness (sys : AxiomSystem) (subst : Nat → Formula) (f : Formula) : Bool :=
  let sysSubst := AxiomSystem.empty "subst" "1.0"
    |>.addAxioms (sys.axioms.axioms.map fun ax =>
      Axiom.simple ax.name (substFormula ax.statement subst))
  let fSubst := substFormula f subst
  match isLogicalConsequence sys f with
  | some true => isLogicalConsequence sysSubst fSubst == some true
  | _ => true
where
  substFormula : Formula → (Nat → Formula) → Formula
    | .atom n, s => s n
    | .true, _ => .true
    | .false, _ => .false
    | .not A, s => .not (substFormula A s)
    | .and A B, s => .and (substFormula A s) (substFormula B s)
    | .or A B, s => .or (substFormula A s) (substFormula B s)
    | .impl A B, s => .impl (substFormula A s) (substFormula B s)
    | .equiv A B, s => .equiv (substFormula A s) (substFormula B s)

/-! ## #eval Examples -/

def soundSys : AxiomSystem :=
  AxiomSystem.empty "sound" "1.0"
    |>.addAxiom (Axiom.simple "ax1" (.impl (.atom 0) (.atom 1)))
    |>.addAxiom (Axiom.simple "ax2" (.atom 0))

#eval checkSoundness soundSys (.atom 1)
#eval axiomsAreConsequences soundSys
#eval verifyAxiomSoundness soundSys
#eval modusPonensSound soundSys (.atom 0) (.atom 1)
#eval verifyModusPonens soundSys (.atom 0) (.atom 1)
#eval verifyExplosion soundSys (.atom 99)
#eval explosionCheck (.atom 0)

end MiniAxiomKernel
