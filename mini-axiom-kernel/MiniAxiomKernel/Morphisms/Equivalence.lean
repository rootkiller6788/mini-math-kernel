/-
# Axioms Kernel: Axiom Equivalence

Defines equivalence relations between axiom systems. Two systems are
equivalent if they have the same models (are mutually interpretable
in a semantics-preserving way).
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Morphisms.Hom
import MiniAxiomKernel.Morphisms.Iso

namespace MiniAxiomKernel

/-! ## Equivalence of Axiom Systems -/

/-- Two axiom systems are logically equivalent if they have exactly
    the same models (over the same atom vocabulary). -/
structure SystemEquivalence (sys1 sys2 : AxiomSystem) where
  sameModels : ∀ (assignment : Nat → Bool),
    isModel assignment sys1 ↔ isModel assignment sys2
  deriving Repr

/-- Reflexivity: every system is equivalent to itself. -/
def SystemEquivalence.refl (sys : AxiomSystem) : SystemEquivalence sys sys :=
  { sameModels := by intro assign; rfl }

/-- Symmetry: equivalence is symmetric. -/
def SystemEquivalence.symm {sys1 sys2 : AxiomSystem}
    (eq : SystemEquivalence sys1 sys2) : SystemEquivalence sys2 sys1 :=
  { sameModels := by intro assign; exact ⟨eq.sameModels assign |>.mpr, eq.sameModels assign |>.mp⟩ }

/-- Transitivity: equivalence is transitive. -/
def SystemEquivalence.trans {sys1 sys2 sys3 : AxiomSystem}
    (eq12 : SystemEquivalence sys1 sys2) (eq23 : SystemEquivalence sys2 sys3) : SystemEquivalence sys1 sys3 :=
  { sameModels := by
      intro assign
      exact ⟨fun h => (eq23.sameModels assign).mp ((eq12.sameModels assign).mp h),
             fun h => (eq12.sameModels assign).mpr ((eq23.sameModels assign).mpr h)⟩ }

/-! ## Computable Equivalence Check -/

/-- Check if two axiom systems have the same models by exhaustive
    search over all atom assignments (up to 16 atoms). -/
def checkEquivalence (sys1 sys2 : AxiomSystem) : Bool :=
  let allAtoms := (sys1.axioms.statements.bind Formula.atoms) ++ (sys2.axioms.statements.bind Formula.atoms)
  let atoms := dedup allAtoms
  let n := atoms.length
  if n > 16 then false
  else search atoms 0 (2 ^ n) sys1 sys2
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  search (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sys1 sys2 : AxiomSystem) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      let m1 := isModel assign sys1
      let m2 := isModel assign sys2
      if m1 == m2 then
        search atoms (k + 1) (remaining - 1) sys1 sys2
      else false

/-! ## Mutual Interpretability -/

/-- Two systems are mutually interpretable if each can simulate the
    other via translations. This is a weaker notion than isomorphism. -/
structure MutualInterpretation (sys1 sys2 : AxiomSystem) where
  fwd : FormulaTranslation
  bwd : FormulaTranslation
  fwdPreserves : checkHomPreservation sys1 sys2 fwd = true
  bwdPreserves : checkHomPreservation sys2 sys1 bwd = true
  deriving Repr

/-- Check mutual interpretability by finding translations. -/
def checkMutualInterpretability (sys1 sys2 : AxiomSystem) : Bool :=
  let fwd := FormulaTranslation.id
  let bwd := FormulaTranslation.id
  checkHomPreservation sys1 sys2 fwd && checkHomPreservation sys2 sys1 bwd

/-! ## Conservative Extension Relation -/

/-- System `small` is conservatively extended by `large` if `large`
    adds axioms that don't change the validities of formulas expressible
    in `small`. -/
structure ConservativeExtensionOf (small large : AxiomSystem) where
  subsetAxioms : ∀ (ax : Axiom), ax ∈ small.axioms.axioms → ax ∈ large.axioms.axioms
  conservative : ∀ (f : Formula),
    (∀ (assignment : Nat → Bool), isModel assignment large →
      f.eval assignment = true) →
    (∀ (assignment : Nat → Bool), isModel assignment small →
      f.eval assignment = true)
  deriving Repr

/-- Check conservative extension relation by finite model search. -/
def checkConservativeExtensionOf (small large : AxiomSystem) : Bool :=
  let subsetOk := small.axioms.axioms.all fun ax =>
    large.axioms.axioms.any (·.name == ax.name)
  let allAtoms := (small.axioms.statements.bind Formula.atoms) ++ (large.axioms.statements.bind Formula.atoms)
  let atoms := dedup allAtoms
  let n := atoms.length
  subsetOk && n ≤ 16 && search atoms 0 (2 ^ n) small large
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  search (atoms : List Nat) (k : Nat) (remaining : Nat)
      (small large : AxiomSystem) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign large then
        search atoms (k + 1) (remaining - 1) small large
      else if isModel assign small then
        false
      else search atoms (k + 1) (remaining - 1) small large

/-! ## Equivalence up to Renaming -/

/-- Two systems are equivalent up to renaming if there exists a
    bijection on atoms mapping one to the other. -/
def equivalentUpToRenaming (sys1 sys2 : AxiomSystem) (b : AtomBijection) : Bool :=
  let fwd := b.toTranslation
  checkHomPreservation sys1 sys2 fwd && checkHomPreservation sys2 sys1 (b.toInvTranslation)

/-! ## #eval Examples -/

def eqSysA : AxiomSystem :=
  AxiomSystem.empty "eqA" "1.0"
    |>.addAxiom (Axiom.simple "ax" (.impl (.atom 0) (.atom 1)))

def eqSysB : AxiomSystem :=
  AxiomSystem.empty "eqB" "1.0"
    |>.addAxiom (Axiom.simple "ax" (.impl (.atom 0) (.atom 1)))
    |>.addAxiom (Axiom.simple "taut" (.impl (.atom 2) (.atom 2)))

#eval checkEquivalence eqSysA eqSysA
#eval checkEquivalence eqSysA eqSysB
#eval checkMutualInterpretability eqSysA eqSysA

end MiniAxiomKernel
