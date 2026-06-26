/-
# Axioms Kernel: Consistency Properties

Defines and analyzes consistency strength, relative consistency,
and equiconsistency of axiom systems.

Provides proper Prop-level lemmas (§ Consistency Theorems) and
computational checks (§ Consistency Classification, § Relative Consistency).
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Constructions.Quotients

namespace MiniAxiomKernel

/-! ## Consistency Theorems (Prop-level)

Fundamental properties of consistency and inconsistency
in propositional axiom systems.
-/

/-- **Inconsistency characterizes trivial entailment**:
    A system is inconsistent iff every formula is a logical consequence. -/
lemma inconsistent_iff_all_consequences (sys : AxiomSystem) :
    isInconsistent sys ↔ ∀ (f : Formula) (assign : Nat → Bool),
      isModel assign sys → f.eval assign = true := by
  constructor
  · intro hIncons f assign hModel
    exfalso; exact hIncons ⟨assign, hModel⟩
  · intro hAll
    intro hCons
    -- Take f = Formula.false (⊥); if ⊥ is true in all models,
    -- then there cannot be any models (since ⊥ is never true)
    have hBot := hAll .false
    -- This gives ∀ assign, isModel assign sys → false = true, which is impossible
    -- So the only way is that there are no assignments satisfying the premise
    rcases hCons with ⟨assign, hModel⟩
    have := hBot assign hModel
    simp [Formula.eval] at this

/-- **Equiconsistency is an equivalence relation** (reflexive). -/
lemma equiconsistent_refl (sys : AxiomSystem) : areEquiconsistent sys sys := by
  unfold areEquiconsistent
  simp [checkConsistencyLE, checkConsistent]

/-- **Equiconsistency is symmetric** (by definition). -/
lemma equiconsistent_symm (sysA sysB : AxiomSystem) (h : areEquiconsistent sysA sysB) :
    areEquiconsistent sysB sysA := by
  unfold areEquiconsistent at h ⊢
  rcases h with ⟨hAB, hBA⟩
  exact ⟨hBA, hAB⟩

/-- **Consistency strength ordering is reflexive (Prop-level)**:
    Every system has at most the consistency strength of itself. -/
lemma consistencyLE_refl (sys : AxiomSystem) : HasConsistencyLE sys sys :=
  { relativeConsistency := fun h => h }

/-- **Consistency strength is transitive**:
    If A ≤ B and B ≤ C in consistency strength, then A ≤ C. -/
lemma consistencyLE_trans (sysA sysB sysC : AxiomSystem)
    (hAB : HasConsistencyLE sysA sysB) (hBC : HasConsistencyLE sysB sysC) :
    HasConsistencyLE sysA sysC :=
  { relativeConsistency := fun h =>
      hAB.relativeConsistency (hBC.relativeConsistency h) }

/-- **Lemma: Adding a true axiom to a consistent system preserves consistency.**
    If ax.statement is true in some model of sys, then sys ∪ {ax} is consistent. -/
lemma consistent_add_true_axiom (sys : AxiomSystem) (ax : Axiom) (assign : Nat → Bool)
    (hModel : isModel assign sys) (hAx : ax.statement.eval assign = true) :
    isConsistent (sys.addAxiom ax) := by
  refine ⟨assign, ?_⟩
  intro ax' hax'
  -- hax' : ax' ∈ (sys.addAxiom ax).axioms.axioms
  have hmem := (mem_addAxiom_iff sys ax ax').mp hax'
  rcases hmem with (h | h)
  · exact hModel ax' h
  · subst h; exact hAx

/-- **Lemma: An axiom system with contradictory axioms is inconsistent.**
    If a system contains both f and ¬f as axioms, it has no models. -/
lemma contradictory_axioms_inconsistent (sys : AxiomSystem) (f : Formula)
    (hF : (Axiom.simple "F" f) ∈ sys.axioms.axioms)
    (hNotF : (Axiom.simple "¬F" (.not f)) ∈ sys.axioms.axioms) :
    isInconsistent sys := by
  intro hCons
  rcases hCons with ⟨assign, hModel⟩
  have hFtrue := hModel (Axiom.simple "F" f) hF
  have hNotFtrue := hModel (Axiom.simple "¬F" (.not f)) hNotF
  simp [Formula.eval] at hFtrue hNotFtrue
  -- Now hFtrue : f.eval assign = true, hNotFtrue : ¬(f.eval assign) = true
  rw [hFtrue] at hNotFtrue; simp at hNotFtrue

/-! ## Consistency Classification

The following provides computational (Bool) classification of
consistency via finite model search. -/

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
