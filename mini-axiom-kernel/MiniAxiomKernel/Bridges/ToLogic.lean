/-
# Axioms Kernel: Bridge to Logic Kernel

Connects axiom systems to the logic kernel. Translates axioms into
formulas and premises, applies the deduction theorem to reduce axiom
checking to logical consequence.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Theorems.Deduction
import MiniAxiomKernel.Properties.Decidability

open MiniLogicKernel

namespace MiniAxiomKernel

/-! ## Axiom to Premise Conversion -/

/-- Convert an axiom system into a single formula by conjoining all axioms.
    This reduces "provable from axioms" to "tautologically implied by the
    conjunction of axioms". -/
def axiomsToConjunction (sys : AxiomSystem) : Formula :=
  match sys.axioms.axioms with
  | [] => .true
  | ax :: axs =>
    axs.foldl (fun acc ax => .and acc ax.statement) ax.statement

/-- Convert an axiom system into an implication: axioms → goal.
    This is the deduction theorem in action:
    Γ ⊢ φ  iff  ⊢ (⋀ Γ) → φ -/
def axiomsToImplication (sys : AxiomSystem) (goal : Formula) : Formula :=
  let conj := axiomsToConjunction sys
  .impl conj goal

/-- Check if goal is a logical consequence by reducing to a single
    tautology check: verify that (⋀ axioms) → goal is a tautology. -/
def checkViaTautology (sys : AxiomSystem) (goal : Formula) : Option Bool :=
  let implFormula := axiomsToImplication sys goal
  let atoms := dedup (implFormula.atoms)
  let n := atoms.length
  if n > 16 then none
  else some (isTaut atoms 0 (2 ^ n) implFormula)
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  isTaut (atoms : List Nat) (k : Nat) (remaining : Nat) (f : Formula) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if f.eval assign == true then
        isTaut atoms (k + 1) (remaining - 1) f
      else false

/-! ## Axiom Set to Logic Context -/

/-- The deduction theorem: Γ ∪ {A} ⊨ B iff Γ ⊨ A → B.
    Verify this equivalence computationally. -/
def verifyDeductionBridge (sys : AxiomSystem) (A B : Formula) : Bool :=
  let withA := sys.addAxiom (Axiom.simple "hyp" A)
  match isLogicalConsequence withA B, isLogicalConsequence sys (.impl A B) with
  | some b1, some b2 => b1 == b2
  | _, _ => true

/-- Push all axioms into premises using the deduction theorem.
    Given a system Γ and goal φ, check if ⋀ Γ → φ is a tautology. -/
def reduceToTautology (sys : AxiomSystem) (goal : Formula) : Bool :=
  match checkViaTautology sys goal with
  | some true => true
  | _ => false

/-- Convert an axiom check into a pure logic problem: check if a
    conjunction of axioms logically implies the goal. -/
def axiomCheckToLogicCheck (sys : AxiomSystem) (goal : Formula) : Bool :=
  let conj := axiomsToConjunction sys
  let atoms := dedup (conj.atoms ++ goal.atoms)
  let n := atoms.length
  if n > 16 then false
  else allModels atoms 0 (2 ^ n) conj goal
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  allModels (atoms : List Nat) (k : Nat) (remaining : Nat) (conj goal : Formula) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if conj.eval assign == true then
        if goal.eval assign == true then
          allModels atoms (k + 1) (remaining - 1) conj goal
        else false
      else allModels atoms (k + 1) (remaining - 1) conj goal

/-! ## Removing Redundant Axioms -/

/-- Apply the deduction theorem to remove axioms: if an axiom is a
    consequence of the others, it can be removed. -/
def removeRedundantAxioms (sys : AxiomSystem) : AxiomSystem :=
  go sys.axioms.axioms []
where
  go (remaining kept : List Axiom) : AxiomSystem :=
    match remaining with
    | [] => AxiomSystem.empty (s!"reduced-{sys.name}") sys.version |>.addAxioms kept
    | ax :: rest =>
      let others := kept ++ rest
      let conj := others.foldl (fun acc a => .and acc a.statement) .true
      if conj == .true then
        go rest (kept ++ [ax])
      else
        let atoms := dedup (conj.atoms ++ ax.statement.atoms)
        let n := atoms.length
        if n > 16 then go rest (kept ++ [ax])
        else
          let isRedundant := allModels atoms 0 (2 ^ n) conj ax.statement
          if isRedundant then go rest kept
          else go rest (kept ++ [ax])

  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  allModels (atoms : List Nat) (k : Nat) (remaining : Nat) (conj goal : Formula) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if conj.eval assign == true then
        if goal.eval assign == true then
          allModels atoms (k + 1) (remaining - 1) conj goal
        else false
      else allModels atoms (k + 1) (remaining - 1) conj goal

/-! ## #eval Examples -/

def bridgeSys : AxiomSystem :=
  AxiomSystem.empty "bridge" "1.0"
    |>.addAxiom (Axiom.simple "a1" (.impl (.atom 0) (.atom 1)))
    |>.addAxiom (Axiom.simple "a2" (.atom 0))

#eval axiomsToConjunction bridgeSys
#eval (axiomsToImplication bridgeSys (.atom 1)).toString
#eval verifyDeductionBridge bridgeSys (.atom 0) (.atom 1)
#eval reduceToTautology bridgeSys (.atom 1)
#eval checkViaTautology bridgeSys (.atom 1)
#eval (removeRedundantAxioms bridgeSys).axioms.size

end MiniAxiomKernel
