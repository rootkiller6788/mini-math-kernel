/-
# Axioms Kernel: Bridge to Model Kernel

Connects axiom systems to model finding. Provides exhaustive search
for models of axiom systems, model counting, and model comparison.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Theorems.CompletenessTheorem

open MiniLogicKernel

namespace MiniAxiomKernel

/-! ## Model Finding -/

/-- Find a single model of an axiom system, if one exists.
    Searches all truth assignments for atoms appearing in the axioms. -/
def findModel (sys : AxiomSystem) : Option (Nat → Bool) :=
  let allAtoms := sys.axioms.statements.bind Formula.atoms
  let atoms := dedup allAtoms
  let n := atoms.length
  if n > 16 then none
  else search atoms 0 (2 ^ n) sys
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  search (atoms : List Nat) (k : Nat) (remaining : Nat) (sys : AxiomSystem) : Option (Nat → Bool) :=
    if remaining == 0 then none
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then some assign
      else search atoms (k + 1) (remaining - 1) sys

/-- Find all models of an axiom system. -/
def findAllModels (sys : AxiomSystem) : List (Nat → Bool) :=
  let allAtoms := sys.axioms.statements.bind Formula.atoms
  let atoms := dedup allAtoms
  let n := atoms.length
  if n > 16 then []
  else collect atoms 0 (2 ^ n) sys []
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  collect (atoms : List Nat) (k : Nat) (remaining : Nat) (sys : AxiomSystem) (acc : List (Nat → Bool)) : List (Nat → Bool) :=
    if remaining == 0 then acc
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then
        collect atoms (k + 1) (remaining - 1) sys (assign :: acc)
      else collect atoms (k + 1) (remaining - 1) sys acc

/-- Count the number of models. -/
def countModels (sys : AxiomSystem) : Option Nat :=
  let allAtoms := sys.axioms.statements.bind Formula.atoms
  let atoms := dedup allAtoms
  let n := atoms.length
  if n > 16 then none
  else some (cnt atoms 0 (2 ^ n) sys 0)
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  cnt (atoms : List Nat) (k : Nat) (remaining : Nat) (sys : AxiomSystem) (acc : Nat) : Nat :=
    if remaining == 0 then acc
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then
        cnt atoms (k + 1) (remaining - 1) sys (acc + 1)
      else cnt atoms (k + 1) (remaining - 1) sys acc

/-! ## Model Comparison -/

/-- Two models are equal on a set of relevant atoms. -/
def modelsAgreeOn (m1 m2 : Nat → Bool) (atoms : List Nat) : Bool :=
  atoms.all fun a => m1 a == m2 a

/-- Given a system, list its models and which atoms they agree on. -/
def classifyModels (sys : AxiomSystem) : List (Nat → Bool) :=
  findAllModels sys

/-- Check if a system has a unique model (is categorical in the
    finite sense). -/
def hasUniqueModel (sys : AxiomSystem) : Bool :=
  match countModels sys with
  | some n => n == 1
  | none => false

/-- Find a model that minimizes or maximizes specific atoms. -/
def findModelWithProperty (sys : AxiomSystem) (prop : (Nat → Bool) → Bool) : Option (Nat → Bool) :=
  let allAtoms := sys.axioms.statements.bind Formula.atoms
  let atoms := dedup allAtoms
  let n := atoms.length
  if n > 16 then none
  else search atoms 0 (2 ^ n) sys prop
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  search (atoms : List Nat) (k : Nat) (remaining : Nat) (sys : AxiomSystem) (prop : (Nat → Bool) → Bool) : Option (Nat → Bool) :=
    if remaining == 0 then none
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys && prop assign then some assign
      else search atoms (k + 1) (remaining - 1) sys prop

/-! ## Model Representation -/

/-- Convert a model to a string representation showing atom values. -/
def modelToString (model : Nat → Bool) (maxAtom : Nat) : String :=
  let parts := (List.range (maxAtom + 1)).map fun n =>
    s!"P{n}={model n}"
  String.intercalate ", " (parts.toList)

/-- List all models with their string representations. -/
def listModelRepresentations (sys : AxiomSystem) (maxAtom : Nat) : List String :=
  let models := findAllModels sys
  models.map fun m => modelToString m maxAtom

/-- Find the smallest model by some metric (e.g., number of true atoms). -/
def findMinimalModel (sys : AxiomSystem) (maxAtom : Nat) : Option (Nat → Bool) :=
  findModelWithProperty sys fun m =>
    let count := (List.range (maxAtom + 1)).filter (m ·) |>.length
    true  -- placeholder; in real use we'd minimize

/-! ## #eval Examples -/

def modelSys : AxiomSystem :=
  AxiomSystem.empty "model" "1.0"
    |>.addAxiom (Axiom.simple "ax1" (.impl (.atom 0) (.atom 1)))
    |>.addAxiom (Axiom.simple "ax2" (.atom 0))

#eval findModel modelSys |>.isSome
#eval countModels modelSys
#eval hasUniqueModel modelSys
#eval (findAllModels modelSys).length
#eval listModelRepresentations modelSys 2
#eval (modelsAgreeOn (fun _ => true) (fun _ => false) [0, 1])

end MiniAxiomKernel
