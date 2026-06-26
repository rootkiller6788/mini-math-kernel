/-
# Example: Basic Axiom Operations

Demonstrates: building axiom systems, checking consistency,
finding models, and independence analysis.
Run with: lake env lean --run examples/basic.lean
-/

import MiniAxiomKernel

open MiniAxiomKernel

def main : IO Unit := do
  IO.println "===== Basic Axiom Operations ====="

  -- 1. Create an axiom
  let ax1 := Axiom.simple "identity" (.impl (.atom 0) (.atom 0))
  IO.println s!"Created axiom: {ax1}"

  -- 2. Create an axiom set
  let axSet := AxiomSet.empty
    |>.add (axiomId (.atom 0))
    |>.add (axiomExcludedMiddle (.atom 0))
  IO.println s!"Axiom set size: {axSet.size}"
  IO.println s!"Contains id: {axSet.containsName "id"}"
  IO.println s!"Contains lem: {axSet.containsName "lem"}"

  -- 3. Create an axiom system
  let sys := AxiomSystem.empty "MyTheory" "1.0.0"
    |>.addAxiom (axiomId (.atom 0))
    |>.addAxiom (axiomNonContradiction (.atom 0))
    |>.addAxiom (axiomExcludedMiddle (.atom 0))
  IO.println s!"System: {sys}"
  IO.println s!"Number of axioms: {sys.axioms.size}"

  -- 4. Check consistency
  let consistent := sys.checkConsistent
  IO.println s!"System is consistent: {consistent}"

  -- 5. Find a model
  match findModel sys with
  | some model =>
    IO.println "Found model:"
    IO.println s!"  atom 0 = {model 0}"
  | none =>
    IO.println "No model found (may be inconsistent or too many atoms)"

  -- 6. Count models
  match countModels sys with
  | some n => IO.println s!"Number of models: {n}"
  | none => IO.println "Too many atoms to count"

  -- 7. Registry usage
  let reg := AxiomRegistry.empty |>.register sys
  IO.println s!"Registry find MyTheory: {(reg.find "MyTheory").isSome}"
  IO.println s!"Registry find Bogus: {(reg.find "Bogus").isSome}"

  IO.println "===== All basic tests complete ====="