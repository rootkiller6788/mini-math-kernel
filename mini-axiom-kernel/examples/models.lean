/-
# Example: Model Exploration

Demonstrates model finding, counting, and classification.
Run with: lake env lean --run examples/models.lean
-/

import MiniAxiomKernel

open MiniAxiomKernel

def main : IO Unit := do
  IO.println "===== Model Exploration ====="

  -- 1. Simple consistent system
  let sys1 := AxiomSystem.empty "SimpleSystem" "1.0.0"
    |>.addAxiom (Axiom.simple "impl" (.impl (.atom 0) (.atom 1)))
    |>.addAxiom (Axiom.simple "fact" (.atom 0))

  IO.println s!"System 1: {sys1.name}"
  IO.println s!"  Axioms: {sys1.axioms.size}"
  IO.println s!"  Consistent: {sys1.checkConsistent}"

  -- Count models
  match countModels sys1 with
  | some n => IO.println s!"  Model count: {n}"
  | none => IO.println "  Too many atoms to count"

  -- List models
  let models := findAllModels sys1
  IO.println s!"  All models ({models.length}):"
  for m in models.take 3 do
    IO.println s!"    atom0={m 0}, atom1={m 1}"

  -- 2. System with unique model
  let sys2 := AxiomSystem.empty "CategoricalSys" "1.0.0"
    |>.addAxiom (Axiom.simple "fix0" (.atom 0))
    |>.addAxiom (Axiom.simple "fix1" (.atom 1))

  IO.println s!"System 2: {sys2.name}"
  IO.println s!"  Has unique model: {hasUniqueModel sys2}"
  IO.println s!"  Consistent: {sys2.checkConsistent}"

  -- 3. Inconsistent system
  let sys3 := AxiomSystem.empty "InconsistentSys" "1.0.0"
    |>.addAxiom (Axiom.simple "contra" (.and (.atom 0) (.not (.atom 0))))

  IO.println s!"System 3: {sys3.name}"
  IO.println s!"  Consistent: {sys3.checkConsistent}"
  match findModel sys3 with
  | some _ => IO.println "  Found model (unexpected)"
  | none => IO.println "  No model (as expected)"

  -- 4. Model comparison
  let m1 (n : Nat) : Bool := n == 0
  let m2 (n : Nat) : Bool := n == 0 || n == 1
  IO.println s!"Models agree on [0]: {modelsAgreeOn m1 m2 [0]}"
  IO.println s!"Models agree on [0,1]: {modelsAgreeOn m1 m2 [0, 1]}"

  -- 5. Model with property
  let prop (m : Nat -> Bool) : Bool := m 0 == true && m 1 == false
  match findModelWithProperty sys1 prop with
  | some m =>
    IO.println s!"Found model with P0=true, P1=false: atom0={m 0}, atom1={m 1}"
  | none =>
    IO.println "No model satisfies P0 and not P1"

  IO.println "===== Model exploration complete ====="