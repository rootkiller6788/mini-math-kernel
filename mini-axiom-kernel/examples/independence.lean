/-
# Example: Independence Analysis

Demonstrates axiom independence checking and classification.
Run with: lake env lean --run examples/independence.lean
-/

import MiniAxiomKernel

open MiniAxiomKernel

def main : IO Unit := do
  IO.println "===== Axiom Independence Analysis ====="

  -- Build a system where axioms are clearly independent
  let sys := AxiomSystem.empty "IndepTest" "1.0.0"
    |>.addAxiom (Axiom.simple "ax1" (.impl (.atom 0) (.atom 1)))
    |>.addAxiom (Axiom.simple "ax2" (.atom 0))
    |>.addAxiom (Axiom.simple "ax3" (.atom 1))

  IO.println s!"System has {sys.axioms.size} axioms"

  -- Check each axiom's independence
  for ax in sys.axioms.axioms do
    let status := classifyIndependence sys ax.name
    IO.println s!"  {ax.name}: {status}"

  -- Check if the system is irredundant
  let irredundant := isIrredundant sys
  IO.println s!"System is irredundant: {irredundant}"

  -- Count independent axioms
  let indepCount := countIndependentAxioms sys
  IO.println s!"Independent axiom count: {indepCount} / {sys.axioms.size}"

  -- Build a system with redundant axioms
  let redSys := AxiomSystem.empty "RedundantTest" "1.0.0"
    |>.addAxiom (Axiom.simple "ax1" (.impl (.atom 0) (.atom 1)))
    |>.addAxiom (Axiom.simple "ax2" (.atom 0))
    |>.addAxiom (Axiom.simple "ax3" (.atom 1))
    |>.addAxiom (Axiom.simple "ax4" (.impl (.atom 0) (.atom 1)))

  IO.println s!"Redundant system has {redSys.axioms.size} axioms"
  for ax in redSys.axioms.axioms do
    let status := classifyIndependence redSys ax.name
    IO.println s!"  {ax.name}: {status}"

  -- Try to find independence witness
  match findIndependenceWitness sys "ax1" with
  | some witness =>
    IO.println "Found countermodel for ax1:"
    IO.println s!"  atom 0 = {witness 0}"
    IO.println s!"  atom 1 = {witness 1}"
  | none =>
    IO.println "No countermodel found for ax1"

  IO.println "===== Independence analysis complete ====="