/-
# Main — MiniAxiomKernel

Entry point that prints package information.
-/

import MiniAxiomKernel

open MiniAxiomKernel

def main : IO Unit := do
  IO.println "══ mini-axiom-kernel ══"
  IO.println "Axiom Kernel for the Mini Math Kernel project."
  IO.println ""
  IO.println "Modules:"
  IO.println "  Core:    Basic, Objects, Laws"
  IO.println "  Morphisms:  Equivalence, Hom, Iso"
  IO.println "  Constructions: Products, Quotients, Subobjects, Universal"
  IO.println "  Properties:   Independence, Completeness, Consistency, Decidability"
  IO.println "  Theorems:     Soundness, Deduction, Compactness, CompletenessTheorem"
  IO.println "  Examples:     Peano, GroupTheory, SetTheory"
  IO.println "  Bridges:      ToLogic, ToProof, ToModel"
  IO.println ""
  IO.println s!"Example: {Axiom.simple "id" (Formula.atom 0)}"
  IO.println s!"Example: {AxiomSet.empty}"
  IO.println s!"Example: {AxiomSystem.empty "Test" "0.1.0"}"
  IO.println ""
  IO.println "══ End of mini-axiom-kernel info ══"
