/-
# Example Tests — MiniAxiomKernel

Run: `lake env lean --run Test/Examples.lean`
-/

import MiniAxiomKernel

open MiniAxiomKernel

#eval "══ MINI-AXIOM-KERNEL EXAMPLE TESTS ══"

/-! ## Axiom Construction -/
def testAxiom := Axiom.described "test-ax" (Formula.atom 0) "A test axiom"
#eval testAxiom.name

/-! ## AxiomSet Operations -/
def testSet := AxiomSet.empty
  |>.add (axiomId (Formula.atom 0))
  |>.add (axiomExcludedMiddle (Formula.atom 1))
#eval testSet.size
#eval testSet.containsName "id"
#eval testSet.containsName "nonexistent"

/-! ## AxiomSystem Construction -/
def exampleSys := AxiomSystem.empty "Example" "1.0.0"
  |>.addAxiom (axiomId (Formula.atom 0))
  |>.addAxiom (axiomNonContradiction (Formula.atom 0))
#eval exampleSys.name
#eval exampleSys.axioms.size

/-! ## Registry Operations -/
def reg := AxiomRegistry.empty
  |>.register exampleSys
#eval (reg.find "Example").isSome
#eval (reg.find "Nonexistent").isNone

#eval "══ ALL MINI-AXIOM-KERNEL EXAMPLE TESTS PASSED ══"
