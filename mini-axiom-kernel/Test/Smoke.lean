/-
# Smoke Tests — MiniAxiomKernel

Run: `lake env lean --run Test/Smoke.lean`
-/

import MiniAxiomKernel

open MiniAxiomKernel

#eval "══ MINI-AXIOM-KERNEL SMOKE TESTS ══"

/-! ## Core.Basic: Axiom -/
#eval Axiom.simple "test" (Formula.atom 0)
#eval AxiomSet.empty.size

/-! ## Core.Objects: Standard Axioms -/
#eval axiomId (Formula.atom 0)
#eval axiomExcludedMiddle (Formula.atom 0)

/-! ## Core.Laws: AxiomSystem -/
def testSys := AxiomSystem.empty "Test" "0.1.0"
#eval testSys.name
#eval checkConsistent testSys

#eval "══ ALL MINI-AXIOM-KERNEL SMOKE TESTS PASSED ══"
