/-
# Regression Tests — MiniAxiomKernel

Run: `lake env lean --run Test/Regression.lean`
-/

import MiniAxiomKernel

open MiniAxiomKernel

#eval "══ MINI-AXIOM-KERNEL REGRESSION TESTS ══"

/-! ## AxiomSet: Empty set has size 0 -/
#eval AxiomSet.empty.size == 0

/-! ## AxiomSet: add increases size by 1 -/
def ax1 := axiomId (Formula.atom 0)
#eval (AxiomSet.empty.add ax1).size == 1

/-! ## AxiomSet: containsName after add -/
#eval (AxiomSet.empty.add ax1).containsName "id" == true

/-! ## AxiomSet: findByName returns some for added axiom -/
#eval ((AxiomSet.empty.add ax1).findByName "id").isSome

/-! ## AxiomSystem: addAxiom preserves name -/
def regSys := AxiomSystem.empty "RegTest" "1.0.0"
  |>.addAxiom ax1
#eval regSys.name == "RegTest"

/-! ## checkConsistent: empty system is consistent -/
#eval checkConsistent (AxiomSystem.empty "Empty" "1.0.0") == true

/-! ## AxiomRegistry: find after register -/
def regReg := AxiomRegistry.empty.register regSys
#eval (regReg.find "RegTest").isSome

/-! ## AxiomRegistry: find nonexistent returns none -/
#eval (regReg.find "Bogus").isNone

#eval "══ ALL MINI-AXIOM-KERNEL REGRESSION TESTS PASSED ══"
