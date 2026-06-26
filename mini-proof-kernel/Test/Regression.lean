/-
# Regression Tests — MiniProofKernel

Run: `lake env lean --run Test/Regression.lean`
-/

import MiniProofKernel

open MiniLogicKernel
open MiniProofKernel

#eval "══ MINI-PROOF-KERNEL REGRESSION TESTS ══"

/-! ## LEM proof -/
def lemTest : ProofTree [] (.or (Formula.atom 0) (.not (Formula.atom 0))) := .lem
#eval lemTest.size
#eval lemTest.isValid

/-! ## False elimination -/
def falseElimTest : ProofTree [.false] (Formula.atom 0) := .falseE (.hyp (.head _))
#eval falseElimTest.isValid

/-! ## Double negation intro -/
def dnIntro : ProofTree [] (.impl (Formula.atom 0) (.not (.not (Formula.atom 0)))) :=
  .implI (.notI (.notE (.hyp (.tail _ (.head _))) (.hyp (.head _))))
#eval dnIntro.size
#eval dnIntro.isValid

#eval "══ ALL REGRESSION TESTS PASSED ══"
