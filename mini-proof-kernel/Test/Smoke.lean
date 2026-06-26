/-
# Smoke Tests — MiniProofKernel

Run: `lake env lean --run Test/Smoke.lean`
-/

import MiniProofKernel

open MiniLogicKernel
open MiniProofKernel

#eval "══ MINI-PROOF-KERNEL SMOKE TESTS ══"

/-! ## Core.Basic: ProofTree -/
def ctx1 : Context := [Formula.atom 0]
def simpleHyp : ProofTree ctx1 (Formula.atom 0) := .hyp (.head _)
#eval simpleHyp.conclusion
#eval simpleHyp.isValid

/-! ## Morphisms.Equivalence: Natural Deduction -/
def idProof : ProofTree [] (.impl (Formula.atom 0) (Formula.atom 0)) :=
  .implI (.hyp (.head _))
#eval idProof.isValid

#eval "══ ALL MINI-PROOF-KERNEL SMOKE TESTS PASSED ══"
