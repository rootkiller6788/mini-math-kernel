/-
# Example Tests — MiniProofKernel

Run: `lake env lean --run Test/Examples.lean`
-/

import MiniProofKernel

open MiniLogicKernel
open MiniProofKernel

#eval "══ MINI-PROOF-KERNEL EXAMPLE TESTS ══"

/-! ## Simple implication proof -/
def implRefl : ProofTree [] (.impl (Formula.atom 0) (Formula.atom 0)) :=
  .implI (.hyp (.head _))
#eval implRefl.size
#eval implRefl.isValid

/-! ## Simple conjunction proof -/
def conjProof : ProofTree [Formula.atom 0, Formula.atom 1] (.and (Formula.atom 0) (Formula.atom 1)) :=
  .andI (.hyp (.head _)) (.hyp (.tail _ (.head _)))
#eval conjProof.conclusion
#eval conjProof.isValid

/-! ## Weakening test -/
def weakened : ProofTree [Formula.atom 2] (.impl (Formula.atom 0) (Formula.atom 0)) :=
  implRefl.weaken (fun _ _ => .tail _ (.head _))
#eval weakened.isValid

#eval "══ ALL EXAMPLE TESTS PASSED ══"
