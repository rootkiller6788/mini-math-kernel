/-
# Benchmark: Princeton — MiniProofKernel

Princeton-style benchmark for proof kernel operations.
-/

import MiniProofKernel

open MiniLogicKernel
open MiniProofKernel

def main : IO Unit := do
  IO.println "══ PRINCETON BENCHMARK ══"
  IO.println "Natural deduction proof construction benchmark..."

  let p : ProofTree [] (.impl (.impl (Formula.atom 0) (Formula.atom 1))
                              (.impl (.impl (Formula.atom 1) (Formula.atom 2))
                                     (.impl (Formula.atom 0) (Formula.atom 2)))) :=
    .implI (.implI (.implI (.implE (.hyp (.tail _ (.tail _ (.head _)))) (.implE (.hyp (.tail _ (.head _))) (.hyp (.head _))))))

  IO.println s!"Proof size: {p.size}"
  IO.println s!"Proof valid: {p.isValid}"
  IO.println "══ PRINCETON DONE ══"
