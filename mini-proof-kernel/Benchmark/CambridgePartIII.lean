/-
# Benchmark: Cambridge Part III — MiniProofKernel

Cambridge Part III-style benchmark for proof kernel.
-/

import MiniProofKernel

open MiniLogicKernel
open MiniProofKernel

def main : IO Unit := do
  IO.println "══ CAMBRIDGE PART III BENCHMARK ══"
  IO.println "Advanced proof construction benchmark..."

  -- Pierce's law: ((P → Q) → P) → P
  let pierce : ProofTree [] (.impl (.impl (.impl (Formula.atom 0) (Formula.atom 1)) (Formula.atom 0)) (Formula.atom 0)) :=
    .implI (.orE (.lem (a:=Formula.atom 0))
      (.hyp (.head _))
      (.falseE (.notE (.hyp (.head _))
        (.implE (.hyp (.tail _ (.head _)))
          (.orIr (.hyp (.head _)))))))

  IO.println s!"Pierce's Law proof size: {pierce.size}"
  IO.println s!"Valid: {pierce.isValid}"
  IO.println "══ CAMBRIDGE PART III DONE ══"
