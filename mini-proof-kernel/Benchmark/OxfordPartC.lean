/-
# Benchmark: Oxford Part C — MiniProofKernel

Oxford Part C-style benchmark for proof kernel operations.
-/

import MiniProofKernel

open MiniLogicKernel
open MiniProofKernel

def main : IO Unit := do
  IO.println "══ OXFORD PART C BENCHMARK ══"
  IO.println "Classical reasoning benchmark..."

  -- Double negation elimination via LEM
  let dneg : ProofTree [.not (.not (Formula.atom 0))] (Formula.atom 0) :=
    .orE (.lem (a:=Formula.atom 0))
      (.hyp (.head _))
      (.falseE (.notE (.hyp (.tail _ (.head _))) (.hyp (.head _))))

  IO.println s!"Double negation proof size: {dneg.size}"
  IO.println s!"Valid: {dneg.isValid}"

  -- Context size
  IO.println s!"Context size: {dneg.context.length}"

  IO.println "══ OXFORD PART C DONE ══"
