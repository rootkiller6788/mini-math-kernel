/-
# Benchmark: Consistency Checking

Measures performance of the brute-force consistency checker.
-/

import MiniAxiomKernel

open MiniAxiomKernel

def main : IO Unit := do
  IO.println "══ Benchmark: Consistency Checking ══"
  let start ← IO.monoMsNow
  let sys := AxiomSystem.empty "Consistent" "1.0.0"
    |>.addAxiom (axiomId (Formula.atom 0))
    |>.addAxiom (axiomExcludedMiddle (Formula.atom 0))
  let _ := checkConsistent sys
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"Consistency check (2 small axioms): {elapsed}ms"
