/-
# Benchmark: AxiomSet Operations

Measures performance of AxiomSet add, lookup, and traversal.
-/

import MiniAxiomKernel

open MiniAxiomKernel

def main : IO Unit := do
  IO.println "══ Benchmark: AxiomSet Operations ══"
  let start ← IO.monoMsNow
  let mut s := AxiomSet.empty
  for i in List.range 1000 do
    s := s.add (Axiom.simple s!"ax{i}" (Formula.atom (i % 20)))
  let _ := s.containsName "ax500"
  let _ := s.findByName "ax999"
  let _ := s.statements
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"AxiomSet 1000-element build + query: {elapsed}ms"
