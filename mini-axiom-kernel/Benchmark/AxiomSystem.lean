/-
# Benchmark: AxiomSystem Operations

Measures performance of AxiomSystem construction and management.
-/

import MiniAxiomKernel

open MiniAxiomKernel

def main : IO Unit := do
  IO.println "══ Benchmark: AxiomSystem Operations ══"
  let start ← IO.monoMsNow
  let mut sys := AxiomSystem.empty "Bench" "1.0.0"
  for i in List.range 1000 do
    sys := sys.addAxiom (Axiom.simple s!"ax{i}" (Formula.atom (i % 10)))
  let _ := sys.axioms.size
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"AxiomSystem 1000-axiom build: {elapsed}ms"
