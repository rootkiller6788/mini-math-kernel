/-
# Benchmark: AxiomRegistry Operations

Measures performance of registry registration and lookup.
-/

import MiniAxiomKernel

open MiniAxiomKernel

def main : IO Unit := do
  IO.println "══ Benchmark: AxiomRegistry Operations ══"
  let start ← IO.monoMsNow
  let mut reg := AxiomRegistry.empty
  for i in List.range 100 do
    let sys := AxiomSystem.empty s!"System{i}" "1.0.0"
      |>.addAxiom (axiomId (Formula.atom 0))
    reg := reg.register sys
  let _ := reg.find "System50"
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"Registry 100-system register + lookup: {elapsed}ms"
