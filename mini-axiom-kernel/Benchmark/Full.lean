/-
# Benchmark: Full Suite

Runs all mini-axiom-kernel benchmarks.
-/

import MiniAxiomKernel

open MiniAxiomKernel

def main : IO Unit := do
  IO.println "══ MiniAxiomKernel Full Benchmark Suite ══"
  let start ← IO.monoMsNow

  -- Build a non-trivial axiom system
  let mut sys := AxiomSystem.empty "FullBench" "1.0.0"
  for i in List.range 100 do
    sys := sys.addAxiom (Axiom.simple s!"ax{i}" (Formula.atom (i % 10)))
  let _ := sys.axioms.size
  let _ := sys.axioms.containsName "ax50"
  let _ := sys.axioms.findByName "ax99"

  -- Registry operations
  let mut reg := AxiomRegistry.empty
  reg := reg.register sys
  let _ := reg.find "FullBench"

  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"Full benchmark: {elapsed}ms"
