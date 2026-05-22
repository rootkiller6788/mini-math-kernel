/-
# Benchmark: Basic Axiom Operations

Measures performance of basic axiom construction and access.
-/

import MiniAxiomKernel

open MiniAxiomKernel

def main : IO Unit := do
  IO.println "══ Benchmark: Basic Axiom Operations ══"

  -- Benchmark 1: Axiom construction throughput
  let start1 ← IO.monoMsNow
  for _ in List.range 10000 do
    let _ := Axiom.simple "bench" (Formula.atom 0)
    pure ()
  let elapsed1 := (← IO.monoMsNow) - start1
  IO.println s!"10000 axiom constructions: {elapsed1}ms"

  -- Benchmark 2: Axiom name access
  let start2 ← IO.monoMsNow
  for _ in List.range 10000 do
    let a := Axiom.simple "bench" (Formula.atom 0)
    let _ := a.name
    pure ()
  let elapsed2 := (← IO.monoMsNow) - start2
  IO.println s!"10000 axiom name accesses: {elapsed2}ms"

  -- Benchmark 3: Axiom formula access
  let start3 ← IO.monoMsNow
  for _ in List.range 5000 do
    let a := Axiom.simple "bench" (Formula.atom 0)
    let _ := a.formula
    pure ()
  let elapsed3 := (← IO.monoMsNow) - start3
  IO.println s!"5000 axiom formula accesses: {elapsed3}ms"

  -- Benchmark 4: Axiom list construction
  let start4 ← IO.monoMsNow
  let axs : List (String × String) := List.range 1000 |>.map fun n =>
    (s!"axiom_{n}", s!"formula_{n}")
  let elapsed4 := (← IO.monoMsNow) - start4
  IO.println s!"1000 axiom list entries: {elapsed4}ms"

  -- Benchmark 5: Bulk axiom evaluation
  let start5 ← IO.monoMsNow
  for _ in List.range 1000 do
    let _ := Axiom.simple "eval_bench" (Formula.atom 0)
    let _ := Axiom.simple "eval_bench2" (Formula.impl (Formula.atom 0) (Formula.atom 1))
    pure ()
  let elapsed5 := (← IO.monoMsNow) - start5
  IO.println s!"1000 bulk axiom eval cycles: {elapsed5}ms"

  IO.println "══ Benchmark Complete ══"
