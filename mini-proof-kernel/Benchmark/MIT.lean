/-
# Benchmark: MIT — MiniProofKernel

MIT-style benchmark for proof kernel operations.
-/

import MiniProofKernel

open MiniLogicKernel
open MiniProofKernel

def main : IO Unit := do
  IO.println "══ MIT BENCHMARK ══"
  IO.println "Tactic combinator benchmark..."

  let st := ⟨[] : Context, .and (Formula.atom 0) (Formula.atom 1)⟩
  match (split `orElse` (fun _ => .failed "fallback")) st with
  | .done _ => IO.println "split succeeded"
  | .failed msg => IO.println s!"split failed (expected): {msg}"
  | .subgoals _ _ => IO.println "split has subgoals"

  IO.println "══ MIT DONE ══"
