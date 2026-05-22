/-
# Benchmark: Harvard — MiniProofKernel

Harvard-style benchmark for proof kernel operations.
-/

import MiniProofKernel

open MiniLogicKernel
open MiniProofKernel

def main : IO Unit := do
  IO.println "══ HARVARD BENCHMARK ══"
  IO.println "Tactic framework benchmark..."

  let st := ⟨[] : Context, .impl (Formula.atom 0) (Formula.atom 0)⟩
  match intro st with
  | .done p =>
    IO.println s!"Tactic intro produced proof of size {p.size}"
    IO.println s!"Valid: {p.isValid}"
  | .failed msg => IO.println s!"Tactic failed: {msg}"
  | .subgoals _ _ => IO.println "Unexpected subgoals"

  IO.println "══ HARVARD DONE ══"
