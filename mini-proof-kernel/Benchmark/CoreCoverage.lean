/-
# Benchmark: Core Coverage — MiniProofKernel

Coverage benchmark for core proof kernel operations.
-/

import MiniProofKernel

open MiniLogicKernel
open MiniProofKernel

def main : IO Unit := do
  IO.println "══ CORE COVERAGE BENCHMARK ══"
  IO.println "Testing core ProofTree constructors..."

  -- Test each constructor
  let _hyp := .hyp (.head _ : Formula.atom 0 ∈ [Formula.atom 0])
  let _trueI : ProofTree [] .true := .trueI
  let _falseE : ProofTree [.false] (Formula.atom 1) := .falseE (.hyp (.head _))
  let _andI : ProofTree [] (.and .true .true) := .andI .trueI .trueI
  let _andEl : ProofTree [] .true := .andEl (.andI .trueI .trueI)
  let _andEr : ProofTree [] .true := .andEr (.andI .trueI .trueI)
  let _orIl : ProofTree [] (.or .true .false) := .orIl .trueI
  let _orIr : ProofTree [] (.or .false .true) := .orIr .trueI
  let _implI : ProofTree [] (.impl .true .true) := .implI (.hyp (.head _))
  let _implE : ProofTree [] .true := .implE (.implI (.hyp (.head _))) .trueI
  let _notI : ProofTree [] (.not .false) := .notI (.falseE (.hyp (.head _)))
  let _lem : ProofTree [] (.or (Formula.atom 0) (.not (Formula.atom 0))) := .lem

  IO.println "All core constructors verified."
  IO.println "══ CORE COVERAGE DONE ══"
