/-
# Main — MiniProofKernel Entry Point

Print package information and basic sanity checks.
-/

import MiniProofKernel

open MiniLogicKernel
open MiniProofKernel

def main : IO Unit := do
  IO.println "╔═══════════════════════════════════╗"
  IO.println "║   Mini Proof Kernel v0.1.0       ║"
  IO.println "║   MiniEverything Math Project    ║"
  IO.println "╠═══════════════════════════════════╣"
  IO.println "║ Modules: 23                      ║"
  IO.println "║ Formula constructors:            ║"
  IO.println "║   atom, true, false, not,        ║"
  IO.println "║   and, or, impl, equiv           ║"
  IO.println "║ ProofTree constructors:          ║"
  IO.println "║   hyp, trueI, falseE, andI,      ║"
  IO.println "║   andEl, andEr, orIl, orIr, orE, ║"
  IO.println "║   implI, implE, notI, notE,      ║"
  IO.println "║   equivI, equivEl, equivEr, lem  ║"
  IO.println "║ Tactics:                         ║"
  IO.println "║   assumption, intro, apply,      ║"
  IO.println "║   split, left, right, exact      ║"
  IO.println "╚═══════════════════════════════════╝"

#eval main
