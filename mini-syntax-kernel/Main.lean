import MiniSyntaxKernel

open MiniSyntaxKernel

def main : IO Unit := do
  IO.println "═══════════════════════════════════════"
  IO.println "  MiniSyntaxKernel v0.1.0"
  IO.println "  Term Language and Syntax"
  IO.println "═══════════════════════════════════════"
  IO.println s!"  Variable: named variable with optional de Bruijn index"
  IO.println s!"  Term: var, app, lam, pi, sort, lit, letE constructors"
  IO.println s!"  Substitution: capture-avoiding substitution"
  IO.println s!"  Alpha equivalence: renaming of bound variables"
  IO.println s!"  Parallel substitution: simultaneous substitution"
  IO.println s!"  Free variable computation: FV(t)"
  IO.println s!"  Binding analysis: bound variable tracking"
  IO.println ""
  IO.println "  Depends on: mini-object-kernel"
  IO.println "  Run `lake env lean --run Test/Smoke.lean` for tests."
