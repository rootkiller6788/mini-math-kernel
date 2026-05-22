/-
# Example Tests — MiniSyntaxKernel

Run: `lake env lean --run Test/Examples.lean`
-/

import MiniSyntaxKernel

open MiniSyntaxKernel

/-! ## Identity function -/
def idFun := Term.lam (Variable.free "x") (Term.var (Variable.free "x"))
#eval idFun
#eval size idFun
#eval isClosed idFun

/-! ## Constant function -/
def constFun := Term.lam (Variable.free "x")
  (Term.lam (Variable.free "y") (Term.var (Variable.free "x")))
#eval constFun
#eval size constFun
#eval freeVars constFun

/-! ## Application -/
def applyTerm := Term.app (Term.var (Variable.free "f")) (Term.var (Variable.free "x"))
#eval applyTerm
#eval freeVars applyTerm

/-! ## Sort hierarchy -/
#eval Term.sort 0
#eval Term.sort 1
#eval size (Term.sort 42)

/-! ## Literals -/
#eval Term.lit 0
#eval Term.lit 42
#eval size (Term.lit 100)

#eval "══ ALL EXAMPLE TESTS PASSED ══"
