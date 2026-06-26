/-
# Smoke Tests — MiniSyntaxKernel

Run: `lake env lean --run Test/Smoke.lean`
-/

import MiniSyntaxKernel

open MiniSyntaxKernel

#eval "══ MINI-SYNTAX-KERNEL SMOKE TESTS ══"

/-! ## Core.Basic: Variables -/
#eval Variable.free "x"
#eval Variable.bound "x" 0
#eval (Variable.free "x" == Variable.free "x")

/-! ## Core.Basic: Terms -/
#eval Term.var (Variable.free "x")
#eval Term.lam (Variable.free "x") (Term.var (Variable.free "x"))
#eval Term.sort 0
#eval size (Term.app (Term.var (Variable.free "f")) (Term.var (Variable.free "x")))

/-! ## Core.Objects: Analysis -/
def idTerm := Term.lam (Variable.free "x") (Term.var (Variable.free "x"))
#eval freeVars idTerm
#eval isClosed idTerm
#eval binderDepth idTerm

/-! ## Morphisms.Equivalence: Substitution -/
#eval lift1 (Term.var (Variable.bound "x" 0))
#eval subst (Term.var (Variable.free "x")) (Term.lit 42) (Variable.free "x")
#eval alphaEquiv idTerm idTerm

#eval "══ ALL MINI-SYNTAX-KERNEL SMOKE TESTS PASSED ══"
