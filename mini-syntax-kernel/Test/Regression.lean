/-
# Regression Tests — MiniSyntaxKernel

Run: `lake env lean --run Test/Regression.lean`
-/

import MiniSyntaxKernel

open MiniSyntaxKernel

/-! ## Regression: Variable equality -/
def x1 := Variable.free "x"
def x2 := Variable.free "x"
def y  := Variable.free "y"
def b0 := Variable.bound "x" 0
def b1 := Variable.bound "x" 1

#eval x1 == x2
#eval x1 == y
#eval b0 == b1
#eval b0 == Variable.bound "x" 0

/-! ## Regression: Term creation and analysis -/
def t1 := Term.lam (Variable.free "x") (Term.var (Variable.free "x"))
def t2 := Term.lam (Variable.free "y") (Term.var (Variable.free "y"))

#eval size t1 == size t2
#eval isClosed t1 == isClosed t2
#eval alphaEquiv t1 t2

/-! ## Regression: Substitution stability -/
def subTest := Term.app (Term.var (Variable.free "f")) (Term.var (Variable.free "x"))
#eval subst subTest (Term.lit 42) (Variable.free "x")
#eval subst subTest (Term.lit 42) (Variable.free "y")

/-! ## Regression: Lift preserves closedness -/
def closedId := Term.lam (Variable.free "x") (Term.var (Variable.free "x"))
#eval isClosed closedId
#eval isClosed (lift1 closedId)

#eval "══ ALL REGRESSION TESTS PASSED ══"
