/-
# Benchmark: Oxford Part C Curriculum Coverage

Oxford Part C mathematics curriculum benchmarks for the syntax kernel.
Covers: Lambda Calculus and Types, Category Theory, Domain Theory,
Mathematical Logic, Computability.
-/

import MiniSyntaxKernel

open MiniSyntaxKernel

namespace MiniSyntaxKernel

/-! Lambda Calculus: Combinators -/
def oxford_I : Term := .lam (Variable.free "x") (.var (Variable.free "x"))
def oxford_K : Term := .lam (Variable.free "x") (.lam (Variable.free "y") (.var (Variable.free "x")))
def oxford_S : Term := .lam (Variable.free "x") (.lam (Variable.free "y") (.lam (Variable.free "z")
  (.app (.app (.var (Variable.free "x")) (.var (Variable.free "z"))) (.app (.var (Variable.free "y")) (.var (Variable.free "z"))))))
#eval isClosed oxford_I
#eval isClosed oxford_K
#eval isClosed oxford_S

/-! Category Theory: Cartesian Closed -/
def oxford_curry : Term := .lam (Variable.free "f") (.lam (Variable.free "x") (.lam (Variable.free "y")
  (.app (.app (.var (Variable.free "f")) (.var (Variable.free "x"))) (.var (Variable.free "y")))))
def oxford_uncurry : Term := .lam (Variable.free "f") (.lam (Variable.free "p")
  (.app (.app (.var (Variable.free "f")) (fst (.var (Variable.free "p")))) (snd (.var (Variable.free "p")))))
#eval reduceCBN (.app oxford_curry oxford_K) 20 |>.1

/-! Domain Theory: Scott topology basis -/
def oxford_approx : Term := .lam (Variable.free "x") (.app (.var (Variable.free "x")) (.lit 1))
#eval finiteApproximations oxford_approx |>.length
#eval wayBelow (.var (Variable.free "x")) oxford_approx

/-! Mathematical Logic: Free variables -/
def oxford_open : Term := .app (.var (Variable.free "P")) (.var (Variable.free "Q"))
#eval isOpen oxford_open
#eval freeVars oxford_open
#eval freeOccurrences (Variable.free "P") oxford_open

/-! Variable binding and scope -/
def oxford_binder : Term := .lam (Variable.bound "x" 0) (.pi (Variable.bound "A" 1) (.sort 0) (.var (Variable.bound "x" 0)))
#eval wf oxford_binder
#eval maxBoundIndex oxford_binder

/-! De Bruijn canonical form -/
def oxford_debruijn : Term := .lam (Variable.free "x") (.lam (Variable.free "y") (.app (.var (Variable.free "x")) (.var (Variable.free "y"))))
#eval toDeBruijn oxford_debruijn

/-! Alpha equivalence in Category Theory -/
#eval alphaEquiv oxford_I (.lam (Variable.free "y") (.var (Variable.free "y")))

#eval "OXFORD PART C BENCHMARKS COMPLETE"

end MiniSyntaxKernel
