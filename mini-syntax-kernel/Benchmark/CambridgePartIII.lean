/-
# Benchmark: Cambridge Part III Curriculum Coverage

Cambridge Part III mathematics curriculum benchmarks for the syntax kernel.
Covers: Category Theory, Proof Theory, Lambda Calculus, Type Theory.
-/

import MiniSyntaxKernel

open MiniSyntaxKernel

namespace MiniSyntaxKernel

/-! Category Theory: Initial algebra of terms -/
def cambridge_initial : Term := .var (Variable.free "x")
#eval termKind cambridge_initial
#eval size cambridge_initial

/-! Proof Theory: Cut elimination via normalization -/
def cambridge_cut : Term :=
  .app (.lam (Variable.free "x") (.lam (Variable.free "y") (.var (Variable.free "x"))))
       (.app (.lam (Variable.free "z") (.var (Variable.free "z"))) (.lit 1))
#eval reduceCBN cambridge_cut 50 |>.1
#eval reductionSteps cambridge_cut 100

/-! Lambda Calculus: Fixed point combinator -/
def cambridge_Y : Term := .lam (Variable.free "f")
  (.app (.lam (Variable.free "x") (.app (.var (Variable.free "f")) (.app (.var (Variable.free "x")) (.var (Variable.free "x")))))
        (.lam (Variable.free "x") (.app (.var (Variable.free "f")) (.app (.var (Variable.free "x")) (.var (Variable.free "x"))))))
#eval size cambridge_Y
#eval isClosed cambridge_Y

/-! Type Theory: Pi types (dependent function space) -/
def cambridge_pi : Term := .pi (Variable.free "A") (.sort 0) (.pi (Variable.free "_") (.var (Variable.free "A")) (.sort 0))
#eval toDeBruijn cambridge_pi
#eval size cambridge_pi

/-! Structural equality under renaming -/
def cambridge_t1 : Term := .lam (Variable.free "x") (.lam (Variable.free "y") (.app (.var (Variable.free "x")) (.var (Variable.free "y"))))
def cambridge_t2 : Term := .lam (Variable.free "a") (.lam (Variable.free "b") (.app (.var (Variable.free "a")) (.var (Variable.free "b"))))
#eval alphaEquiv cambridge_t1 cambridge_t2
#eval structEq cambridge_t1 cambridge_t2

/-! Universal property: Currying -/
def cambridge_curry : Term := .lam (Variable.free "f") (.lam (Variable.free "x") (.lam (Variable.free "y")
  (.app (.app (.var (Variable.free "f")) (.var (Variable.free "x"))) (.var (Variable.free "y")))))
#eval isClosed cambridge_curry
#eval binderDepth cambridge_curry

#eval "CAMBRIDGE PART III BENCHMARKS COMPLETE"

end MiniSyntaxKernel
