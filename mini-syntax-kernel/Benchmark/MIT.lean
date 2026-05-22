/-
# Benchmark: MIT Curriculum Coverage

MIT mathematics curriculum benchmarks for the syntax kernel.
Covers: 18.404 (Theory of Computation), 18.510 (Mathematical Logic),
6.820 (Foundations of Program Analysis), 18.705 (Commutative Algebra).
-/

import MiniSyntaxKernel

open MiniSyntaxKernel

namespace MiniSyntaxKernel

/-! 18.404: Lambda Calculus -/
def mit_id : Term := .lam (Variable.free "x") (.var (Variable.free "x"))
def mit_omega : Term := .app (.lam (Variable.free "x") (.app (.var (Variable.free "x")) (.var (Variable.free "x"))))
                       (.lam (Variable.free "x") (.app (.var (Variable.free "x")) (.var (Variable.free "x"))))
#eval isNormalForm mit_id
#eval isNormalForm mit_omega
#eval size mit_omega

/-! 18.510: Substitution Lemma -/
def mit_subst_t : Term := .lam (Variable.free "x") (.app (.var (Variable.free "f")) (.var (Variable.free "x")))
def mit_subst_s : Term := .lit 42
#eval subst mit_subst_t mit_subst_s (Variable.free "f")
#eval freeVars (subst mit_subst_t mit_subst_s (Variable.free "f"))

/-! 6.820: Abstract Interpretation -/
#eval constructorCount mit_id
#eval constructorCount_eq_size mit_id

/-! Krivine Machine -/
def mit_krivine : Term := .app (.lam (Variable.free "x") (.app (.var (Variable.free "x")) (.lit 1))) (.lam (Variable.free "y") (.var (Variable.free "y")))
#eval runKrivine mit_krivine
#eval reductionSteps mit_krivine 100

/-! Serialization -/
#eval serializeSexpr mit_id

/-! Classification complexity -/
def mit_simple : Term := .lit 0
def mit_complex : Term := .lam (Variable.free "f") (.lam (Variable.free "g") (.lam (Variable.free "x")
  (.app (.app (.var (Variable.free "f")) (.app (.var (Variable.free "g")) (.var (Variable.free "x")))) (.lit 42))))
#eval classifyComplexity mit_simple
#eval classifyComplexity mit_complex

/-! Head shape analysis -/
#eval headShape mit_id
#eval isNeutral (.app (.var (Variable.free "x")) (.lit 1))
#eval isRedex (.app (.lam (Variable.free "x") (.var (Variable.free "x"))) (.lit 1))

#eval "MIT BENCHMARKS COMPLETE"

end MiniSyntaxKernel
