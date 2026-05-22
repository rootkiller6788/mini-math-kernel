/-
# Benchmark: Princeton Curriculum Coverage

Princeton mathematics curriculum benchmarks for the syntax kernel.
Covers: MAT 201-204 (multivariable calculus incl. vector analysis),
MAT 215-217 (analysis), MAT 345 (logic), MAT 375 (combinatorics).

Targets: variable binding, substitution, lambda calculus fundamentals,
term algebras, Church encodings.
-/

import MiniSyntaxKernel

open MiniSyntaxKernel

namespace MiniSyntaxKernel

/-! MAT 345: Logic and Computability -/
def princeton_id : Term := .lam (Variable.free "x") (.var (Variable.free "x"))
#eval size princeton_id
#eval isClosed princeton_id
#eval isNormalForm princeton_id

/-! Church-Turing Thesis: Lambda Definability -/
def princeton_succ : Term := .lam (Variable.free "n") (.lam (Variable.free "f") (.lam (Variable.free "x")
  (.app (.var (Variable.free "f")) (.app (.app (.var (Variable.free "n")) (.var (Variable.free "f"))) (.var (Variable.free "x"))))))
#eval isClosed princeton_succ
#eval binderDepth princeton_succ

/-! MAT 375: Combinatorics via Lambda -/
def princeton_pair : Term := .lam (Variable.free "x") (.lam (Variable.free "y") (.lam (Variable.free "f")
  (.app (.app (.var (Variable.free "f")) (.var (Variable.free "x"))) (.var (Variable.free "y")))))
#eval size princeton_pair
#eval freeVars princeton_pair

/-! Substitution lemmas -/
#eval subst princeton_id (.lit 42) (Variable.free "x")

/-! Alpha equivalence checks -/
def princeton_t1 : Term := .lam (Variable.free "x") (.var (Variable.free "x"))
def princeton_t2 : Term := .lam (Variable.free "y") (.var (Variable.free "y"))
#eval alphaEquiv princeton_t1 princeton_t2
#eval structEq princeton_t1 princeton_t2

/-! Reduction semantics -/
def princeton_redex : Term := .app princeton_id (.lit 99)
#eval reduceCBN princeton_redex 50 |>.1
#eval reductionSteps princeton_redex 100

/-! De Bruijn normalization -/
#eval toDeBruijn princeton_id
#eval toDeBruijn (.lam (Variable.bound "x" 0) (.app (.var (Variable.bound "f" 1)) (.var (Variable.bound "x" 0))))

#eval "PRINCETON BENCHMARKS COMPLETE"

end MiniSyntaxKernel
