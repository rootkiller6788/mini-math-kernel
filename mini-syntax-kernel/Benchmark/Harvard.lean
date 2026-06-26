/-
# Benchmark: Harvard Curriculum Coverage

Harvard mathematics curriculum benchmarks for the syntax kernel.
Covers: Math 25a/b (Honors Abstract Algebra/Real Analysis),
Math 141-145 (Logic, Model Theory, Proof Theory), CS 152 (Programming Languages).
-/

import MiniSyntaxKernel

open MiniSyntaxKernel

namespace MiniSyntaxKernel

/-! Abstract Algebra: Term algebras as free algebras -/
def harvard_free : Term := .app (.var (Variable.free "add")) (.app (.var (Variable.free "x")) (.var (Variable.free "y")))
#eval size harvard_free
#eval freeVars harvard_free
#eval decompose harvard_free

/-! Model Theory: Terms as syntactic objects -/
def harvard_syntax : Term :=
  .app (.lam (Variable.free "f") (.var (Variable.free "f")))
       (.lam (Variable.free "x") (.app (.var (Variable.free "x")) (.lit 1)))
#eval isClosed harvard_syntax
#eval normalOrderEval harvard_syntax

/-! Proof Theory: Normal forms -/
def harvard_nf : Term := .lam (Variable.free "x") (.lam (Variable.free "y") (.var (Variable.free "x")))
#eval isNormalForm harvard_nf
#eval isValue harvard_nf

/-! Programming Languages: CBN vs CBV -/
def harvard_redex : Term := .app (.lam (Variable.free "x") (.var (Variable.free "x"))) (.lit 42)
#eval reduceCBN harvard_redex 10
#eval reduceCBV harvard_redex 10

/-! Alpha equivalence: Binder invariance -/
def harvard_alpha1 : Term := .lam (Variable.free "x") (.lam (Variable.free "y") (.var (Variable.free "x")))
def harvard_alpha2 : Term := .lam (Variable.free "a") (.lam (Variable.free "b") (.var (Variable.free "a")))
#eval structEq harvard_alpha1 harvard_alpha2

/-! De Bruijn conversion -/
#eval toDeBruijn harvard_alpha1
#eval normalizeNames harvard_alpha1

/-! Subterm analysis -/
#eval isSubterm (.var (Variable.free "x")) harvard_nf
#eval subterms harvard_nf |>.length

#eval "HARVARD BENCHMARKS COMPLETE"

end MiniSyntaxKernel
