/-
# Syntax Kernel: Examples — Counterexamples

Counterexamples for properties that do not hold in the term language:
non-normalizing terms, terms that fail wf, variable capture, non-alpha-equivalent terms.
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects
import MiniSyntaxKernel.Core.Laws
import MiniSyntaxKernel.Morphisms.Equivalence
import MiniSyntaxKernel.Theorems.Main
import MiniSyntaxKernel.Properties.ClassificationData

namespace MiniSyntaxKernel

open Term

/-- Identity function (local definition for counterexamples, to avoid name conflict with Standard.lean). -/
def idTermCE : Term := .lam (Variable.free "x") (.var (Variable.free "x"))

/-! ## Non-Normalizing Terms -/

/-- The omega combinator: (λ x. x x) (λ x. x x) — has no normal form. -/
def omega : Term :=
  .app (.lam (Variable.free "x") (.app (.var (Variable.free "x")) (.var (Variable.free "x"))))
       (.lam (Variable.free "x") (.app (.var (Variable.free "x")) (.var (Variable.free "x"))))

/-- Omega reduces to itself: non-terminating. Check that it contains a redex. -/
example : isNormalForm omega = false := by
  simp [isNormalForm, omega]

/-! ## Terms That Fail Well-formedness -/

/-- A term with a de Bruijn index out of scope: λ x. x#5 where 5 ≥ context size 1. -/
def badBoundIndex : Term :=
  .lam (Variable.free "x") (.var (Variable.bound "x" 5))

/-- This term is not well-formed because x#5 has index ≥ context size. -/
example : wf badBoundIndex = false := by
  native_decide

/-- A variable with index exceeding the context size in an application. -/
def badApp : Term :=
  .app (.var (Variable.bound "f" 3)) (.lit 1)

/-- Not well-formed: index 3 exceeds context size 0. -/
example : wf badApp = false := by
  native_decide

/-! ## Variable Capture Examples -/

/-- A term that could cause variable capture if substitution were naive.
    Here we use raw substitution and check that capture-avoidance works. -/
def captureTestBody : Term :=
  .lam (Variable.free "y") (.app (.var (Variable.free "x")) (.var (Variable.free "y")))

/-- Substitute `y` (free) for `x` in `λ y. x y`. Capture-avoiding substitution
    should avoid the bound `y`. -/
def captureSubst : Term := subst captureTestBody (.var (Variable.free "y")) (Variable.free "x")

/-- After substitution, the inner `y` is bound, the outer one is free if not captured. -/
example : freeVars captureSubst |>.contains (Variable.free "y") = true := by
  native_decide

/-! ## Non-Alpha-Equivalent Terms -/

/-- Two terms that look similar but are not alpha-equivalent because
    of different binder structures. -/
def nonAlpha1 : Term := .lam (Variable.free "x") (.lam (Variable.free "y") (.app (.var (Variable.free "x")) (.var (Variable.free "y"))))
def nonAlpha2 : Term := .lam (Variable.free "x") (.lam (Variable.free "y") (.app (.var (Variable.free "y")) (.var (Variable.free "x"))))

/-- These are different: one applies x to y, the other applies y to x. -/
example : structEq nonAlpha1 nonAlpha2 = false := by
  native_decide

/-- Terms with different numbers of binders cannot be alpha-equivalent. -/
def bindDiff1 : Term := .lam (Variable.free "x") (.var (Variable.free "x"))
def bindDiff2 : Term := .lam (Variable.free "x") (.lam (Variable.free "y") (.var (Variable.free "x")))

example : structEq bindDiff1 bindDiff2 = false := by
  native_decide

/-! ## Non-Closed Terms -/

/-- A term with a dangling free variable. -/
def openTerm : Term := .app (.var (Variable.free "f")) (.lit 1)

/-- This term is open (has free variables). -/
example : isClosed openTerm = false := by
  native_decide

/-! ## Terms That Are Not Values -/

/-- An application is not a value. -/
example : isValue (.app idTermCE (.lit 42)) = false := by
  simp [isValue, idTermCE]

/-- A naked variable is neutral but not a value. -/
example : isValue (.var (Variable.free "x")) = false := by
  simp [isValue]

/-! ## #eval Examples -/

#eval isNormalForm omega
#eval wf badBoundIndex
#eval wf badApp

#eval structEq nonAlpha1 nonAlpha2
#eval structEq bindDiff1 bindDiff2

#eval freeVars openTerm
#eval isClosed openTerm

end MiniSyntaxKernel
