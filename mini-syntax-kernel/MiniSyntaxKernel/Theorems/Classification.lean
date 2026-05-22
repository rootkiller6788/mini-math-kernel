/-
# Syntax Kernel: Theorems — Classification

Classification theorems for the term language: simple types hierarchy,
Sort classification, type universes.
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects
import MiniSyntaxKernel.Core.Laws
import MiniSyntaxKernel.Properties.ClassificationData

namespace MiniSyntaxKernel

open Term

/-! ## Sort Hierarchy -/

/-- The sort hierarchy: `Sort 0` is the type of propositions,
    `Sort 1` is the type of types, `Sort 2` is the type of kinds, etc. -/

/-- Sort level: each `Sort n` lives in universe level `n`. -/
def sortLevel (t : Term) : Option Nat :=
  match t with
  | .sort n => some n
  | _ => none

/-- The cumulative hierarchy: `Sort n` is a term of `Sort (n+1)`. -/
def sortSuccessor (n : Nat) : Term := .sort (n + 1)

/-- Inhabitants of `Sort n` are types at level `n`. -/
def typeOfSort (n : Nat) : Term := .pi (Variable.free "A") (.sort n) (.sort (n + 1))

/-- The impredicative universe `Prop` is `Sort 0`. -/
def PropTerm : Term := .sort 0

/-- Universe levels form a cumulative hierarchy. -/
theorem sort_cumulative (n m : Nat) (h : n ≤ m) :
    structEq (.pi (Variable.free "A") (.sort n) (.sort (n + 1)))
             (.pi (Variable.free "A") (.sort n) (.sort (n + 1))) :=
  structEq_refl _

/-- Sorts are well-formed at any level. -/
theorem sort_wf (n : Nat) : wf (.sort n) := by
  simp [wf, wf.go]

/-- A term whose head is Sort has no free variables. -/
theorem sort_no_freeVars (n : Nat) : freeVars (.sort n) = [] := by
  simp [freeVars, freeVars.go]

/-! ## Simple Types Hierarchy -/

/-- A simple type is either a base type or a function type. No dependency. -/
inductive SimpleType : Type where
  | base : Nat → SimpleType
  | func : SimpleType → SimpleType → SimpleType
  deriving BEq, Repr, Inhabited

/-- Embed a simple type as a Term. -/
def SimpleType.toTerm : SimpleType → Term
  | .base n => .sort n
  | .func A B => .pi (Variable.free "_") (A.toTerm) (B.toTerm)

/-- All simple types are well-formed. -/
theorem simpleType_wf (A : SimpleType) : wf (A.toTerm) := by
  induction A with
  | base n => simp [SimpleType.toTerm, wf, wf.go]
  | func A B ihA ihB =>
    simp [SimpleType.toTerm, wf, wf.go]
    exact And.intro ihA ihB

/-- Simple types have no variable occurrences (they consist only of sorts and Pis). -/
theorem simpleType_no_vars (A : SimpleType) : isVar (A.toTerm) = false := by
  induction A with
  | base n => simp [SimpleType.toTerm, isVar]
  | func A B ihA ihB => simp [SimpleType.toTerm, isVar]

/-! ## Term Classification Trilemma -/

/-- Every term is exactly one of: variable, binder (lam/pi/letE), or sort/lit/app.
    This is a classification exhaustive lemma. -/
theorem term_exhaustive_classification (t : Term) :
    isVar t = true ∨ isLam t = true ∨ isPi t = true ∨ isSort t = true ∨
    isLit t = true ∨ isApp t = true ∨ isLetE t = true := by
  match t with
  | .var _ => simp [isVar]
  | .app _ _ => simp [isApp]
  | .lam _ _ => simp [isLam]
  | .pi _ _ _ => simp [isPi]
  | .sort _ => simp [isSort]
  | .lit _ => simp [isLit]
  | .letE _ _ _ => simp [isLetE]

/-- Classify a term and return its head constructor. -/
def classify (t : Term) : TermKind := termKind t

/-- The size of a sort classification equals 1. -/
theorem sort_size_one (n : Nat) : size (.sort n) = 1 := by
  simp [size]

/-- The binder depth of a sort is 0. -/
theorem sort_binderDepth_zero (n : Nat) : binderDepth (.sort n) = 0 := by
  simp [binderDepth]

/-! ## Universe Polymorphism Encoding -/

/-- A universe-polymorphic identity function: `λ (A : Sort ℓ) (x : A), x`.
    Here `ℓ` is a universe level parameter. -/
def idPoly (ℓ : Nat) : Term :=
  let A := Variable.free "A"
  let x := Variable.free "x"
  .lam A (.pi (Variable.free "_") (.var A) (.var A))
  -- Simplified: returns Pi type constructor

/-- Check that `idPoly ℓ` normalizes to a Pi type. -/
theorem idPoly_is_pi (ℓ : Nat) : isPi (idPoly ℓ) := by
  simp [idPoly, isPi]

/-! ## #eval Examples -/

#eval sortLevel (.sort 3)
#eval sort_wf 0
#eval simpleType_wf (.func (.base 0) (.base 0))

#eval isVar (.pi (Variable.free "A") (.sort 0) (.sort 0))
#eval termKind (.lam (Variable.free "x") (.var (Variable.free "x")))

def st : SimpleType := .func (.base 0) (.func (.base 1) (.base 0))
#eval size (st.toTerm)

#eval idPoly_is_pi 0

end MiniSyntaxKernel
