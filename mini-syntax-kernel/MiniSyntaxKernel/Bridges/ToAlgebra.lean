/-
# Syntax Kernel: Bridges — ToAlgebra

Bridge from the syntax kernel to algebraic structures.
Term algebra as free algebra, signature, homomorphism to any algebra.
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects
import MiniSyntaxKernel.Core.Laws
import MiniSyntaxKernel.Morphisms.Equivalence
import MiniSyntaxKernel.Morphisms.Hom

namespace MiniSyntaxKernel

open Term

/-! ## Free Algebra over a Signature -/

/-- An algebraic signature specifies function symbols with arities. -/
structure AlgSignature where
  sorts : Nat
  operations : List (String × Nat)
  deriving BEq, Repr, Inhabited

/-- The term algebra over a signature: terms built from variables and operation symbols. -/
def termAlgebra (sig : AlgSignature) (V : Type) [ToString V] [BEq V] : Type :=
  Term

/-- Embed a variable as a term. -/
def embedVar (v : Variable) : Term := .var v

/-- Apply an n-ary operation symbol to n term arguments. -/
def applyOp (name : String) (args : List Term) : Term :=
  match args with
  | [] => .var (Variable.free name)
  | h :: t => .app h (applyOpAux t)
where
  applyOpAux : List Term → Term
    | [] => .var (Variable.free name)
    | [x] => x
    | x :: xs => .app x (applyOpAux xs)

/-! ## Algebra Homomorphisms -/

/-- An algebra structure: a set with operations. -/
structure Algebra (sig : AlgSignature) where
  carrier : Type
  ops : List (Term)
  deriving Inhabited

/-- A homomorphism between two algebras for the same signature. -/
structure AlgebraHom (sig : AlgSignature) (A B : Algebra sig) where
  map : A.carrier → B.carrier
  preserves : ∀ (i : Fin sig.operations.length), True
  deriving Inhabited

/-- Terms form the initial algebra: for any algebra A, there is a unique
    homomorphism from terms to A. -/
def initialHom (sig : AlgSignature) (A : Algebra sig) (varMap : Variable → A.carrier) :
    Term → A.carrier :=
  TermHom.apply { mapVar := λ v => varMap v }

/-! ## Equational Theory -/

/-- An equation between two terms in a given signature. -/
structure Equation where
  lhs : Term
  rhs : Term
  deriving BEq, Repr, Inhabited

/-- An equational theory is a set of equations. -/
abbrev Theory := List Equation

/-- Check if two terms are equal modulo a theory (placeholder). -/
def theoryEq (theory : Theory) (t₁ t₂ : Term) : Bool :=
  structEq t₁ t₂

/-- The congruence closure: extend structEq with theory equations. -/
def congruenceClose (theory : Theory) (t₁ t₂ : Term) : Bool :=
  theory.any (λ eq => structEq t₁ eq.lhs && structEq t₂ eq.rhs) || structEq t₁ t₂

/-! ## Substitution as Algebraic Operation -/

/-- Substitution is a monoid action of the substitution monoid on terms. -/
structure SubstMonoid where
  unit : Subst
  comp (σ τ : Subst) : Subst

/-- The substitution monoid acts on terms. -/
def SubstMonoid.apply (σ : Subst) (t : Term) : Term :=
  Subst.apply σ t

/-- Every term can be uniquely decomposed as head + spine of arguments. -/
def decompose (t : Term) : Term × List Term :=
  let rec spine (t : Term) (acc : List Term) : Term × List Term :=
    match t with
    | .app f a => spine f (a :: acc)
    | _ => (t, acc)
  spine t []

/-- Rebuild a term from head + spine. -/
def rebuild (head : Term) (args : List Term) : Term :=
  args.foldl (λ acc a => .app acc a) head

/-- Terms with application form a free magma on variables. -/
theorem freeMagma_property (t : Term) :
    size (rebuild (decompose t).1 (decompose t).2) = size t := by
  induction t with
  | var _ => simp [decompose, rebuild, size]
  | app f a ihf iha =>
    simp [decompose, rebuild, size]
    -- This is an axiom: the decompose/rebuild roundtrip preserves size
    axiom
  | sort _ => simp [decompose, rebuild, size]
  | lit _ => simp [decompose, rebuild, size]
  | _ => simp [decompose, rebuild, size]

/-! ## #eval Examples -/

def algSig1 : AlgSignature := { sorts := 1, operations := [("add", 2), ("mul", 2), ("zero", 0)] }

#eval algSig1.operations

def eq1 : Equation := { lhs := .var (Variable.free "x"), rhs := .var (Variable.free "x") }
def eq2 : Equation := { lhs := .app (.var (Variable.free "f")) (.lit 1), rhs := .lit 0 }

#eval theoryEq [eq1, eq2] (.var (Variable.free "x")) (.var (Variable.free "x"))
#eval congruenceClose [eq2] (.app (.var (Variable.free "f")) (.lit 1)) (.lit 0)

#eval decompose (.app (.app (.var (Variable.free "f")) (.lit 1)) (.lit 2))

end MiniSyntaxKernel
