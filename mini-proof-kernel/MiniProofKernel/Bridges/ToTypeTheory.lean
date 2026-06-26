/-
# Proof Kernel: Bridge to Type Theory

Curry-Howard correspondence: proofs are programs, formulas are types.
Natural deduction proof trees correspond to simply typed lambda terms.

Key mapping:
  - implI = lambda abstraction
  - implE = application
  - andI   = pairing
  - andEl/andEr = projections
  - orIl/orIr = injections
  - orE = case analysis
-/

import MiniProofKernel.Core.Basic
import MiniProofKernel.Core.Objects

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Simple Type Representation (Curry-Howard) -/

/-- Simple types: atomic types, function types, product types, sum types. -/
inductive SimpleType : Type where
  | base  : Nat → SimpleType
  | unit   : SimpleType
  | empty  : SimpleType
  | fn    : SimpleType → SimpleType → SimpleType
  | prod  : SimpleType → SimpleType → SimpleType
  | sum   : SimpleType → SimpleType → SimpleType
  deriving Repr, DecidableEq, Inhabited

/-- Convert a Formula to a SimpleType (Curry-Howard). -/
def Formula.toSimpleType : Formula → SimpleType
  | .atom n => .base n
  | .true   => .unit
  | .false  => .empty
  | .not A   => .fn (A.toSimpleType) .empty
  | .impl A B => .fn (A.toSimpleType) (B.toSimpleType)
  | .and A B => .prod (A.toSimpleType) (B.toSimpleType)
  | .or A B  => .sum (A.toSimpleType) (B.toSimpleType)
  | .equiv A B =>
    .prod (.fn (A.toSimpleType) (B.toSimpleType))
          (.fn (B.toSimpleType) (A.toSimpleType))

/-- Convert a SimpleType back to a Formula. -/
def SimpleType.toFormula : SimpleType → Formula
  | .base n   => .atom n
  | .unit     => .true
  | .empty    => .false
  | .fn A B   => .impl (A.toFormula) (B.toFormula)
  | .prod A B => .and (A.toFormula) (B.toFormula)
  | .sum A B  => .or (A.toFormula) (B.toFormula)

/-! ## Type Context -/

/-- A type context is a list of simple types. -/
abbrev TypeContext := List SimpleType

instance : Membership SimpleType TypeContext where
  mem τ Γ := List.Mem τ Γ

/-- Convert a formula context to a type context. -/
def Context.toTypeCtx (Γ : Context) : TypeContext :=
  Γ.map Formula.toSimpleType

/-! ## Simply Typed Lambda Terms -/

/-- Simply typed lambda terms with products and sums. -/
inductive LambdaTerm : TypeContext → SimpleType → Type where
  | var  (h : τ ∈ Γ) : LambdaTerm Γ τ
  | lam  (body : LambdaTerm (τ :: Γ) σ) : LambdaTerm Γ (.fn τ σ)
  | app  (f : LambdaTerm Γ (.fn τ σ)) (a : LambdaTerm Γ τ) : LambdaTerm Γ σ
  | pair (a : LambdaTerm Γ τ) (b : LambdaTerm Γ σ) : LambdaTerm Γ (.prod τ σ)
  | fst  (p : LambdaTerm Γ (.prod τ σ)) : LambdaTerm Γ τ
  | snd  (p : LambdaTerm Γ (.prod τ σ)) : LambdaTerm Γ σ
  | inl  (a : LambdaTerm Γ τ) : LambdaTerm Γ (.sum τ σ)
  | inr  (b : LambdaTerm Γ σ) : LambdaTerm Γ (.sum τ σ)
  | case (s : LambdaTerm Γ (.sum τ σ))
         (l : LambdaTerm (τ :: Γ) ρ)
         (r : LambdaTerm (σ :: Γ) ρ) : LambdaTerm Γ ρ
  | unit : LambdaTerm Γ .unit
  | absurd (e : LambdaTerm Γ .empty) : LambdaTerm Γ τ
  deriving Repr

/-! ## Translating Proofs to Lambda Terms -/

/-- Helper: lift membership from Formula context to Type context. -/
def memToType {Γ : Context} {A : Formula} (h : A ∈ Γ) : A.toSimpleType ∈ Γ.toTypeCtx := by
  induction Γ with
  | nil => exact nomatch h
  | cons f fs ih =>
    cases h with
    | head _ => exact .head _
    | tail _ h' => exact .tail _ (ih h')

/-- Curry-Howard translation: ProofTree → LambdaTerm. -/
def ProofTree.toLambda {Γ : Context} {A : Formula} : ProofTree Γ A → LambdaTerm (Γ.toTypeCtx) (A.toSimpleType)
  | .hyp h => .var (memToType h)
  | .trueI => .unit
  | .falseE p => .absurd (toLambda p)
  | .andI p q => .pair (toLambda p) (toLambda q)
  | .andEl p => .fst (toLambda p)
  | .andEr p => .snd (toLambda p)
  | .orIl p => .inl (toLambda p)
  | .orIr p => .inr (toLambda p)
  | .orE p q r => .case (toLambda p) (toLambda q) (toLambda r)
  | .implI p => .lam (toLambda p)
  | .implE p q => .app (toLambda p) (toLambda q)
  | .notI p => .lam (toLambda p)
  | .notE p q => .app (toLambda p) (toLambda q)
  | .equivI p q => .pair (toLambda p) (toLambda q)
  | .equivEl p => .fst (toLambda p)
  | .equivEr p => .snd (toLambda p)
  | .lem => .inr (.lam (.var (.head _)))

/-! ## Size of Lambda Terms -/

def LambdaTerm.size {Γ : TypeContext} {τ : SimpleType} : LambdaTerm Γ τ → Nat
  | .var _ => 1
  | .lam b => 1 + b.size
  | .app f a => 1 + f.size + a.size
  | .pair a b => 1 + a.size + b.size
  | .fst p => 1 + p.size
  | .snd p => 1 + p.size
  | .inl a => 1 + a.size
  | .inr b => 1 + b.size
  | .case s l r => 1 + s.size + l.size + r.size
  | .unit => 1
  | .absurd e => 1 + e.size

/-! ## Simple Type Utilities -/

/-- Check if a simple type is a base type. -/
def SimpleType.isBase : SimpleType → Bool
  | .base _ => true
  | _ => false

/-- Get the arity of a function type (number of arguments). -/
def SimpleType.arity : SimpleType → Nat
  | .fn _ B => 1 + B.arity
  | _ => 0

/-- Compute the size of a simple type (number of constructors). -/
def SimpleType.typeSize : SimpleType → Nat
  | .base _ => 1
  | .unit => 1
  | .empty => 1
  | .fn A B => 1 + A.typeSize + B.typeSize
  | .prod A B => 1 + A.typeSize + B.typeSize
  | .sum A B => 1 + A.typeSize + B.typeSize

/-! ## Evaluation Examples -/

def sa : Formula := .atom 0
def sb : Formula := .atom 1

-- A ⊢ A as lambda term
def idLambda : LambdaTerm [] (.fn (.base 0) (.base 0)) :=
  .lam (.var (.head _))

-- Proof of A → A
def proofId : ProofTree [] (.impl sa sa) := .implI (.hyp (.head _))

-- Translate proof to lambda term
def translatedId : LambdaTerm (([].toTypeCtx : TypeContext)) (sa.toSimpleType.fn sa.toSimpleType) :=
  proofId.toLambda

#eval idLambda.size
#eval proofId.size
#eval sa.toSimpleType
#eval sb.toSimpleType
#eval SimpleType.toFormula (.fn (.base 0) (.base 0))
#eval (.base 0).arity
#eval (.fn (.base 0) (.base 1)).typeSize

end MiniProofKernel
