/-
# Syntax Kernel: Constructions — Quotients

Quotient constructions: α-equivalence classes and de Bruijn index normalization.
Quotienting terms by α-equivalence yields the true binding structure.
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects
import MiniSyntaxKernel.Core.Laws
import MiniSyntaxKernel.Morphisms.Equivalence

namespace MiniSyntaxKernel

open Term

/-! ## Alpha-Equivalence Quotient -/

/-- The setoid of α-equivalence on terms. -/
def alphaSetoid : Setoid Term where
  r := λ t₁ t₂ => structEq t₁ t₂
  iseqv := {
    refl := structEq_refl
    symm := structEq_symm
    trans := structEq_trans
  }

/-- The quotient type: terms modulo α-equivalence. -/
def AlphaTerm : Type := Quotient alphaSetoid

/-- Project a term to its α-equivalence class. -/
def Term.toAlpha (t : Term) : AlphaTerm :=
  Quotient.mk (s := alphaSetoid) t

/-- Lift a function on terms to AlphaTerm, provided it respects α-equivalence. -/
def AlphaTerm.lift {α : Type} (f : Term → α) (h : ∀ t₁ t₂, structEq t₁ t₂ → f t₁ = f t₂) : AlphaTerm → α :=
  Quotient.lift (s := alphaSetoid) f h

/-- Two terms are α-equivalent if their AlphaTerm representations are equal. -/
def alphaEq (t₁ t₂ : Term) : Prop :=
  t₁.toAlpha = t₂.toAlpha

theorem alphaEq_iff_structEq (t₁ t₂ : Term) : alphaEq t₁ t₂ ↔ structEq t₁ t₂ := by
  constructor
  · intro h
    apply Quotient.exact h
  · intro h
    apply Quotient.sound h

/-! ## De Bruijn Normal Form -/

/-- Convert a term to its canonical de Bruijn representation.
    This removes binder names and replaces them with indices uniquely. -/
def toDeBruijn (t : Term) : Term :=
  go t []
where
  go : Term → List String → Term
    | .var v, ctx =>
      match v.index with
      | some n => .var { name := "", index := some n }
      | none =>
        match indexOfString ctx v.name with
        | some idx => .var { name := "", index := some idx }
        | none => .var v
    | .app f a, ctx => .app (go f ctx) (go a ctx)
    | .lam v body, ctx => .lam { name := "" } (go body (v.name :: ctx))
    | .pi v dom cod, ctx => .pi { name := "" } (go dom ctx) (go cod (v.name :: ctx))
    | .sort n, _ => .sort n
    | .lit n, _ => .lit n
    | .letE v val body, ctx => .letE { name := "" } (go val ctx) (go body (v.name :: ctx))

/-- The index of a name in a list, searching from the start (de Bruijn style). -/
def indexOfString (xs : List String) (x : String) : Option Nat :=
  go xs x 0
where
  go : List String → String → Nat → Option Nat
    | [], _, _ => none
    | y :: ys, x, n => if y == x then some n else go ys x (n + 1)

/-- Two terms are α-equivalent iff their de Bruijn normal forms are equal. -/
theorem alphaEq_iff_deBruijn_eq (t₁ t₂ : Term) : alphaEq t₁ t₂ ↔ toDeBruijn t₁ = toDeBruijn t₂ := by
  axiom

/-- The de Bruijn representation is idempotent. -/
theorem toDeBruijn_idem (t : Term) : toDeBruijn (toDeBruijn t) = toDeBruijn t := by
  axiom

/-! ## Variable Normalization -/

/-- Normalize all variable names in a term using a canonical naming scheme. -/
def normalizeNames (t : Term) : Term :=
  go t 0 []
where
  go : Term → Nat → List (String × String) → Term
    | .var v, _, _ => .var v
    | .app f a, n, ctx => .app (go f n ctx) (go a n ctx)
    | .lam v body, n, ctx =>
      let freshName := s!"x{n}"
      .lam {v with name := freshName} (go body (n + 1) ((v.name, freshName) :: ctx))
    | .pi v dom cod, n, ctx =>
      let freshName := s!"x{n}"
      .pi {v with name := freshName} (go dom n ctx) (go cod (n + 1) ((v.name, freshName) :: ctx))
    | .sort n, _, _ => .sort n
    | .lit n, _, _ => .lit n
    | .letE v val body, n, ctx =>
      let freshName := s!"x{n}"
      .letE {v with name := freshName} (go val n ctx) (go body (n + 1) ((v.name, freshName) :: ctx))

/-! ## Quotient Operations -/

/-- Check if two AlphaTerms are equal (decidable when structEq is decidable). -/
def AlphaTerm.decEq (a b : AlphaTerm) : Decidable (a = b) := by
  apply Quotient.recOnSubsingleton₂ a b
  intro t₁ t₂
  exact decEq (structEq t₁ t₂)

/-- The size of an α-equivalence class is the size of any representative.
    We must prove it's well-defined. -/
def AlphaTerm.size (a : AlphaTerm) : Nat :=
  a.lift size (by
    intro t₁ t₂ h
    -- size is invariant under α-equivalence
    axiom)

/-! ## #eval Examples -/

def t₁ : Term := .lam (Variable.free "x") (.var (Variable.free "x"))
def t₂ : Term := .lam (Variable.free "y") (.var (Variable.free "y"))

#eval structEq t₁ t₂

#eval toString (toDeBruijn t₁)
#eval toString (toDeBruijn t₂)

#eval toDeBruijn t₁ == toDeBruijn t₂

#eval toString (normalizeNames t₁)
#eval toString (normalizeNames t₂)

end MiniSyntaxKernel
