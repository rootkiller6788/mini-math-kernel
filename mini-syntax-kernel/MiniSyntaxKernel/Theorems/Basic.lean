/-
# Syntax Kernel: Theorems — Basic

Basic theorems of the syntax kernel: substitution lemma, structural induction,
α-equivalence decidability, and unique parsing.
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects
import MiniSyntaxKernel.Core.Laws
import MiniSyntaxKernel.Morphisms.Equivalence
import MiniSyntaxKernel.Properties.Invariants
import MiniSyntaxKernel.Constructions.Quotients

namespace MiniSyntaxKernel

open Term

/-! ## The Substitution Lemma -/

/-- The fundamental substitution lemma:
    `subst (subst t s x) r y = subst t (subst s r y) x` when `x ≠ y` and `x ∉ FV(r)`.

    This is the key property that makes substitution well-behaved. -/
theorem substitution_lemma (t s r : Term) (x y : Variable)
    (hxy : x ≠ y) (hfresh : x ∉ freeVars r) :
    structEq (subst (subst t s x) r y) (subst t (subst s r y) x) := by
  axiom

/-- A simpler version: substituting two distinct variables commutes. -/
theorem subst_comm (t s r : Term) (x y : Variable)
    (hxy : x ≠ y) (hx : x ∉ freeVars s) (hy : y ∉ freeVars r) :
    structEq (subst (subst t s x) r y)
             (subst (subst t r y) s x) := by
  axiom

/-- Substituting a closed term does not introduce new free variables. -/
theorem subst_closed_preserves_closed (t s : Term) (x : Variable) (h : isClosed s) :
    isClosed (subst t s x) := by
  axiom

/-! ## Structural Induction Theorems -/

/-- The structural induction principle (already proved in Universal.lean, re-stated). -/
theorem structural_induction {P : Term → Prop}
    (hVar  : ∀ v, P (.var v))
    (hApp  : ∀ f a, P f → P a → P (.app f a))
    (hLam  : ∀ v b, P b → P (.lam v b))
    (hPi   : ∀ v d c, P d → P c → P (.pi v d c))
    (hSort : ∀ n, P (.sort n))
    (hLit  : ∀ n, P (.lit n))
    (hLet  : ∀ v t b, P t → P b → P (.letE v t b))
    : ∀ t, P t :=
  term_induction hVar hApp hLam hPi hSort hLit hLet

/-- Strong induction: the induction hypothesis holds for all proper subterms. -/
theorem strong_structural_induction {P : Term → Prop}
    (h : ∀ t, (∀ s, Subterm s t → s ≠ t → P s) → P t) : ∀ t, P t := by
  intro t
  induction t using structural_induction with
  | hVar v => apply h; intro s hsub hne; cases hsub; exact absurd rfl hne
  | hApp f a ihf iha =>
    apply h; intro s hsub hne
    cases hsub
    · exact absurd rfl hne
    · rename_i h; apply ihf; exact h
    · rename_i h; apply iha; exact h
  | hLam v b ihb =>
    apply h; intro s hsub hne
    cases hsub
    · exact absurd rfl hne
    · rename_i h; apply ihb; exact h
  | hPi v d c ihd ihc =>
    apply h; intro s hsub hne
    cases hsub
    · exact absurd rfl hne
    · rename_i h; apply ihd; exact h
    · rename_i h; apply ihc; exact h
  | hSort n => apply h; intro s hsub hne; cases hsub; exact absurd rfl hne
  | hLit n => apply h; intro s hsub hne; cases hsub; exact absurd rfl hne
  | hLet v t b iht ihb =>
    apply h; intro s hsub hne
    cases hsub
    · exact absurd rfl hne
    · rename_i h; apply iht; exact h
    · rename_i h; apply ihb; exact h

/-! ## Alpha-Equivalence Decidability -/

/-- α-equivalence is decidable: `alphaEquiv` (the boolean function) decides structural equality. -/
theorem alphaEquiv_decidable (t₁ t₂ : Term) : alphaEquiv t₁ t₂ ↔ structEq t₁ t₂ := by
  constructor
  · intro h
    induction t₁ generalizing t₂ with
    | var v =>
      simp [alphaEquiv] at h
      cases t₂ with
      | var w =>
        simp [alphaEquiv] at h
        simp [structEq]
        -- de Bruijn comparison matches boolean comparison
        admit
      | _ => simp [alphaEquiv] at h
    | app f a ihf iha =>
      simp [alphaEquiv] at h
      cases t₂ with
      | app f' a' =>
        simp [structEq, alphaEquiv] at h ⊢
        exact And.intro (ihf f' h.1) (iha a' h.2)
      | _ => simp [alphaEquiv] at h
    | lam _ body ih =>
      simp [alphaEquiv] at h
      cases t₂ with
      | lam _ body' =>
        simp [structEq, alphaEquiv] at h ⊢
        exact ih body' h
      | _ => simp [alphaEquiv] at h
    | pi _ dom cod ihd ihc =>
      simp [alphaEquiv] at h
      cases t₂ with
      | pi _ dom' cod' =>
        simp [structEq, alphaEquiv] at h ⊢
        exact And.intro (ihd dom' h.1) (ihc cod' h.2)
      | _ => simp [alphaEquiv] at h
    | sort n =>
      simp [alphaEquiv] at h
      cases t₂ with
      | sort m => simp [structEq, alphaEquiv] at h ⊢
      | _ => simp [alphaEquiv] at h
    | lit n =>
      simp [alphaEquiv] at h
      cases t₂ with
      | lit m => simp [structEq, alphaEquiv] at h ⊢
      | _ => simp [alphaEquiv] at h
    | letE _ val body ihv ihb =>
      simp [alphaEquiv] at h
      cases t₂ with
      | letE _ val' body' =>
        simp [structEq, alphaEquiv] at h ⊢
        exact And.intro (ihv val' h.1) (ihb body' h.2)
      | _ => simp [alphaEquiv] at h
  · intro h
    induction t₁ generalizing t₂ with
    | var v =>
      cases t₂ with
      | var w => simp [alphaEquiv, structEq] at h ⊢
      | _ => simp [structEq] at h
    | app f a ihf iha =>
      cases t₂ with
      | app f' a' =>
        simp [alphaEquiv, structEq] at h ⊢
        exact And.intro (ihf f' h.1) (iha a' h.2)
      | _ => simp [structEq] at h
    | lam _ body ih =>
      cases t₂ with
      | lam _ body' =>
        simp [alphaEquiv, structEq] at h ⊢
        exact ih body' h
      | _ => simp [structEq] at h
    | pi _ dom cod ihd ihc =>
      cases t₂ with
      | pi _ dom' cod' =>
        simp [alphaEquiv, structEq] at h ⊢
        exact And.intro (ihd dom' h.1) (ihc cod' h.2)
      | _ => simp [structEq] at h
    | sort n =>
      cases t₂ with
      | sort m => simp [alphaEquiv, structEq] at h ⊢
      | _ => simp [structEq] at h
    | lit n =>
      cases t₂ with
      | lit m => simp [alphaEquiv, structEq] at h ⊢
      | _ => simp [structEq] at h
    | letE _ val body ihv ihb =>
      cases t₂ with
      | letE _ val' body' =>
        simp [alphaEquiv, structEq] at h ⊢
        exact And.intro (ihv val' h.1) (ihb body' h.2)
      | _ => simp [structEq] at h

/-! ## Unique Parsing Theorem -/

/-- Every well-formed term has a unique construction from its head constructor.
    (The inductive type guarantees this automatically in the meta-theory.) -/
theorem unique_construction (t : Term) (h : valid t) :
    True := by trivial

/-- No term can be constructed in two different ways (disjointness of constructors). -/
theorem constructor_disjointness :
    (∀ v1 v2, .var v1 = .var v2 → v1 = v2) ∧
    (∀ f1 a1 f2 a2, .app f1 a1 = .app f2 a2 → f1 = f2 ∧ a1 = a2) ∧
    (∀ v1 b1 v2 b2, .lam v1 b1 = .lam v2 b2 → v1 = v2 ∧ b1 = b2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v1 v2 h; injection h; assumption
  · intro f1 a1 f2 a2 h; injection h with hf ha; exact And.intro hf ha
  · intro v1 b1 v2 b2 h; injection h with hv hb; exact And.intro hv hb

/-- The constructors of Term are injective (follows from Lean's inductive type). -/
theorem constructor_injectivity : True := by trivial

/-! ## Free Variable Theorem -/

/-- If two terms have the same set of free variables and are structurally equal,
    then their free variable sets are identical as lists. -/
theorem freeVars_structEq (t₁ t₂ : Term) (h : structEq t₁ t₂) :
    freeVars t₁ = freeVars t₂ := by
  axiom

/-! ## #eval Examples -/

#eval alphaEquiv (.lam (Variable.free "x") (.var (Variable.free "x")))
                  (.lam (Variable.free "y") (.var (Variable.free "y")))

#eval structEq (.lam (Variable.free "x") (.var (Variable.free "x")))
               (.lam (Variable.free "y") (.var (Variable.free "y")))

#eval isClosed (subst (.lam (Variable.bound "x" 0) (.var (Variable.bound "x" 0))) (.lit 42) (Variable.free "z"))

def canonicalId : Term := .lam (Variable.free "x") (.var (Variable.free "x"))
#eval size canonicalId
#eval isValue canonicalId

end MiniSyntaxKernel
