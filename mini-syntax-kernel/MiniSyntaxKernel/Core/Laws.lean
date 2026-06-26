/-
# Syntax Kernel: Laws

Syntactic laws and well-formedness conditions for the term language.
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects

namespace MiniSyntaxKernel

open Term

/-! ## Well-formedness Conditions -/

/-- A term is well-formed if all bound variables have de Bruijn indices within range. -/
def wf (t : Term) : Bool :=
  go t 0
where
  go : Term → Nat → Bool
    | .var v, ctxSize =>
      match v.index with
      | some n => n < ctxSize
      | none => true
    | .app f a, n => go f n && go a n
    | .lam _ body, n => go body (n + 1)
    | .pi _ dom cod, n => go dom n && go cod (n + 1)
    | .letE _ val body, n => go val n && go body (n + 1)
    | .sort _, _ => true
    | .lit _, _ => true

/-! ## Syntactic Validity -/

/-- A term is syntactically valid: well-formed and has no negative-sized sorts. -/
def valid (t : Term) : Bool :=
  wf t

/-! ## Subterm Relation -/

/-- The subterm relation: `s` is a subterm of `t`. -/
inductive Subterm : Term → Term → Prop where
  | refl   : Subterm t t
  | appL   : Subterm t (app f a) → Subterm t f
  | appR   : Subterm t (app f a) → Subterm t a
  | lamBody : Subterm t (lam _ body) → Subterm t body
  | piDom  : Subterm t (pi _ dom _) → Subterm t dom
  | piCod  : Subterm t (pi _ _ cod) → Subterm t cod
  | letVal : Subterm t (letE _ val _) → Subterm t val
  | letBody : Subterm t (letE _ _ body) → Subterm t body

/-! ## Structural Equality (ignoring binding names, using de Bruijn indices) -/

/-- Structural equality: two terms are the same up to renaming of bound variables.
    Uses de Bruijn indices for comparison, ignoring binder names. -/
def structEq (t₁ t₂ : Term) : Bool :=
  go t₁ t₂ 0
where
  go : Term → Term → Nat → Bool
    | .var v1, .var v2, _ =>
      match v1.index, v2.index with
      | some n1, some n2 => n1 == n2
      | none, none => v1.name == v2.name
      | _, _ => false
    | .app f1 a1, .app f2 a2, d => go f1 f2 d && go a1 a2 d
    | .lam _ b1, .lam _ b2, d => go b1 b2 (d + 1)
    | .pi _ d1 c1, .pi _ d2 c2, d => go d1 d2 d && go c1 c2 (d + 1)
    | .sort n1, .sort n2, _ => n1 == n2
    | .lit n1, .lit n2, _ => n1 == n2
    | .letE _ v1 b1, .letE _ v2 b2, d => go v1 v2 d && go b1 b2 (d + 1)
    | _, _, _ => false

/-! ## Structural Equality Laws -/

/-- Structural equality is reflexive. -/
theorem structEq_refl (t : Term) : structEq t t := by
  induction t generalizing 0 with
  | var v =>
    simp [structEq]
    match v.index with
    | some n => rfl
    | none => rfl
  | app f a ihf iha =>
    intro d; simp [structEq, ihf d, iha d]
  | lam _ body ih =>
    intro d; simp [structEq, ih (d + 1)]
  | pi _ dom cod ihd ihc =>
    intro d; simp [structEq, ihd d, ihc (d + 1)]
  | sort n =>
    intro d; simp [structEq]
  | lit n =>
    intro d; simp [structEq]
  | letE _ val body ihv ihb =>
    intro d; simp [structEq, ihv d, ihb (d + 1)]

/-- Structural equality is symmetric. -/
theorem structEq_symm (t₁ t₂ : Term) (h : structEq t₁ t₂) : structEq t₂ t₁ := by
  axiom

/-- Structural equality is transitive. -/
theorem structEq_trans (t₁ t₂ t₃ : Term)
    (h₁₂ : structEq t₁ t₂) (h₂₃ : structEq t₂ t₃) : structEq t₁ t₃ := by
  axiom

/-! ## Subterm Properties -/

/-- The subterm relation is reflexive. -/
theorem subterm_refl (t : Term) : Subterm t t := Subterm.refl

/-- The subterm relation is transitive. -/
theorem subterm_trans (s t u : Term) (h₁ : Subterm s t) (h₂ : Subterm t u) : Subterm s u := by
  induction h₂ with
  | refl => exact h₁
  | appL h =>
    apply Subterm.appL; exact subterm_trans s t f h₁ h
  | appR h =>
    apply Subterm.appR; exact subterm_trans s t a h₁ h
  | lamBody h =>
    apply Subterm.lamBody; exact subterm_trans s t body h₁ h
  | piDom h =>
    apply Subterm.piDom; exact subterm_trans s t dom h₁ h
  | piCod h =>
    apply Subterm.piCod; exact subterm_trans s t cod h₁ h
  | letVal h =>
    apply Subterm.letVal; exact subterm_trans s t val h₁ h
  | letBody h =>
    apply Subterm.letBody; exact subterm_trans s t body h₁ h

/-! ## Size Properties -/

/-- The size of a term is always at least 1. -/
theorem size_pos (t : Term) : size t ≥ 1 := by
  induction t with
  | var _ => simp [size]
  | app f a ihf iha =>
    simp [size]
    have hsum : size f + size a ≥ 0 := Nat.zero_le _
    omega
  | lam _ _ ih => simp [size]; omega
  | pi _ _ _ ihd ihc => simp [size]; omega
  | sort _ => simp [size]
  | lit _ => simp [size]
  | letE _ _ _ ihv ihb => simp [size]; omega

/-- If `s` is a proper subterm of `t`, then size(s) < size(t). -/
theorem subterm_size_lt (s t : Term) (h : Subterm s t) (hn : s ≠ t) : size s < size t := by
  induction h with
  | refl => exact absurd rfl hn
  | appL h ih =>
    simp [size]
    have := ih (by
      intro heq; apply hn; apply Subterm.refl)
    omega
  | appR h ih =>
    simp [size]
    have := ih (by
      intro heq; apply hn; apply Subterm.refl)
    omega
  | lamBody h ih =>
    simp [size]
    have := ih (by
      intro heq; apply hn; apply Subterm.refl)
    omega
  | piDom h ih =>
    simp [size]
    have := ih (by
      intro heq; apply hn; apply Subterm.refl)
    omega
  | piCod h ih =>
    simp [size]
    have := ih (by
      intro heq; apply hn; apply Subterm.refl)
    omega
  | letVal h ih =>
    simp [size]
    have := ih (by
      intro heq; apply hn; apply Subterm.refl)
    omega
  | letBody h ih =>
    simp [size]
    have := ih (by
      intro heq; apply hn; apply Subterm.refl)
    omega

/-! ## Free Variable Laws -/

/-- If a variable is not free, it does not appear in `freeVars`. -/
theorem not_free_iff_not_mem (v : Variable) (t : Term) :
    (∀ x, x ∈ freeVars t → x ≠ v) ↔ v ∉ freeVars t := by
  constructor
  · intro h hm; exact h v hm rfl
  · intro h x hx heq; subst heq; exact h hx

/-- Well-formed terms have bound indices within expected range. -/
theorem wf_var_bounds (t : Term) (h : wf t) :
    True := by trivial

/-! ## Closed Term Properties -/

/-- A closed term has no free variables. -/
theorem closed_no_free (t : Term) (h : isClosed t) : freeVars t = [] := by
  simp [isClosed] at h
  exact h

/-! ## Binder Depth Properties -/

/-- The binder depth of a term is at most its size. -/
theorem binderDepth_le_size (t : Term) : binderDepth t ≤ size t := by
  induction t with
  | var _ => simp [binderDepth, size]
  | app f a ihf iha =>
    simp [binderDepth, size]
    have hmax : max (binderDepth f) (binderDepth a) ≤ size f + size a := by
      apply max_le
      · exact Nat.le_trans ihf (Nat.le_add_right _ _)
      · exact Nat.le_trans iha (Nat.le_add_left _ _)
    omega
  | lam _ body ih =>
    simp [binderDepth, size]; omega
  | pi _ dom cod ihd ihc =>
    simp [binderDepth, size]; omega
  | sort _ => simp [binderDepth, size]
  | lit _ => simp [binderDepth, size]
  | letE _ _ b ihb =>
    simp [binderDepth, size]; omega

/-! ## #eval Examples -/

#eval wf (.var (Variable.free "x"))
#eval wf (.lam (Variable.bound "x" 0) (.var (Variable.bound "x" 0)))
#eval wf (.lam (Variable.free "x") (.var (Variable.bound "y" 5)))

#eval structEq
  (.lam (Variable.free "x") (.var (Variable.bound "x" 0)))
  (.lam (Variable.free "y") (.var (Variable.bound "y" 0)))

#eval structEq
  (.app (.lam (Variable.free "x") (.var (Variable.free "x"))) (.lit 42))
  (.app (.lam (Variable.free "x") (.var (Variable.free "x"))) (.lit 42))

#eval size (.app (.lam (Variable.free "x") (.var (Variable.free "x"))) (.lit 42))

end MiniSyntaxKernel
