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

/-- Structural equality as a decidable boolean function.
    Two terms are the same up to renaming of bound variables.
    Uses de Bruijn indices for comparison, ignoring binder names. -/
def structEq (t₁ t₂ : Term) : Bool :=
  go t₁ t₂ 0
where
  go : Term → Term → Nat → Bool
    | .var v1, .var v2, _ =>
      match decEq v1 v2 with
      | isTrue _ => true
      | isFalse _ => false
    | .app f1 a1, .app f2 a2, d => go f1 f2 d && go a1 a2 d
    | .lam _ b1, .lam _ b2, d => go b1 b2 (d + 1)
    | .pi _ d1 c1, .pi _ d2 c2, d => go d1 d2 d && go c1 c2 (d + 1)
    | .sort n1, .sort n2, _ =>
      match decEq n1 n2 with
      | isTrue _ => true
      | isFalse _ => false
    | .lit n1, .lit n2, _ =>
      match decEq n1 n2 with
      | isTrue _ => true
      | isFalse _ => false
    | .letE _ v1 b1, .letE _ v2 b2, d => go v1 v2 d && go b1 b2 (d + 1)
    | _, _, _ => false

/-- Structural equality as a Prop (the boolean version is true). -/
def StructEq (t₁ t₂ : Term) : Prop := structEq t₁ t₂ = true

/-! ## Structural Equality Laws -/

/-- The `go` helper is reflexive at any depth. -/
theorem structEq_go_refl (t : Term) (d : Nat) : structEq.go t t d = true := by
  induction t generalizing d with
  | var v =>
    unfold structEq.go
    cases h : decEq v v with
    | isTrue _ => rfl
    | isFalse hne => exfalso; exact hne rfl
  | app f a ihf iha =>
    simp [structEq.go]
    exact And.intro (ihf d) (iha d)
  | lam _ body ih =>
    simp [structEq.go]
    exact ih (d + 1)
  | pi _ dom cod ihd ihc =>
    simp [structEq.go]
    exact And.intro (ihd d) (ihc (d + 1))
  | sort n =>
    unfold structEq.go
    cases h : decEq n n with
    | isTrue _ => rfl
    | isFalse hne => exfalso; exact hne rfl
  | lit n =>
    unfold structEq.go
    cases h : decEq n n with
    | isTrue _ => rfl
    | isFalse hne => exfalso; exact hne rfl
  | letE _ val body ihv ihb =>
    simp [structEq.go]
    exact And.intro (ihv d) (ihb (d + 1))

/-- Structural equality is reflexive. -/
theorem structEq_refl (t : Term) : StructEq t t := by
  simp [StructEq, structEq, structEq_go_refl]

/-- The `go` helper is symmetric at any depth. -/
theorem structEq_go_symm (t₁ t₂ : Term) (d : Nat) (h : structEq.go t₁ t₂ d = true) : structEq.go t₂ t₁ d = true := by
  induction t₁ generalizing t₂ d with
  | var v1 =>
    cases t₂ with
    | var v2 =>
      dsimp [structEq.go] at h
      dsimp [structEq.go]
      -- h : (match decEq v1 v2 with | isTrue _ => true | isFalse _ => false) = true
      -- goal: (match decEq v2 v1 with | isTrue _ => true | isFalse _ => false) = true
      have heq : v1 = v2 := by
        cases hdec : decEq v1 v2 with
        | isTrue h_eq => exact h_eq
        | isFalse h_ne => rw [hdec] at h; simp at h
      subst heq
      cases h' : decEq v1 v1 with
      | isTrue _ => rfl
      | isFalse hne => exfalso; exact hne rfl
    | app _ _ => dsimp [structEq.go] at h; simp at h
    | lam _ _ => dsimp [structEq.go] at h; simp at h
    | pi _ _ _ => dsimp [structEq.go] at h; simp at h
    | sort _ => dsimp [structEq.go] at h; simp at h
    | lit _ => dsimp [structEq.go] at h; simp at h
    | letE _ _ _ => dsimp [structEq.go] at h; simp at h
  | app f1 a1 ihf iha =>
    cases t₂ with
    | app f2 a2 =>
      have h_simp : structEq.go f1 f2 d = true ∧ structEq.go a1 a2 d = true := by
        simpa [structEq.go] using h
      rcases h_simp with ⟨hf, ha⟩
      have hres : structEq.go f2 f1 d = true ∧ structEq.go a2 a1 d = true :=
        And.intro (ihf f2 d hf) (iha a2 d ha)
      simpa [structEq.go] using hres
    | _ => dsimp [structEq.go] at h; simp at h
  | lam v1 b1 ih =>
    cases t₂ with
    | lam v2 b2 =>
      have hres : structEq.go b2 b1 (d + 1) := ih b2 (d + 1) (by simpa [structEq.go] using h)
      simpa [structEq.go] using hres
    | _ => dsimp [structEq.go] at h; simp at h
  | pi v1 d1 c1 ihd ihc =>
    cases t₂ with
    | pi v2 d2 c2 =>
      have h_simp : structEq.go d1 d2 d = true ∧ structEq.go c1 c2 (d + 1) = true := by
        simpa [structEq.go] using h
      rcases h_simp with ⟨hd, hc⟩
      have hres : structEq.go d2 d1 d = true ∧ structEq.go c2 c1 (d + 1) = true :=
        And.intro (ihd d2 d hd) (ihc c2 (d + 1) hc)
      simpa [structEq.go] using hres
    | _ => dsimp [structEq.go] at h; simp at h
  | sort n1 =>
    cases t₂ with
    | sort n2 =>
      dsimp [structEq.go] at h ⊢
      have heq : n1 = n2 := by
        cases hdec : decEq n1 n2 with
        | isTrue h_eq => exact h_eq
        | isFalse h_ne => rw [hdec] at h; simp at h
      subst heq
      cases h' : decEq n1 n1 with
      | isTrue _ => rfl
      | isFalse hne => exfalso; exact hne rfl
    | _ => dsimp [structEq.go] at h; simp at h
  | lit n1 =>
    cases t₂ with
    | lit n2 =>
      dsimp [structEq.go] at h ⊢
      have heq : n1 = n2 := by
        cases hdec : decEq n1 n2 with
        | isTrue h_eq => exact h_eq
        | isFalse h_ne => rw [hdec] at h; simp at h
      subst heq
      cases h' : decEq n1 n1 with
      | isTrue _ => rfl
      | isFalse hne => exfalso; exact hne rfl
    | _ => dsimp [structEq.go] at h; simp at h
  | letE v1 t1 b1 ihv ihb =>
    cases t₂ with
    | letE v2 t2 b2 =>
      have h_simp : structEq.go t1 t2 d = true ∧ structEq.go b1 b2 (d + 1) = true := by
        simpa [structEq.go] using h
      rcases h_simp with ⟨ht, hb⟩
      have hres : structEq.go t2 t1 d = true ∧ structEq.go b2 b1 (d + 1) = true :=
        And.intro (ihv t2 d ht) (ihb b2 (d + 1) hb)
      simpa [structEq.go] using hres
    | _ => dsimp [structEq.go] at h; simp at h

/-- Structural equality is symmetric. -/
theorem structEq_symm (t₁ t₂ : Term) (h : StructEq t₁ t₂) : StructEq t₂ t₁ := by
  simp [StructEq, structEq] at h ⊢
  exact structEq_go_symm t₁ t₂ 0 h

/-- The `go` helper is transitive at any depth. -/
theorem structEq_go_trans (t₁ t₂ t₃ : Term) (d : Nat)
    (h₁₂ : structEq.go t₁ t₂ d) (h₂₃ : structEq.go t₂ t₃ d) : structEq.go t₁ t₃ d := by
  induction t₁ generalizing t₂ t₃ d with
  | var v1 =>
    cases t₂ with
    | var v2 =>
      cases t₃ with
      | var v3 =>
        dsimp [structEq.go] at h₁₂ h₂₃
        dsimp [structEq.go]
        have heq12 : v1 = v2 := by
          cases hdec : decEq v1 v2 with
          | isTrue h_eq => exact h_eq
          | isFalse h_ne => simp [hdec] at h₁₂
        have heq23 : v2 = v3 := by
          cases hdec : decEq v2 v3 with
          | isTrue h_eq => exact h_eq
          | isFalse h_ne => simp [hdec] at h₂₃
        subst heq12; subst heq23
        cases h' : decEq v1 v1 with
        | isTrue _ => rfl
        | isFalse hne => exfalso; exact hne rfl
      | _ => dsimp [structEq.go] at h₂₃; simp at h₂₃
    | _ => dsimp [structEq.go] at h₁₂; simp at h₁₂
  | app f1 a1 ihf iha =>
    cases t₂ with
    | app f2 a2 =>
      cases t₃ with
      | app f3 a3 =>
        have h_simp12 : structEq.go f1 f2 d = true ∧ structEq.go a1 a2 d = true := by
          simpa [structEq.go] using h₁₂
        have h_simp23 : structEq.go f2 f3 d = true ∧ structEq.go a2 a3 d = true := by
          simpa [structEq.go] using h₂₃
        rcases h_simp12 with ⟨hf12, ha12⟩
        rcases h_simp23 with ⟨hf23, ha23⟩
        have hres : structEq.go f1 f3 d = true ∧ structEq.go a1 a3 d = true :=
          And.intro (ihf f2 f3 d hf12 hf23) (iha a2 a3 d ha12 ha23)
        simpa [structEq.go] using hres
      | _ => dsimp [structEq.go] at h₂₃; simp at h₂₃
    | _ => dsimp [structEq.go] at h₁₂; simp at h₁₂
  | lam v1 b1 ih =>
    cases t₂ with
    | lam v2 b2 =>
      cases t₃ with
      | lam v3 b3 =>
        have hres : structEq.go b1 b3 (d + 1) :=
          ih b2 b3 (d + 1) (by simpa [structEq.go] using h₁₂) (by simpa [structEq.go] using h₂₃)
        simpa [structEq.go] using hres
      | _ => dsimp [structEq.go] at h₂₃; simp at h₂₃
    | _ => dsimp [structEq.go] at h₁₂; simp at h₁₂
  | pi v1 d1 c1 ihd ihc =>
    cases t₂ with
    | pi v2 d2 c2 =>
      cases t₃ with
      | pi v3 d3 c3 =>
        have h_simp12 : structEq.go d1 d2 d = true ∧ structEq.go c1 c2 (d + 1) = true := by
          simpa [structEq.go] using h₁₂
        have h_simp23 : structEq.go d2 d3 d = true ∧ structEq.go c2 c3 (d + 1) = true := by
          simpa [structEq.go] using h₂₃
        rcases h_simp12 with ⟨hd12, hc12⟩
        rcases h_simp23 with ⟨hd23, hc23⟩
        have hres : structEq.go d1 d3 d = true ∧ structEq.go c1 c3 (d + 1) = true :=
          And.intro (ihd d2 d3 d hd12 hd23) (ihc c2 c3 (d + 1) hc12 hc23)
        simpa [structEq.go] using hres
      | _ => dsimp [structEq.go] at h₂₃; simp at h₂₃
    | _ => dsimp [structEq.go] at h₁₂; simp at h₁₂
  | sort n1 =>
    cases t₂ with
    | sort n2 =>
      cases t₃ with
      | sort n3 =>
        dsimp [structEq.go] at h₁₂ h₂₃
        dsimp [structEq.go]
        have heq12 : n1 = n2 := by
          cases hdec : decEq n1 n2 with
          | isTrue h_eq => exact h_eq
          | isFalse h_ne => rw [hdec] at h₁₂; simp at h₁₂
        have heq23 : n2 = n3 := by
          cases hdec : decEq n2 n3 with
          | isTrue h_eq => exact h_eq
          | isFalse h_ne => rw [hdec] at h₂₃; simp at h₂₃
        subst heq12; subst heq23
        cases h' : decEq n1 n1 with
        | isTrue _ => rfl
        | isFalse hne => exfalso; exact hne rfl
      | _ => dsimp [structEq.go] at h₂₃; simp at h₂₃
    | _ => dsimp [structEq.go] at h₁₂; simp at h₁₂
  | lit n1 =>
    cases t₂ with
    | lit n2 =>
      cases t₃ with
      | lit n3 =>
        dsimp [structEq.go] at h₁₂ h₂₃
        dsimp [structEq.go]
        have heq12 : n1 = n2 := by
          cases hdec : decEq n1 n2 with
          | isTrue h_eq => exact h_eq
          | isFalse h_ne => rw [hdec] at h₁₂; simp at h₁₂
        have heq23 : n2 = n3 := by
          cases hdec : decEq n2 n3 with
          | isTrue h_eq => exact h_eq
          | isFalse h_ne => rw [hdec] at h₂₃; simp at h₂₃
        subst heq12; subst heq23
        cases h' : decEq n1 n1 with
        | isTrue _ => rfl
        | isFalse hne => exfalso; exact hne rfl
      | _ => dsimp [structEq.go] at h₂₃; simp at h₂₃
    | _ => dsimp [structEq.go] at h₁₂; simp at h₁₂
  | letE v1 t1 b1 ihv ihb =>
    cases t₂ with
    | letE v2 t2 b2 =>
      cases t₃ with
      | letE v3 t3 b3 =>
        have h_simp12 : structEq.go t1 t2 d = true ∧ structEq.go b1 b2 (d + 1) = true := by
          simpa [structEq.go] using h₁₂
        have h_simp23 : structEq.go t2 t3 d = true ∧ structEq.go b2 b3 (d + 1) = true := by
          simpa [structEq.go] using h₂₃
        rcases h_simp12 with ⟨ht12, hb12⟩
        rcases h_simp23 with ⟨ht23, hb23⟩
        have hres : structEq.go t1 t3 d = true ∧ structEq.go b1 b3 (d + 1) = true :=
          And.intro (ihv t2 t3 d ht12 ht23) (ihb b2 b3 (d + 1) hb12 hb23)
        simpa [structEq.go] using hres
      | _ => dsimp [structEq.go] at h₂₃; simp at h₂₃
    | _ => dsimp [structEq.go] at h₁₂; simp at h₁₂

/-- Structural equality is transitive. -/
theorem structEq_trans (t₁ t₂ t₃ : Term)
    (h₁₂ : StructEq t₁ t₂) (h₂₃ : StructEq t₂ t₃) : StructEq t₁ t₃ := by
  simp [StructEq, structEq] at h₁₂ h₂₃ ⊢
  exact structEq_go_trans t₁ t₂ t₃ 0 h₁₂ h₂₃


end MiniSyntaxKernel
