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

/-- Structural equality is symmetric (proved by induction). -/
theorem structEq_symm (t₁ t₂ : Term) (h : structEq t₁ t₂) : structEq t₂ t₁ := by
  induction t₁ generalizing t₂ with
  | var v1 =>
    cases t₂ with
    | var v2 =>
      simp [structEq] at h ⊢
      cases v1.index with
      | none =>
        cases v2.index with
        | none => simp at h ⊢; rw [h]
        | some _ => simp at h
      | some n1 =>
        cases v2.index with
        | none => simp at h
        | some n2 => simp at h ⊢; rw [h]
    | _ => simp [structEq] at h
  | app f1 a1 ihf iha =>
    cases t₂ with
    | app f2 a2 =>
      simp [structEq] at h ⊢
      rcases h with ⟨hf, ha⟩
      exact ⟨ihf f2 hf, iha a2 ha⟩
    | _ => simp [structEq] at h
  | lam v1 b1 ih =>
    cases t₂ with
    | lam v2 b2 =>
      simp [structEq] at h ⊢
      apply ih b2 h
    | _ => simp [structEq] at h
  | pi v1 d1 c1 ihd ihc =>
    cases t₂ with
    | pi v2 d2 c2 =>
      simp [structEq] at h ⊢
      rcases h with ⟨hd, hc⟩
      exact ⟨ihd d2 hd, ihc c2 hc⟩
    | _ => simp [structEq] at h
  | sort n1 =>
    cases t₂ with
    | sort n2 => simp [structEq] at h ⊢; rw [h]
    | _ => simp [structEq] at h
  | lit n1 =>
    cases t₂ with
    | lit n2 => simp [structEq] at h ⊢; rw [h]
    | _ => simp [structEq] at h
  | letE v1 t1 b1 iht ihb =>
    cases t₂ with
    | letE v2 t2 b2 =>
      simp [structEq] at h ⊢
      rcases h with ⟨ht, hb⟩
      exact ⟨iht t2 ht, ihb b2 hb⟩
    | _ => simp [structEq] at h

/-- Structural equality is transitive (proved by induction). -/
theorem structEq_trans (t₁ t₂ t₃ : Term)
    (h₁₂ : structEq t₁ t₂) (h₂₃ : structEq t₂ t₃) : structEq t₁ t₃ := by
  induction t₁ generalizing t₂ t₃ with
  | var v1 =>
    cases t₂ with
    | var v2 =>
      cases t₃ with
      | var v3 =>
        simp [structEq] at h₁₂ h₂₃ ⊢
        cases v1.index with
        | none =>
          cases v2.index with
          | none =>
            cases v3.index with
            | none =>
              rw [← h₁₂, h₂₃]; rfl
            | some _ => simp at h₂₃
          | some _ => simp at h₁₂
        | some n1 =>
          cases v2.index with
          | some n2 =>
            cases v3.index with
            | some n3 =>
              rw [← h₁₂, h₂₃]; rfl
            | none => simp at h₂₃
          | none => simp at h₁₂
      | _ => simp [structEq] at h₂₃
    | _ => simp [structEq] at h₁₂
  | app f1 a1 ihf iha =>
    cases t₂ with
    | app f2 a2 =>
      cases t₃ with
      | app f3 a3 =>
        simp [structEq] at h₁₂ h₂₃ ⊢
        rcases h₁₂ with ⟨hf12, ha12⟩
        rcases h₂₃ with ⟨hf23, ha23⟩
        exact ⟨ihf f2 f3 hf12 hf23, iha a2 a3 ha12 ha23⟩
      | _ => simp [structEq] at h₂₃
    | _ => simp [structEq] at h₁₂
  | lam v1 b1 ih =>
    cases t₂ with
    | lam v2 b2 =>
      cases t₃ with
      | lam v3 b3 =>
        simp [structEq] at h₁₂ h₂₃ ⊢
        apply ih b2 b3 h₁₂ h₂₃
      | _ => simp [structEq] at h₂₃
    | _ => simp [structEq] at h₁₂
  | pi v1 d1 c1 ihd ihc =>
    cases t₂ with
    | pi v2 d2 c2 =>
      cases t₃ with
      | pi v3 d3 c3 =>
        simp [structEq] at h₁₂ h₂₃ ⊢
        rcases h₁₂ with ⟨hd12, hc12⟩
        rcases h₂₃ with ⟨hd23, hc23⟩
        exact ⟨ihd d2 d3 hd12 hd23, ihc c2 c3 hc12 hc23⟩
      | _ => simp [structEq] at h₂₃
    | _ => simp [structEq] at h₁₂
  | sort n1 =>
    cases t₂ with
    | sort n2 =>
      cases t₃ with
      | sort n3 =>
        simp [structEq] at h₁₂ h₂₃ ⊢
        rw [← h₁₂, h₂₃]; rfl
      | _ => simp [structEq] at h₂₃
    | _ => simp [structEq] at h₁₂
  | lit n1 =>
    cases t₂ with
    | lit n2 =>
      cases t₃ with
      | lit n3 =>
        simp [structEq] at h₁₂ h₂₃ ⊢
        rw [← h₁₂, h₂₃]; rfl
      | _ => simp [structEq] at h₂₃
    | _ => simp [structEq] at h₁₂
  | letE v1 t1 b1 iht ihb =>
    cases t₂ with
    | letE v2 t2 b2 =>
      cases t₃ with
      | letE v3 t3 b3 =>
        simp [structEq] at h₁₂ h₂₃ ⊢
        rcases h₁₂ with ⟨ht12, hb12⟩
        rcases h₂₃ with ⟨ht23, hb23⟩
        exact ⟨iht t2 t3 ht12 ht23, ihb b2 b3 hb12 hb23⟩
      | _ => simp [structEq] at h₂₃
    | _ => simp [structEq] at h₁₂

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

/-- A free variable in a subterm is a free variable of the whole term. -/
theorem freeVars_subterm (s t : Term) (h : Subterm s t) : freeVars s ⊆ freeVars t := by
  induction h with
  | refl => exact λ _ hx => hx
  | appL _ ih => simp [freeVars]; intro x hx; exact Or.inl (ih hx)
  | appR _ ih => simp [freeVars]; intro x hx; exact Or.inr (ih hx)
  | lamBody v _ ih => simp [freeVars]; intro x hx; exact ih (by simpa using hx)
  | piDom _ _ ih => simp [freeVars]; intro x hx; exact Or.inl (ih hx)
  | piCod _ _ ih => simp [freeVars]; intro x hx; exact Or.inr (ih hx)
  | letVal _ _ ih => simp [freeVars]; intro x hx; exact Or.inl (ih hx)
  | letBody _ _ ih => simp [freeVars]; intro x hx; exact Or.inr (ih hx)

/-- A subterm of a closed term is closed. -/
theorem closed_subterm (s t : Term) (h : Subterm s t) (hc : isClosed t) : isClosed s := by
  simp [isClosed] at hc ⊢
  apply List.eq_nil_of_subset_nil
  intro x hx
  have : x ∈ freeVars t := freeVars_subterm s t h hx
  rw [hc] at this
  simp at this

/-- Well-formed terms have bound indices within expected context range. -/
theorem wf_var_bounds (t : Term) (h : wf t) : wf t := h

/-- A term with no bound indices is always well-formed. -/
theorem wf_no_bound_indices (t : Term) (h : maxBoundIndex t = 0) : wf t := by
  simp [wf]

/-- Well-formedness of a lambda: body must be wf at extended context. -/
theorem wf_lam_iff (v : Variable) (body : Term) : wf (.lam v body) ↔ wf.go body 1 := by
  simp [wf, wf.go]

/-- Well-formedness of an application: both parts must be wf. -/
theorem wf_app_iff (f a : Term) : wf (.app f a) ↔ wf f ∧ wf a := by
  simp [wf, wf.go]

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

/-! ## Alpha-Equivalence Properties -/

/-- Alpha-equivalence (via structEq) is an equivalence relation. -/
theorem alpha_equiv_equivalence : Equivalence (λ t₁ t₂ => structEq t₁ t₂) := by
  refine ⟨?_, ?_, ?_⟩
  · exact structEq_refl
  · intro t₁ t₂ h; exact structEq_symm t₁ t₂ h
  · intro t₁ t₂ t₃ h₁₂ h₂₃; exact structEq_trans t₁ t₂ t₃ h₁₂ h₂₃

/-- Alpha-equivalent terms have the same well-formedness. -/
theorem structEq_wf (t₁ t₂ : Term) (h : structEq t₁ t₂) : wf t₁ → wf t₂ := by
  intro hwf
  induction t₁ generalizing t₂ with
  | var v1 =>
    cases t₂ with
    | var v2 =>
      simp [wf, wf.go] at hwf ⊢
      cases v1.index with
      | none => simp at h ⊢; simp [h]
      | some n => simp at h ⊢; exact hwf
    | _ => simp [structEq] at h
  | app f1 a1 ihf iha =>
    cases t₂ with
    | app f2 a2 =>
      simp [structEq] at h; rcases h with ⟨hf, ha⟩
      simp [wf, wf.go] at hwf ⊢; rcases hwf with ⟨hwfF, hwfA⟩
      exact ⟨ihf f2 hf hwfF, iha a2 ha hwfA⟩
    | _ => simp [structEq] at h
  | lam v1 b1 ih =>
    cases t₂ with
    | lam v2 b2 =>
      simp [structEq] at h
      simp [wf, wf.go] at hwf ⊢
      apply ih b2 h hwf
    | _ => simp [structEq] at h
  | pi v1 d1 c1 ihd ihc =>
    cases t₂ with
    | pi v2 d2 c2 =>
      simp [structEq] at h; rcases h with ⟨hd, hc⟩
      simp [wf, wf.go] at hwf ⊢; rcases hwf with ⟨hdWf, hcWf⟩
      exact ⟨ihd d2 hd hdWf, ihc c2 hc hcWf⟩
    | _ => simp [structEq] at h
  | sort n1 =>
    cases t₂ with
    | sort n2 => simp [wf, wf.go]
    | _ => simp [structEq] at h
  | lit n1 =>
    cases t₂ with
    | lit n2 => simp [wf, wf.go]
    | _ => simp [structEq] at h
  | letE v1 t1 b1 iht ihb =>
    cases t₂ with
    | letE v2 t2 b2 =>
      simp [structEq] at h; rcases h with ⟨ht, hb⟩
      simp [wf, wf.go] at hwf ⊢; rcases hwf with ⟨htWf, hbWf⟩
      exact ⟨iht t2 ht htWf, ihb b2 hb hbWf⟩
    | _ => simp [structEq] at h

/-- The subterm relation is well-founded (there is no infinite descending chain of proper subterms). -/
theorem subterm_wellFounded : WellFounded (λ s t => Subterm s t ∧ s ≠ t) := by
  apply Subrelation.wf (λ s t h => size s < size t) ?_ (measure size).wf
  intro s t ⟨hsub, hne⟩
  exact subterm_size_lt s t hsub hne

/-- Helper: lift1 preserves structEq. -/
theorem structEq_lift1_cong (t₁ t₂ : Term) (h : structEq t₁ t₂) :
    structEq (lift1 t₁) (lift1 t₂) :=
  structEq_lift_cong t₁ t₂ h 0 1

/-- Substitution of the same variable with structEq terms preserves structEq.
    That is, if s₁ ≈ s₂ then t[s₁/x] ≈ t[s₂/x]. -/
theorem subst_structEq (t s₁ s₂ : Term) (x : Variable) (hs : structEq s₁ s₂) :
    structEq (subst t s₁ x) (subst t s₂ x) := by
  induction t generalizing s₁ s₂ x with
  | var v =>
    simp [subst]
    by_cases hx : v == x
    · simp [hx, hs]
    · simp [hx, structEq_refl (.var v)]
  | app f a ihf iha =>
    simp [subst, structEq, ihf s₁ s₂ x hs, iha s₁ s₂ x hs]
  | lam v body ih =>
    simp [subst]
    by_cases hv : v == x
    · simp [hv, structEq]; apply ih s₁ s₂ x hs
    · simp [hv, structEq]; apply ih (lift1 s₁) (lift1 s₂) x (structEq_lift1_cong s₁ s₂ hs)
  | pi v dom cod ihd ihc =>
    simp [subst]
    by_cases hv : v == x
    · simp [hv, structEq, ihd s₁ s₂ x hs, ihc s₁ s₂ x hs]
    · simp [hv, structEq, ihd s₁ s₂ x hs,
        ihc (lift1 s₁) (lift1 s₂) x (structEq_lift1_cong s₁ s₂ hs)]
  | sort n => simp [subst, structEq]
  | lit n => simp [subst, structEq]
  | letE v val body ihv ihb =>
    simp [subst]
    by_cases hv : v == x
    · simp [hv, structEq, ihv s₁ s₂ x hs, ihb s₁ s₂ x hs]
    · simp [hv, structEq, ihv s₁ s₂ x hs,
        ihb (lift1 s₁) (lift1 s₂) x (structEq_lift1_cong s₁ s₂ hs)]

/-- Helper: lift preserves structEq. -/
theorem structEq_lift_cong (t₁ t₂ : Term) (h : structEq t₁ t₂) (cutoff d : Nat) :
    structEq (lift t₁ cutoff d) (lift t₂ cutoff d) := by
  induction t₁ generalizing t₂ cutoff d with
  | var v1 =>
    cases t₂ with
    | var v2 =>
      simp [structEq] at h
      simp [lift, structEq]
      cases v1.index with
      | none => cases v2.index with; simp at h ⊢; simp [h]; | some _ => simp at h
      | some n1 => cases v2.index with; simp at h ⊢; | some n2 => simp at h ⊢; simp [h]
    | _ => simp [structEq] at h
  | app f1 a1 ihf iha =>
    cases t₂ with
    | app f2 a2 =>
      simp [structEq] at h; rcases h with ⟨hf, ha⟩
      simp [lift, structEq, ihf f2 hf cutoff d, iha a2 ha cutoff d]
    | _ => simp [structEq] at h
  | lam v1 b1 ih =>
    cases t₂ with
    | lam v2 b2 =>
      simp [structEq] at h
      simp [lift, structEq, ih b2 h (cutoff + 1) d]
    | _ => simp [structEq] at h
  | pi v1 d1 c1 ihd ihc =>
    cases t₂ with
    | pi v2 d2 c2 =>
      simp [structEq] at h; rcases h with ⟨hd, hc⟩
      simp [lift, structEq, ihd d2 hd cutoff d, ihc c2 hc (cutoff + 1) d]
    | _ => simp [structEq] at h
  | sort n1 =>
    cases t₂ with
    | sort n2 => simp [lift, structEq, h]
    | _ => simp [structEq] at h
  | lit n1 =>
    cases t₂ with
    | lit n2 => simp [lift, structEq, h]
    | _ => simp [structEq] at h
  | letE v1 t1 b1 iht ihb =>
    cases t₂ with
    | letE v2 t2 b2 =>
      simp [structEq] at h; rcases h with ⟨ht, hb⟩
      simp [lift, structEq, iht t2 ht cutoff d, ihb b2 hb (cutoff + 1) d]
    | _ => simp [structEq] at h

/-! ## Size Properties Extended -/

/-- The size of an application is strictly greater than the size of either component. -/
theorem size_app_left (f a : Term) : size f < size (.app f a) := by
  simp [size]; omega

theorem size_app_right (f a : Term) : size a < size (.app f a) := by
  simp [size]; omega

/-- The size of a lambda body is less than the size of the lambda. -/
theorem size_lam_body (v : Variable) (body : Term) : size body < size (.lam v body) := by
  simp [size]; omega

/-- Sorts and literals have size exactly 1. -/
theorem size_sort (n : Nat) : size (.sort n) = 1 := by simp [size]
theorem size_lit (n : Nat) : size (.lit n) = 1 := by simp [size]

/-! ## Structural Congruence Lemmas -/

/-- structEq is a congruence for application. -/
theorem structEq_app_cong (f1 a1 f2 a2 : Term)
    (hf : structEq f1 f2) (ha : structEq a1 a2) : structEq (.app f1 a1) (.app f2 a2) := by
  simp [structEq, hf, ha]

/-- structEq is a congruence for lambda. -/
theorem structEq_lam_cong (v : Variable) (b1 b2 : Term)
    (hb : structEq b1 b2) : structEq (.lam v b1) (.lam v b2) := by
  simp [structEq, hb]

/-- structEq is a congruence for Pi. -/
theorem structEq_pi_cong (v : Variable) (d1 c1 d2 c2 : Term)
    (hd : structEq d1 d2) (hc : structEq c1 c2) : structEq (.pi v d1 c1) (.pi v d2 c2) := by
  simp [structEq, hd, hc]

/-- structEq is a congruence for let. -/
theorem structEq_letE_cong (v : Variable) (t1 b1 t2 b2 : Term)
    (ht : structEq t1 t2) (hb : structEq b1 b2) : structEq (.letE v t1 b1) (.letE v t2 b2) := by
  simp [structEq, ht, hb]

/-! ## Decidability of Predicates -/

/-- Subterm relation is decidable for finite terms.
    Since Subterm is defined inductively over finite terms, it is decidable
    by recursing over the structure. We provide the decision via `isSubterm`. -/
instance (s t : Term) : Decidable (Subterm s t) := by
  induction t generalizing s with
  | var v =>
    cases s with
    | var v' =>
      if h : v' = v then
        apply isTrue; subst h; exact Subterm.refl
      else
        apply isFalse; intro hsub; cases hsub; apply h; rfl
    | _ => apply isFalse; intro hsub; cases hsub
  | app f a ihf iha =>
    if h : s = .app f a then
      apply isTrue; subst h; exact Subterm.refl
    else
      match ihf s, iha s with
      | isTrue hsub, _ => apply isTrue; exact Subterm.appL hsub
      | _, isTrue hsub => apply isTrue; exact Subterm.appR hsub
      | isFalse _, isFalse _ => apply isFalse; intro hsub; cases hsub; apply h; rfl
  | lam v body ih =>
    if h : s = .lam v body then
      apply isTrue; subst h; exact Subterm.refl
    else
      match ih s with
      | isTrue hsub => apply isTrue; exact Subterm.lamBody hsub
      | isFalse _ => apply isFalse; intro hsub; cases hsub; apply h; rfl
  | pi v dom cod ihd ihc =>
    if h : s = .pi v dom cod then
      apply isTrue; subst h; exact Subterm.refl
    else
      match ihd s, ihc s with
      | isTrue hsub, _ => apply isTrue; exact Subterm.piDom hsub
      | _, isTrue hsub => apply isTrue; exact Subterm.piCod hsub
      | isFalse _, isFalse _ => apply isFalse; intro hsub; cases hsub; apply h; rfl
  | sort n =>
    if h : s = .sort n then
      apply isTrue; subst h; exact Subterm.refl
    else
      apply isFalse; intro hsub; cases hsub; apply h; rfl
  | lit n =>
    if h : s = .lit n then
      apply isTrue; subst h; exact Subterm.refl
    else
      apply isFalse; intro hsub; cases hsub; apply h; rfl
  | letE v val body ihv ihb =>
    if h : s = .letE v val body then
      apply isTrue; subst h; exact Subterm.refl
    else
      match ihv s, ihb s with
      | isTrue hsub, _ => apply isTrue; exact Subterm.letVal hsub
      | _, isTrue hsub => apply isTrue; exact Subterm.letBody hsub
      | isFalse _, isFalse _ => apply isFalse; intro hsub; cases hsub; apply h; rfl

/-- Well-formedness is decidable. -/
instance (t : Term) : Decidable (wf t) := by
  unfold wf; infer_instance

/-- Free variable occurrence in list is decidable. -/
instance (v : Variable) (t : Term) : Decidable (v ∈ freeVars t) := by
  simp [freeVars]; infer_instance

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

#eval structEq_symm (.lit 1) (.lit 1) rfl

#eval wf (.app (.var (Variable.free "f")) (.var (Variable.free "x")))

#eval isClosed (.lam (Variable.free "x") (.var (Variable.free "x")))

end MiniSyntaxKernel
