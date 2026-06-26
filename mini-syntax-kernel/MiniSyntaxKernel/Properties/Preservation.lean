/-
# Syntax Kernel: Properties — Preservation

Preservation properties: what properties of terms are preserved under
various morphisms, transformations, and constructions.
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects
import MiniSyntaxKernel.Core.Laws
import MiniSyntaxKernel.Morphisms.Equivalence
import MiniSyntaxKernel.Properties.Invariants

namespace MiniSyntaxKernel

open Term

/-! ## Preservation Under Substitution -/

/-- Substitution preserves the well-formedness property. -/
theorem subst_preserves_wf (t s : Term) (x : Variable) (ht : wf t) (hs : wf s) : wf (subst t s x) :=
  wf_subst_invariant t s x ht hs

/-- Substitution preserves the ``valid'' property. -/
theorem subst_preserves_valid (t s : Term) (x : Variable) (ht : valid t) (hs : valid s) : valid (subst t s x) := by
  simp [valid]
  apply And.intro
  · exact wf_subst_invariant t s x ht.1 hs.1
  · exact ht.2

/-- Substitution preserves structural equality when both terms
    have the same structure. Proved by induction on the first term. -/
theorem subst_preserves_structEq_same (t s₁ s₂ : Term) (x : Variable)
    (h : structEq s₁ s₂) : structEq (subst t s₁ x) (subst t s₂ x) := by
  induction t generalizing s₁ s₂ x with
  | var v =>
    simp [subst]
    by_cases hx : v == x
    · simp [hx, h]
    · simp [hx, structEq_refl (.var v)]
  | app f a ihf iha =>
    simp [subst, structEq, ihf s₁ s₂ x h, iha s₁ s₂ x h]
  | lam v body ih =>
    simp [subst]
    by_cases hv : v == x
    · simp [hv, structEq, ih s₁ s₂ x h]
    · simp [hv, structEq, ih (lift1 s₁) (lift1 s₂) x (structEq_lift1_cong s₁ s₂ h)]
  | pi v dom cod ihd ihc =>
    simp [subst]
    by_cases hv : v == x
    · simp [hv, structEq, ihd s₁ s₂ x h, ihc s₁ s₂ x h]
    · simp [hv, structEq, ihd s₁ s₂ x h,
        ihc (lift1 s₁) (lift1 s₂) x (structEq_lift1_cong s₁ s₂ h)]
  | sort n => simp [subst, structEq]
  | lit n => simp [subst, structEq]
  | letE v val body ihv ihb =>
    simp [subst]
    by_cases hv : v == x
    · simp [hv, structEq, ihv s₁ s₂ x h, ihb s₁ s₂ x h]
    · simp [hv, structEq, ihv s₁ s₂ x h,
        ihb (lift1 s₁) (lift1 s₂) x (structEq_lift1_cong s₁ s₂ h)]

/-! ## Preservation Under Renaming -/

/-- Renaming preserves the size of a term. -/
theorem renaming_preserves_size (t : Term) (ρ : Renaming) : size (ρ.apply t) = size t := by
  induction t with
  | var v => simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, size]
  | app f a ihf iha =>
    simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, size, ihf, iha]
  | lam _ body ih =>
    simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, size, ih]
  | pi _ dom cod ihd ihc =>
    simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, size, ihd, ihc]
  | sort _ => simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, size]
  | lit _ => simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, size]
  | letE _ val body ihv ihb =>
    simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, size, ihv, ihb]

/-- Renaming preserves the binder depth. -/
theorem renaming_preserves_binderDepth (t : Term) (ρ : Renaming) : binderDepth (ρ.apply t) = binderDepth t := by
  induction t with
  | var v => simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, binderDepth]
  | app f a ihf iha =>
    simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, binderDepth, ihf, iha]
  | lam _ body ih =>
    simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, binderDepth, ih]
  | pi _ dom cod ihd ihc =>
    simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, binderDepth, ihd, ihc]
  | sort _ => simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, binderDepth]
  | lit _ => simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, binderDepth]
  | letE _ val body ihv ihb =>
    simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, binderDepth, ihv, ihb]

/-! ## Preservation Under Alpha-Equivalence -/

/-- Alpha-equivalent terms have the same size. -/
theorem alpha_preserves_size (t₁ t₂ : Term) (h : alphaEquiv t₁ t₂) : size t₁ = size t₂ := by
  rcases Quotient.exact h with h_eq
  exact size_alpha_invariant t₁ t₂ h_eq

/-- Alpha-equivalent terms have the same binder depth.
    Binder depth depends on term structure, preserved by structEq. -/
theorem alpha_preserves_binderDepth (t₁ t₂ : Term) (h : alphaEquiv t₁ t₂) : binderDepth t₁ = binderDepth t₂ := by
  -- alphaEquiv and structEq give the same boolean result on the de Bruijn structure
  -- so we prove by induction that if alphaEquiv t₁ t₂ then binderDepth t₁ = binderDepth t₂
  induction t₁ generalizing t₂ with
  | var v1 =>
    cases t₂ with
    | var v2 => simp [alphaEquiv] at h; cases v1.index <;> cases v2.index <;> simp [binderDepth] at h ⊢; try simp [h]
    | _ => simp [alphaEquiv] at h
  | app f1 a1 ihf iha =>
    cases t₂ with
    | app f2 a2 =>
      simp [alphaEquiv] at h
      have hf : alphaEquiv f1 f2 := by
        have := h; simp [alphaEquiv] at this; exact this.1
      have ha : alphaEquiv a1 a2 := by
        have := h; simp [alphaEquiv] at this; exact this.2
      simp [binderDepth, ihf f2 hf, iha a2 ha]
    | _ => simp [alphaEquiv] at h
  | lam v1 b1 ih =>
    cases t₂ with
    | lam v2 b2 =>
      simp [alphaEquiv] at h
      simp [binderDepth, ih b2 h]
    | _ => simp [alphaEquiv] at h
  | pi v1 d1 c1 ihd ihc =>
    cases t₂ with
    | pi v2 d2 c2 =>
      simp [alphaEquiv] at h
      have hd : alphaEquiv d1 d2 := by
        simp [alphaEquiv] at h; exact h.1
      have hc : alphaEquiv c1 c2 := by
        simp [alphaEquiv] at h; exact h.2
      simp [binderDepth, ihd d2 hd, ihc c2 hc]
    | _ => simp [alphaEquiv] at h
  | sort n1 =>
    cases t₂ with
    | sort n2 => simp [binderDepth]
    | _ => simp [alphaEquiv] at h
  | lit n1 =>
    cases t₂ with
    | lit n2 => simp [binderDepth]
    | _ => simp [alphaEquiv] at h
  | letE v1 t1 b1 iht ihb =>
    cases t₂ with
    | letE v2 t2 b2 =>
      simp [alphaEquiv] at h
      have ht : alphaEquiv t1 t2 := by
        simp [alphaEquiv] at h; exact h.1
      have hb : alphaEquiv b1 b2 := by
        simp [alphaEquiv] at h; exact h.2
      simp [binderDepth, iht t2 ht, ihb b2 hb]
    | _ => simp [alphaEquiv] at h

/-- Alpha-equivalent terms have the same free variables count.
    The list metadata (length) is preserved by structural equality. -/
theorem alpha_preserves_freeVarCount (t₁ t₂ : Term) (h : alphaEquiv t₁ t₂) :
    (freeVars t₁).length = (freeVars t₂).length := by
  induction t₁ generalizing t₂ with
  | var v1 =>
    cases t₂ with
    | var v2 => simp [alphaEquiv] at h; cases v1.index <;> cases v2.index <;> simp [freeVars] at h ⊢; try simp [h]
    | _ => simp [alphaEquiv] at h
  | app f1 a1 ihf iha =>
    cases t₂ with
    | app f2 a2 =>
      simp [alphaEquiv] at h
      have hf : alphaEquiv f1 f2 := by simp [alphaEquiv] at h; exact h.1
      have ha : alphaEquiv a1 a2 := by simp [alphaEquiv] at h; exact h.2
      simp [freeVars, ihf f2 hf, iha a2 ha]
    | _ => simp [alphaEquiv] at h
  | lam v1 b1 ih =>
    cases t₂ with
    | lam v2 b2 =>
      simp [alphaEquiv] at h
      simp [freeVars, ih b2 h]
    | _ => simp [alphaEquiv] at h
  | pi v1 d1 c1 ihd ihc =>
    cases t₂ with
    | pi v2 d2 c2 =>
      simp [alphaEquiv] at h
      have hd : alphaEquiv d1 d2 := by simp [alphaEquiv] at h; exact h.1
      have hc : alphaEquiv c1 c2 := by simp [alphaEquiv] at h; exact h.2
      simp [freeVars, ihd d2 hd, ihc c2 hc]
    | _ => simp [alphaEquiv] at h
  | sort n1 =>
    cases t₂ with
    | sort n2 => simp [freeVars]
    | _ => simp [alphaEquiv] at h
  | lit n1 =>
    cases t₂ with
    | lit n2 => simp [freeVars]
    | _ => simp [alphaEquiv] at h
  | letE v1 t1 b1 iht ihb =>
    cases t₂ with
    | letE v2 t2 b2 =>
      simp [alphaEquiv] at h
      have ht : alphaEquiv t1 t2 := by simp [alphaEquiv] at h; exact h.1
      have hb : alphaEquiv b1 b2 := by simp [alphaEquiv] at h; exact h.2
      simp [freeVars, iht t2 ht, ihb b2 hb]
    | _ => simp [alphaEquiv] at h

/-! ## Preservation Under Term Construction -/

/-- The subterm relation preserves well-formedness: subterms of well-formed terms are well-formed. -/
theorem subterm_preserves_wf (s t : Term) (h : Subterm s t) (hwfT : wf t) : wf s := by
  induction h with
  | refl => exact hwfT
  | appL h ih =>
    simp [wf] at hwfT
    exact ih hwfT.1
  | appR h ih =>
    simp [wf] at hwfT
    exact ih hwfT.2
  | lamBody h ih =>
    simp [wf] at hwfT
    exact ih hwfT
  | piDom h ih =>
    simp [wf] at hwfT
    exact ih hwfT.1
  | piCod h ih =>
    simp [wf] at hwfT
    exact ih hwfT.2
  | letVal h ih =>
    simp [wf] at hwfT
    exact ih hwfT.1
  | letBody h ih =>
    simp [wf] at hwfT
    exact ih hwfT.2

/-- Constructing a lambda term preserves closedness of the body. -/
theorem lam_preserves_closed_body (v : Variable) (body : Term) (h : isClosed body) : isClosed (.lam v body) := by
  simp [isClosed, freeVars] at h ⊢
  omega

/-- Application preserves closedness. -/
theorem app_preserves_closed (f a : Term) (hf : isClosed f) (ha : isClosed a) : isClosed (.app f a) := by
  simp [isClosed, freeVars, hf, ha]

/-! ## Preservation Under Lifting -/

/-- Lifting preserves the size of a term. -/
theorem lift_preserves_size (t : Term) (cutoff d : Nat) : size (lift t cutoff d) = size t := by
  induction t generalizing cutoff d with
  | var v => simp [lift, size]
  | app f a ihf iha =>
    simp [lift, size, ihf cutoff d, iha cutoff d]
  | lam _ body ih =>
    simp [lift, size, ih (cutoff + 1) d]
  | pi _ dom cod ihd ihc =>
    simp [lift, size, ihd cutoff d, ihc (cutoff + 1) d]
  | sort _ => simp [lift, size]
  | lit _ => simp [lift, size]
  | letE _ val body ihv ihb =>
    simp [lift, size, ihv cutoff d, ihb (cutoff + 1) d]

/-- Lifting preserves structural equality. -/
theorem lift_preserves_structEq (t₁ t₂ : Term) (cutoff d : Nat) (h : structEq t₁ t₂) :
    structEq (lift t₁ cutoff d) (lift t₂ cutoff d) :=
  structEq_lift_cong t₁ t₂ h cutoff d

/-! ## #eval Examples -/

#eval size (lift wfEx 0 2) == size wfEx

#eval subst_preserves_wf wfEx (.lit 42) (Variable.free "x") (by native_decide) (by native_decide)

#eval renaming_preserves_size (.app (.var (Variable.free "x")) (.lit 1)) Renaming.id

#eval app_preserves_closed (.lit 1) (.lit 2) (by decide) (by decide)

end MiniSyntaxKernel
