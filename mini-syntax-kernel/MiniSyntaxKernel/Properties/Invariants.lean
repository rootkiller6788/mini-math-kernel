/-
# Syntax Kernel: Properties — Invariants

Invariant properties of terms: properties preserved under substitution,
renaming, and α-equivalence.
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects
import MiniSyntaxKernel.Core.Laws
import MiniSyntaxKernel.Morphisms.Equivalence

namespace MiniSyntaxKernel

open Term

/-! ## Well-formedness Invariants -/

/-- Well-formedness is preserved under lifting. -/
theorem wf_lift_invariant (t : Term) (cutoff d : Nat) (hwf : wf t) : wf (lift t cutoff d) :=
  lift_wf t cutoff d hwf

/-- Well-formedness is preserved under single-variable substitution. -/
theorem wf_subst_invariant (t s : Term) (x : Variable) (hwfT : wf t) (hwfS : wf s) :
    wf (subst t s x) := by
  induction t generalizing s x with
  | var v =>
    simp [subst]
    split
    · exact hwfS
    · simpa [wf] using hwfT
  | app f a ihf iha =>
    simp [subst, wf] at hwfT ⊢
    exact And.intro (ihf s x hwfT.1 hwfS) (iha s x hwfT.2 hwfS)
  | lam v body ih =>
    simp [subst, wf] at hwfT ⊢
    split
    · exact hwfT
    · apply ih (lift1 s) x hwfT hwfS
  | pi v dom cod ihd ihc =>
    simp [subst, wf] at hwfT ⊢
    split
    · exact And.intro (ihd s x hwfT.1 hwfS) hwfT.2
    · apply And.intro (ihd s x hwfT.1 hwfS) (ihc (lift1 s) x hwfT.2 hwfS)
  | sort n => simp [subst, wf]
  | lit n => simp [subst, wf]
  | letE v val body ihv ihb =>
    simp [subst, wf] at hwfT ⊢
    split
    · exact And.intro (ihv s x hwfT.1 hwfS) hwfT.2
    · apply And.intro (ihv s x hwfT.1 hwfS) (ihb (lift1 s) x hwfT.2 hwfS)

/-! ## Closedness Invariants -/

/-- Closedness is preserved under substitution of closed terms (proved by induction). -/
theorem closed_subst_invariant (t s : Term) (x : Variable) (ht : isClosed t) (hs : isClosed s) :
    isClosed (subst t s x) := by
  induction t generalizing s x with
  | var v =>
    simp [subst]
    by_cases hx : v == x
    · simp [hx, isClosed, hs]
    · simp [hx, isClosed]; simp [isClosed] at ht; exact ht
  | app f a ihf iha =>
    simp [subst, isClosed, freeVars] at ht ⊢
    rcases ht with ⟨hf, ha⟩
    have hf' := ihf s x hf hs
    have ha' := iha s x ha hs
    simp [isClosed, freeVars] at hf' ha' ⊢
    simp [hf', ha']
  | lam v body ih =>
    simp [subst]
    by_cases hv : v == x
    · simp [hv, isClosed, freeVars]; simp [isClosed] at ht; exact ht
    · simp [hv, isClosed, freeVars]
      simp [isClosed, freeVars] at ht
      -- When v ≠ x, the body stays closed under subst with lifted s
      have hlift : isClosed (lift1 s) := by
        have : freeVars (lift1 s) = [] := by
          simp [lift1, lift, freeVars, isClosed] at hs ⊢
          exact hs
        simp [isClosed, this]
      have hbody := ih (lift1 s) x ht hlift
      simp [isClosed, freeVars] at hbody ⊢
      exact hbody
  | pi v dom cod ihd ihc =>
    simp [subst]
    by_cases hv : v == x
    · simp [hv, isClosed, freeVars]
      simp [isClosed, freeVars] at ht; rcases ht with ⟨hd, hc⟩
      have hd' := ihd s x hd hs
      simp [isClosed, freeVars] at hd' hc ⊢
      simp [hd', hc]
    · simp [hv, isClosed, freeVars]
      simp [isClosed, freeVars] at ht; rcases ht with ⟨hd, hc⟩
      have hd' := ihd s x hd hs
      have hlift : isClosed (lift1 s) := by
        have : freeVars (lift1 s) = [] := by
          simp [lift1, lift, freeVars, isClosed] at hs ⊢
          exact hs
        simp [isClosed, this]
      have hc' := ihc (lift1 s) x hc hlift
      simp [isClosed, freeVars] at hd' hc' ⊢
      simp [hd', hc']
  | sort n => simp [subst, isClosed, freeVars]
  | lit n => simp [subst, isClosed, freeVars]
  | letE v val body ihv ihb =>
    simp [subst]
    by_cases hv : v == x
    · simp [hv, isClosed, freeVars]
      simp [isClosed, freeVars] at ht; rcases ht with ⟨hv', hb⟩
      have hv'' := ihv s x hv' hs
      simp [isClosed, freeVars] at hv'' hb ⊢
      simp [hv'', hb]
    · simp [hv, isClosed, freeVars]
      simp [isClosed, freeVars] at ht; rcases ht with ⟨hv', hb⟩
      have hv'' := ihv s x hv' hs
      have hlift : isClosed (lift1 s) := by
        have : freeVars (lift1 s) = [] := by
          simp [lift1, lift, freeVars, isClosed] at hs ⊢
          exact hs
        simp [isClosed, this]
      have hb' := ihb (lift1 s) x hb hlift
      simp [isClosed, freeVars] at hv'' hb' ⊢
      simp [hv'', hb']

/-- A closed term stays closed under renaming of variables. -/
theorem closed_rename_invariant (t : Term) (ρ : Renaming) (h : isClosed t) : isClosed (ρ.apply t) := by
  induction t with
  | var v =>
    simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, isClosed, freeVars]
    simp [isClosed] at h
    exact h
  | app f a ihf iha =>
    simp [isClosed, freeVars] at h; rcases h with ⟨hf, ha⟩
    simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, isClosed, freeVars, ihf hf, iha ha]
  | lam v body ih =>
    simp [isClosed, freeVars] at h
    simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, isClosed, freeVars, ih h]
  | pi v dom cod ihd ihc =>
    simp [isClosed, freeVars] at h; rcases h with ⟨hd, hc⟩
    simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, isClosed, freeVars, ihd hd, ihc hc]
  | sort n => simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, isClosed, freeVars]
  | lit n => simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, isClosed, freeVars]
  | letE v val body ihv ihb =>
    simp [isClosed, freeVars] at h; rcases h with ⟨hv, hb⟩
    simp [Renaming.apply, Renaming.toTermHom, TermHom.apply, isClosed, freeVars, ihv hv, ihb hb]

/-- The de Bruijn representation preserves closedness:
    converting to nameless form removes free variable names but preserves
    the structural closedness property. -/
theorem closed_deBruijn_invariant (t : Term) (h : isClosed t) : isClosed (toDeBruijn t) := by
  induction t with
  | var v =>
    simp [toDeBruijn, toDeBruijn.go, isClosed, freeVars]
    simp [isClosed] at h; exact h
  | app f a ihf iha =>
    simp [toDeBruijn, toDeBruijn.go, isClosed, freeVars]
    simp [isClosed] at h; rcases h with ⟨hf, ha⟩
    simp [ihf hf, iha ha]
  | lam v body ih =>
    simp [toDeBruijn, toDeBruijn.go, isClosed, freeVars]
    simp [isClosed] at h
    simp [ih h]
  | pi v dom cod ihd ihc =>
    simp [toDeBruijn, toDeBruijn.go, isClosed, freeVars]
    simp [isClosed] at h; rcases h with ⟨hd, hc⟩
    simp [ihd hd, ihc hc]
  | sort n => simp [toDeBruijn, toDeBruijn.go, isClosed, freeVars]
  | lit n => simp [toDeBruijn, toDeBruijn.go, isClosed, freeVars]
  | letE v val body ihv ihb =>
    simp [toDeBruijn, toDeBruijn.go, isClosed, freeVars]
    simp [isClosed] at h; rcases h with ⟨hv, hb⟩
    simp [ihv hv, ihb hb]

/-! ## Size Invariants -/

/-- Substitution does not increase size beyond a linear bound. -/
theorem size_subst_bound (t s : Term) (x : Variable) :
    size (subst t s x) ≤ size t * size s := by
  induction t generalizing s x with
  | var v =>
    simp [subst, size]
    split
    · exact Nat.one_le_mul (by omega) (size_pos s)
    · simp [size]
  | app f a ihf iha =>
    simp [subst, size]
    have hsum : size (subst f s x) + size (subst a s x) ≤ size f * size s + size a * size s := by
      exact Nat.add_le_add ihf iha
    omega
  | lam v body ih =>
    simp [subst, size]
    split
    · simp [size]
    · have h := ih (lift1 s) x
      omega
  | pi v dom cod ihd ihc =>
    simp [subst, size]
    split
    · omega
    · omega
  | sort n => simp [subst, size]; omega
  | lit n => simp [subst, size]; omega
  | letE v val body ihv ihb =>
    simp [subst, size]
    split
    · omega
    · omega

/-- Size is invariant under α-conversion (renaming of bound variables).
    Proved by structural induction on the structEq relation. -/
theorem size_alpha_invariant (t₁ t₂ : Term) (h : structEq t₁ t₂) : size t₁ = size t₂ := by
  induction t₁ generalizing t₂ with
  | var v1 =>
    cases t₂ with
    | var v2 => simp [structEq] at h; simp [size]
    | _ => simp [structEq] at h
  | app f1 a1 ihf iha =>
    cases t₂ with
    | app f2 a2 =>
      simp [structEq] at h; rcases h with ⟨hf, ha⟩
      simp [size, ihf f2 hf, iha a2 ha]
    | _ => simp [structEq] at h
  | lam v1 b1 ih =>
    cases t₂ with
    | lam v2 b2 =>
      simp [structEq] at h; simp [size, ih b2 h]
    | _ => simp [structEq] at h
  | pi v1 d1 c1 ihd ihc =>
    cases t₂ with
    | pi v2 d2 c2 =>
      simp [structEq] at h; rcases h with ⟨hd, hc⟩
      simp [size, ihd d2 hd, ihc c2 hc]
    | _ => simp [structEq] at h
  | sort n1 =>
    cases t₂ with
    | sort n2 => simp [size]
    | _ => simp [structEq] at h
  | lit n1 =>
    cases t₂ with
    | lit n2 => simp [size]
    | _ => simp [structEq] at h
  | letE v1 t1 b1 iht ihb =>
    cases t₂ with
    | letE v2 t2 b2 =>
      simp [structEq] at h; rcases h with ⟨ht, hb⟩
      simp [size, iht t2 ht, ihb b2 hb]
    | _ => simp [structEq] at h

/-! ## Binder Depth Invariants -/

/-- Binder depth is invariant under substitution of terms with no binders. -/
theorem binderDepth_subst_invariant (t s : Term) (x : Variable)
    (hsNoBinders : binderDepth s = 0) : binderDepth (subst t s x) ≤ binderDepth t + binderDepth s := by
  induction t generalizing s x with
  | var v =>
    simp [subst, binderDepth]
    split
    · simp [hsNoBinders]
    · simp
  | app f a ihf iha =>
    simp [subst, binderDepth]
    omega
  | lam v body ih =>
    simp [subst, binderDepth]
    split
    · simp
    · omega
  | pi v dom cod ihd ihc =>
    simp [subst, binderDepth]
    split
    · omega
    · omega
  | sort n => simp [subst, binderDepth]
  | lit n => simp [subst, binderDepth]
  | letE v val body ihv ihb =>
    simp [subst, binderDepth]
    split
    · omega
    · omega

/-! ## Structural Invariants -/

/-- Structural equality preserves well-formedness. -/
theorem structEq_preserves_wf (t₁ t₂ : Term) (h : structEq t₁ t₂) : wf t₁ ↔ wf t₂ :=
  ⟨structEq_wf t₁ t₂ h, structEq_wf t₂ t₁ (structEq_symm t₁ t₂ h)⟩

/-- Structural equality preserves closedness. -/
theorem structEq_preserves_closed (t₁ t₂ : Term) (h : structEq t₁ t₂) : isClosed t₁ ↔ isClosed t₂ := by
  induction t₁ generalizing t₂ with
  | var v1 =>
    cases t₂ with
    | var v2 =>
      simp [structEq] at h
      simp [isClosed, freeVars]
      -- if both are vars, structEq means they have same de Bruijn index pattern
      -- so both have same free variable status
      simp
    | _ => simp [structEq] at h
  | app f1 a1 ihf iha =>
    cases t₂ with
    | app f2 a2 =>
      simp [structEq] at h; rcases h with ⟨hf, ha⟩
      simp [isClosed, freeVars]
      rcases ihf f2 hf with ⟨hf1, hf2⟩
      rcases iha a2 ha with ⟨ha1, ha2⟩
      constructor
      · intro h; rcases h with ⟨hfv, hav⟩; exact ⟨hf2 hfv, ha2 hav⟩
      · intro h; rcases h with ⟨hfv, hav⟩; exact ⟨hf1 hfv, ha1 hav⟩
    | _ => simp [structEq] at h
  | lam v1 b1 ih =>
    cases t₂ with
    | lam v2 b2 =>
      simp [structEq] at h
      simp [isClosed, freeVars]
      rcases ih b2 h with ⟨hb1, hb2⟩
      constructor
      · intro h; exact hb2 h
      · intro h; exact hb1 h
    | _ => simp [structEq] at h
  | pi v1 d1 c1 ihd ihc =>
    cases t₂ with
    | pi v2 d2 c2 =>
      simp [structEq] at h; rcases h with ⟨hd, hc⟩
      simp [isClosed, freeVars]
      rcases ihd d2 hd with ⟨hd1, hd2⟩
      rcases ihc c2 hc with ⟨hc1, hc2⟩
      constructor
      · intro h; rcases h with ⟨hdv, hcv⟩; exact ⟨hd2 hdv, hc2 hcv⟩
      · intro h; rcases h with ⟨hdv, hcv⟩; exact ⟨hd1 hdv, hc1 hcv⟩
    | _ => simp [structEq] at h
  | sort n1 =>
    cases t₂ with
    | sort n2 => simp [structEq, isClosed, freeVars]
    | _ => simp [structEq] at h
  | lit n1 =>
    cases t₂ with
    | lit n2 => simp [structEq, isClosed, freeVars]
    | _ => simp [structEq] at h
  | letE v1 t1 b1 iht ihb =>
    cases t₂ with
    | letE v2 t2 b2 =>
      simp [structEq] at h; rcases h with ⟨ht, hb⟩
      simp [isClosed, freeVars]
      rcases iht t2 ht with ⟨ht1, ht2⟩
      rcases ihb b2 hb with ⟨hb1, hb2⟩
      constructor
      · intro h; rcases h with ⟨htv, hbv⟩; exact ⟨ht2 htv, hb2 hbv⟩
      · intro h; rcases h with ⟨htv, hbv⟩; exact ⟨ht1 htv, hb1 hbv⟩
    | _ => simp [structEq] at h

/-- Variable count is invariant under substitution when the variable is fresh. -/
theorem freeVars_subst_fresh (t s : Term) (x : Variable) (h : x ∉ freeVars t) :
    freeVars (subst t s x) = freeVars t := by
  induction t generalizing s x with
  | var v =>
    simp [subst, freeVars]
    intro hnot; split
    · exfalso; exact h hnot
    · rfl
  | app f a ihf iha =>
    simp [subst, freeVars, h]
    simp [ihf s x (by intro hm; apply h; simp [freeVars, hm]),
          iha s x (by intro hm; apply h; simp [freeVars, hm])]
  | lam v body ih =>
    simp [subst, freeVars]
    split
    · simp
    · simp [ih (lift1 s) x (by intro hm; apply h; simp [freeVars, hm])]
  | pi v dom cod ihd ihc =>
    simp [subst, freeVars]
    split
    · simp [ihd s x (by intro hm; apply h; simp [freeVars, hm])]
    · simp [ihd s x (by intro hm; apply h; simp [freeVars, hm]),
            ihc (lift1 s) x (by intro hm; apply h; simp [freeVars, hm])]
  | sort n => simp [subst, freeVars]
  | lit n => simp [subst, freeVars]
  | letE v val body ihv ihb =>
    simp [subst, freeVars]
    split
    · simp [ihv s x (by intro hm; apply h; simp [freeVars, hm])]
    · simp [ihv s x (by intro hm; apply h; simp [freeVars, hm]),
            ihb (lift1 s) x (by intro hm; apply h; simp [freeVars, hm])]

/-! ## #eval Examples -/

def wfEx : Term := .lam (Variable.bound "f" 0) (.app (.var (Variable.bound "f" 0)) (.lit 1))
#eval wf wfEx
#eval wf (subst wfEx (.lit 42) (Variable.free "x"))

#eval isClosed (.lam (Variable.bound "x" 0) (.var (Variable.bound "x" 0)))

#eval size wfEx
#eval binderDepth wfEx

end MiniSyntaxKernel
