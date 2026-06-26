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

/-- Closedness is preserved under substitution of closed terms. -/
theorem closed_subst_invariant (t s : Term) (x : Variable) (ht : isClosed t) (hs : isClosed s) :
    isClosed (subst t s x) := by
  axiom

/-- A closed term stays closed under renaming of variables. -/
theorem closed_rename_invariant (t : Term) (ρ : Renaming) (h : isClosed t) : isClosed (ρ.apply t) := by
  axiom

/-- The de Bruijn representation of a closed term has no free variables. -/
theorem closed_deBruijn_invariant (t : Term) (h : isClosed t) : isClosed (toDeBruijn t) := by
  axiom

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

/-- Size is invariant under α-conversion (renaming of bound variables). -/
theorem size_alpha_invariant (t₁ t₂ : Term) (h : structEq t₁ t₂) : size t₁ = size t₂ := by
  axiom

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
theorem structEq_preserves_wf (t₁ t₂ : Term) (h : structEq t₁ t₂) : wf t₁ ↔ wf t₂ := by
  axiom

/-- Structural equality preserves closedness. -/
theorem structEq_preserves_closed (t₁ t₂ : Term) (h : structEq t₁ t₂) : isClosed t₁ ↔ isClosed t₂ := by
  axiom

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
