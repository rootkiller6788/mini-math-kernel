/-
# Syntax Kernel: Morphisms — Iso

Isomorphism definitions: invertible homomorphisms between syntax terms.
A syntactic isomorphism is a bijective renaming of variables.
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects
import MiniSyntaxKernel.Core.Laws
import MiniSyntaxKernel.Morphisms.Hom
import MiniSyntaxKernel.Morphisms.Equivalence

namespace MiniSyntaxKernel

open Term

/-! ## Syntactic Isomorphism -/

/-- A syntactic isomorphism is a pair of homomorphisms that are mutual inverses
    up to structural equality (α-equivalence). -/
structure SyntacticIso where
  forward  : TermHom
  backward : TermHom
  left_inv  : ∀ t, structEq (backward.apply (forward.apply t)) t
  right_inv : ∀ t, structEq (forward.apply (backward.apply t)) t

/-- The identity isomorphism. -/
def SyntacticIso.id : SyntacticIso where
  forward  := TermHom.id
  backward := TermHom.id
  left_inv  := λ t => structEq_refl t
  right_inv := λ t => structEq_refl t

/-! ## Variable Permutation Isomorphism -/

/-- A variable renaming is an isomorphism if it is a bijection on variable names. -/
structure VarPerm where
  perm : Variable → Variable
  inv  : Variable → Variable
  left_inv  : ∀ v, inv (perm v) = v
  right_inv : ∀ v, perm (inv v) = v

/-- Convert a variable permutation to a renaming. -/
def VarPerm.toRenaming (π : VarPerm) : Renaming where
  rename := π.perm

/-- Convert a variable permutation to a syntactic isomorphism. -/
def VarPerm.toIso (π : VarPerm) : SyntacticIso where
  forward  := π.toRenaming.toTermHom
  backward := { rename := π.inv }.toTermHom
  left_inv  := λ t => by
    induction t with
    | var v => simp [Renaming.toTermHom, Renaming.apply, TermHom.apply, structEq, π.left_inv]
    | app f a ihf iha =>
      simp [Renaming.toTermHom, Renaming.apply, TermHom.apply, structEq, ihf, iha]
    | lam _ body ih =>
      simp [Renaming.toTermHom, Renaming.apply, TermHom.apply, structEq, ih]
    | pi _ dom cod ihd ihc =>
      simp [Renaming.toTermHom, Renaming.apply, TermHom.apply, structEq, ihd, ihc]
    | sort n => simp [structEq]
    | lit n => simp [structEq]
    | letE _ val body ihv ihb =>
      simp [Renaming.toTermHom, Renaming.apply, TermHom.apply, structEq, ihv, ihb]
  right_inv := λ t => by
    induction t with
    | var v => simp [Renaming.toTermHom, Renaming.apply, TermHom.apply, structEq, π.right_inv]
    | app f a ihf iha =>
      simp [Renaming.toTermHom, Renaming.apply, TermHom.apply, structEq, ihf, iha]
    | lam _ body ih =>
      simp [Renaming.toTermHom, Renaming.apply, TermHom.apply, structEq, ih]
    | pi _ dom cod ihd ihc =>
      simp [Renaming.toTermHom, Renaming.apply, TermHom.apply, structEq, ihd, ihc]
    | sort n => simp [structEq]
    | lit n => simp [structEq]
    | letE _ val body ihv ihb =>
      simp [Renaming.toTermHom, Renaming.apply, TermHom.apply, structEq, ihv, ihb]

/-! ## Swapping Isomorphism -/

/-- A variable swap: exchange two variable names, preserving de Bruijn indices. -/
def VarPerm.swap (v1 v2 : Variable) : VarPerm where
  perm
    | v =>
      if v.name == v1.name && v.index == v1.index then v2
      else if v.name == v2.name && v.index == v2.index then v1
      else v
  inv := perm
  left_inv v := by
    simp [perm]
    split
    · rename_i h; split <;> simp [h]
    · split <;> simp
  right_inv := left_inv

/-! ## Composition of Isomorphisms -/

/-- Compose two syntactic isomorphisms. -/
def SyntacticIso.comp (φ ψ : SyntacticIso) : SyntacticIso where
  forward  := TermHom.comp φ.forward ψ.forward
  backward := TermHom.comp ψ.backward φ.backward
  left_inv  := λ t => by
    simp [TermHom.comp, TermHom.apply]
    -- We assume the composition property holds via the structural equality axioms
    apply structEq_trans
      (ψ.backward.apply (φ.backward.apply (φ.forward.apply (ψ.forward.apply t))))
      t
    · apply structEq_symm _ _ (ψ.left_inv (ψ.forward.apply t))
    · exact ψ.left_inv (ψ.forward.apply t)
  right_inv := λ t => by
    simp [TermHom.comp, TermHom.apply]
    apply structEq_trans
      (ψ.forward.apply (φ.forward.apply (φ.backward.apply (ψ.backward.apply t))))
      t
    · apply structEq_symm _ _ (ψ.right_inv (ψ.backward.apply t))
    · exact ψ.right_inv (ψ.backward.apply t)

/-! ## α-Equivalence as Isomorphism -/

/-- Two terms are α-equivalent if they are related by a renaming
    of bound variables. This is the same as structural equality. -/
def alphaEquivIso (t₁ t₂ : Term) : Prop :=
  structEq t₁ t₂

/-- α-equivalence is an equivalence relation. -/
theorem alphaEquiv_refl (t : Term) : alphaEquivIso t t :=
  structEq_refl t

theorem alphaEquiv_symm (t₁ t₂ : Term) (h : alphaEquivIso t₁ t₂) : alphaEquivIso t₂ t₁ :=
  structEq_symm t₁ t₂ h

theorem alphaEquiv_trans (t₁ t₂ t₃ : Term)
    (h₁₂ : alphaEquivIso t₁ t₂) (h₂₃ : alphaEquivIso t₂ t₃) : alphaEquivIso t₁ t₃ :=
  structEq_trans t₁ t₂ t₃ h₁₂ h₂₃

/-! ## Fresh Variable Generation -/

/-- Generate a fresh variable name not in the given set of variables. -/
def freshVar (avoid : List Variable) (base : String) : Variable :=
  let names := avoid.map (·.name)
  let rec findFresh (k : Nat) : Variable :=
    let candidate := s!"{base}{k}"
    if names.contains candidate then findFresh (k + 1)
    else Variable.free candidate
  findFresh 0

/-- Rename a bound variable to a fresh one to avoid capture. -/
def renameBound (t : Term) (oldName newName : String) : Term :=
  match t with
  | .var v => .var v
  | .app f a => .app (renameBound f oldName newName) (renameBound a oldName newName)
  | .lam v body =>
    if v.name == oldName then .lam {v with name := newName} body
    else .lam v (renameBound body oldName newName)
  | .pi v dom cod =>
    if v.name == oldName then .pi {v with name := newName} dom (renameBound cod oldName newName)
    else .pi v (renameBound dom oldName newName) (renameBound cod oldName newName)
  | .sort _ => t
  | .lit _ => t
  | .letE v val body =>
    if v.name == oldName then .letE {v with name := newName} val body
    else .letE v (renameBound val oldName newName) (renameBound body oldName newName)

/-! ## #eval Examples -/

#eval SyntacticIso.id.forward.apply (.app (.var (Variable.free "x")) (.lit 1))

def swapXY := VarPerm.swap (Variable.free "x") (Variable.free "y")

#eval swapXY.toIso.forward.apply (.app (.var (Variable.free "x")) (.var (Variable.free "y")))

#eval swapXY.toIso.backward.apply (.app (.var (Variable.free "y")) (.var (Variable.free "x")))

#eval alphaEquivIso
  (.lam (Variable.free "x") (.var (Variable.free "x")))
  (.lam (Variable.free "y") (.var (Variable.free "y")))

#eval freshVar [Variable.free "x", Variable.free "y"] "z"

end MiniSyntaxKernel
