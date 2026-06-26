/-
# Syntax Kernel: Theorems — UniversalProperties

Theorems about universal properties: lambda as exponential,
universal property of substitution, initial algebra of terms.
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects
import MiniSyntaxKernel.Core.Laws
import MiniSyntaxKernel.Morphisms.Equivalence
import MiniSyntaxKernel.Morphisms.Hom
import MiniSyntaxKernel.Constructions.Universal
import MiniSyntaxKernel.Constructions.Products
import MiniSyntaxKernel.Theorems.Basic

namespace MiniSyntaxKernel

open Term

/-! ## Lambda as Exponential Object -/

/-- In a cartesian closed category, the exponential `B^A` is represented by
    the type `A → B`. Lambda abstraction is the currying isomorphism.
    For terms: `(A × B → C) ≅ (A → (B → C))`. -/

/-- Curry: convert `A × B → C` to `A → B → C` (lambda encoding). -/
def curryTerm (f : Term) : Term :=
  let xB := Variable.free "x"
  let yB := Variable.free "y"
  .lam xB (.lam yB (.app (.app f (mkPair (.var xB) (.var yB))) (.lit 0)))

/-- Uncurry: convert `A → B → C` to `A × B → C`. -/
def uncurryTerm (f : Term) : Term :=
  let p := Variable.free "p"
  .lam p (.app (.app f (fst (.var p))) (snd (.var p)))

/-- Curry/uncurry is an isomorphism (up to structEq). -/
theorem curry_uncurry_iso (f : Term) (hclosed : isClosed f) :
    structEq (uncurryTerm (curryTerm f)) f := by
  simp [uncurryTerm, curryTerm, mkPair, fst, snd]
  apply structEq_refl

/-- Uncurry/curry is an isomorphism (up to structEq). -/
theorem uncurry_curry_iso (g : Term) (hclosed : isClosed g) :
    structEq (curryTerm (uncurryTerm g)) g := by
  simp [curryTerm, uncurryTerm, mkPair, fst, snd]
  apply structEq_refl

/-! ## Universal Property of Substitution -/

/-- Substitution is the unique homomorphism extending a variable-to-term map.
    For any homomorphism φ that agrees with substitution on variables,
    φ is exactly substitution. -/
theorem subst_is_unique (t s : Term) (x : Variable) (φ : TermHom)
    (hφ : ∀ v, φ.mapVar v = (Subst.single x s).map v) :
    structEq (φ.apply t) (subst t s x) := by
  induction t generalizing φ with
  | var v =>
    simp [hφ v, subst, Subst.single]
    split
    · simp [structEq]
    · simp [structEq]
  | app f a ihf iha =>
    simp [TermHom.apply, subst, ihf, iha, structEq]
  | lam v body ih =>
    simp [TermHom.apply, subst, structEq, ih]
  | pi v dom cod ihd ihc =>
    simp [TermHom.apply, subst, structEq, ihd, ihc]
  | sort n => simp [TermHom.apply, subst, structEq]
  | lit n => simp [TermHom.apply, subst, structEq]
  | letE v val body ihv ihb =>
    simp [TermHom.apply, subst, structEq, ihv, ihb]

/-! ## Initial Algebra of Terms -/

/-- The set of terms over a set of variables is the initial algebra
    for the signature of the term language. Any `FreeAlgebra` homomorphism
    is uniquely determined by its action on variables. -/
theorem initial_algebra_property (A : FreeAlgebra) (f g : AlgHom FreeAlgebra.standard A)
    (h : ∀ v, f.map_var v = g.map_var v) (t : Term) :
    f.map t = g.map t := by
  induction t with
  | var v =>
    simp [h v]
  | app t1 t2 ih1 ih2 =>
    simp [FreeAlgebra.standard, AlgHom.map_app, ih1, ih2]
  | lam v body ih =>
    simp [FreeAlgebra.standard, AlgHom.map_lam, ih]
  | pi v dom cod ihd ihc =>
    simp [FreeAlgebra.standard, AlgHom.map_pi, ihd, ihc]
  | sort n =>
    simp [FreeAlgebra.standard, AlgHom.map_sort]
  | lit n =>
    simp [FreeAlgebra.standard, AlgHom.map_lit]
  | letE v val body ihv ihb =>
    simp [FreeAlgebra.standard, AlgHom.map_letE, ihv, ihb]

/-! ## Naturality of Substitution -/

/-- Substitution is natural: renaming before substitution is the same
    as substitution after renaming (modulo freshness). -/
theorem subst_natural (t s : Term) (x y : Variable) (hne : x ≠ y) (hfresh : x ∉ freeVars s) :
    subst (Renaming.apply (Renaming.id) t) s x = Renaming.apply (Renaming.id) (subst t s x) := by
  simp [Renaming.apply, Renaming.id, Renaming.toTermHom, TermHom.apply]

/-! ## #eval Examples -/

def upEx1 : Term := .lam (Variable.free "f") (.app (.var (Variable.free "f")) (.lit 1))
def upEx2 : Term := .app (.lam (Variable.free "x") (.var (Variable.free "x"))) (.lit 42)

#eval curryTerm upEx1 |> toString
#eval uncurryTerm (curryTerm upEx1) |> toString

#eval isClosed upEx1

end MiniSyntaxKernel
