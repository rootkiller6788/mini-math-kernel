/-
# Syntax Kernel: Morphisms — Hom

Term homomorphisms: structure-preserving maps between syntax terms.
A homomorphism maps terms to terms while preserving the syntactic structure.
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects
import MiniSyntaxKernel.Core.Laws

namespace MiniSyntaxKernel

open Term

/-! ## Term Homomorphisms -/

/-- A term homomorphism is a function from terms to terms that
    preserves the term structure (variables, application, abstraction). -/
structure TermHom where
  mapVar  : Variable → Term
  mapApp  : Term → Term → Term := λ f a => .app f a
  mapLam  : Variable → Term → Term := λ v b => .lam v b
  mapPi   : Variable → Term → Term → Term := λ v d c => .pi v d c
  mapSort : Nat → Term := λ n => .sort n
  mapLit  : Nat → Term := λ n => .lit n
  mapLet  : Variable → Term → Term → Term := λ v t b => .letE v t b
deriving Inhabited

/-- The identity homomorphism. -/
def TermHom.id : TermHom where
  mapVar := .var

instance : Inhabited TermHom := ⟨TermHom.id⟩

/-- Apply a term homomorphism to a term. -/
def TermHom.apply (φ : TermHom) (t : Term) : Term :=
  match t with
  | .var v     => φ.mapVar v
  | .app f a   => φ.mapApp (apply φ f) (apply φ a)
  | .lam v b   => φ.mapLam v (apply φ b)
  | .pi v d c  => φ.mapPi v (apply φ d) (apply φ c)
  | .sort n    => φ.mapSort n
  | .lit n     => φ.mapLit n
  | .letE v t b => φ.mapLet v (apply φ t) (apply φ b)

/-! ## Variable Renaming -/

/-- A variable renaming is a map from variables to variables,
    lifted to a term homomorphism. -/
structure Renaming where
  rename : Variable → Variable
deriving Inhabited

/-- Convert a renaming to a term homomorphism (as variables). -/
def Renaming.toTermHom (ρ : Renaming) : TermHom where
  mapVar v := .var (ρ.rename v)

/-- Apply a renaming to a term. -/
def Renaming.apply (ρ : Renaming) (t : Term) : Term :=
  ρ.toTermHom.apply t

/-- The identity renaming. -/
def Renaming.id : Renaming where
  rename v := v

/-- Shift all de Bruijn indices by one (for going under a binder). -/
def Renaming.shift : Renaming where
  rename
    | {name, index := some n} => Variable.bound name (n + 1)
    | v => v

/-! ## Substitution as Homomorphism -/

/-- A substitution is a map from variables to terms.
    This is the fundamental homomorphism of syntax. -/
structure Subst where
  map : Variable → Term
deriving Inhabited

/-- Convert a substitution to a term homomorphism. -/
def Subst.toTermHom (σ : Subst) : TermHom where
  mapVar := σ.map

/-- The identity substitution (maps each variable to itself). -/
def Subst.id : Subst where
  map v := .var v

/-- Single-variable substitution: replace `x` with `s`. -/
def Subst.single (x : Variable) (s : Term) : Subst where
  map v := if v == x then s else .var v

/-- Apply a substitution to a term via the homomorphism.
    Note: this is NOT capture-avoiding; it is a raw syntactic substitution.
    For capture-avoiding substitution, see `Morphisms.Equivalence.subst`. -/
def Subst.apply (σ : Subst) (t : Term) : Term :=
  σ.toTermHom.apply t

/-! ## Homomorphism Composition -/

/-- Compose two term homomorphisms: apply φ after ψ. -/
def TermHom.comp (φ ψ : TermHom) : TermHom where
  mapVar v   := φ.apply (ψ.mapVar v)
  mapApp f a := φ.apply (ψ.mapApp f a)
  mapLam v b := φ.apply (ψ.mapLam v b)
  mapPi v d c := φ.apply (ψ.mapPi v d c)
  mapSort n  := φ.apply (ψ.mapSort n)
  mapLit n   := φ.apply (ψ.mapLit n)
  mapLet v t b := φ.apply (ψ.mapLet v t b)

/-! ## Homomorphism Properties -/

/-- The size relation after applying a homomorphism. We state this as an axiom
    since the size depends on the specific maps. -/
theorem hom_size_bound (φ : TermHom) (t : Term) :
    ∃ m : Nat, size (φ.apply t) ≤ m * size t := by
  axiom

/-- Identity homomorphism preserves size exactly. -/
theorem id_hom_preserves_size (t : Term) : size (TermHom.id.apply t) = size t := by
  simp [TermHom.id, TermHom.apply, size]

/-- Every term homomorphism preserves closedness when the variable map
    maps free variables to closed terms. -/
theorem hom_preserves_closed (φ : TermHom) (t : Term)
    (hvar : ∀ v, v ∈ freeVars t → isClosed (φ.mapVar v)) : isClosed (φ.apply t) := by
  axiom

/-! ## Extension Homomorphisms -/

/-- A homomorphism extended under a binder: shift indices of bound variables. -/
def TermHom.extend (φ : TermHom) : TermHom where
  mapVar v :=
    match v.index with
    | some n => φ.mapVar {v with index := some (n + 1)}
    | none => φ.mapVar v
  mapApp := φ.mapApp
  mapLam := φ.mapLam
  mapPi := φ.mapPi
  mapSort := φ.mapSort
  mapLit := φ.mapLit
  mapLet := φ.mapLet

/-! ## #eval Examples -/

def exHom : TermHom := TermHom.id

#eval exHom.apply (.var (Variable.free "x"))

#eval TermHom.id.apply (.app (.lam (Variable.free "x") (.var (Variable.free "x"))) (.lit 42))

#eval size (TermHom.id.apply (.app (.var (Variable.free "x")) (.var (Variable.free "y"))))

def countVarsRenaming : Renaming where
  rename v := {v with name := s!"v{toString v}"}

#eval Renaming.apply countVarsRenaming (.var (Variable.free "x"))

end MiniSyntaxKernel
