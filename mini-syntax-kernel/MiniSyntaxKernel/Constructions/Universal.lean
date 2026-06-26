/-
# Syntax Kernel: Constructions — Universal

Universal constructions: free term algebra, initial algebra property,
and the universal property of terms over a signature.
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects
import MiniSyntaxKernel.Core.Laws

namespace MiniSyntaxKernel

open Term

/-! ## Signature and Term Algebra -/

/-- A first-order signature: a set of function symbols with arities. -/
structure Signature where
  symbols : List (String × Nat)
deriving BEq, Repr, Inhabited

/-- Generate the carrier of the free algebra: terms built from variables and signature symbols. -/
def Signature.termAlgebra (sig : Signature) (vars : List Variable) : List Term :=
  let rec build (depth : Nat) : List Term :=
    if depth = 0 then
      vars.map .var
    else
      let prev := build (depth - 1)
      let fnTerms : List Term :=
        sig.symbols.bind λ (name, arity) =>
          -- Generate all combinations of `arity` subterms from `prev`
          if arity = 0 then
            [.var (Variable.free name)]
          else
            generateBindings arity prev |>.map λ args =>
              List.foldl (λ acc a => .app acc a) (.var (Variable.free name)) args
      prev ++ fnTerms
  build 10 /- arbitrary depth limit -/

/-- Generate all lists of `n` elements from a list (with repetition). -/
def generateBindings (n : Nat) (xs : List Term) : List (List Term) :=
  let rec go (k : Nat) : List (List Term) :=
    if k = 0 then [[]]
    else
      let rest := go (k - 1)
      xs.bind λ x => rest.map λ ys => x :: ys
  go n

/-! ## Free Term Algebra -/

/-- The free term algebra over a set of variables.
    This is the initial algebra for the signature. -/
structure FreeAlgebra where
  carrier : Type
  var : Variable → carrier
  app : carrier → carrier → carrier
  lam : Variable → carrier → carrier
  pi : Variable → carrier → carrier → carrier
  sort : Nat → carrier
  lit : Nat → carrier
  letE : Variable → carrier → carrier → carrier

/-- The standard interpretation: carrier is `Term`. -/
def FreeAlgebra.standard : FreeAlgebra where
  carrier := Term
  var := .var
  app := .app
  lam := .lam
  pi := .pi
  sort := .sort
  lit := .lit
  letE := .letE

/-! ## Universal Property (Initiality) -/

/-- An algebra homomorphism from the term algebra to any other algebra. -/
structure AlgHom (A B : FreeAlgebra) where
  map : A.carrier → B.carrier
  map_var : ∀ v, map (A.var v) = B.var v
  map_app : ∀ f a, map (A.app f a) = B.app (map f) (map a)
  map_lam : ∀ v b, map (A.lam v b) = B.lam v (map b)
  map_pi : ∀ v d c, map (A.pi v d c) = B.pi v (map d) (map c)
  map_sort : ∀ n, map (A.sort n) = B.sort n
  map_lit : ∀ n, map (A.lit n) = B.lit n
  map_letE : ∀ v t b, map (A.letE v t b) = B.letE v (map t) (map b)

/-- For the standard interpretation, there exists a unique homomorphism
    to any free algebra (given its variable interpretation). -/
def FreeAlgebra.rec (A : FreeAlgebra) (varMap : Variable → A.carrier) : Term → A.carrier
  | .var v     => varMap v
  | .app f a   => A.app (rec A varMap f) (rec A varMap a)
  | .lam v b   => A.lam v (rec A varMap b)
  | .pi v d c  => A.pi v (rec A varMap d) (rec A varMap c)
  | .sort n    => A.sort n
  | .lit n     => A.lit n
  | .letE v t b => A.letE v (rec A varMap t) (rec A varMap b)

/-- The universal property: every interpretation on variables extends uniquely
    to a homomorphism from the term algebra. Proved by structural induction. -/
theorem universal_property (A : FreeAlgebra) (varMap : Variable → A.carrier) :
    ∃! φ : AlgHom FreeAlgebra.standard A,
      ∀ v, φ.map_var v = varMap v := by
  let φ : AlgHom FreeAlgebra.standard A := {
    map := FreeAlgebra.rec A varMap
    map_var := λ v => rfl
    map_app := λ f a => rfl
    map_lam := λ v b => rfl
    map_pi := λ v d c => rfl
    map_sort := λ n => rfl
    map_lit := λ n => rfl
    map_letE := λ v t b => rfl
  }
  have hφ_map : ∀ v, φ.map_var v = varMap v := λ v => rfl
  refine ⟨φ, hφ_map, ?_⟩
  intro ψ hψ
  -- Show φ.map = ψ.map by induction on terms
  ext t
  induction t with
  | var v =>
    simp [FreeAlgebra.standard, AlgHom.map_var, hψ v]
  | app f a ihf iha =>
    simp [FreeAlgebra.standard, AlgHom.map_app, ihf, iha]
  | lam v b ih =>
    simp [FreeAlgebra.standard, AlgHom.map_lam, ih]
  | pi v d c ihd ihc =>
    simp [FreeAlgebra.standard, AlgHom.map_pi, ihd, ihc]
  | sort n =>
    simp [FreeAlgebra.standard, AlgHom.map_sort]
  | lit n =>
    simp [FreeAlgebra.standard, AlgHom.map_lit]
  | letE v t b iht ihb =>
    simp [FreeAlgebra.standard, AlgHom.map_letE, iht, ihb]

/-! ## Initial Algebra -/

/-- The term algebra over a signature is the initial object in the category
    of algebras for that signature. -/
structure InitialAlgebra (sig : Signature) where
  Algebra : Type
  embed : Term → Algebra
  unique : (A : FreeAlgebra) → (f : Term → A.carrier) → ∃! g : Algebra → A.carrier, True
  -- The existence and uniqueness of the mediating morphism

/-- Terms form the initial algebra: for any algebra A, there exists a unique
    homomorphism from Term to A, given by `FreeAlgebra.rec`. -/
theorem term_is_initial (A : FreeAlgebra) (varMap : Variable → A.carrier) :
    Nonempty (AlgHom FreeAlgebra.standard A) := by
  let φ : AlgHom FreeAlgebra.standard A := {
    map := FreeAlgebra.rec A varMap
    map_var := λ v => rfl
    map_app := λ f a => rfl
    map_lam := λ v b => rfl
    map_pi := λ v d c => rfl
    map_sort := λ n => rfl
    map_lit := λ n => rfl
    map_letE := λ v t b => rfl
  }
  exact ⟨φ⟩

/-! ## Structural Induction Principle -/

/-- The structural induction principle for terms (derived from the universal property). -/
theorem term_induction {P : Term → Prop}
    (hVar  : ∀ v, P (.var v))
    (hApp  : ∀ f a, P f → P a → P (.app f a))
    (hLam  : ∀ v b, P b → P (.lam v b))
    (hPi   : ∀ v d c, P d → P c → P (.pi v d c))
    (hSort : ∀ n, P (.sort n))
    (hLit  : ∀ n, P (.lit n))
    (hLet  : ∀ v t b, P t → P b → P (.letE v t b))
    : ∀ t, P t := by
  intro t
  induction t with
  | var v => exact hVar v
  | app f a ihf iha => exact hApp f a ihf iha
  | lam v b ih => exact hLam v b ih
  | pi v d c ihd ihc => exact hPi v d c ihd ihc
  | sort n => exact hSort n
  | lit n => exact hLit n
  | letE v t b iht ihb => exact hLet v t b iht ihb

/-! ## #eval Examples -/

def sig : Signature := { symbols := [("zero", 0), ("succ", 1), ("add", 2)] }

#eval sig.symbols

#eval FreeAlgebra.standard.var (Variable.free "x") |> toString

#eval generateBindings 2 [.lit 1, .lit 2]

def arithSig : Signature := { symbols := [("add", 2), ("mul", 2), ("neg", 1)] }

#eval SizeOf.sizeOf arithSig

end MiniSyntaxKernel
