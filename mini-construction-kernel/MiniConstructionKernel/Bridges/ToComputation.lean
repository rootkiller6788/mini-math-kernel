/-
# Constructions Kernel: Bridge to Computation

Connections between construction theory and computation.
Data type constructions, generic programming patterns,
algebraic data types, functors, and monads as constructions.
-/

import MiniConstructionKernel.Core.Basic
import MiniConstructionKernel.Constructions.Products
import MiniConstructionKernel.Constructions.Subobjects
import MiniConstructionKernel.Constructions.Quotients

namespace MiniConstructionKernel

open MiniObjectKernel

/-! ## Object instances -/

instance : Object Nat where
  theory := TheoryName.ofString "Set"
  objName := "Nat"
  repr n := toString n

instance : Object Bool where
  theory := TheoryName.ofString "Set"
  objName := "Bool"
  repr b := toString b

instance : Object String where
  theory := TheoryName.ofString "Set"
  objName := "String"
  repr s := s

/-! ## Algebraic Data Type as Coproduct -/

/-- An algebraic data type `data Option a = None | Some a` is a coproduct. -/
def optionAsConstruction (α : Type u) [Object α] : CoproductConstruction (Fin 2) fun
    | 0 => Unit
    | 1 => α :=
  buildCoproduct Unit α

/-! ## Product Type (Tuple) -/

/-- Tuple/pair type as a binary product. -/
def pairAsConstruction (α β : Type u) [Object α] [Object β] : ProductConstruction (Fin 2) fun
    | 0 => α
    | 1 => β :=
  buildProduct α β

/-! ## Generic Functor Pattern -/

structure GenericFunctor (F : Type u → Type v) where
  map : {α β : Type u} → [Object α] → [Object β] → (α → β) → F α → F β
  name : String

instance optionFunctor : GenericFunctor Option where
  map f
    | none => none
    | some a => some (f a)
  name := "OptionFunctor"

instance listFunctor : GenericFunctor List where
  map f
    | [] => []
    | a :: as => f a :: map f as
  name := "ListFunctor"

/-! ## Monad as Construction -/

structure MonadConstruction (M : Type u → Type u) [∀ α, Object (M α)] where
  pure : {α : Type u} → [Object α] → α → M α
  bind : {α β : Type u} → [Object α] → [Object β] → M α → (α → M β) → M β
  pure_bind : ∀ {α β : Type u} [Object α] [Object β] (a : α) (f : α → M β),
    bind (pure a) f = f a
  bind_pure : ∀ {α : Type u} [Object α] (m : M α),
    bind m pure = m
  bind_assoc : ∀ {α β γ : Type u} [Object α] [Object β] [Object γ]
    (m : M α) (f : α → M β) (g : β → M γ),
    bind (bind m f) g = bind m (fun a => bind (f a) g)
  name : String

instance (α : Type u) [Object α] : Object (Option α) where
  theory := TheoryName.ofString "Set"
  objName := s!"Option({describe α})"
  repr
    | none => "None"
    | some a => s!"Some({repr a})"

def optionMonad : MonadConstruction Option where
  pure a := some a
  bind m f :=
    match m with
    | none => none
    | some a => f a
  pure_bind a f := rfl
  bind_pure m := by
    cases m <;> rfl
  bind_assoc m f g := by
    cases m <;> rfl
  name := "OptionMonad"

/-! ## Subtype as Subobject (Computation-Style) -/

/-- A refinement type { x : Nat // x > 0 } is a subobject. -/
def positiveNatSubobject : SubConstruction Nat :=
  { pred := fun n => n > 0
    name := "PositiveNat"
  }

/-! ## Quotient for Modular Arithmetic (Computation) -/

/-- Modular arithmetic as a quotient construction. -/
def modNQuotient (n : Nat) : QuotientConstruction Nat :=
  { rel := fun a b => a % n = b % n
    isEquiv := {
      refl := fun a => rfl
      symm := fun h => h.symm
      trans := fun h₁ h₂ => h₁.trans h₂
    }
    name := s!"Mod{n}Arithmetic"
  }

/-! ## Function Space as Exponential Object -/

/-- The function type A → B is an exponential object in the cartesian closed category. -/
def exponentialObject (α β : Type u) [Object α] [Object β] : FunctionSpaceConstruction α β :=
  { name := s!"{describe α}→{describe β}" }

/-! ## Generic Programming: Type Class Derivation -/

structure Deriveable (F : Type u → Type u) [∀ α, Object (F α)] where
  equality : ∀ {α : Type u} [Object α], F α → F α → Bool
  ordering : ∀ {α : Type u} [Object α], F α → F α → Bool
  name : String

/-! ## Recursive Type as Initial Algebra -/

/-- A recursive type like `data Tree a = Leaf | Node (Tree a) a (Tree a)`
    is the initial algebra of a polynomial functor. -/
inductive Tree (α : Type u) : Type u
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
  deriving Inhabited

instance (α : Type u) [Object α] : Object (Tree α) where
  theory := TheoryName.ofString "Set"
  objName := s!"Tree({describe α})"
  repr
    | Tree.leaf => "Leaf"
    | Tree.node l a r => s!"Node({repr l},{repr a},{repr r})"

def treeAsConstruction (α : Type u) [Object α] : Construction Unit (fun _ => α) (Tree α) :=
  { build := Tree.leaf
    name := s!"Tree({describe α})"
  }

/-! ## Evaluations -/

#eval optionMonad.name
#eval optionAsConstruction Nat |>.name
#eval positiveNatSubobject.name
#eval (modNQuotient 7).name
#eval exponentialObject Nat Bool |>.name
#eval treeAsConstruction Nat |>.name

end MiniConstructionKernel
