/-
# Constructions Kernel: Preservation

Preservation properties of constructions on mathematical objects.
Which properties are preserved, reflected, or created by various
construction operations.
-/

import MiniConstructionKernel.Core.Basic
import MiniConstructionKernel.Core.Objects
import MiniConstructionKernel.Morphisms.Hom
import MiniConstructionKernel.Morphisms.Iso
import MiniConstructionKernel.Properties.Invariants

namespace MiniConstructionKernel

/-! ## Preservation of Properties -/

-- A construction preserves a property
structure PreservesProperty (C : Type u → Type v) (P : (Type u) → Prop) [∀ α, Object (C α)] where
  map : {α : Type u} → [Object α] → P α → P (C α)
  name : String

/-! ## Reflection of Properties -/

-- A construction reflects a property
structure ReflectsProperty (C : Type u → Type v) (P : (Type u) → Prop) [∀ α, Object (C α)] where
  map : {α : Type u} → [Object α] → P (C α) → P α
  name : String

/-! ## Creation of Properties -/

-- A construction creates a property (preserves and reflects)
structure CreatesProperty (C : Type u → Type v) (P : (Type u) → Prop) [∀ α, Object (C α)] where
  preserves : PreservesProperty C P
  reflects : ReflectsProperty C P
  name : String

/-! ## Preservation by Product Construction -/

structure ProductPreserves (α β : Type u) [Object α] [Object β] where
  property : α → Prop
  preserved : ∀ (a : α) (b : β), property a → property (Product.mk a b).fst
  name : String

/-! ## Preservation by Coproduct Construction -/

structure CoproductPreserves (α β : Type u) [Object α] [Object β] where
  property : Coproduct α β → Prop
  preserved_inl : ∀ (a : α), property (Coproduct.inl a)
  preserved_inr : ∀ (b : β), property (Coproduct.inr b)
  name : String

/-! ## Preservation by Subobject -/

-- A property is preserved when taking subobjects
structure SubobjectPreserves (α : Type u) [Object α] where
  property : α → Prop
  preserved : ∀ (S : Subobject α) (s : S.carrier), property (S.embedding s)
  name : String

/-! ## Preservation by Quotient -/

-- A property is preserved under quotients
structure QuotientPreserves (α : Type u) [Object α] where
  property : α → Prop
  preserved : ∀ (q : QuotientByEquiv α) (a : α), property a → property (q.proj a)
  name : String

/-! ## Finite Product Preservation -/

-- A functor preserves finite products
structure PreservesFiniteProducts (F : Type u → Type v) [∀ α, Object (F α)] where
  preservesBinary : ∀ {α β : Type u} [Object α] [Object β],
    Nonempty (ConstructionIso (F (BinProduct α β)) (BinProduct (F α) (F β)))
  preservesTerminal : Nonempty (ConstructionIso (F Unit) Unit)
  name : String

/-! ## Finite Coproduct Preservation -/

-- A functor preserves finite coproducts
structure PreservesFiniteCoproducts (F : Type u → Type v) [∀ α, Object (F α)] where
  preservesBinary : ∀ {α β : Type u} [Object α] [Object β],
    Nonempty (ConstructionIso (F (Coproduct α β)) (Coproduct (F α) (F β)))
  preservesInitial : Nonempty (ConstructionIso (F Empty) Empty)
  name : String

/-! ## Exactness Preservation -/

-- A functor is exact (preserves finite limits and colimits)
structure ExactFunctor (F : Type u → Type v) [∀ α, Object (F α)] where
  preservesFiniteLimits : ContinuousFunctor F
  preservesFiniteColimits : CocontinuousFunctor F
  name : String

/-! ## Monomorphism Preservation -/

-- A construction preserves monomorphisms
structure PreservesMonomorphisms (F : Type u → Type v) [∀ α, Object (F α)] where
  property : ∀ {α β : Type u} [Object α] [Object β] (f : α → β),
    (ConstructionMono α β) → (ConstructionMono (F α) (F β))
  name : String

/-! ## Epimorphism Preservation -/

-- A construction preserves epimorphisms
structure PreservesEpimorphisms (F : Type u → Type v) [∀ α, Object (F α)] where
  property : ∀ {α β : Type u} [Object α] [Object β] (f : α → β),
    (ConstructionEpi α β) → (ConstructionEpi (F α) (F β))
  name : String

/-! ## Continuous Functor (limit-preserving) -/

-- A functor F preserves limits of shape J if for any limit cone,
-- the image under F is also a limit cone. We formalize this as:
-- If L is a limit of D, then F(L) is isomorphic to the limit of F∘D
def LimitType (J : Type u) (D : J → Type v) : Type v :=
  { f : (∀ j : J, D j) // True }

structure ContinuousFunctor (F : Type u → Type v) [∀ α, Object (F α)] where
  preservesProducts : PreservesFiniteProducts F
  preservesEqualizers : ∀ {α β : Type u} [Object α] [Object β] (f g : α → β),
    Nonempty (ConstructionIso (F { x : α // f x = g x }) { x : F α // True })
  name : String

/-! ## Cocontinuous Functor (colimit-preserving) -/

structure CocontinuousFunctor (F : Type u → Type v) [∀ α, Object (F α)] where
  preservesCoproducts : PreservesFiniteCoproducts F
  preservesCoequalizers : ∀ {α β : Type u} [Object α] [Object β] (f g : β → α),
    Nonempty (ConstructionIso (F (Coproduct α α)) (Coproduct (F α) (F α)))
  name : String

/-! ## Examples and evaluations -/

section Examples

def optionPreservesNonempty : PreservesProperty Option (fun α => Nonempty α) where
  map h := by
    rcases h with ⟨a⟩
    exact ⟨some a⟩
  name := "OptionPreservesNonempty"

def trivialPreservesFiniteProducts : PreservesFiniteProducts id where
  preservesBinary α β := ⟨identityIso (BinProduct α β)⟩
  preservesTerminal := ⟨identityIso Unit⟩
  name := "IdPreservesFiniteProducts"

#eval optionPreservesNonempty.name
#eval trivialPreservesFiniteProducts.name
#eval (optionPreservesNonempty.map ⟨42⟩).nonEmpty

end Examples

end MiniConstructionKernel
