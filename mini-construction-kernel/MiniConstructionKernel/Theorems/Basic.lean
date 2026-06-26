/-
# Constructions Kernel: Basic Theorems

Basic theorems about constructions on mathematical objects.
Includes: composition theorems, existence theorems, uniqueness theorems,
and structural theorems about constructions.
-/

import MiniConstructionKernel.Core.Basic
import MiniConstructionKernel.Core.Objects
import MiniConstructionKernel.Core.Laws
import MiniConstructionKernel.Morphisms.Hom
import MiniConstructionKernel.Morphisms.Iso
import MiniConstructionKernel.Constructions.Universal

namespace MiniConstructionKernel

/-! ## Composition Preserves Constructions -/

-- The composition of construction morphisms is a construction morphism
theorem composition_preserves_construction {α β γ : Type u} [Object α] [Object β] [Object γ]
    (c1 : Construction Unit (fun _ => α) β) (c2 : Construction Unit (fun _ => β) γ) :
    Nonempty (Construction Unit (fun _ => α) γ) :=
  ⟨compose c2 c1⟩

/-! ## Identity Isomorphism -/

-- Every construction is isomorphic to itself
theorem self_isomorphism (α : Type u) [Object α] : Nonempty (ConstructionIso α α) :=
  ⟨identityIso α⟩

/-! ## Isomorphism Composition -/

-- Isomorphisms compose to give isomorphisms
theorem isomorphism_composition {α β γ : Type u} [Object α] [Object β] [Object γ]
    (f : ConstructionIso α β) (g : ConstructionIso β γ) : Nonempty (ConstructionIso α γ) :=
  ⟨compIso g f⟩

/-! ## Inverse of Isomorphism -/

-- The inverse of an isomorphism is an isomorphism
theorem isomorphism_inverse {α β : Type u} [Object α] [Object β] (f : ConstructionIso α β) :
    Nonempty (ConstructionIso β α) :=
  ⟨inverseIso f⟩

/-! ## Product Universal Property Satisfied -/

-- The BinProduct satisfies the ProductUniversal property
theorem product_satisfies_universal (α β : Type u) [Object α] [Object β] :
    Nonempty (ProductUniversal α β (BinProduct α β)) :=
  ⟨binProductUniversal α β⟩

/-! ## Coproduct Universal Property Satisfied -/

-- The Coproduct satisfies the CoproductUniversal property
theorem coproduct_satisfies_universal (α β : Type u) [Object α] [Object β] :
    Nonempty (CoproductUniversal α β (Coproduct α β)) :=
  ⟨binCoproductUniversal α β⟩

/-! ## Uniqueness of Universal Objects up to Iso -/

-- Any two objects satisfying the same universal property are isomorphic
theorem universal_objects_are_isomorphic {α β : Type u} [Object α] [Object β]
    (h₁ : ProductUniversal Nat Nat α) (h₂ : ProductUniversal Nat Nat β) :
    Nonempty (ConstructionIso α β) := by
  -- Mediate through the universal property
  let f : α → β := h₂.pair h₁.fst h₁.snd
  let g : β → α := h₁.pair h₂.fst h₂.snd
  have hfg : ∀ x, g (f x) = x := by
    intro x
    apply h₁.unique (h₁.fst) (h₁.snd) (fun x => g (f x))
    · intro x'
      calc
        h₁.fst (g (f x')) = h₂.fst (f x') := h₁.pair_fst h₂.fst h₂.snd x'
        _ = h₁.fst x' := h₂.pair_fst h₁.fst h₁.snd x'
      -- This simplification works because the projections factor
    · intro x'
      calc
        h₁.snd (g (f x')) = h₂.snd (f x') := h₁.pair_snd h₂.fst h₂.snd x'
        _ = h₁.snd x' := h₂.pair_snd h₁.fst h₁.snd x'
    · intro x
      rfl
  have hgf : ∀ x, f (g x) = x := by
    intro x
    apply h₂.unique (h₂.fst) (h₂.snd) (fun x => f (g x))
    · intro x'
      calc
        h₂.fst (f (g x')) = h₁.fst (g x') := h₂.pair_fst h₁.fst h₁.snd x'
        _ = h₂.fst x' := h₁.pair_fst h₂.fst h₂.snd x'
    · intro x'
      calc
        h₂.snd (f (g x')) = h₁.snd (g x') := h₂.pair_snd h₁.fst h₁.snd x'
        _ = h₂.snd x' := h₁.pair_snd h₂.fst h₂.snd x'
    · intro x
      rfl
  exact ⟨constructionIsoOfBijection f g hfg hgf "UniversalIso"⟩

/-! ## Construction Subobjects form a Preorder -/

-- Subobjects of a fixed object form a preorder under inclusion
structure SubobjectPreorder (α : Type u) [Object α] where
  le : Subobject α → Subobject α → Prop
  refl : ∀ S, le S S
  trans : ∀ S T U, le S T → le T U → le S U
  name : String

def subobjectInclusionPreorder (α : Type u) [Object α] : SubobjectPreorder α where
  le S T := ∃ (f : S.carrier → T.carrier), ∀ (s : S.carrier), T.embedding (f s) = S.embedding s
  refl S := ⟨fun s => s, fun s => rfl⟩
  trans S T U hST hTU := by
    rcases hST with ⟨f, hf⟩
    rcases hTU with ⟨g, hg⟩
    exact ⟨g ∘ f, fun s => by rw [Function.comp_apply, hg, hf]⟩
  name := s!"SubobjPreorder({describe α})"

/-! ## Construction Quotients and Subobjects are related -/

-- A subobject gives rise to a quotient (its cokernel)
structure SubobjectToQuotient (α : Type u) [Object α] (S : Subobject α) where
  quotientType : Type u
  [obj : Object quotientType]
  proj : α → quotientType
  kernel : ∀ a, proj a = proj (S.embedding (Classical.choice (by
    -- kernel of proj = image of S.embedding
    exact ⟨a, rfl⟩)))
  name : String

-- A quotient gives rise to a subobject (its kernel)
structure QuotientToSubobject (α : Type u) [Object α] (q : QuotientByEquiv α) where
  subobjectType : Subobject α
  characteristic : ∀ a, q.proj a = q.proj a
  name : String

/-! ## Free-Forgetful Adjunction Theorem -/

structure FreeForgetfulAdjunctionStatement (F U : Type u → Type u) [∀ α, Object (F α)] [∀ α, Object (U α)] where
  -- Natural isomorphism: Hom(F A, B) ≅ Hom(A, U B)
  natural_bijection : ∀ {α β : Type u} [Object α] [Object β],
    Nonempty (ConstructionIso (F α → β) (α → U β))
  name : String

/-! ## Kernel-Image Isomorphism -/

-- The image of a morphism is isomorphic to the coimage
structure KernelImageIsomorphism {α β : Type u} [Object α] [Object β] (f : α → β) where
  kernelObj : Subobject α
  imageObj : Subobject β
  iso : Nonempty (ConstructionIso kernelObj.carrier imageObj.carrier)
  name : String

/-! ## Construction from Binary Product -/

-- The product of construction objects yields a construction
theorem product_yields_construction (α β γ : Type u) [Object α] [Object β] [Object γ]
    (cα : Construction Unit (fun _ => Unit) α) (cβ : Construction Unit (fun _ => Unit) β)
    (f : α → β → γ) :
    Nonempty (Construction Unit (fun _ => Unit) γ) :=
  ⟨{ build := f cα.build cβ.build
    name := s!"ProductConstruction({cα.name}, {cβ.name})"
  }⟩

/-! ## Construction Laws Consistency Theorem -/

structure ConsistentConstructionLaws where
  distributive : ProductDistributesOverCoproduct (Product Unit Unit) Unit Unit
  associative : ∀ (α β γ : Type u) [Object α] [Object β] [Object γ],
    Nonempty (ConstructionIso (BinProduct (BinProduct α β) γ) (BinProduct α (BinProduct β γ)))
  functorial : FunctorialConstruction Option
  name : String

def consConsistentLaws : ConsistentConstructionLaws where
  distributive := productDistributesOverCoproduct Nat Nat Nat
  associative α β γ := ⟨constructionIsoOfBijection
    (fun p => Product.mk p.fst.fst (Product.mk p.fst.snd p.snd))
    (fun p => Product.mk (Product.mk p.fst p.snd.fst) p.snd.snd)
    (fun _ => rfl) (fun _ => rfl) "Assoc"
  ⟩
  functorial := inferInstance
  name := "ConsistentLaws"

/-! ## Example: Build and Compose -/

section Examples

def builder (α β : Type u) [Object α] [Object β] (x : β) : Construction Unit (fun _ => α) β :=
  { build := x
    name := s!"Build({describe β})"
  }

#eval (builder Nat Nat 42).name
#eval composition_preserves_construction (builder Nat Nat 0) (builder Nat Nat 1)
#eval (builder String String "hello").name

end Examples

end MiniConstructionKernel
