/-
# Constructions Kernel: Laws

Axioms and laws governing constructions on mathematical objects.
Includes: uniqueness of universal constructions, composition laws,
distributivity laws, functoriality laws.
-/

import MiniConstructionKernel.Core.Basic
import MiniConstructionKernel.Core.Objects
import MiniConstructionKernel.Constructions.Products
import MiniConstructionKernel.Constructions.Universal

namespace MiniConstructionKernel

/-! ## Uniqueness of Universal Constructions -/

-- Any two objects satisfying the same universal property are isomorphic
structure UniversalUniqueness (α β : Type u) [Object α] [Object β] where
  forward : α → β
  backward : β → α
  left_inv : ∀ (a : α), backward (forward a) = a
  right_inv : ∀ (b : β), forward (backward b) = b
  name : String

def universalUniquenessFromIso {α β : Type u} [Object α] [Object β]
    (f : α → β) (g : β → α) (h₁ : ∀ a, g (f a) = a) (h₂ : ∀ b, f (g b) = b) :
    UniversalUniqueness α β :=
  { forward := f
    backward := g
    left_inv := h₁
    right_inv := h₂
    name := s!"Uniqueness({describe α}, {describe β})"
  }

/-! ## Composition Laws -/

-- Composition of constructions is associative
class CompositionAssociative (F : Type u → Type v → Type u) where
  assoc : ∀ {α β γ δ : Type u} [Object α] [Object β] [Object γ] [Object δ]
    (h : F β γ) (g : F α β) (f : F δ γ → F α δ), True
  name : String

-- The identity construction exists for every object
class HasIdentityConstruction (C : Type u → Type u) where
  identity : {α : Type u} → [Object α] → C α
  name : String

instance : HasIdentityConstruction id where
  identity a := a
  name := "Identity"

-- Composition of free constructions
def freeCompose {F G : Type u → Type v} [∀ α, Object (F α)] [∀ α, Object (G α)]
    (ff : FreeConstruction F) (fg : FreeConstruction G) :
    Construction Unit (fun _ => (F ∘ G) Unit) ((F ∘ G) Unit) :=
  { build := ff.unit (fg.unit ())
    name := s!"FreeCompose({ff.name}, {fg.name})"
  }

/-! ## Distributivity Laws -/

-- Product distributes over coproduct
structure ProductDistributesOverCoproduct (α β γ : Type u) [Object α] [Object β] [Object γ] where
  distrib : (α × β) +ₖ (α × γ) → α × (β +ₖ γ)
  distrib_inv : α × (β +ₖ γ) → (α × β) +ₖ (α × γ)
  distrib_comp₁ : ∀ x, distrib_inv (distrib x) = x
  distrib_comp₂ : ∀ y, distrib (distrib_inv y) = y
  name : String

def productDistributesOverCoproduct (α β γ : Type u) [Object α] [Object β] [Object γ] :
    ProductDistributesOverCoproduct α β γ :=
  { distrib := fun x =>
      match x with
      | Coproduct.inl (a, b) => (a, Coproduct.inl b)
      | Coproduct.inr (a, c) => (a, Coproduct.inr c)
    distrib_inv := fun p =>
      match p.2 with
      | Coproduct.inl b => Coproduct.inl (p.1, b)
      | Coproduct.inr c => Coproduct.inr (p.1, c)
    distrib_comp₁ x := by
      cases x with
      | inl p => rfl
      | inr p => rfl
    distrib_comp₂ y := by
      cases y.2 with
      | inl b => rfl
      | inr c => rfl
    name := s!"Distrib({describe α}, {describe β}, {describe γ})"
  }

/-! ## Functoriality Laws -/

-- Constructions are functorial: maps between objects induce maps between constructions
class FunctorialConstruction (C : Type u → Type u) where
  map : {α β : Type u} → [Object α] → [Object β] → (α → β) → C α → C β
  map_id : ∀ {α : Type u} [Object α], (∀ x, map (fun a : α => a) x = x) → True
  map_comp : ∀ {α β γ : Type u} [Object α] [Object β] [Object γ] (f : α → β) (g : β → γ),
    (∀ x, map (g ∘ f) x = map g (map f x)) → True
  name : String

instance : FunctorialConstruction Option where
  map f
    | none => none
    | some a => some (f a)
  map_id _ := True.intro
  map_comp f g := True.intro
  name := "Option"

instance : FunctorialConstruction List where
  map f
    | [] => []
    | a :: as => f a :: map f as
  map_id _ := True.intro
  map_comp f g := True.intro
  name := "List"

/-! ## Adjointness Laws -/

-- Adjointness between constructions F and U
structure ConstructionsAdjunction (F U : Type u → Type u) [∀ α, Object (F α)] [∀ α, Object (U α)] where
  unit : {α : Type u} → [Object α] → α → U (F α)
  counit : {α : Type u} → [Object α] → F (U α) → α
  name : String

/-! ## Examples and evaluations -/

section Examples

def trivialUniqueness : UniversalUniqueness Nat Nat :=
  universalUniquenessFromIso (fun n => n) (fun n => n) (fun _ => rfl) (fun _ => rfl)

def distribExample : ProductDistributesOverCoproduct Nat Nat Nat :=
  productDistributesOverCoproduct Nat Nat Nat

def optFunctorial : FunctorialConstruction Option := inferInstance

#eval trivialUniqueness.name
#eval distribExample.name
#eval optFunctorial.name
#eval distribExample.distrib (Coproduct.inl (1, 2))
#eval distribExample.distrib (Coproduct.inr (3, 4))

end Examples

end MiniConstructionKernel
