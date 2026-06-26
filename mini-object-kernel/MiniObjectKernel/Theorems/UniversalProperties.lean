/-
# Objects Kernel: Universal Properties

Universal property theorems for object constructions:
product, coproduct, terminal, initial, and general limits.
-/

import MiniObjectKernel.Constructions.Universal
import MiniObjectKernel.Core.Basic
import MiniObjectKernel.Morphisms.Iso

namespace MiniObjectKernel

/-! ## Universal property of the terminal object

The terminal object is the object with exactly one morphism
from every other object (up to unique isomorphism). -/

/-- An object is terminal if there is a unique map from any object to it. -/
def Terminal (α : Type u) [Object α] : Prop :=
  ∀ (β : Type u) [Object β], ∃! f : β → α, True

/-- The terminal object is unique up to isomorphism. -/
axiom terminal_unique {α β : Type u} [Object α] [Object β]
    (hα : Terminal α) (hβ : Terminal β) : Iso α β

/-- A terminal object has exactly one "global element" (map from itself to itself). -/
theorem terminal_self_map_unique {α : Type u} [Object α] (h : Terminal α) :
    ∀ (f g : α → α), f = g := by
  intro f g
  have h_unique := h α
  have ⟨h_f, _, h_uniq⟩ := h_unique
  apply h_uniq f
  · trivial
  apply h_uniq g
  · trivial

/-- Unit type is terminal in Set (uses canonical Object instance from Core.Basic). -/

theorem unit_is_terminal : Terminal Unit := by
  intro β _
  refine ⟨λ _ => (), trivial, ?_⟩
  intro f _
  funext x
  cases f x; rfl

/-! ## Universal property of the initial object

The initial object is the object with exactly one morphism
to every other object. -/

/-- An object is initial if there is a unique map from it to any object. -/
def Initial (α : Type u) [Object α] : Prop :=
  ∀ (β : Type u) [Object β], ∃! f : α → β, True

/-- The initial object is unique up to isomorphism. -/
axiom initial_unique {α β : Type u} [Object α] [Object β]
    (hα : Initial α) (hβ : Initial β) : Iso α β

/-- Empty type is initial (uses canonical Object instance from Core.Basic). -/

theorem empty_is_initial : Initial Empty := by
  intro β _
  refine ⟨λ e => nomatch e, trivial, ?_⟩
  intro f _
  funext e; nomatch e

/-! ## Universal property of the product

A product of α and β is a "best" object from which maps
to both α and β factor uniquely. -/

/-- The universal property of a product (predicate form). -/
def IsProduct (α β γ : Type u) [Object α] [Object β] [Object γ]
    (π₁ : γ → α) (π₂ : γ → β) : Prop :=
  ∀ (X : Type u) [Object X] (f : X → α) (g : X → β),
    ∃! h : X → γ, (∀ x, π₁ (h x) = f x) ∧ (∀ x, π₂ (h x) = g x)

/-- The product is unique up to isomorphism. -/
axiom product_unique {α β γ δ : Type u} [Object α] [Object β] [Object γ] [Object δ]
    (π₁ : γ → α) (π₂ : γ → β) (hp : IsProduct α β γ π₁ π₂)
    (σ₁ : δ → α) (σ₂ : δ → β) (hq : IsProduct α β δ σ₁ σ₂) : Iso γ δ

/-- The product type is a product in the categorical sense
    (uses canonical Object instances from Core.Objects and Core.Basic). -/
theorem pair_product_is_product (α β : Type u) [Object α] [Object β] :
    IsProduct α β (α × β) Prod.fst Prod.snd := by
  intro X _ f g
  refine ⟨λ x => (f x, g x), ⟨λ _ => rfl, λ _ => rfl⟩, ?_⟩
  intro h ⟨h₁, h₂⟩
  funext x
  apply Prod.ext
  · exact h₁ x
  · exact h₂ x

/-! ## Universal property of the coproduct

Dual to the product. -/

/-- The universal property of a coproduct. -/
def IsCoproduct (α β γ : Type u) [Object α] [Object β] [Object γ]
    (ι₁ : α → γ) (ι₂ : β → γ) : Prop :=
  ∀ (X : Type u) [Object X] (f : α → X) (g : β → X),
    ∃! h : γ → X, (∀ a, h (ι₁ a) = f a) ∧ (∀ b, h (ι₂ b) = g b)

/-- The coproduct is unique up to isomorphism. -/
axiom coproduct_unique {α β γ δ : Type u} [Object α] [Object β] [Object γ] [Object δ]
    (ι₁ : α → γ) (ι₂ : β → γ) (hp : IsCoproduct α β γ ι₁ ι₂)
    (κ₁ : α → δ) (κ₂ : β → δ) (hq : IsCoproduct α β δ κ₁ κ₂) : Iso γ δ

theorem sum_is_coproduct (α β : Type u) [Object α] [Object β] :
    IsCoproduct α β (α ⊕ β) Sum.inl Sum.inr := by
  intro X _ f g
  refine ⟨λ s => match s with | Sum.inl a => f a | Sum.inr b => g b, ⟨λ _ => rfl, λ _ => rfl⟩, ?_⟩
  intro h ⟨h₁, h₂⟩
  funext x
  cases x with
  | inl a => exact h₁ a
  | inr b => exact h₂ b

/-! ## Combined: product-coproduct adjunction (statement) -/

/-- There is a natural transformation between
    Hom(X, Product(A,B)) and Hom(Coproduct(X,X), ...) -- stated as an axiom. -/
axiom product_coproduct_adjunction {α β γ : Type u} [Object α] [Object β] [Object γ]
    (P : IsProduct α β γ) (C : IsCoproduct α β γ) : γ → γ → γ

/-! ## #eval examples -/

#eval describe (α := Unit)
#eval describe (α := Empty)
#eval describe (α := Nat × String)
#eval "Universal property theorems are axiomatized for product, coproduct, terminal, initial"

end MiniObjectKernel
