/-
# Objects Kernel: Products

Product and coproduct constructions for mathematical objects.
-/

import MiniObjectKernel.Core.Basic

namespace MiniObjectKernel

/-! ## Product

A `Product` of two objects `α` and `β` is an object `γ`
together with projection maps `π₁ : γ → α` and `π₂ : γ → β`
satisfying the universal property. -/

structure Product (α β : Type u) [Object α] [Object β] where
  carrier : Type u
  [carrierObj : Object carrier]
  proj₁ : carrier → α
  proj₂ : carrier → β
  /-- Universal property: given maps from any object X to α and β,
      there is a unique map to the product making the diagram commute. -/
  universal : ∀ (X : Type u) [Object X] (f : X → α) (g : X → β),
    ∃! h : X → carrier, (∀ x, proj₁ (h x) = f x) ∧ (∀ x, proj₂ (h x) = g x)

/-- The canonical product type with projection maps. -/
def Product.canonical (α β : Type u) [Object α] [Object β] : Product α β where
  carrier := α × β
  proj₁ := Prod.fst
  proj₂ := Prod.snd
  universal := λ X _ f g => by
    refine ⟨λ x => (f x, g x), ⟨λ _ => rfl, λ _ => rfl⟩, ?_⟩
    intro h ⟨h₁, h₂⟩
    funext x
    apply Prod.ext
    · exact h₁ x
    · exact h₂ x

/-- The pairing map induced by the universal property. -/
def Product.pair {α β : Type u} [Object α] [Object β] (P : Product α β)
    (X : Type u) [Object X] (f : X → α) (g : X → β) : X → P.carrier :=
  (P.universal X f g).exists.choose

theorem Product.pair_proj₁ {α β : Type u} [Object α] [Object β]
    (P : Product α β) (X : Type u) [Object X] (f : X → α) (g : X → β) (x : X) :
    P.proj₁ (P.pair X f g x) = f x :=
  ((P.universal X f g).exists.choose_spec).1.1 x

theorem Product.pair_proj₂ {α β : Type u} [Object α] [Object β]
    (P : Product α β) (X : Type u) [Object X] (f : X → α) (g : X → β) (x : X) :
    P.proj₂ (P.pair X f g x) = g x :=
  ((P.universal X f g).exists.choose_spec).1.2 x

theorem Product.pair_unique {α β : Type u} [Object α] [Object β]
    (P : Product α β) (X : Type u) [Object X] (f : X → α) (g : X → β)
    (h : X → P.carrier) (h₁ : ∀ x, P.proj₁ (h x) = f x) (h₂ : ∀ x, P.proj₂ (h x) = g x) :
    P.pair X f g = h :=
  funext λ x => ((P.universal X f g).exists.choose_spec).2 h ⟨h₁, h₂⟩ x

/-! ## Coproduct

Dual to product: a `Coproduct` of `α` and `β` with injections `ι₁ : α → γ`, `ι₂ : β → γ`. -/

structure Coproduct (α β : Type u) [Object α] [Object β] where
  carrier : Type u
  [carrierObj : Object carrier]
  inj₁ : α → carrier
  inj₂ : β → carrier
  /-- Universal property: given maps α → X and β → X, unique factorisation. -/
  universal : ∀ (X : Type u) [Object X] (f : α → X) (g : β → X),
    ∃! h : carrier → X, (∀ a, h (inj₁ a) = f a) ∧ (∀ b, h (inj₂ b) = g b)

/-- The canonical coproduct (sum type). -/
def Coproduct.canonical (α β : Type u) [Object α] [Object β] : Coproduct α β where
  carrier := α ⊕ β
  inj₁ := Sum.inl
  inj₂ := Sum.inr
  universal := λ X _ f g => by
    refine ⟨λ s => match s with | Sum.inl a => f a | Sum.inr b => g b, ⟨λ _ => rfl, λ _ => rfl⟩, ?_⟩
    intro h ⟨h₁, h₂⟩
    funext x
    cases x with
    | inl a => exact h₁ a
    | inr b => exact h₂ b

/-- The cotuple (codiagonal) map induced by the coproduct universal property. -/
def Coproduct.copair {α β : Type u} [Object α] [Object β] (C : Coproduct α β)
    (X : Type u) [Object X] (f : α → X) (g : β → X) : C.carrier → X :=
  (C.universal X f g).exists.choose

/-! ## Object instances for examples -/

instance : Object (List String) where
  theory := TheoryName.ofString "SetTheory"
  objName := "StringList"
  repr xs := toString xs

instance : Object Unit where
  theory := TheoryName.root
  objName := "Terminal"
  repr _ := "()"

/-- Terminal object: any type with exactly one element (up to isomorphism). -/
def isTerminal (α : Type u) [Object α] : Prop :=
  ∀ (β : Type u) [Object β], ∃! f : β → α, True

theorem unit_isTerminal : isTerminal Unit := by
  intro β _
  refine ⟨λ _ => (), trivial, ?_⟩
  intro f _
  funext x
  cases f x; rfl

/-- Initial object: unique map FROM it to any other object (up to isomorphism). -/
def isInitial (α : Type u) [Object α] : Prop :=
  ∀ (β : Type u) [Object β], ∃! f : α → β, True

instance : Object Empty where
  theory := TheoryName.root
  objName := "Initial"
  repr e := nomatch e

theorem empty_isInitial : isInitial Empty := by
  intro β _
  refine ⟨λ e => nomatch e, trivial, ?_⟩
  intro f _
  funext e; nomatch e

/-! ## #eval examples -/

#eval TheoryName.ofString "Algebra.Group"
#eval describe (α := List String)
#eval "Product and Coproduct constructions defined"

end MiniObjectKernel
