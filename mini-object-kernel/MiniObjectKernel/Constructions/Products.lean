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

/-! ## Terminal and Initial Objects — L2: Core Concepts

Terminal objects have a unique morphism from every object.
Initial objects have a unique morphism to every object.
These are the 0-ary cases of product and coproduct. -/

/-- Terminal object: any type with exactly one element (up to isomorphism). -/
def isTerminal (α : Type u) [Object α] : Prop :=
  ∀ (β : Type u) [Object β], ∃! f : β → α, True

/-- Unit is terminal (its Object instance is in Core.Basic). -/
theorem unit_isTerminal : isTerminal Unit := by
  intro β _
  refine ⟨λ _ => (), trivial, ?_⟩
  intro f _
  funext x
  cases f x; rfl

/-- Initial object: unique map FROM it to any other object (up to isomorphism). -/
def isInitial (α : Type u) [Object α] : Prop :=
  ∀ (β : Type u) [Object β], ∃! f : α → β, True

/-- Empty is initial (its Object instance is in Core.Basic). -/
theorem empty_isInitial : isInitial Empty := by
  intro β _
  refine ⟨λ e => nomatch e, trivial, ?_⟩
  intro f _
  funext e; nomatch e

/-! ## Fiber Product (Pullback) — L3: Advanced Construction

The fiber product of two morphisms f : A → C, g : B → C
is the limit of the cospan A → C ← B. -/

/-- A pullback of f : α → γ and g : β → γ is an object P
    with maps to α and β making the square commute, universal. -/
structure Pullback {α β γ : Type u} [Object α] [Object β] [Object γ]
    (f : α → γ) (g : β → γ) where
  carrier : Type u
  [carrierObj : Object carrier]
  p₁ : carrier → α
  p₂ : carrier → β
  commutativity : ∀ x, f (p₁ x) = g (p₂ x)
  universal : ∀ (X : Type u) [Object X] (h₁ : X → α) (h₂ : X → β),
    (∀ x, f (h₁ x) = g (h₂ x)) → ∃! k : X → carrier, (∀ x, p₁ (k x) = h₁ x) ∧ (∀ x, p₂ (k x) = h₂ x)

/-- The canonical pullback using the subtype of the product. -/
def Pullback.canonical {α β γ : Type u} [Object α] [Object β] [Object γ]
    (f : α → γ) (g : β → γ) : Pullback f g where
  carrier := { p : α × β // f p.1 = g p.2 }
  p₁ := λ ⟨(a, _), _⟩ => a
  p₂ := λ ⟨(_, b), _⟩ => b
  commutativity := λ ⟨(a, b), h⟩ => h
  universal := λ X _ h₁ h₂ h_comm => by
    refine ⟨λ x => ⟨(h₁ x, h₂ x), h_comm x⟩, ⟨λ _ => rfl, λ _ => rfl⟩, ?_⟩
    intro k ⟨hk₁, hk₂⟩
    funext x
    apply Subtype.ext
    apply Prod.ext
    · exact hk₁ x
    · exact hk₂ x

/-! ## Exponential Objects — L8: Advanced Topic

In a cartesian closed category, for any two objects A, B
there is an exponential object B^A representing the hom-set. -/

/-- An exponential object B^A with evaluation map ev : B^A × A → B. -/
structure Exponential {α β : Type u} [Object α] [Object β] where
  carrier : Type u
  [carrierObj : Object carrier]
  ev : carrier × α → β
  universal : ∀ (X : Type u) [Object X] (f : X × α → β),
    ∃! f̂ : X → carrier, ∀ x a, ev (f̂ x, a) = f (x, a)

/-- The canonical exponential in Set: the function type. -/
def Exponential.canonical (α β : Type u) [Object α] [Object β] : Exponential (α := α) (β := β) where
  carrier := α → β
  ev := λ (f, a) => f a
  universal := λ X _ f => by
    refine ⟨λ x a => f (x, a), λ _ _ => rfl, ?_⟩
    intro g hg
    funext x a
    exact hg x a

/-! ## #eval examples — L6: Verified Examples -/

#eval TheoryName.ofString "Algebra.Group"
#eval describe (α := Nat)
#eval describe (α := String)
#eval "Product, Coproduct, Pullback, and Exponential constructions defined"

end MiniObjectKernel

end MiniObjectKernel
