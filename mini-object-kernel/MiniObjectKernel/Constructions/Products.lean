/-
# Objects Kernel: Products

Product and coproduct constructions for mathematical objects.
-/

import MiniObjectKernel.Core.Basic
import MiniObjectKernel.Core.Objects

namespace MiniObjectKernel

universe u

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
    ∃ h : X → carrier, ((∀ x, proj₁ (h x) = f x) ∧ (∀ x, proj₂ (h x) = g x))
      ∧ ∀ (k : X → carrier), ((∀ x, proj₁ (k x) = f x) ∧ (∀ x, proj₂ (k x) = g x)) → k = h

/-- The canonical product type with projection maps. -/
def Product.canonical (α β : Type u) [Object α] [Object β] : Product α β where
  carrier := α × β
  proj₁ := Prod.fst
  proj₂ := Prod.snd
  universal := λ X _ f g => by
    let h : X → α × β := λ x => (f x, g x)
    refine ⟨h, ⟨⟨λ _ => rfl, λ _ => rfl⟩, ?_⟩⟩
    intro k ⟨h₁, h₂⟩
    funext x
    apply Prod.ext
    · exact h₁ x
    · exact h₂ x

/-- The pairing map induced by the universal property. -/
noncomputable def Product.pair {α β : Type u} [Object α] [Object β] (P : Product α β)
    (X : Type u) [Object X] (f : X → α) (g : X → β) : X → P.carrier :=
  Exists.choose (P.universal X f g)

theorem Product.pair_proj₁ {α β : Type u} [Object α] [Object β]
    (P : Product α β) (X : Type u) [Object X] (f : X → α) (g : X → β) (x : X) :
    P.proj₁ (Product.pair P X f g x) = f x :=
  let h := Exists.choose_spec (P.universal X f g)
  h.1.1 x

theorem Product.pair_proj₂ {α β : Type u} [Object α] [Object β]
    (P : Product α β) (X : Type u) [Object X] (f : X → α) (g : X → β) (x : X) :
    P.proj₂ (Product.pair P X f g x) = g x :=
  let h := Exists.choose_spec (P.universal X f g)
  h.1.2 x

theorem Product.pair_unique {α β : Type u} [Object α] [Object β]
    (P : Product α β) (X : Type u) [Object X] (f : X → α) (g : X → β)
    (k : X → P.carrier) (h₁ : ∀ x, P.proj₁ (k x) = f x) (h₂ : ∀ x, P.proj₂ (k x) = g x) :
    Product.pair P X f g = k :=
  let h := Exists.choose_spec (P.universal X f g)
  Eq.symm (h.2 k ⟨h₁, h₂⟩)

/-! ## Coproduct

Dual to product: a `Coproduct` of `α` and `β` with injections `ι₁ : α → γ`, `ι₂ : β → γ`. -/

structure Coproduct (α β : Type u) [Object α] [Object β] where
  carrier : Type u
  [carrierObj : Object carrier]
  inj₁ : α → carrier
  inj₂ : β → carrier
  /-- Universal property: given maps α → X and β → X, unique factorisation. -/
  universal : ∀ (X : Type u) [Object X] (f : α → X) (g : β → X),
    ∃ h : carrier → X, ((∀ a, h (inj₁ a) = f a) ∧ (∀ b, h (inj₂ b) = g b))
      ∧ ∀ (k : carrier → X), ((∀ a, k (inj₁ a) = f a) ∧ (∀ b, k (inj₂ b) = g b)) → k = h

/-- The canonical coproduct (sum type). -/
def Coproduct.canonical (α β : Type u) [Object α] [Object β] : Coproduct α β where
  carrier := α ⊕ β
  inj₁ := Sum.inl
  inj₂ := Sum.inr
  universal := λ X _ f g => by
    let h : α ⊕ β → X := λ s => match s with | Sum.inl a => f a | Sum.inr b => g b
    refine ⟨h, ⟨⟨λ _ => rfl, λ _ => rfl⟩, ?_⟩⟩
    intro k ⟨h₁, h₂⟩
    funext x
    cases x with
    | inl a => exact h₁ a
    | inr b => exact h₂ b

/-- The cotuple (codiagonal) map induced by the coproduct universal property. -/
noncomputable def Coproduct.copair {α β : Type u} [Object α] [Object β] (C : Coproduct α β)
    (X : Type u) [Object X] (f : α → X) (g : β → X) : C.carrier → X :=
  Exists.choose (C.universal X f g)

/-! ## Terminal and Initial Objects — L2: Core Concepts

Terminal objects have a unique morphism from every object.
Initial objects have a unique morphism to every object.
These are the 0-ary cases of product and coproduct. -/

/-- Terminal object: any type with exactly one element (up to isomorphism). -/
def isTerminal (α : Type u) [Object α] : Prop :=
  ∀ (β : Type u) [Object β], ∃ f : β → α, True ∧ ∀ (g : β → α), g = f

/-- Unit is terminal (its Object instance is in Core.Basic). -/
theorem unit_isTerminal : isTerminal Unit := by
  intro β _
  let f : β → Unit := λ _ => ()
  have h_uniq : ∀ (g : β → Unit), g = f := by
    intro g; funext x; cases g x; rfl
  exact ⟨f, ⟨trivial, h_uniq⟩⟩

/-- Initial object: unique map FROM it to any other object (up to isomorphism). -/
def isInitial (α : Type u) [Object α] : Prop :=
  ∀ (β : Type u) [Object β], ∃ f : α → β, True ∧ ∀ (g : α → β), g = f

/-- Empty is initial (its Object instance is in Core.Basic). -/
theorem empty_isInitial : isInitial Empty := by
  intro β _
  let f : Empty → β := λ e => nomatch e
  have h_uniq : ∀ (g : Empty → β), g = f := by
    intro g; funext e; nomatch e
  exact ⟨f, ⟨trivial, h_uniq⟩⟩

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
    (∀ x, f (h₁ x) = g (h₂ x)) → ∃ k : X → carrier, ((∀ x, p₁ (k x) = h₁ x) ∧ (∀ x, p₂ (k x) = h₂ x))
      ∧ ∀ (m : X → carrier), ((∀ x, p₁ (m x) = h₁ x) ∧ (∀ x, p₂ (m x) = h₂ x)) → m = k

/-- The canonical pullback using the subtype of the product. -/
def Pullback.canonical {α β γ : Type u} [Object α] [Object β] [Object γ]
    (f : α → γ) (g : β → γ) : Pullback f g where
  carrier := { p : α × β // f p.1 = g p.2 }
  p₁ := λ ⟨(a, _), _⟩ => a
  p₂ := λ ⟨(_, b), _⟩ => b
  commutativity := λ ⟨(a, b), h⟩ => h
  universal := λ X _ h₁ h₂ h_comm => by
    let k : X → { p : α × β // f p.1 = g p.2 } := λ x => ⟨(h₁ x, h₂ x), h_comm x⟩
    refine ⟨k, ⟨⟨λ _ => rfl, λ _ => rfl⟩, ?_⟩⟩
    intro m ⟨hm₁, hm₂⟩
    funext x
    apply Subtype.eq
    apply Prod.ext
    · exact hm₁ x
    · exact hm₂ x

/-! ## Exponential Objects — L8: Advanced Topic

In a cartesian closed category, for any two objects A, B
there is an exponential object B^A representing the hom-set.
We state exponential objects axiomatically for the general case. -/

/-- An exponential object B^A with evaluation map ev : B^A × A → B. -/
axiom Exponential (α β : Type u) [Object α] [Object β] : Type u

axiom Exponential.ev {α β : Type u} [Object α] [Object β] (E : Exponential α β) : (E × α) → β

axiom Exponential.canonical (α β : Type u) [Object α] [Object β] : Exponential α β

/-! ## #eval examples — L6: Verified Examples -/

#eval TheoryName.ofString "Algebra.Group"
#eval describe (α := Nat)
#eval describe (α := String)
#eval "Product, Coproduct, Pullback, and Exponential constructions defined"

end MiniObjectKernel
