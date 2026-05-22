/-
# Constructions Kernel: Universal Properties

The universal property framework.
-/

import MiniConstructionKernel.Core.Basic

namespace MiniConstructionKernel

structure UniversalProperty (U : Type u) [Object U] where
  solutions : Type u → Type u
  universal : solutions U
  mediate  : {X : Type u} → [Object X] → solutions X → (U → X)
  mediate_universal : ∀ {X : Type u} [objX : Object X] (x : solutions X), True
  unique : ∀ {X : Type u} [Object X] (x : solutions X) (f g : U → X), True

structure InitialObject (U : Type u) [Object U] where
  initiate : {X : Type u} → [Object X] → U → X
  unique : ∀ {X : Type u} [Object X] (f g : U → X), ∀ u, f u = g u

def emptyInitial : InitialObject Empty where
  initiate _ _ e := nomatch e
  unique _ _ _ e := nomatch e

structure TerminalObject (U : Type u) [Object U] where
  terminate : {X : Type u} → [Object X] → X → U
  unique : ∀ {X : Type u} [Object X] (f g : X → U), ∀ x, f x = g x

def unitTerminal : TerminalObject Unit where
  terminate _ _ := fun _ => ()
  unique f g x := by
    have : f x = () := rfl
    have : g x = () := rfl
    rfl

structure ProductUniversal (α β P : Type u) [Object α] [Object β] [Object P] where
  fst : P → α
  snd : P → β
  pair : {X : Type u} → [Object X] → (X → α) → (X → β) → (X → P)
  pair_fst : ∀ {X : Type u} [Object X] (p : X → α) (q : X → β) (x : X), fst (pair p q x) = p x
  pair_snd : ∀ {X : Type u} [Object X] (p : X → α) (q : X → β) (x : X), snd (pair p q x) = q x
  unique : ∀ {X : Type u} [Object X] (p : X → α) (q : X → β) (h : X → P),
    (∀ x, fst (h x) = p x) → (∀ x, snd (h x) = q x) → (∀ x, h x = pair p q x)

structure CoproductUniversal (α β C : Type u) [Object α] [Object β] [Object C] where
  inl : α → C
  inr : β → C
  cases : {X : Type u} → [Object X] → (α → X) → (β → X) → (C → X)
  cases_inl : ∀ {X : Type u} [Object X] (f : α → X) (g : β → X) (a : α), cases f g (inl a) = f a
  cases_inr : ∀ {X : Type u} [Object X] (f : α → X) (g : β → X) (b : β), cases f g (inr b) = g b
  unique : ∀ {X : Type u} [Object X] (f : α → X) (g : β → X) (h : C → X),
    (∀ a, h (inl a) = f a) → (∀ b, h (inr b) = g b) → (∀ c, h c = cases f g c)

end MiniConstructionKernel
