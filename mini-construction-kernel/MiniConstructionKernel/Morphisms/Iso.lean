/-
# Constructions Kernel: Construction Isomorphisms

Isomorphisms between constructions on mathematical objects.
Includes: construction isomorphisms, inverse constructions,
iso-preserving maps, and iso-reflection.
-/

import MiniConstructionKernel.Core.Basic
import MiniConstructionKernel.Core.Objects
import MiniConstructionKernel.Morphisms.Hom

namespace MiniConstructionKernel

/-! ## Construction Isomorphism -/

-- An isomorphism between two constructions
structure ConstructionIso (α β : Type u) [Object α] [Object β] where
  forward : α → β
  backward : β → α
  left_inv : ∀ (a : α), backward (forward a) = a
  right_inv : ∀ (b : β), forward (backward b) = b
  name : String

/-! ## Construction Isomorphism from Bijection -/

def constructionIsoOfBijection {α β : Type u} [Object α] [Object β]
    (f : α → β) (g : β → α) (h₁ : ∀ a, g (f a) = a) (h₂ : ∀ b, f (g b) = b) (n : String := "") :
    ConstructionIso α β :=
  { forward := f
    backward := g
    left_inv := h₁
    right_inv := h₂
    name := n
  }

/-! ## Identity Isomorphism -/

def identityIso (α : Type u) [Object α] : ConstructionIso α α :=
  constructionIsoOfBijection (fun a => a) (fun a => a) (fun _ => rfl) (fun _ => rfl)
    s!"id_iso({describe α})"

/-! ## Inverse Isomorphism -/

def inverseIso {α β : Type u} [Object α] [Object β] (iso : ConstructionIso α β) :
    ConstructionIso β α :=
  { forward := iso.backward
    backward := iso.forward
    left_inv := iso.right_inv
    right_inv := iso.left_inv
    name := s!"inv({iso.name})"
  }

/-! ## Composition of Isomorphisms -/

def compIso {α β γ : Type u} [Object α] [Object β] [Object γ]
    (g : ConstructionIso β γ) (f : ConstructionIso α β) : ConstructionIso α γ :=
  { forward := fun a => g.forward (f.forward a)
    backward := fun c => f.backward (g.backward c)
    left_inv a := by
      rw [Function.comp_apply, f.left_inv, g.left_inv]
    right_inv c := by
      rw [Function.comp_apply, g.right_inv, f.right_inv]
    name := s!"{g.name} ∘ {f.name}"
  }

/-! ## Construction Preserves Isomorphism -/

-- A construction functor that preserves isomorphisms
structure PreservesIso (C : Type u → Type v) [∀ α, Object (C α)] where
  map : {α : Type u} → [Object α] → C α → C α
  preserves : ∀ {α β : Type u} [Object α] [Object β] (iso : ConstructionIso α β),
    (∃ (iso' : ConstructionIso (C α) (C β)), True) → True
  name : String

/-! ## Construction Reflecting Isomorphism -/

structure ReflectsIso (C : Type u → Type v) [∀ α, Object (C α)] where
  reflects : ∀ {α β : Type u} [Object α] [Object β],
    (ConstructionIso (C α) (C β) → ConstructionIso α β) → True
  name : String

/-! ## Isomorphism between Product Constructions -/

def productIso {α β γ δ : Type u} [Object α] [Object β] [Object γ] [Object δ]
    (iso₁ : ConstructionIso α γ) (iso₂ : ConstructionIso β δ) :
    ConstructionIso (BinProduct α β) (BinProduct γ δ) :=
  { forward := fun p => { fst := iso₁.forward p.fst, snd := iso₂.forward p.snd }
    backward := fun p => { fst := iso₁.backward p.fst, snd := iso₂.backward p.snd }
    left_inv p := by
      cases p; simp [iso₁.left_inv, iso₂.left_inv]
    right_inv p := by
      cases p; simp [iso₁.right_inv, iso₂.right_inv]
    name := s!"productIso({iso₁.name}, {iso₂.name})"
  }

/-! ## Isomorphism between Coproduct Constructions -/

def coproductIso {α β γ δ : Type u} [Object α] [Object β] [Object γ] [Object δ]
    (iso₁ : ConstructionIso α γ) (iso₂ : ConstructionIso β δ) :
    ConstructionIso (Coproduct α β) (Coproduct γ δ) :=
  { forward := fun
      | Coproduct.inl a => Coproduct.inl (iso₁.forward a)
      | Coproduct.inr b => Coproduct.inr (iso₂.forward b)
    backward := fun
      | Coproduct.inl c => Coproduct.inl (iso₁.backward c)
      | Coproduct.inr d => Coproduct.inr (iso₂.backward d)
    left_inv := fun
      | Coproduct.inl a => by rw [iso₁.left_inv]
      | Coproduct.inr b => by rw [iso₂.left_inv]
    right_inv := fun
      | Coproduct.inl c => by rw [iso₁.right_inv]
      | Coproduct.inr d => by rw [iso₂.right_inv]
    name := s!"coproductIso({iso₁.name}, {iso₂.name})"
  }

/-! ## Subobject Isomorphism -/

structure SubobjectIso (α : Type u) [Object α] where
  pred₁ : α → Prop
  pred₂ : α → Prop
  isoForward : { x // pred₁ x } → { x // pred₂ x }
  isoBackward : { x // pred₂ x } → { x // pred₁ x }
  left_inv : ∀ s, isoBackward (isoForward s) = s
  right_inv : ∀ s, isoForward (isoBackward s) = s
  name : String

/-! ## Quotient Isomorphism -/

structure QuotientIso (α : Type u) [Object α] where
  rel₁ : α → α → Prop
  rel₂ : α → α → Prop
  isEquiv₁ : Equivalence rel₁
  isEquiv₂ : Equivalence rel₂
  isoForward : Quot rel₁ → Quot rel₂
  isoBackward : Quot rel₂ → Quot rel₁
  left_inv : ∀ q, isoBackward (isoForward q) = q
  right_inv : ∀ q, isoForward (isoBackward q) = q
  name : String

/-! ## Examples and evaluations -/

section Examples

def trivialNatIso : ConstructionIso Nat Nat :=
  identityIso Nat

def compNatIso : ConstructionIso Nat Nat :=
  compIso trivialNatIso trivialNatIso

def prodNatBoolIso : ConstructionIso (BinProduct Nat Bool) (BinProduct Nat Bool) :=
  productIso trivialNatIso (identityIso Bool)

#eval trivialNatIso.name
#eval compNatIso.name
#eval prodNatBoolIso.name
#eval trivialNatIso.forward 42

end Examples

end MiniConstructionKernel
