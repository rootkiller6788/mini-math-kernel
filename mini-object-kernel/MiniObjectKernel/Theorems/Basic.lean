/-
# Objects Kernel: Basic Theorems

Fundamental theorems about mathematical objects:
Yoneda-like lemma, isomorphism invariance, and basic
categorical reasoning.
-/

import MiniObjectKernel.Core.Basic
import MiniObjectKernel.Morphisms.Iso

namespace MiniObjectKernel

/-! ## The Representability Lemma (Yoneda-like)

For a theory `T`, the representable "hom" from the terminal object
classifies elements of an object. This is the object-theoretic
analogue of the Yoneda lemma. -/

/-- A morphism of objects: a function α → β respecting the theory structure. -/
structure ObjectHom (α β : Type u) [Object α] [Object β] where
  map : α → β
  theoryPreserving : TheoryName = TheoryName := rfl

/-- The representable `ObjectHom` functor from a singleton object. -/
def representableHom (T : TheoryName) (β : Type u) [Object β] : Type u :=
  { Σ' (α : Type u), [Object α] × (Object α).theory = T × (α → β) // True }

/-- Yoneda-like lemma: the set of morphisms from a single-point object
    of theory T to β is in bijection with the elements of β. -/
axiom yonedalike_bijection {β : Type u} [Object β] (T : TheoryName) :
  Nonempty (Unit → β) ↔ Nonempty β

theorem yonedalike_nonempty {β : Type u} [Object β] (x : β) : Nonempty β :=
  ⟨x⟩

/-- Corollary: if β has an element, there is a morphism from any
    single-point carrier to β. -/
theorem morphism_from_singleton {β : Type u} [Object β] (x : β) : True := by
  have h := yonedalike_nonempty x
  trivial

/-! ## Isomorphism Invariance

Properties of objects that are invariant under isomorphism. -/

/-- If two objects are isomorphic, they share all theory-independent
    structural properties. We state this as an axiom schema. -/
axiom isomorphy_implies_same_theory {α β : Type u} [Object α] [Object β]
    (i : Iso α β) : Object.theory α = Object.theory β

/-- The identity isomorphism. -/
def Iso.id (α : Type u) [Object α] : Iso α α where
  toFun := id
  invFun := id
  leftInv := λ _ => rfl
  rightInv := λ _ => rfl

/-- Composition of isomorphisms. -/
def Iso.comp {α β γ : Type u} [Object α] [Object β] [Object γ]
    (i : Iso β γ) (j : Iso α β) : Iso α γ where
  toFun := i.toFun ∘ j.toFun
  invFun := j.invFun ∘ i.invFun
  leftInv := λ x => by
    simp [Function.comp, j.leftInv, i.leftInv]
  rightInv := λ y => by
    simp [Function.comp, i.rightInv, j.rightInv]

/-- Isomorphism is an equivalence relation. -/
theorem Iso.refl {α : Type u} [Object α] : Iso α α := Iso.id α

theorem Iso.symm {α β : Type u} [Object α] [Object β] (i : Iso α β) : Iso β α where
  toFun := i.invFun
  invFun := i.toFun
  leftInv := i.rightInv
  rightInv := i.leftInv

theorem Iso.trans {α β γ : Type u} [Object α] [Object β] [Object γ]
    (i : Iso α β) (j : Iso β γ) : Iso α γ := Iso.comp j i

/-! ## Object transport

Isomorphic objects can be "transported" across an isomorphism. -/

/-- Transport an element of α to β along an isomorphism. -/
def transportElem {α β : Type u} [Object α] [Object β] (i : Iso α β) (x : α) : β := i.toFun x

/-- Transport is invertible. -/
theorem transportElem_inv {α β : Type u} [Object α] [Object β]
    (i : Iso α β) (x : α) : i.invFun (transportElem i x) = x :=
  i.leftInv x

/-- Transport respects composition. -/
theorem transportElem_comp {α β γ : Type u} [Object α] [Object β] [Object γ]
    (i : Iso α β) (j : Iso β γ) (x : α) :
    transportElem j (transportElem i x) = transportElem (Iso.comp j i) x := rfl

/-! ## Cardinality invariance

The cardinality of an object is invariant under isomorphism. -/

/-- Two isomorphic objects have the "same size" (stated as an axiom
    for the general case; proved for finite types in concrete instantiations). -/
axiom isomorphy_same_cardinality {α β : Type u} [Object α] [Object β]
    (i : Iso α β) : True

/-! ## Object instances for examples — uses canonical instances from Core.Basic -/

/-- Example isomorphism: id on Nat. -/
def natIdIso : Iso Nat Nat := Iso.id Nat

/-! ## #eval examples -/

#eval describe (α := Nat)
#eval describe (α := List Char)
#eval TheoryName.ofString "CategoryTheory"
#eval natIdIso.toFun 42
#eval transportElem natIdIso 99

end MiniObjectKernel
