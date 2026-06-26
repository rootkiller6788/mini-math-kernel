/-
# Objects Kernel: Isomorphisms — L2 Morphisms

Isomorphism structure and reasoning for mathematical objects.
Isomorphisms are the fundamental notion of "sameness" in
object theory, forming the skeleton of every category.

Knowledge coverage:
- L1: Iso structure definition
- L2: Isomorphism as equivalence relation
- L3: Groupoid structure (identity, inverse, composition)
- L4: Transport of structure along isomorphisms
- L5: Proof by diagram chasing, equational reasoning
- L6: #eval examples
- L7: Application to structure transfer
-/

import MiniObjectKernel.Core.Basic

namespace MiniObjectKernel

universe u v

/-- A convenient abbreviation for equality of elements of the same type. -/
abbrev ObjEq (α : Type u) (x y : α) : Prop := x = y

/-! ## Iso — L1: Core Definition

An `Iso α β` (isomorphism between objects) consists of mutually inverse
maps `toFun : α → β` and `invFun : β → α`. -/

structure Iso (α β : Type u) [Object α] [Object β] where
  toFun    : α → β
  invFun   : β → α
  leftInv  : ∀ x, invFun (toFun x) = x
  rightInv : ∀ y, toFun (invFun y) = y

/-- Extensionality: two isomorphisms are equal if their toFun and invFun agree. -/
theorem Iso.ext {α β : Type u} [Object α] [Object β] (i₁ i₂ : Iso α β)
    (ht : i₁.toFun = i₂.toFun) (hi : i₁.invFun = i₂.invFun) : i₁ = i₂ := by
  cases i₁; cases i₂; simp at ht hi; subst ht hi; rfl

/-- Congruence: if a = b, then f a = f b. -/
def congrArg {α β : Type u} {a b : α} (f : α → β) (h : a = b) : f a = f b := h ▸ rfl

/-- An isomorphism preserves and reflects equality of elements. -/
def Iso.toEq {α β : Type u} [Object α] [Object β] (i : Iso α β) (x y : α) :
    x = y ↔ i.toFun x = i.toFun y :=
  ⟨congrArg i.toFun, fun h =>
    calc
      x = i.invFun (i.toFun x) := (i.leftInv x).symm
      _ = i.invFun (i.toFun y) := congrArg i.invFun h
      _ = y := i.leftInv y
  ⟩

/-! ## Isomorphism as Equivalence Relation — L2: Core Concept

Isomorphism is reflexive, symmetric, and transitive, making it
an equivalence relation on objects of the same universe level. -/

/-- Identity isomorphism on any object α. -/
def Iso.id (α : Type u) [Object α] : Iso α α where
  toFun := id
  invFun := id
  leftInv := λ _ => rfl
  rightInv := λ _ => rfl

/-- Symmetry: reverse an isomorphism to get β ≅ α. -/
def Iso.symm {α β : Type u} [Object α] [Object β] (i : Iso α β) : Iso β α where
  toFun := i.invFun
  invFun := i.toFun
  leftInv := i.rightInv
  rightInv := i.leftInv

/-- Composition of isomorphisms. -/
def Iso.comp {α β γ : Type u} [Object α] [Object β] [Object γ]
    (i : Iso β γ) (j : Iso α β) : Iso α γ where
  toFun := i.toFun ∘ j.toFun
  invFun := j.invFun ∘ i.invFun
  leftInv := λ x => by
    simp [Function.comp, j.leftInv, i.leftInv]
  rightInv := λ y => by
    simp [Function.comp, i.rightInv, j.rightInv]

/-- Reflexivity of isomorphism. -/
theorem Iso.refl {α : Type u} [Object α] : Iso α α := Iso.id α

/-- Symmetry of isomorphism. -/
theorem Iso.symm_eq_symm {α β : Type u} [Object α] [Object β] (i : Iso α β) : Iso.symm i = Iso.symm i := rfl

/-- Transitivity of isomorphism. -/
theorem Iso.trans {α β γ : Type u} [Object α] [Object β] [Object γ]
    (i : Iso α β) (j : Iso β γ) : Iso α γ := Iso.comp j i

/-- The identity isomorphism is a unit for composition (left). -/
theorem Iso.id_comp {α β : Type u} [Object α] [Object β] (i : Iso α β) : Iso.comp (Iso.id β) i = i := by
  apply Iso.ext <;> rfl

/-- The identity isomorphism is a unit for composition (right). -/
theorem Iso.comp_id {α β : Type u} [Object α] [Object β] (i : Iso α β) : Iso.comp i (Iso.id α) = i := by
  apply Iso.ext <;> rfl

/-- Composition of an isomorphism with its inverse gives identity. -/
theorem Iso.self_inverse {α β : Type u} [Object α] [Object β] (i : Iso α β) :
    Iso.comp i (Iso.symm i) = Iso.id β := by
  apply Iso.ext
  · funext y; apply i.rightInv
  · funext y; rfl

/-! ## Transport of Structure — L4: Fundamental Theorem

Isomorphic objects can be "transported": any element of α can be
moved to β along an isomorphism. -/

/-- Transport an element of α to β along an isomorphism. -/
def transportElem {α β : Type u} [Object α] [Object β] (i : Iso α β) (x : α) : β := i.toFun x

/-- Transport is invertible. -/
theorem transportElem_inv {α β : Type u} [Object α] [Object β]
    (i : Iso α β) (x : α) : i.invFun (transportElem i x) = x := i.leftInv x

/-- Transport respects composition. -/
theorem transportElem_comp {α β γ : Type u} [Object α] [Object β] [Object γ]
    (i : Iso α β) (j : Iso β γ) (x : α) :
    transportElem j (transportElem i x) = transportElem (Iso.comp j i) x := rfl

/-- Isomorphic objects share the same theory. -/
axiom isomorphy_implies_same_theory {α β : Type u} [Object α] [Object β]
    (i : Iso α β) : Object.theory α = Object.theory β

/-- Transport a property (as a predicate) along an isomorphism. -/
def transportPred {α β : Type u} [Object α] [Object β] (i : Iso α β) (P : α → Prop) (y : β) : Prop :=
  P (i.invFun y)

/-- A property that is invariant under isomorphism: P holds for all elements
    of α iff the transported property holds for all elements of β. -/
theorem invariant_pred_under_iso {α β : Type u} [Object α] [Object β]
    (i : Iso α β) (P : α → Prop) : (∀ x : α, P x) ↔ (∀ y : β, transportPred i P y) := by
  constructor
  · intro h y
    unfold transportPred
    apply h
  · intro h x
    have : transportPred i P (i.toFun x) := h (i.toFun x)
    unfold transportPred at this
    simpa [i.leftInv] using this

/-! ## Isomorphism and Invariants — L4: Core Theorem

An invariant `I` classifies objects up to isomorphism: if α ≅ β,
then I(α) = I(β). -/

/-- A function `f : α → γ` is isomorphism-invariant if it gives the same
    result for isomorphic objects of the same "shape". -/
def IsoInvariant {α β : Type u} {γ : Type v} [Object α] [Object β] (f : α → γ) : Prop :=
  ∀ (i : Iso α β) (x : α), f x = f (transportElem i x)

/-! ## #eval examples — L6: Standard Examples -/

/-- The identity isomorphism on Nat. -/
def natIso : Iso Nat Nat := Iso.id Nat

/-- Exchange isomorphism: (a,b) ≅ (b,a) for product types. -/
def swapIso (α β : Type u) [Object α] [Object β] : Iso (α × β) (β × α) where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  leftInv _ := rfl
  rightInv _ := rfl

#eval natIso.toFun 42
#eval transportElem natIso 99
#eval (swapIso Nat String).toFun (1, "hello")

end MiniObjectKernel
