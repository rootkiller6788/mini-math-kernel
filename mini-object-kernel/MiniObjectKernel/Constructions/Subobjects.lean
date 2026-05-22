/-
# Objects Kernel: Subobjects

Subobject lattice constructions for mathematical objects.
-/

import MiniObjectKernel.Core.Basic
import MiniObjectKernel.Core.Objects

namespace MiniObjectKernel

/-! ## Subobject lattice operations

We extend the `Subobject` structure from `Core.Objects` with
lattice-theoretic operations: inclusion order, meet, join,
top element (the whole object), and bottom element (the empty subobject). -/

/-- A subobject A is less than or equal to subobject B if
    there is a factorisation of A's embedding through B's embedding. -/
def Subobject.le {α : Type u} [Object α] (s t : Subobject α) : Prop :=
  ∃ (f : s.carrier → t.carrier), ∀ x, t.embed (f x) = s.embed x

infix:50 " ≤ₛ " => Subobject.le

/-- Two subobjects are equal when their carriers are in bijection
    compatible with embeddings. We use Iso to state this. -/
def Subobject.equiv {α : Type u} [Object α] (s t : Subobject α) : Prop :=
  s ≤ₛ t ∧ t ≤ₛ s

/-- The identity subobject (the whole object α as a subobject of itself). -/
def Subobject.top (α : Type u) [Object α] : Subobject α where
  carrier := α
  embed := id
  injective := λ x y h => h
  theoryCompat := rfl

/-- The trivial (empty) subobject. Since Lean's `Empty` type has
    no elements, the `embed` is vacuously injective. -/
def Subobject.bot (α : Type u) [Object α] : Subobject α where
  carrier := Empty
  embed := λ e => nomatch e
  injective := λ x _ _ => nomatch x
  theoryCompat := rfl

/-- Binary meet of two subobjects.
    We model the meet as the fiber product / pullback of the embeddings. -/
def Subobject.meet {α : Type u} [Object α] (s t : Subobject α) : Subobject α where
  carrier := { p : s.carrier × t.carrier // s.embed p.1 = t.embed p.2 }
  embed := λ ⟨(x, y), _⟩ => s.embed x
  injective := λ ⟨(x₁, y₁), h₁⟩ ⟨(x₂, y₂), h₂⟩ heq => by
    have hx := s.injective x₁ x₂ (by
      have : s.embed x₁ = s.embed x₂ := heq
      exact this)
    have hy := t.injective y₁ y₂ (by
      calc
        t.embed y₁ = s.embed x₁ := h₁.symm
        _ = s.embed x₂ := heq
        _ = t.embed y₂ := h₂
      )
    have hpair : (x₁, y₁) = (x₂, y₂) := by
      cases hx; cases hy; rfl
    exact Subtype.ext hpair
  theoryCompat := s.theoryCompat

/-- Binary join of two subobjects.
    We model the join as the disjoint union modulo the relation
    that identifies overlapping parts. For simplicity we use
    `SubobjectPredicate` via the union of images. -/
def Subobject.join {α : Type u} [Object α] (s t : Subobject α) : Subobject α where
  carrier := { p : α // ∃ (x : s.carrier), s.embed x = p.val ∨ ∃ (y : t.carrier), t.embed y = p.val }
  embed := λ p => p.val
  injective := λ x y h => Subtype.ext h
  theoryCompat := s.theoryCompat

/-- The image of a subobject under an embedding between theories. -/
def Subobject.map {α β : Type u} [Object α] [Object β]
    (f : α → β) (hinj : ∀ x y, f x = f y → x = y)
    (s : Subobject α) : Subobject β where
  carrier := { y : β // ∃ (x : s.carrier), f (s.embed x) = y }
  embed := λ ⟨y, _⟩ => y
  injective := λ x y h => Subtype.ext h
  theoryCompat := s.theoryCompat

/-! ## Helper: a simple Object instance for examples -/

instance : Object Nat where
  theory := TheoryName.ofString "SetTheory"
  objName := "NaturalNumbers"
  repr n := toString n

def singletonSubobj (n : Nat) : Subobject Nat where
  carrier := Unit
  embed := λ _ => n
  injective := λ _ _ _ => rfl
  theoryCompat := rfl

def evenSubobj : Subobject Nat where
  carrier := { n : Nat // n % 2 = 0 }
  embed := λ ⟨n, _⟩ => n
  injective := λ ⟨x, _⟩ ⟨y, _⟩ h => by
    have hx := h
    subst hx; rfl
  theoryCompat := rfl

/-! ## Lattice laws -/

theorem Subobject.meet_le_left {α : Type u} [Object α]
    (s t : Subobject α) : Subobject.meet s t ≤ₛ s := by
  refine ⟨λ ⟨(x, _), _⟩ => x, ?_⟩
  intro ⟨(x, y), h⟩
  rfl

theorem Subobject.meet_le_right {α : Type u} [Object α]
    (s t : Subobject α) : Subobject.meet s t ≤ₛ t := by
  refine ⟨λ ⟨(_, y), _⟩ => y, ?_⟩
  intro ⟨(x, y), h⟩
  simp [h]

theorem Subobject.le_top {α : Type u} [Object α]
    (s : Subobject α) : s ≤ₛ Subobject.top α := by
  refine ⟨λ x => s.embed x, ?_⟩
  intro x; rfl

theorem Subobject.bot_le {α : Type u} [Object α]
    (s : Subobject α) : Subobject.bot α ≤ₛ s := by
  refine ⟨λ e => nomatch e, ?_⟩
  intro e; nomatch e

/-! ## #eval examples -/

#eval TheoryName.ofString "Algebra.Group"
#eval describe (α := Nat)
#eval "Subobject lattice defined for all Object instances"

end MiniObjectKernel
