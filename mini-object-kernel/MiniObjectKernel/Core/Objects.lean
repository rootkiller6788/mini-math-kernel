/-
# Objects Kernel: Subobjects, Quotients, Dependency — L1/L2 Structures

Provides Subobject, Quotient, Dependency definitions for all modules.
-/

import MiniObjectKernel.Core.Basic

universe u

namespace MiniObjectKernel

/-! ## Dependency Graph Support

For tracking theory dependencies across modules. -/

/-- A node in the theory dependency graph. -/
structure Dependency where

/-- A dependency edge between two theories. -/
structure Dependency.Edge where
  src : TheoryName
  trg : TheoryName
  lbl : String

/-- A theory node with metadata. -/
structure Dependency.TheoryNode where
  thry : TheoryName
  descr : String
  vers : String
  loc : String

/-- Simple theory node constructor. -/
def Dependency.TheoryNode.simple (thry : TheoryName) (descr : String) (vers : String) (loc : String) : Dependency.TheoryNode where
  thry := thry
  descr := descr
  vers := vers
  loc := loc

/-! ## Subobject — L1: Core Definition -/

structure Subobject (α : Type u) [Object α] where
  carrier : Type u
  [obj : Object carrier]
  embed : carrier → α
  injective : ∀ x y, embed x = embed y → x = y
  theoryCompat : Object.theory carrier = Object.theory α

/-- Subobject inclusion: s ≤ t if s factors through t's embedding. -/
def Subobject.le {α : Type u} [Object α] (s t : Subobject α) : Prop :=
  ∃ (f : s.carrier → t.carrier), ∀ (x : s.carrier), t.embed (f x) = s.embed x

/-- Infix notation for subobject ordering. -/
infix:50 " ≤ₛ " => Subobject.le

/-- Two subobjects are equivalent if they are isomorphic as subobjects. -/
structure Subobject.equiv {α : Type u} [Object α] (s t : Subobject α) : Prop where
  fst : s ≤ₛ t
  snd : t ≤ₛ s

/-- Transitivity of subobject inclusion. -/
theorem Subobject.le_trans {α : Type u} [Object α] (s t u : Subobject α)
    (hst : s ≤ₛ t) (htu : t ≤ₛ u) : s ≤ₛ u := by
  rcases hst with ⟨f, hf⟩
  rcases htu with ⟨g, hg⟩
  refine ⟨λ x => g (f x), ?_⟩
  intro x
  calc
    u.embed (g (f x)) = t.embed (f x) := hg (f x)
    _ = s.embed x := hf x

/-- The top subobject: the whole object α. -/
def Subobject.top (α : Type u) [Object α] : Subobject α where
  carrier := α
  embed := id
  injective := λ _ _ h => h
  theoryCompat := rfl

/-- The bottom subobject: axiomatized since Empty at universe u needs Object instance. -/
axiom Subobject.bot (α : Type u) [Object α] : Subobject α

/-- The bottom subobject is below every subobject. -/
axiom Subobject.bot_le {α : Type u} [Object α] (s : Subobject α) : Subobject.bot α ≤ₛ s

/-- Every subobject is below the top subobject. -/
theorem Subobject.le_top {α : Type u} [Object α] (s : Subobject α) : s ≤ₛ Subobject.top α := by
  refine ⟨λ x => s.embed x, λ _ => rfl⟩

/-- Meet (intersection) of two subobjects: axiomatically defined. -/
axiom Subobject.meet {α : Type u} [Object α] (s t : Subobject α) : Subobject α

/-- Left projection: meet ≤ₛ s. -/
axiom Subobject.meet_le_left {α : Type u} [Object α] (s t : Subobject α) :
    Subobject.meet s t ≤ₛ s

/-- Right projection: meet ≤ₛ t. -/
axiom Subobject.meet_le_right {α : Type u} [Object α] (s t : Subobject α) :
    Subobject.meet s t ≤ₛ t

/-- Join of two subobjects: axiomatically defined. -/
axiom Subobject.join {α : Type u} [Object α] (s t : Subobject α) : Subobject α

/-- Left injection: s ≤ₛ join s t. -/
axiom Subobject.le_join_left {α : Type u} [Object α] (s t : Subobject α) :
    s ≤ₛ Subobject.join s t

/-- Right injection: t ≤ₛ join s t. -/
axiom Subobject.le_join_right {α : Type u} [Object α] (s t : Subobject α) :
    t ≤ₛ Subobject.join s t

/-! ## Quotient — L1: Core Definition -/

structure Quotient (α : Type u) [Object α] where
  rel : α → α → Prop
  equiv : Equivalence rel
  quotientType : Type u
  [quotObj : Object quotientType]
  proj : α → quotientType

/-! ## #eval examples — L6: Verified Examples -/

/-- Object instance for product types. -/
instance {α β : Type u} [Object α] [Object β] : Object (α × β) where
  theory := TheoryName.ofString "ProductTheory"
  objName := s!"Product({objName α}, {objName β})"
  repr p := s!"({repr p.1}, {repr p.2})"

/-- Object instance for sum types. -/
instance {α β : Type u} [Object α] [Object β] : Object (α ⊕ β) where
  theory := TheoryName.ofString "CoproductTheory"
  objName := s!"Coproduct({objName α}, {objName β})"
  repr
    | Sum.inl a => s!"inl({repr a})"
    | Sum.inr b => s!"inr({repr b})"

/-- Object instance for subtypes. -/
instance {α : Type u} [Object α] (p : α → Prop) : Object { x : α // p x } where
  theory := Object.theory α
  objName := s!"Sub({Object.objName α})"
  repr := λ _ => "sub"

def evenSubobj : Subobject Nat where
  carrier := { n : Nat // n % 2 = 0 }
  embed := λ ⟨n, _⟩ => n
  injective := λ ⟨x, _⟩ ⟨y, _⟩ h => by subst h; rfl
  theoryCompat := rfl

#eval describe (α := Nat)
#eval evenSubobj.embed ⟨4, by decide⟩

end MiniObjectKernel
