/-
# Objects Kernel: Subobjects, Quotients, Dependency — L1/L2 Structures

Provides Subobject, Quotient, Dependency definitions for all modules.
-/

import MiniObjectKernel.Core.Basic

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

structure Subobject (α : Type) [Object α] where
  carrier : Type
  [obj : Object carrier]
  embed : carrier → α
  injective : ∀ x y, embed x = embed y → x = y

/-- Subobject inclusion: s ≤ t if s factors through t's embedding. -/
def Subobject.le {α : Type} [Object α] (s t : Subobject α) : Prop :=
  ∃ (f : s.carrier → t.carrier), ∀ (x : s.carrier), t.embed (f x) = s.embed x

/-- The top subobject: the whole object α. -/
def Subobject.top (α : Type) [Object α] : Subobject α where
  carrier := α
  embed := id
  injective := λ _ _ h => h

/-- The bottom subobject: the empty carrier. -/
def Subobject.bot (α : Type) [Object α] : Subobject α where
  carrier := Empty
  embed := λ e => nomatch e
  injective := λ x _ _ => nomatch x

/-! ## Quotient — L1: Core Definition -/

structure Quotient (α : Type) [Object α] where
  rel : α → α → Prop
  isEquiv : Equivalence rel
  quotientType : Type
  [quotObj : Object quotientType]
  proj : α → quotientType

/-! ## #eval examples — L6: Verified Examples -/

/-- Object instance for subtypes. -/
instance {α : Type} [Object α] (p : α → Prop) : Object { x : α // p x } where
  theory := Object.theory α
  objName := s!"Sub({Object.objName α})"
  repr := λ _ => "sub"

def evenSubobj : Subobject Nat where
  carrier := { n : Nat // n % 2 = 0 }
  embed := λ ⟨n, _⟩ => n
  injective := λ ⟨x, _⟩ ⟨y, _⟩ h => by subst h; rfl

#eval describe (α := Nat)
#eval evenSubobj.embed ⟨4, by decide⟩

end MiniObjectKernel
