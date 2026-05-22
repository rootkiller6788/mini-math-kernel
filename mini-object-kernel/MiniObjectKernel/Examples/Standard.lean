/-
# Objects Kernel: Standard Examples

Standard examples of mathematical objects:
Set, Group, Ring as Object instances.
Free object on one generator.
Trivial group as terminal, empty set as initial.
-/

import MiniObjectKernel.Core.Basic

namespace MiniObjectKernel

/-! ## Set as an Object

A set is the simplest mathematical object: no structure, just elements. -/

instance : Object (List String) where
  theory := TheoryName.ofString "SetTheory"
  objName := "Set"
  repr xs := "{" ++ String.intercalate ", " (xs.map (λ s => "\"" ++ s ++ "\"")) ++ "}"

/-- The theory of sets. -/
def setTheory : TheoryName := TheoryName.ofString "SetTheory"

/-- An element of a set (represented as a list for simplicity). -/
def setMember (xs : List String) (x : String) : Bool :=
  xs.elem x

/-- Empty set is initial in the category of sets. -/
instance : Object Unit where
  theory := setTheory
  objName := "EmptySet"
  repr _ := "∅"

def emptySet : List String := []

/-- Singleton set. -/
def singletonSet (x : String) : List String := [x]

/-! ## Group as an Object

A group is a set with associative binary operation, identity, and inverses. -/

/-- Represent a finite group as a list of elements with a multiplication table. -/
structure GroupObject where
  elements : List String
  identity : String
  multiply : String → String → String
  inverse : String → String
  deriving Repr

instance : Object GroupObject where
  theory := TheoryName.ofString "Algebra.GroupTheory"
  objName := "Group"
  repr g := s!"Group({g.elements.length} elements, id={g.identity})"

/-- The trivial group (one element): terminal in the category of groups. -/
def trivialGroup : GroupObject :=
  { elements := ["e"]
    identity := "e"
    multiply := λ _ _ => "e"
    inverse := λ _ => "e"
  }

/-- Group axioms as predicates. -/
def groupAxiomsHold (g : GroupObject) : Prop :=
  (∀ a b c, g.multiply (g.multiply a b) c = g.multiply a (g.multiply b c))  -- associativity
  ∧ (∀ a, g.multiply g.identity a = a ∧ g.multiply a g.identity = a)         -- identity
  ∧ (∀ a, g.multiply (g.inverse a) a = g.identity ∧ g.multiply a (g.inverse a) = g.identity) -- inverse

theorem trivialGroup_axioms : groupAxiomsHold trivialGroup := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c; rfl
  · intro a; exact ⟨rfl, rfl⟩
  · intro a; exact ⟨rfl, rfl⟩

/-! ## Ring as an Object

A ring is a set with two operations (addition and multiplication)
satisfying ring axioms. -/

structure RingObject where
  elements : List String
  zero : String
  one : String
  add : String → String → String
  mul : String → String → String
  neg : String → String
  deriving Repr

instance : Object RingObject where
  theory := TheoryName.ofString "Algebra.RingTheory"
  objName := "Ring"
  repr r := s!"Ring({r.elements.length} elements)"

/-- The zero ring: the terminal object in the category of rings. -/
def zeroRing : RingObject :=
  { elements := ["0"]
    zero := "0"
    one := "0"
    add := λ _ _ => "0"
    mul := λ _ _ => "0"
    neg := λ _ => "0"
  }

/-- The ring of integers (as a finitely presented algebraic object). -/
def integerRing : RingObject :=
  { elements := ["0", "1", "-1"]
    zero := "0"
    one := "1"
    add := λ a b =>
      if a == "0" then b
      else if b == "0" then a
      else if a == "1" && b == "1" then "-1"
      else if a == "-1" && b == "-1" then "1"
      else "0"
    mul := λ a b =>
      if a == "0" ∨ b == "0" then "0"
      else if a == "1" then b
      else if b == "1" then a
      else if a == "-1" && b == "-1" then "1"
      else "-1"
    neg := λ a =>
      if a == "1" then "-1"
      else if a == "-1" then "1"
      else "0"
  }

/-! ## Free Object on One Generator

The free object on one generator in a theory T: the "most general"
object with a single distinguished element. -/

/-- The free object on one generator: represented as expressions
    built from a single generator symbol. -/
inductive FreeOnOneGenerator (T : TheoryName) where
  | gen : FreeOnOneGenerator T
  | constant : String → FreeOnOneGenerator T
  | op : String → FreeOnOneGenerator T → FreeOnOneGenerator T → FreeOnOneGenerator T
  deriving Repr

instance (T : TheoryName) : Object (FreeOnOneGenerator T) where
  theory := T
  objName := s!"Free({T}, 1)"
  repr := λ _ => s!"F({T}, 1)"

/-- The generator element of the free object on one generator. -/
def freeGenerator {T : TheoryName} : FreeOnOneGenerator T := .gen

/-- Map out of the free object: given a target object α and
    an element a : α, there is a unique morphism sending gen to a. -/
axiom freeObjectUniversal {T : TheoryName} {α : Type u} [Object α]
    (a : α) : FreeOnOneGenerator T → α

/-! ## Terminal and Initial Objects

Terminal objects have a unique morphism from every object.
Initial objects have a unique morphism to every object. -/

instance : Object Empty where
  theory := TheoryName.root
  objName := "Initial"
  repr e := nomatch e

/-- Unit is terminal. -/
theorem unit_isTerminal : ∀ (β : Type u) [Object β], ∃! f : β → Unit, True := by
  intro β _
  refine ⟨λ _ => (), trivial, ?_⟩
  intro f _
  funext x; cases f x; rfl

/-- Empty is initial. -/
theorem empty_isInitial : ∀ (β : Type u) [Object β], ∃! f : Empty → β, True := by
  intro β _
  refine ⟨λ e => nomatch e, trivial, ?_⟩
  intro f _
  funext e; nomatch e

/-! ## Morphism between standard objects

Example morphisms between standard objects. -/

/-- The trivial morphism from any group to the trivial group. -/
def toTrivialGroup (g : GroupObject) : GroupObject → GroupObject := λ _ => trivialGroup

/-- The zero morphism from any ring to the zero ring. -/
def toZeroRing (r : RingObject) : RingObject → RingObject := λ _ => zeroRing

/-! ## #eval examples -/

#eval describe (α := List String)
#eval setMember ["a", "b", "c"] "b"
#eval trivialGroup
#eval zeroRing
#eval freeGenerator (T := TheoryName.ofString "Group")

end MiniObjectKernel
