/-
# Objects Kernel: Invariants

Invariants of mathematical objects: properties that are
preserved under isomorphism and characterize objects up to
categorical equivalence.
-/

import MiniObjectKernel.Core.Basic

namespace MiniObjectKernel

/-! ## Invariant typeclass

An `Invariant` for objects of type `α` is a function `α → β`
(for some value type `β`) whose value classifies the object
up to isomorphism within its category. -/

class Invariant (α : Type u) [Object α] (β : Type v) where
  compute : α → β
  name : String
  description : String

export Invariant (compute)

/-- Cardinality as an invariant: the "size" of an object,
    represented as a cardinal number (approximated by `Nat` or `∞`). -/
inductive Cardinality where
  | finite (n : Nat)
  | infinite
  | uncountable
  deriving BEq, Repr, Inhabited

def Cardinality.add (a b : Cardinality) : Cardinality :=
  match a, b with
  | finite n, finite m => finite (n + m)
  | _, _ => a.max b
where
  max (x y : Cardinality) : Cardinality :=
    match x, y with
    | uncountable, _ => uncountable
    | _, uncountable => uncountable
    | infinite, _ => infinite
    | _, infinite => infinite
    | finite n, finite m => finite (max n m)

instance : Add Cardinality where
  add := Cardinality.add

def Cardinality.mult (a b : Cardinality) : Cardinality :=
  match a, b with
  | finite n, finite m => finite (n * m)
  | finite 0, _ => finite 0
  | _, finite 0 => finite 0
  | _, _ => b.max a
where
  max (x y : Cardinality) : Cardinality :=
    match x, y with
    | uncountable, _ => uncountable
    | _, uncountable => uncountable
    | infinite, _ => infinite
    | _, infinite => infinite
    | finite n, finite m => finite (max n m)

instance : Mul Cardinality where
  mul := Cardinality.mult

/-- Rank invariant: the minimal number of generators (for algebraic objects),
    or the dimension (for vector spaces / free objects). -/
structure Rank where
  value : Cardinality
  isMinimal : Bool
  deriving Repr, Inhabited

def Rank.zero : Rank := { value := Cardinality.finite 0, isMinimal := true }
def Rank.one : Rank := { value := Cardinality.finite 1, isMinimal := true }
def Rank.ofNat (n : Nat) : Rank := { value := Cardinality.finite n, isMinimal := false }

/-- Dimension invariant: for objects with a notion of basis or dimension. -/
structure Dimension where
  dim : Cardinality
  field : String
  deriving Repr, Inhabited

/-- Structure invariant: the internal categorical structure of an object
    (e.g., group axioms, ring axioms). -/
structure StructureInvariant where
  axioms : List String
  operations : List String
  deriving Repr, Inhabited

instance : ToString StructureInvariant where
  toString si :=
    s!"Axioms: {String.intercalate ", " si.axioms}; Ops: {String.intercalate ", " si.operations}"

/-! ## Object instance for examples -/

instance : Object (List Nat) where
  theory := TheoryName.ofString "SetTheory"
  objName := "NatList"
  repr xs := toString xs

/-- Compute the cardinality of a finite list. -/
noncomputable def cardinalityOfList (xs : List Nat) : Cardinality :=
  Cardinality.finite xs.length

/-- Example invariant: length of a list. -/
instance : Invariant (List Nat) Cardinality where
  compute := cardinalityOfList
  name := "listLength"
  description := "The number of elements in the list"

/-- Example invariant: whether a list is sorted. -/
instance : Invariant (List Nat) Bool where
  compute xs :=
    match xs with
    | [] => true
    | [x] => true
    | x :: y :: rest => x ≤ y && compute (y :: rest)
  name := "isSorted"
  description := "Whether the list elements are in nondecreasing order"

/-! ## Invariant comparison and classification -/

/-- Two objects have the same invariant value (for a given invariant). -/
def sameInvariant {α : Type u} [Object α] {β : Type v} {γ : Type w} [DecidableEq γ]
    [Invariant α β] (proj : β → γ) (x y : α) : Bool :=
  proj (compute x) == proj (compute y)

/-- Objects are classified the same if they agree on all named invariants. -/
structure ClassifiedBy (α : Type u) [Object α] where
  invariants : List (String × String)
  deriving Repr

/-! ## #eval examples -/

#eval describe (α := List Nat)
#eval cardinalityOfList [1, 2, 3]
#eval cardinalityOfList ([] : List Nat)
#eval "Invariant framework defined for Object typeclass"

end MiniObjectKernel
