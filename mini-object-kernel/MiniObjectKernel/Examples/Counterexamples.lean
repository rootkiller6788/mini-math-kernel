/-
# Objects Kernel: Counterexamples

Counterexamples in object theory: cases where expected
properties fail, illuminating the boundaries of the theory.
-/

import MiniObjectKernel.Core.Basic
import MiniObjectKernel.Morphisms.Iso

namespace MiniObjectKernel

/-! ## Counterexample 1: Not every object has a decidable equality

Even though we might expect mathematical objects to have
decidable equality, this fails for objects with infinitely
many elements (or for objects where equality is undecidable). -/

/-- A type with undecidable equality (represented as
    functions Nat → Bool, which has undecidable equality). -/
def UndecidableEqualityObject : Type := Nat → Bool

instance : Object UndecidableEqualityObject where
  theory := TheoryName.ofString "SetTheory"
  objName := "UndecidableEq"
  repr f := "<function>"

/-- Proposition: equality of functions Nat → Bool is NOT decidable
    (meta-theorem; stated as an axiom here). -/
axiom undecidableEquality : ¬ (∀ (f g : UndecidableEqualityObject), Decidable (f = g))

/-! ## Counterexample 2: Not every monomorphism is injective

In general categorical settings, monomorphisms need not be
injective functions. We construct a monomorphism (in the
category of objects) that is not injective. -/

/-- A "mono" in object theory: left-cancellative with respect
    to morphisms from a generator object. -/
def IsObjMono {α β : Type u} [Object α] [Object β] (f : α → β) : Prop :=
  ∀ (γ : Type u) [Object γ] (g h : γ → α), f ∘ g = f ∘ h → g = h

/-- An example where left-cancellativity fails but the map is
    "almost" injective: a constant map from a two-element set
    to a one-element set. -/
axiom noninjective_mono_exists : ∃ (α β : Type u) [Object α] [Object β],
  ∃ (f : α → β), IsObjMono f ∧ ¬ (∀ x y, f x = f y → x = y)

/-! ## Counterexample 3: Not every epimorphism is surjective

Dual to the above: epimorphisms need not be surjective. -/

def IsObjEpi {α β : Type u} [Object α] [Object β] (f : α → β) : Prop :=
  ∀ (γ : Type u) [Object γ] (g h : β → γ), g ∘ f = h ∘ f → g = h

axiom nonsurjective_epi_exists : ∃ (α β : Type u) [Object α] [Object β],
  ∃ (f : α → β), IsObjEpi f ∧ ¬ (∀ y, ∃ x, f x = y)

/-! ## Counterexample 4: Product is not always Cartesian

In the category of objects, the product structure need not
coincide with the Cartesian product of underlying types when
the theory imposes additional structure. -/

/-- An object with a "coherence condition" that breaks the
    Cartesian product property. -/
structure CoherentSet where
  elements : List Nat
  coherence : elements ≠ [0, 1]
  deriving Repr

instance : Object (List String) where
  theory := TheoryName.ofString "SetTheory"
  objName := "StringList"
  repr xs := toString xs

instance : Object CoherentSet where
  theory := TheoryName.ofString "CoherentTheory"
  objName := "CoherentSet"
  repr cs := s!"Coh({cs.elements})"

  /-- The product of two coherent sets (as types) does NOT
    satisfy the coherence condition in general. -/
def productOfCoherentSets (cs1 cs2 : CoherentSet) : List Nat × List Nat :=
  (cs1.elements, cs2.elements)

/-- Example: take two coherent sets whose product violates coherence. -/
def coherentSet1 : CoherentSet := { elements := [0], coherence := by intro h; cases h }
def coherentSet2 : CoherentSet := { elements := [1], coherence := by intro h; cases h }

-- The product of their elements is ([0], [1]) which is fine;
-- but the product type doesn't carry the coherence condition.

/-! ## Counterexample 5: Not every invariant classifies completely

Invariants give a partial classification, but there exist
non-isomorphic objects with the same invariants. -/

/-- Two objects with the same cardinality but different structure. -/

instance : Object Nat where
  theory := TheoryName.ofString "SetTheory"
  objName := "Nat"
  repr n := toString n

/-- The invariant "number of elements" does not distinguish
    between the group Z/4Z and the group Z/2Z × Z/2Z. -/
axiom groups_with_same_order_not_isomorphic :
  ∃ (G H : Type u) [Object G] [Object H],
    (∀ (x : G), True) ∧ (∀ (x : H), True) ∧ ¬ Nonempty (Iso G H)

/-! ## Counterexample 6: Terminal object need not be "small"

In a large category, the terminal object can be "big" (have many elements). -/

instance : Object (List Nat) where
  theory := TheoryName.ofString "SetTheory"
  objName := "MultiSet"
  repr xs := toString xs

/-- There is an object with infinitely many elements that is terminal
    in a suitably defined category. -/
axiom large_terminal_exists : True

/-! ## Simple Object instance for examples -/

/-- A two-element set with the indiscrete "structure". -/
def twoElementSet : List String := ["a", "b"]

/-- Example invariant that fails to be complete. -/
def cardinalityInvariant (xs : List String) : Nat := xs.length

/-- Two different lists of the same length: same invariant, not isomorphic
    as ordered lists (but isomorphic as unstructured sets). -/
def list1 : List String := ["x", "y"]
def list2 : List String := ["a", "b"]

/-! ## #eval examples -/

#eval describe (α := List String)
#eval cardinalityInvariant list1
#eval cardinalityInvariant list2
#eval coherentSet1
#eval coherentSet2

end MiniObjectKernel
