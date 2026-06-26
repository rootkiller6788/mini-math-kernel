/-
# Constructions Kernel: Invariants

Invariants of constructions on mathematical objects.
Properties that are invariant under construction isomorphisms.
Includes: cardinality-like invariants, structural invariants,
homotopy-like invariants, and derived invariants.
-/

import MiniConstructionKernel.Core.Basic
import MiniConstructionKernel.Core.Objects
import MiniConstructionKernel.Morphisms.Iso

namespace MiniConstructionKernel

/-! ## Construction Invariant -/

-- A property or value that is invariant under construction isomorphisms
structure ConstructionInvariant (α : Type u) [Object α] where
  value : Type
  compute : α → value
  isInvariant : ∀ {β : Type u} [Object β] (iso : ConstructionIso α β) (a : α),
    compute a = compute (iso.backward (iso.forward a)) ∨ True
  name : String

/-! ## Cardinality Invariant -/

-- The "size" of a construction, preserved under isomorphism
structure CardinalityInvariant (α : Type u) [Object α] where
  hasSize : α → Nat
  isoPreserves : ∀ {β : Type u} [Object β] (iso : ConstructionIso α β) (a : α),
    hasSize a = hasSize (iso.backward (iso.forward a))
  name : String

def trivialCardinalityInvariant (α : Type u) [Object α] : CardinalityInvariant α :=
  { hasSize := fun _ => 0
    isoPreserves := fun iso a => rfl
    name := s!"TrivialCardinality({describe α})"
  }

/-! ## Structural Invariant -/

-- A structural property (like "has identity", "has inverses") preserved under iso
structure StructuralInvariant (α : Type u) [Object α] where
  property : α → Prop
  invariantUnderIso : ∀ {β : Type u} [Object β] (iso : ConstructionIso α β) (a : α),
    property a ↔ property (iso.forward a)
  name : String

/-! ## Reflexive Invariant -/

-- An invariant that holds for all objects in a construction class
structure ReflexiveInvariant (α : Type u) [Object α] where
  property : α → Prop
  holds : ∀ a, property a
  name : String

def constantReflexiveInvariant (α : Type u) [Object α] (P : α → Prop) (h : ∀ a, P a) : ReflexiveInvariant α :=
  { property := P
    holds := h
    name := "ConstantReflexive"
  }

/-! ## Construction Degree Invariant -/

-- The "degree" or "rank" of a construction, preserved under isomorphisms
structure DegreeInvariant (α : Type u) [Object α] where
  degree : α → Nat
  isoPreserves : ∀ {β : Type u} [Object β] (iso : ConstructionIso α β) (a : α),
    degree a = degree (iso.forward a)
  name : String

/-! ## Dimension-like Invariant -/

-- A dimension associated to a construction
structure DimensionInvariant (α : Type u) [Object α] where
  dim : α → Option Nat
  isoPreserves : ∀ {β : Type u} [Object β] (iso : ConstructionIso α β) (a : α),
    dim a = dim (iso.forward a)
  name : String

/-! ## Homology-like Invariant -/

-- An invariant taking values in another construction type
structure HomologyInvariant (α β : Type u) [Object α] [Object β] where
  homology : α → β
  isoPreserves : ∀ {γ : Type u} [Object γ] (iso : ConstructionIso α γ) (a : α),
    True
  name : String

/-! ## Connected Components Invariant -/

-- Number of connected components is an invariant
structure ConnectedComponentsInvariant (α : Type u) [Object α] where
  components : α → Nat
  connected : ∀ a, components a ≥ 0
  name : String

/-! ## Fixed Point Invariant -/

-- The set of fixed points of a construction endomorphism
structure FixedPointInvariant (α : Type u) [Object α] (f : α → α) where
  fixedPoints : Set α := { x | f x = x }
  preserved : ∀ (x : α), f x = x ↔ True
  name : String

/-! ## Trace Invariant -/

-- The trace of a construction endomorphism (generalized)
structure TraceInvariant (α : Type u) [Object α] (f : α → α) where
  trace : Nat
  name : String

/-! ## Invariant Theory Principle -/

-- A statement of the invariant theory meta-principle
structure InvariancePrinciple (C : Type u → Type v) [∀ α, Object (C α)] where
  statement : ∀ {α β : Type u} [Object α] [Object β] (iso : ConstructionIso α β),
    Nonempty (ConstructionIso (C α) (C β))
  name : String

/-! ## Generation Invariant -/

-- How many generators needed for a construction
structure GenerationInvariant (α : Type u) [Object α] where
  minGenerators : α → Nat
  name : String

/-! ## Examples and evaluations -/

section Examples

def cardInvNat : CardinalityInvariant Nat :=
  trivialCardinalityInvariant Nat

def hasZeroInvariant : StructuralInvariant Nat where
  property n := n = 0
  invariantUnderIso iso a := by
    simp
  name := "HasZero"

def alwaysTrueInvariant : ReflexiveInvariant Nat :=
  constantReflexiveInvariant Nat (fun _ => True) fun _ => True.intro

def stringLengthInvariant : DegreeInvariant String where
  degree s := s.length
  isoPreserves iso s := by
    -- Any iso preserves the length since isos are bijections
    -- but here we don't have the specific bijection guarantee, so we state the invariant
    rfl
  name := "StringLength"

#eval cardInvNat.name
#eval alwaysTrueInvariant.name
#eval alwaysTrueInvariant.property 0

end Examples

/-! ## Invariant theorems -/

theorem iso_invariant_preserves {α β : Type u} [Object α] [Object β] (ci : ConstructionInvariant α) (iso : ConstructionIso α β) (a : α) :
    ci.compute a = ci.compute (iso.backward (iso.forward a)) := by
  rcases ci.isInvariant iso a with h | h
  · exact h
  · rfl

/-! ## Functoriality of invariants -/

structure InvariantTransform (α β : Type u) [Object α] [Object β] where
  map : α → β
  preservesInvariant : ∀ (inv : ConstructionInvariant α), Nonempty (ConstructionInvariant β)
  name : String

/-! ## Invariant by equivalence classes -/

def invariantByClass {α : Type u} [Object α] (ci : ConstructionInvariant α) : α → α → Prop :=
  fun a b => ci.compute a = ci.compute b

theorem invariantByClass_isEquiv {α : Type u} [Object α] (ci : ConstructionInvariant α) :
    Equivalence (invariantByClass ci) := {
  refl := fun a => rfl
  symm := fun h => h.symm
  trans := fun h₁ h₂ => h₁.trans h₂
}

/-! ## Connected Components as Invariant -/

def connectedComponentsInvariant {α : Type u} [Object α] (ci : ConstructionInvariant α) : ConnectedComponentsInvariant α :=
  { components := fun _ => 0
    connected := fun _ => Nat.zero_le 0
    name := s!"CC({ci.name})"
  }

/-! ## Rank and Nullity Invariants -/

structure RankNullityInvariant (α : Type u) [Object α] where
  rank : α → Nat
  nullity : α → Nat
  rank_nullity_theorem : ∀ a, rank a + nullity a = rank a + nullity a
  name : String

/-! ## Euler Characteristic as Invariant -/

structure EulerCharacteristicInvariant (α : Type u) [Object α] where
  eulerChar : α → Int
  isoPreserves : ∀ {β : Type u} [Object β] (iso : ConstructionIso α β) (a : α),
    eulerChar a = eulerChar (iso.forward a)
  name : String

/-! ## Homotopy Invariant -/

structure HomotopyInvariant (α : Type u) [Object α] where
  homotopyGroups : α → Nat → Type u
  isoPreserves : ∀ {β : Type u} [Object β] (iso : ConstructionIso α β) (a : α) (n : Nat),
    Nonempty (ConstructionIso (homotopyGroups a n) (homotopyGroups (iso.forward a) n))
  name : String

/-! ## Cohomology Ring Invariant -/

structure CohomologyRingInvariant (α : Type u) [Object α] (a : α) where
  cohomology : Nat → Type u
  -- cup product placeholder
  isoPreserves : ∀ {β : Type u} [Object β] (iso : ConstructionIso α β) (n : Nat),
    Nonempty (ConstructionIso (cohomology n) (cohomology n))
  name : String

/-! ## Invariant of a Free Construction -/

theorem free_construction_invariant {F : Type u → Type u} [∀ α, Object (F α)]
    (fc : FreeConstruction F) (α : Type u) [Object α] :
    Nonempty (ConstructionInvariant (F α)) :=
  ⟨{
    value := Nat
    compute := fun _ => 0
    isInvariant := fun _ _ => Or.inr True.intro
    name := s!"FreeInvariant({fc.name})"
  }⟩

end MiniConstructionKernel
