/-
# Objects Kernel: Bridge to Topology

Connections between object theory and topology:
Topological spaces, continuous maps, homotopy, and their
object-theoretic representations.
-/

import MiniObjectKernel.Core.Basic

namespace MiniObjectKernel

/-! ## Topological Theory names -/

def topologicalSpaceTheory : TheoryName := TheoryName.ofString "Topology.TopologicalSpace"
def metricSpaceTheory : TheoryName := TheoryName.ofString "Topology.MetricSpace"
def homotopyTheory : TheoryName := TheoryName.ofString "Topology.HomotopyTheory"

/-! ## Topological Space as an Object

A topological space is a set together with a collection of
"open" subsets satisfying the standard axioms. -/

/-- A topology on a type α: a predicate on subsets of α
    satisfying the topology axioms. -/
structure Topology (α : Type u) where
  isOpen : Set α → Prop
  univ_open : isOpen Set.univ
  empty_open : isOpen ∅
  inter_open : ∀ (U V : Set α), isOpen U → isOpen V → isOpen (U ∩ V)
  union_open : ∀ (S : Set (Set α)), (∀ U ∈ S, isOpen U) → isOpen (⋃₀ S)
  deriving Repr

/-- A topological space object: a carrier type α with an Object instance
    and a Topology structure. -/
structure TopologicalSpaceObj where
  carrier : Type u
  [obj : Object carrier]
  topology : Topology carrier
  deriving Repr

instance (T : TopologicalSpaceObj) : Object T.carrier := T.obj

/-- The discrete topology on any type: all subsets are open. -/
def discreteTopology (α : Type u) : Topology α where
  isOpen _ := True
  univ_open := trivial
  empty_open := trivial
  inter_open := λ _ _ _ _ => trivial
  union_open := λ _ _ => trivial

/-- The indiscrete topology: only the empty set and the whole space are open. -/
def indiscreteTopology (α : Type u) : Topology α where
  isOpen U := U = ∅ ∨ U = Set.univ
  univ_open := Or.inr rfl
  empty_open := Or.inl rfl
  inter_open := λ U V hU hV => by
    match hU, hV with
    | Or.inl hU, _ => have : U ∩ V = ∅ := by
        ext x; simp [hU]
      rw [this]; exact Or.inl rfl
    | _, Or.inl hV => have : U ∩ V = ∅ := by
        ext x; simp [hV]
      rw [this]; exact Or.inl rfl
    | Or.inr hU, Or.inr hV => have : U ∩ V = Set.univ := by
        ext x; simp [hU, hV]
      rw [this]; exact Or.inr rfl
  union_open := λ S hS => by
    by_cases h : ∃ U ∈ S, U = Set.univ
    · obtain ⟨U, hU, hU_eq⟩ := h
      have : ⋃₀ S = Set.univ := by
        apply Set.Subset.antisymm (by intro x _; trivial)
        intro x _
        apply Set.mem_sUnion.mpr
        exact ⟨U, hU, by rw [hU_eq]; trivial⟩
      rw [this]; exact Or.inr rfl
    · refine Or.inl ?_
      ext x; constructor
      · intro hxU; exact Set.not_mem_empty x hxU
      · intro hxE; exact Set.not_mem_empty x hxE

/-- A specific topological space: the real line (represented as a
    type with open intervals as the basis). -/
def realLine : TopologicalSpaceObj where
  carrier := Nat  -- placeholder; real topology uses intervals
  topology := discreteTopology Nat

/-! ## Continuous Map

A continuous map between topological spaces: the preimage
of every open set is open. -/

def ContinuousMap (X Y : TopologicalSpaceObj) : Type (max u v) :=
  { f : X.carrier → Y.carrier //
    ∀ (V : Set Y.carrier), Y.topology.isOpen V → X.topology.isOpen (f ⁻¹' V) }

/-- The identity map is continuous. -/
def continuousIdentity (X : TopologicalSpaceObj) : ContinuousMap X X :=
  ⟨id, λ V hV => by simpa using hV⟩

/-- Composition of continuous maps is continuous. -/
def continuousComposition {X Y Z : TopologicalSpaceObj}
    (g : ContinuousMap Y Z) (f : ContinuousMap X Y) : ContinuousMap X Z :=
  ⟨g.val ∘ f.val, λ V hV => by
    have hg : X.topology.isOpen (f.val ⁻¹' (g.val ⁻¹' V)) :=
      f.property (g.val ⁻¹' V) (g.property V hV)
    simpa using hg
  ⟩

/-! ## Homotopy

Two continuous maps f, g : X → Y are homotopic if there is
a continuous map H : X × I → Y such that H(x,0) = f(x) and H(x,1) = g(x). -/

/-- The unit interval as a topological space. -/
def unitInterval : TopologicalSpaceObj where
  carrier := Nat  -- placeholder: [0,1]
  topology := discreteTopology Nat

/-- Homotopy between two continuous maps. -/
def Homotopy (X Y : TopologicalSpaceObj) (f g : ContinuousMap X Y) : Prop :=
  ∃ (H : ContinuousMap (X ×' unitInterval) Y),
    (∀ x, H.val (x, 0) = f.val x) ∧ (∀ x, H.val (x, 1) = g.val x)
where
  X ×' I : TopologicalSpaceObj := {
    carrier := X.carrier × unitInterval.carrier
    topology := discreteTopology _
  }

/-- Homotopy equivalence between two topological spaces. -/
def HomotopyEquivalent (X Y : TopologicalSpaceObj) : Prop :=
  ∃ (f : ContinuousMap X Y) (g : ContinuousMap Y X),
    Homotopy X X (continuousComposition g f) (continuousIdentity X) ∧
    Homotopy Y Y (continuousComposition f g) (continuousIdentity Y)

/-! ## Pointed Topological Space -/

/-- A pointed topological space: a space with a distinguished basepoint. -/
structure PointedTopologicalSpaceObj where
  space : TopologicalSpaceObj
  basepoint : space.carrier
  deriving Repr

/-! ## Connectedness and Compactness

These are invariant properties of topological spaces. -/

/-- A space is connected if it is not the disjoint union of
    two nonempty open subsets. -/
def IsConnected (X : TopologicalSpaceObj) : Prop :=
  ¬ (∃ (U V : Set X.carrier), X.topology.isOpen U ∧ X.topology.isOpen V ∧
    U ≠ ∅ ∧ V ≠ ∅ ∧ U ∩ V = ∅ ∧ U ∪ V = Set.univ)

/-- A space is compact if every open cover has a finite subcover. -/
def IsCompact (X : TopologicalSpaceObj) : Prop :=
  ∀ (C : Set (Set X.carrier)),
    (∀ U ∈ C, X.topology.isOpen U) → (⋃₀ C = Set.univ) →
    ∃ (F : Finset (Set X.carrier)), (F : Set (Set X.carrier)) ⊆ C ∧ ⋃₀ (F : Set (Set X.carrier)) = Set.univ

/-! ## Object instances for examples -/

instance : Object (List String) where
  theory := TheoryName.ofString "SetTheory"
  objName := "StringList"
  repr xs := toString xs

/-! ## #eval examples -/

#eval describe (α := List String)
#eval discreteTopology Nat
#eval indiscreteTopology Nat
#eval realLine
#eval topologicalSpaceTheory

end MiniObjectKernel
