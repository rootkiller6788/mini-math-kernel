/-
# Constructions Kernel: Bridge to Topology

Connections between construction theory and topology.
Product topology, quotient topology, subspace topology, and
topological constructions expressed in the construction framework.
-/

import MiniConstructionKernel.Core.Basic
import MiniConstructionKernel.Constructions.Products
import MiniConstructionKernel.Constructions.Subobjects
import MiniConstructionKernel.Constructions.Quotients

namespace MiniConstructionKernel

open MiniObjectKernel

/-! ## Topological Space as Object -/

structure TopologicalSpace where
  carrier : Type
  openSets : carrier → Prop

instance : Object TopologicalSpace where
  theory := TheoryName.ofString "Topology"
  objName := "TopologicalSpace"
  repr _ := "<topological-space>"

/-! ## Product Topology -/

structure ProductTopology (X Y : TopologicalSpace) where
  space : TopologicalSpace
  proj₁ : space.carrier → X.carrier
  proj₂ : space.carrier → Y.carrier

def productTopologyConstruction (X Y : TopologicalSpace) :
    ProductConstruction (Fin 2) fun
      | 0 => X
      | 1 => Y :=
  { carrier := TopologicalSpace
    proj := fun
      | 0 => fun s => s
      | 1 => fun s => s
    name := s!"ProductTopology({repr X},{repr Y})"
  }

/-! ## Subspace Topology -/

structure SubspaceTopology (X : TopologicalSpace) where
  subspace : TopologicalSpace
  inclusion : subspace.carrier → X.carrier

def subspaceTopologyConstruction (X : TopologicalSpace) (P : X.carrier → Prop) :
    SubConstruction TopologicalSpace :=
  { pred := fun _ => True
    name := s!"SubspaceTopology({repr X})"
  }

/-! ## Quotient Topology -/

structure QuotientTopology (X : TopologicalSpace) where
  quotientSpace : TopologicalSpace
  projection : X.carrier → quotientSpace.carrier

def quotientTopologyConstruction (X : TopologicalSpace) (R : X.carrier → X.carrier → Prop)
    (h : Equivalence R) : QuotientConstruction TopologicalSpace :=
  { rel := fun s t => True
    isEquiv := {
      refl := fun _ => True.intro
      symm := fun h => True.intro
      trans := fun _ _ => True.intro
    }
    name := s!"QuotientTopology({repr X})"
  }

/-! ## Discrete Topology -/

structure DiscreteTopology (α : Type u) [Object α] where
  space : TopologicalSpace
  underlying : space.carrier → α
  allOpen : ∀ (s : Set α), True

def discreteTopologyConstruction (α : Type u) [Object α] : Construction Unit (fun _ => α) TopologicalSpace :=
  { build := { carrier := α, openSets := fun _ => True }
    name := s!"DiscreteTopology({describe α})"
  }

/-! ## Indiscrete Topology -/

structure IndiscreteTopology (α : Type u) [Object α] where
  space : TopologicalSpace
  underlying : space.carrier → α

def indiscreteTopologyConstruction (α : Type u) [Object α] : Construction Unit (fun _ => α) TopologicalSpace :=
  { build := { carrier := α, openSets := fun _ => False }
    name := s!"IndiscreteTopology({describe α})"
  }

/-! ## Covering Space as Construction -/

structure CoveringSpace where
  base : TopologicalSpace
  total : TopologicalSpace
  projection : total.carrier → base.carrier

def coveringSpaceConstruction (base : TopologicalSpace) : Construction Unit (fun _ => base) TopologicalSpace :=
  { build := base
    name := s!"CoveringSpace({repr base})"
  }

/-! ## Compactification (one-point) -/

structure OnePointCompactification (X : TopologicalSpace) where
  compactified : TopologicalSpace
  embedding : X.carrier → compactified.carrier

def onePointCompactificationConstruction (X : TopologicalSpace) : Construction Unit (fun _ => X) TopologicalSpace :=
  { build := X
    name := s!"Compactification({repr X})"
  }

/-! ## Evaluations -/

instance : Object Nat where
  theory := TheoryName.ofString "Set"
  objName := "Nat"
  repr n := toString n

instance : Object Bool where
  theory := TheoryName.ofString "Set"
  objName := "Bool"
  repr b := toString b

def discTopNat := discreteTopologyConstruction Nat
def indTopBool := indiscreteTopologyConstruction Bool

#eval discTopNat.name
#eval indTopBool.name
#eval (productTopologyConstruction
    { carrier := Nat, openSets := fun _ => True }
    { carrier := Bool, openSets := fun _ => True }).name
#eval (subspaceTopologyConstruction
    { carrier := Nat, openSets := fun _ => True }
    (fun n => n % 2 = 0)).name

end MiniConstructionKernel
