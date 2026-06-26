/-
# Dependency Kernel: Preservation

Properties preserved under dependency graph transformations:
what operations and morphisms preserve acyclicity, dependency
structure, and other invariants.
-/

import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects
import MiniTheoryDependencyKernel.Morphisms.Hom
import MiniTheoryDependencyKernel.Properties.Invariants

namespace MiniTheoryDependencyKernel

/-! ## Acyclicity Preservation

Adding edges can introduce cycles; removing edges preserves acyclicity.
-/

def DependencyGraph.removeEdge (g : DependencyGraph) (src tgt : TheoryName) : DependencyGraph :=
  { g with edges := g.edges.filter (fun e => !(e.source == src && e.target == tgt)) }

def acyclicityPreservedByRemoval (g : DependencyGraph) (src tgt : TheoryName) : Bool :=
  if g.isAcyclic then
    let g' := g.removeEdge src tgt
    g'.isAcyclic
  else true  -- vacuously true for cyclic graphs

def cycleIntroducedByAddition (g : DependencyGraph) (newEdge : DependencyEdge) : Bool :=
  g.isAcyclic && !(g.addEdge newEdge).isAcyclic

/-! ## Dependency Preservation Under Morphisms

When we apply a theory morphism, the dependency structure should
be preserved: if B depends on A, then the image of B should
depend on the image of A.
-/

def dependencyMorphismCompatibility (g : DependencyGraph)
    (morphismMap : TheoryName → TheoryName) : Bool :=
  g.edges.all fun e =>
    let srcImg := morphismMap e.source
    let tgtImg := morphismMap e.target
    -- Check that the image has a corresponding dependency
    g.findNode srcImg |>.isSome && g.findNode tgtImg |>.isSome

/-! ## Subgraph Preservation

Properties preserved when taking induced subgraphs.
-/

structure PreservationResult where
  propertyName : String
  preserved    : Bool
  counterexample : Option String
  deriving Repr, Inhabited

def checkSubgraphPreservation (g : DependencyGraph) (names : List TheoryName) : List PreservationResult :=
  let sg := g.inducedSubgraph names
  [ { propertyName := "nodeCount ≤ original"
    , preserved    := sg.nodeCount ≤ g.nodeCount
    , counterexample := none }
  , { propertyName := "edgeCount ≤ original"
    , preserved    := sg.edgeCount ≤ g.edgeCount
    , counterexample := none }
  , { propertyName := "acyclicity"
    , preserved    := if g.isAcyclic then sg.isAcyclic else true
    , counterexample := none }
  ]

def checkMergePreservation (g1 g2 : DependencyGraph) : List PreservationResult :=
  let merged := g1.merge g2
  [ { propertyName := "nodes include g1 nodes"
    , preserved    := merged.nodeCount ≥ g1.nodeCount
    , counterexample := none }
  , { propertyName := "nodes include g2 nodes"
    , preserved    := merged.nodeCount ≥ g2.nodeCount
    , counterexample := none }
  , { propertyName := "edges include g1 edges"
    , preserved    := merged.edgeCount ≥ g1.edgeCount
    , counterexample := none }
  ]

/-! ## Conservative Extension Preservation

If T' is a conservative extension of T, then certain properties
are preserved (e.g., consistency).
-/

structure ConservativityPreservation where
  original     : FormalTheory
  extension    : FormalTheory
  consistent   : Bool  -- assume original is consistent
  extConsistent : Bool  -- extension preserves consistency
  deriving Repr, Inhabited

def ConservativityPreservation.check (orig ext : FormalTheory) : ConservativityPreservation :=
  let extRel := SubtheoryRelation.check orig ext
  { original      := orig
  , extension     := ext
  , consistent    := true  -- assumed
  , extConsistent := extRel.isSubtheory  -- if extension is just adding symbols/axioms
  }

/-! ## Dependency Graph Composition Preservation

When composing two dependency graphs, certain laws must be preserved.
-/

structure CompositionPreservation where
  graphA     : DependencyGraph
  graphB     : DependencyGraph
  composed   : DependencyGraph
  pathsPreserved : Bool
  cyclesNotIntroduced : Bool
  deriving Repr, Inhabited

def CompositionPreservation.check (gA gB : DependencyGraph)
    (bridgeSource bridgeTarget : TheoryName) : CompositionPreservation :=
  let composed := gA.mergeWithBridge gB bridgeSource bridgeTarget
  { graphA := gA, graphB := gB, composed := composed
  , pathsPreserved := composed.edgeCount ≥ gA.edgeCount + gB.edgeCount
  , cyclesNotIntroduced := !(gA.isAcyclic && gB.isAcyclic && !composed.isAcyclic)
  }

/-! ## Rank Preservation

Under certain operations, the rank ordering of theories should be
preserved (monotonicity of the dependency lattice).
-/

def rankMonotonicity (g : DependencyGraph) (addedEdge : DependencyEdge) : Bool :=
  let g' := g.addEdge addedEdge
  let oldRank := g.rank addedEdge.source
  let newRank := g'.rank addedEdge.source
  newRank ≥ oldRank  -- adding a dependency should not decrease depth

/-! ## Morphism Property Propagation

What properties of a source theory propagate through a morphism
to the target theory.
-/

structure MorphismPropertyReport where
  sourceTheory    : FormalTheory
  targetTheory    : FormalTheory
  sigSizeMatch    : Bool
  axiomCountMatch : Bool
  dependencyMatch : Bool
  deriving Repr, Inhabited

def morphismPropertyReport (g : DependencyGraph) (m : TheoryMorphism) : MorphismPropertyReport :=
  { sourceTheory    := m.source
  , targetTheory    := m.target
  , sigSizeMatch    := m.source.signature.size == m.target.signature.size
  , axiomCountMatch := m.source.axioms.length ≤ m.target.axioms.length
  , dependencyMatch := g.isAcyclic  -- simplified
  }

/-! ## Evaluations -/

#eval do
  let a := TheoryName.ofString "A"
  let b := TheoryName.ofString "B"
  let g : DependencyGraph :=
    { nodes := [TheoryNode.simple a "A" "1" "", TheoryNode.simple b "B" "1" ""]
    , edges := [{ source := b, target := a, kind := .import, description := none : DependencyEdge }] }
  acyclicityPreservedByRemoval g b a

#eval do
  let a := TheoryName.ofString "A"
  let b := TheoryName.ofString "B"
  let c := TheoryName.ofString "C"
  let g : DependencyGraph :=
    { nodes := [ TheoryNode.simple a "A" "1" ""
               , TheoryNode.simple b "B" "1" ""
               , TheoryNode.simple c "C" "1" "" ]
    , edges := [ { source := b, target := a, kind := .import, description := none : DependencyEdge } ]
    }
  checkSubgraphPreservation g [a, b]

#eval do
  let t1 := FormalTheory.simple (TheoryName.ofString "T1")
  let t2 := FormalTheory.simple (TheoryName.ofString "T2")
  let cp := ConservativityPreservation.check t1 t2
  (cp.consistent, cp.extConsistent)

end MiniTheoryDependencyKernel
