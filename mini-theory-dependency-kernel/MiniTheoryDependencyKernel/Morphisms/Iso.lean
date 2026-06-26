/-
# Dependency Kernel: Isomorphisms

Isomorphisms between formal theories and dependency graphs.
Two theories are isomorphic if there exist invertible morphisms
between them — they are essentially the same theory up to renaming.
-/

import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects
import MiniTheoryDependencyKernel.Morphisms.Hom

namespace MiniTheoryDependencyKernel

open MiniObjectKernel

/-! ## Theory Isomorphism

A theory isomorphism is a pair of morphisms that are mutual inverses.
-/

structure TheoryIsomorphism where
  forward  : TheoryMorphism
  backward : TheoryMorphism
  isInverse : Bool  -- forward ∘ backward = id and backward ∘ forward = id
  deriving Repr, Inhabited

instance : ToString TheoryIsomorphism where
  toString iso := s!"Iso({iso.forward.source.theoryName} ≅ {iso.forward.target.theoryName})"

def TheoryIsomorphism.ofIdentity (t : FormalTheory) : TheoryIsomorphism :=
  { forward  := TheoryMorphism.id t
  , backward := TheoryMorphism.id t
  , isInverse := true
  }

def TheoryIsomorphism.isValid (iso : TheoryIsomorphism) : Bool :=
  iso.isInverse
  && iso.forward.source.theoryName == iso.backward.target.theoryName
  && iso.forward.target.theoryName == iso.backward.source.theoryName

/-! ## Signature Isomorphism

Two signatures are isomorphic if there is a bijection between
their symbols preserving arities.
-/

structure SignatureIsomorphism where
  sigA : Signature
  sigB : Signature
  constantBijection : List (String × String)
  functionBijection : List (String × String)
  relationBijection : List (String × String)
  preservesArities : Bool
  deriving Repr, Inhabited

def SignatureIsomorphism.areIsomorphic (iso : SignatureIsomorphism) : Bool :=
  iso.constantBijection.length == iso.sigA.constants.length
  && iso.constantBijection.length == iso.sigB.constants.length
  && iso.functionBijection.length == iso.sigA.functions.length
  && iso.functionBijection.length == iso.sigB.functions.length
  && iso.relationBijection.length == iso.sigA.relations.length
  && iso.relationBijection.length == iso.sigB.relations.length
  && iso.preservesArities

/-! ## Dependency Graph Isomorphism

Two dependency graphs are isomorphic if there is a bijection
between their nodes that preserves edge structure.
-/

structure GraphIsomorphism where
  graphA   : DependencyGraph
  graphB   : DependencyGraph
  nodeMap  : List (TheoryName × TheoryName)
  edgePreserved : Bool
  deriving Repr, Inhabited

instance : ToString GraphIsomorphism where
  toString iso := s!"GraphIso(edges={iso.graphA.edgeCount}↔{iso.graphB.edgeCount})"

def GraphIsomorphism.check (iso : GraphIsomorphism) : Bool :=
  let nodeCountMatch := iso.graphA.nodeCount == iso.graphB.nodeCount
  let edgeCountMatch := iso.graphA.edgeCount == iso.graphB.edgeCount
  nodeCountMatch && edgeCountMatch && iso.edgePreserved

def GraphIsomorphism.tryConstruct (g1 g2 : DependencyGraph) : Option GraphIsomorphism :=
  if g1.nodeCount == g2.nodeCount && g1.edgeCount == g2.edgeCount then
    let nameMap := g1.nodes.map (·.name) |>.zip g2.nodes.map (·.name)
    some { graphA := g1, graphB := g2, nodeMap := nameMap, edgePreserved := true }
  else none

/-! ## Dependency Graph Invariants

Properties preserved under graph isomorphism.
-/

structure GraphInvariants where
  nodeCount     : Nat
  edgeCount     : Nat
  maxInDegree   : Nat
  maxOutDegree  : Nat
  isAcyclicBool : Bool
  deriving BEq, Repr, Inhabited

def DependencyGraph.invariants (g : DependencyGraph) : GraphInvariants :=
  let maxIn := g.nodes.map (fun n => (g.edgesTo n.name).length) |>.foldl max 0
  let maxOut := g.nodes.map (fun n => (g.edgesFrom n.name).length) |>.foldl max 0
  { nodeCount     := g.nodeCount
  , edgeCount     := g.edgeCount
  , maxInDegree   := maxIn
  , maxOutDegree  := maxOut
  , isAcyclicBool := g.isAcyclic
  }

def invariantCheck (g1 g2 : DependencyGraph) : Bool :=
  g1.invariants == g2.invariants

/-! ## Graph Renaming

Applying a renaming of theory names to a dependency graph produces an isomorphic graph.
-/

def DependencyGraph.rename (g : DependencyGraph) (renaming : List (TheoryName × TheoryName)) : DependencyGraph :=
  let lookup (name : TheoryName) : TheoryName :=
    match renaming.find? (fun (old, _) => old == name) with
    | some (_, new) => new
    | none => name
  let newNodes := g.nodes.map (fun n => { n with name := lookup n.name })
  let newEdges := g.edges.map (fun e => { e with
    source := lookup e.source
    target := lookup e.target
  })
  { nodes := newNodes, edges := newEdges }

/-! ## Evaluations -/

#eval
  let t := FormalTheory.simple (TheoryName.ofString "Trivial")
  let iso := TheoryIsomorphism.ofIdentity t
  (toString iso, iso.isValid)

#eval
  let g1 : DependencyGraph :=
    { nodes := [TheoryNode.simple (TheoryName.ofString "A") "A" "1" ""
               ,TheoryNode.simple (TheoryName.ofString "B") "B" "1" ""]
    , edges := [{ source := TheoryName.ofString "A", target := TheoryName.ofString "B"
                 , kind := .import, description := none : DependencyEdge }]
    }
  let g2 := g1.rename [(TheoryName.ofString "A", TheoryName.ofString "X")
                       ,(TheoryName.ofString "B", TheoryName.ofString "Y")]
  (g1.invariants, g2.invariants, invariantCheck g1 g2)

#eval
  let g1 : DependencyGraph :=
    { nodes := [TheoryNode.simple (TheoryName.ofString "X") "X" "1" ""]
    , edges := []
    }
  let g2 : DependencyGraph :=
    { nodes := [TheoryNode.simple (TheoryName.ofString "Y") "Y" "1" ""]
    , edges := []
    }
  GraphIsomorphism.tryConstruct g1 g2

end MiniTheoryDependencyKernel
