/-
# Dependency Kernel: Subobjects

Subtheory constructions: subtheories, induced subgraphs of
dependency graphs, and the subtheory relation.
-/

import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects

namespace MiniTheoryDependencyKernel

open MiniObjectKernel

/-! ## Subtheory Relation

A theory T' is a subtheory of T if the signature of T' is contained
in the signature of T and every axiom of T' is an axiom of T.
-/

structure SubtheoryRelation where
  subTheory    : FormalTheory
  superTheory  : FormalTheory
  sigInclusion : Bool
  axiomInclusion : Bool
  deriving Repr, Inhabited

instance : ToString SubtheoryRelation where
  toString r := s!"Sub({r.subTheory.theoryName} ⊆ {r.superTheory.theoryName})"

def SubtheoryRelation.check (sub super : FormalTheory) : SubtheoryRelation :=
  { subTheory      := sub
  , superTheory    := super
  , sigInclusion   := sub.signature.isSubsig super.signature
  , axiomInclusion := sub.axioms.all super.axioms.contains
  }

def SubtheoryRelation.isSubtheory (r : SubtheoryRelation) : Bool :=
  r.sigInclusion && r.axiomInclusion

/-! ## Induced Subgraph of Dependency Graph

Given a dependency graph and a set of theory names, produce the
induced subgraph containing only those nodes and edges between them.
-/

def DependencyGraph.inducedSubgraph (g : DependencyGraph) (names : List TheoryName) : DependencyGraph :=
  let subNodes := g.nodes.filter (fun n => names.contains n.name)
  let subEdges := g.edges.filter (fun e => names.contains e.source && names.contains e.target)
  { nodes := subNodes, edges := subEdges }

def DependencyGraph.subgraphOn (g : DependencyGraph) (pred : TheoryNode → Bool) : DependencyGraph :=
  let subNodes := g.nodes.filter pred
  let nameSet := subNodes.map (·.name)
  let subEdges := g.edges.filter (fun e => nameSet.contains e.source && nameSet.contains e.target)
  { nodes := subNodes, edges := subEdges }

/-! ## Subgraph Closure

The downward closure of a set of nodes includes all dependencies
of the selected nodes.
-/

def DependencyGraph.downwardClosure (g : DependencyGraph) (names : List TheoryName) : List TheoryName :=
  go (g.nodeCount + 1) names []
where
  go : Nat → List TheoryName → List TheoryName → List TheoryName
    | 0, _, visited => visited
    | fuel + 1, [], visited => visited
    | fuel + 1, n :: rest, visited =>
      if visited.contains n then go fuel rest visited
      else
        let deps := g.depsOf n
        go fuel (rest ++ deps) (n :: visited)

def DependencyGraph.closedSubgraph (g : DependencyGraph) (names : List TheoryName) : DependencyGraph :=
  let closure := g.downwardClosure names
  g.inducedSubgraph closure

/-! ## Subtheory-based Dependency Edge

When T' is a subtheory of T, there is an implicit dependency:
T depends on T'. We can make this explicit by adding an edge.
-/

def subtheoryEdge (sub super : FormalTheory) (kind : DependencyKind := .import) : DependencyEdge :=
  { source      := super.theoryName
  , target      := sub.theoryName
  , kind        := kind
  , description := some s!"{sub.theoryName} is a subtheory of {super.theoryName}"
  }

def DependencyGraph.addSubtheoryDependency (g : DependencyGraph) (sub super : FormalTheory) : DependencyGraph :=
  let edge := subtheoryEdge sub super
  g.addEdge edge

/-! ## Subtheory Lattice

The set of all subtheories of a given theory forms a lattice
under inclusion.
-/

structure SubtheoryLattice where
  theory     : FormalTheory
  subtheories : List FormalTheory
  deriving Repr, Inhabited

def SubtheoryLattice.ofTheory (t : FormalTheory) : SubtheoryLattice :=
  { theory      := t
  , subtheories := [t]  -- base case: every theory is a subtheory of itself
  }

def SubtheoryLattice.addSubtheory (l : SubtheoryLattice) (sub : FormalTheory) : SubtheoryLattice :=
  let rel := SubtheoryRelation.check sub l.theory
  if rel.isSubtheory then
    { l with subtheories := l.subtheories ++ [sub] }
  else l

def SubtheoryLattice.minimalSubtheories (l : SubtheoryLattice) : List FormalTheory :=
  -- A subtheory is minimal if it has no proper subtheories in the lattice
  l.subtheories.filter fun sub =>
    l.subtheories.all fun other =>
      other.theoryName == sub.theoryName
      || !(SubtheoryRelation.check other sub).isSubtheory
      || other.theoryName == sub.theoryName

/-! ## Evaluations -/

#eval
  let semi := FormalTheory.simple (TheoryName.ofString "SemiGroup")
              |>.addAxiom { name := "assoc", statement := "assoc" }
  let group := semi.addAxiom { name := "ident", statement := "ident" }
              |>.addAxiom { name := "inv", statement := "inv" }
  let rel := SubtheoryRelation.check semi group
  (toString rel, rel.isSubtheory)

#eval
  let nA := TheoryNode.simple (TheoryName.ofString "A") "" "" ""
  let nB := TheoryNode.simple (TheoryName.ofString "B") "" "" ""
  let nC := TheoryNode.simple (TheoryName.ofString "C") "" "" ""
  let eAB : DependencyEdge := { source := TheoryName.ofString "B", target := TheoryName.ofString "A", kind := .import, description := none }
  let eBC : DependencyEdge := { source := TheoryName.ofString "C", target := TheoryName.ofString "B", kind := .import, description := none }
  let g : DependencyGraph := { nodes := [nA, nB, nC], edges := [eAB, eBC] }
  let sub := g.inducedSubgraph [TheoryName.ofString "A", TheoryName.ofString "B"]
  (sub.nodeCount, sub.edgeCount)

#eval
  let lattice := SubtheoryLattice.ofTheory (FormalTheory.simple (TheoryName.ofString "Group")
                |>.addAxiom { name := "assoc", statement := "assoc" }
                |>.addAxiom { name := "ident", statement := "ident" })
  let lattice := lattice.addSubtheory (FormalTheory.simple (TheoryName.ofString "SemiGroup")
                |>.addAxiom { name := "assoc", statement := "assoc" })
  lattice.subtheories.length

end MiniTheoryDependencyKernel
