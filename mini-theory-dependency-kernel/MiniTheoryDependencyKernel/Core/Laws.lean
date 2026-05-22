/-
# Dependency Kernel: Laws

Formal laws and predicates governing theory dependency relationships:
acyclicity, transitivity, monotonicity, conservative extension,
and dependency closure properties.
-/

import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects

namespace MiniTheoryDependencyKernel

/-! ## Acyclicity Laws

A valid theory dependency graph must be acyclic: no theory should
depend on itself (directly or transitively).
-/

def DependencyGraph.isAcyclic (g : DependencyGraph) : Bool :=
  g.topologicalOrder.isSome

def DependencyGraph.hasDirectCycle (g : DependencyGraph) : Bool :=
  g.edges.any (fun e => e.source == e.target)

/-! ## Transitivity Laws

Dependencies are transitive: if A depends on B and B depends on C,
then A transitively depends on C.
-/

structure DependencyPath where
  source  : TheoryName
  target  : TheoryName
  path    : List TheoryName
  edges   : List DependencyEdge
  deriving Repr, Inhabited

def DependencyGraph.allPaths (g : DependencyGraph) (from to_ : TheoryName) : List DependencyPath :=
  go [from] [] from
where
  go : List TheoryName → List DependencyEdge → TheoryName → List DependencyPath
    | path, edges, current =>
      if current == to_ && path.length > 1 then
        [{ source := from, target := to_, path, edges }]
      else
        let nextEdges := g.edgesFrom current
        nextEdges.bind fun e =>
          if path.contains e.target then []  -- avoid cycles
          else go (path ++ [e.target]) (edges ++ [e]) e.target

def DependencyGraph.hasPath (g : DependencyGraph) (from to_ : TheoryName) : Bool :=
  g.allPaths from to_ |>.length > 0

/-! ## Transitive Closure Operation

The transitive closure adds all implied dependencies.
-/

def DependencyGraph.transitiveClosure (g : DependencyGraph) : DependencyGraph :=
  let tcEdges := g.nodes.bind fun n =>
    let reachable := g.transitiveDeps n.name |>.erase n.name
    reachable.map fun r =>
      { source := n.name, target := r, kind := DependencyKind.import, description := some "transitive" : DependencyEdge }
  { g with edges := g.edges ++ tcEdges }

/-! ## Conservative Extension Law

A theory B is a conservative extension of A if:
1. The language of A is contained in the language of B.
2. Every theorem of B in the language of A is already a theorem of A.

We model this as: every dependency edge from B to C where C is in A's
language should have a corresponding dependency from A to C.
-/

structure ConservativityReport where
  theoryA     : FormalTheory
  theoryB     : FormalTheory
  isExt       : Bool      -- B extends A's signature
  isConserv   : Bool      -- no new theorems in old language
  newAxioms   : List Axiom -- axioms B adds
  deriving Repr, Inhabited

def ConservativityReport.check (ext : TheoryExtension) : ConservativityReport :=
  { theoryA   := ext.original
  , theoryB   := ext.extended
  , isExt     := ext.isSignatureExtension
  , isConserv := ext.isConservative
  , newAxioms := ext.newAxioms
  }

/-! ## Monotonicity Law

Adding dependencies (edges) to a graph preserves existing dependencies.
-/

def DependencyGraph.isExtensionOf (g1 g2 : DependencyGraph) : Bool :=
  g2.nodes.all (fun n => g1.nodes.any (·.name == n.name))
  && g2.edges.all (fun e => g1.edges.any (fun e' => e'.source == e.source && e'.target == e.target))

def monotonicityCheck (g : DependencyGraph) (newEdge : DependencyEdge) : Bool :=
  let g' := g.addEdge newEdge
  g'.isExtensionOf g

/-! ## Dependency Composition Law

If theory A imports B and B imports C, then the combined graph
shows A's transitive dependency on C.
-/

def composeEdges (e1 e2 : DependencyEdge) : Option DependencyEdge :=
  if e1.target == e2.source then
    some { source := e1.source, target := e2.target, kind := .import, description := some "composed" }
  else none

def DependencyGraph.composeViaIntermediate (g : DependencyGraph) (e1 e2 : DependencyEdge) : DependencyGraph :=
  match composeEdges e1 e2 with
  | none   => g
  | some e => g.addEdge e

/-! ## Law: No Self-Dependency

A valid theory should never depend on itself.
-/

def DependencyGraph.hasSelfDependency (g : DependencyGraph) (name : TheoryName) : Bool :=
  g.edges.any (fun e => e.source == name && e.target == name)

def DependencyGraph.isValid (g : DependencyGraph) : Bool :=
  g.isAcyclic && g.nodes.all (fun n => !g.hasSelfDependency n.name)

/-! ## Evaluations -/

#eval do
  let sig : Signature := { constants := [""], functions := [("+", 2)], relations := [] }
  let mono : FormalTheory := FormalTheory.simple (TheoryName.ofString "Monoid")
            |>.addAxiom { name := "assoc", statement := "assoc" }
            |>.addAxiom { name := "ident", statement := "ident" }
  let group := mono.addAxiom { name := "inverse", statement := "inv" }
  let ext : TheoryExtension :=
    { original := mono, extended := group,
      newConstants := [], newFunctions := [], newRelations := [],
      newAxioms := [{ name := "inverse", statement := "inv" }] }
  ConservativityReport.check ext

#eval do
  let a := TheoryName.ofString "A"
  let b := TheoryName.ofString "B"
  let c := TheoryName.ofString "C"
  let e1 : DependencyEdge := { source := a, target := b, kind := .import, description := none }
  let e2 : DependencyEdge := { source := b, target := c, kind := .import, description := none }
  composeEdges e1 e2

#eval do
  let n := TheoryNode.simple (TheoryName.ofString "SelfLoop") "" "" ""
  let e : DependencyEdge := { source := n.name, target := n.name, kind := .import, description := none }
  let g := { nodes := [n], edges := [e] : DependencyGraph }
  (g.isValid, g.hasSelfDependency n.name)

end MiniTheoryDependencyKernel
