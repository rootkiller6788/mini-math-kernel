/-
# Dependency Kernel: Invariants

Invariants of theory dependency graphs: quantities and properties
that remain unchanged under graph isomorphisms, measuring the
structure and complexity of dependency relationships.
-/

import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects

namespace MiniTheoryDependencyKernel

/-! ## Dependency Closure

The dependency closure of a theory is the set of all theories
it transitively depends on, plus itself.
-/

def DependencyGraph.dependencyClosure (g : DependencyGraph) (name : TheoryName) : List TheoryName :=
  name :: g.transitiveDeps name

def DependencyGraph.dependencyClosureSize (g : DependencyGraph) (name : TheoryName) : Nat :=
  (g.dependencyClosure name).length

def DependencyGraph.fullDependencyClosure (g : DependencyGraph) : List (TheoryName × List TheoryName) :=
  g.nodes.map (fun n => (n.name, g.dependencyClosure n.name))

/-! ## Theory Hierarchy Depth

The longest chain of dependencies from a theory to its leaves
(most fundamental dependencies). This measures the theory's
vertical complexity.
-/

def DependencyGraph.depth (g : DependencyGraph) (name : TheoryName) : Nat :=
  go name 0
where
  go : TheoryName → Nat → Nat
    | n, visitedCount =>
      let deps := g.depsOf n
      if deps.isEmpty then visitedCount
      else
        let subDepths := deps.map (fun d => go d (visitedCount + 1))
        subDepths.foldl max 0

def DependencyGraph.maxDepth (g : DependencyGraph) : Nat :=
  g.nodes.map (fun n => g.depth n.name) |>.foldl max 0

def DependencyGraph.leafTheories (g : DependencyGraph) : List TheoryName :=
  g.nodes.filter (fun n => g.depsOf n.name == []) |>.map (·.name)

def DependencyGraph.rootTheories (g : DependencyGraph) : List TheoryName :=
  g.nodes.filter (fun n => g.edgesTo n.name == []) |>.map (·.name)

/-! ## Dependency Width

The maximum number of direct dependencies any single theory has.
-/

def DependencyGraph.maxWidth (g : DependencyGraph) : Nat :=
  g.nodes.map (fun n => (g.depsOf n.name).length) |>.foldl max 0

def DependencyGraph.dependencyFanOut (g : DependencyGraph) : Nat × Nat :=
  let outs := g.nodes.map (fun n => (g.depsOf n.name).length)
  (outs.foldl (fun a b => a + b) 0, outs.foldl max 0)

/-! ## Consistency Strength Rank

Assigns a numerical rank to theories based on their dependency
structure. Theories depending on fewer things are more fundamental
(rank closer to 0). Theories that are depended on by many are
more basic.
-/

def DependencyGraph.rank (g : DependencyGraph) (name : TheoryName) : Nat :=
  -- Higher dependents count = more basic = lower rank
  let depCount := (g.edgesTo name).length
  let depth := g.depth name
  depth

def DependencyGraph.rankAll (g : DependencyGraph) : List (TheoryName × Nat) :=
  g.nodes.map (fun n => (n.name, g.rank n.name))

def DependencyGraph.sortByRank (g : DependencyGraph) : List (TheoryName × Nat) :=
  let ranked := g.rankAll
  ranked.qsort (fun a b => a.2 < b.2)

/-! ## Strongly Connected Components

In the presence of cycles (which should not occur in valid theory
graphs), strongly connected components group mutually dependent theories.
-/

def DependencyGraph.sccSize (g : DependencyGraph) : List (TheoryName × Nat) :=
  g.nodes.map fun n =>
    let reachable := g.dependencyClosure n.name
    let reachingBack := g.nodes.filter fun m =>
      g.dependencyClosure m.name |>.contains n.name
    (n.name, reachingBack.length)

def DependencyGraph.isMutuallyDependent (g : DependencyGraph) (a b : TheoryName) : Bool :=
  g.dependencyClosure a |>.contains b
  && g.dependencyClosure b |>.contains a

/-! ## Connectivity Measures

Measures of how connected the dependency graph is.
-/

structure ConnectivityReport where
  nodeCount   : Nat
  edgeCount   : Nat
  density     : Float
  componentCount : Nat
  avgDepth    : Float
  deriving Repr

def DependencyGraph.connectivity (g : DependencyGraph) : ConnectivityReport :=
  let n := g.nodeCount.toFloat
  let e := g.edgeCount.toFloat
  let density := if n > 1.0 then e / (n * (n - 1.0)) else 0.0
  let depths := g.nodes.map (fun n => g.depth n.name |>.toFloat)
  let avgDepth := if depths.length > 0 then
    (depths.foldl (· + ·) 0.0) / depths.length.toFloat else 0.0
  { nodeCount      := g.nodeCount
  , edgeCount      := g.edgeCount
  , density        := density
  , componentCount := 1  -- simplified
  , avgDepth       := avgDepth
  }

/-! ## Evaluations -/

#eval do
  let a := TheoryName.ofString "A"
  let b := TheoryName.ofString "B"
  let c := TheoryName.ofString "C"
  let g : DependencyGraph :=
    { nodes := [ TheoryNode.simple a "A" "1" ""
               , TheoryNode.simple b "B" "1" ""
               , TheoryNode.simple c "C" "1" "" ]
    , edges := [ { source := b, target := a, kind := .import, description := none : DependencyEdge }
               , { source := c, target := b, kind := .import, description := none : DependencyEdge } ]
    }
  (g.leafTheories, g.rootTheories, g.depth a)

#eval do
  let a := TheoryName.ofString "Kernel"
  let b := TheoryName.ofString "Algebra"
  let c := TheoryName.ofString "Analysis"
  let g : DependencyGraph :=
    { nodes := [ TheoryNode.simple a "Kernel" "1" ""
               , TheoryNode.simple b "Algebra" "1" ""
               , TheoryNode.simple c "Analysis" "1" "" ]
    , edges := [ { source := b, target := a, kind := .import, description := none : DependencyEdge }
               , { source := c, target := a, kind := .import, description := none : DependencyEdge } ]
    }
  (g.maxDepth, g.maxWidth, g.rankAll)

#eval do
  let connectivity := (DependencyGraph.empty).connectivity
  connectivity

end MiniTheoryDependencyKernel
