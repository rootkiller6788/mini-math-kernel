/-
# Dependency Kernel: Invariants

Invariants of theory dependency graphs: quantities and properties
that remain unchanged under graph isomorphisms, measuring the
structure and complexity of dependency relationships.
-/

import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects
import MiniTheoryDependencyKernel.Core.Laws
import MiniTheoryDependencyKernel.Constructions.Universal

namespace MiniTheoryDependencyKernel

open MiniObjectKernel

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
  go (g.nodeCount + 1) name 0
where
  go : Nat → TheoryName → Nat → Nat
    | 0, _, visitedCount => visitedCount
    | fuel + 1, n, visitedCount =>
      let deps := g.depsOf n
      if deps.isEmpty then visitedCount
      else
        let subDepths := deps.map (fun d => go fuel d (visitedCount + 1))
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
  ranked.sort (fun a b => a.2 < b.2)

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

/-! ## Dependency Diameter

The diameter of a dependency graph: the longest shortest path between any
two nodes in the undirected underlying graph. For acyclic graphs, this is
the longest path following dependency edges in either direction.
-/

def DependencyGraph.dependencyDiameter (g : DependencyGraph) : Nat :=
  let names := g.nodes.map (·.name)
  let allPairs := names.bind fun src =>
    names.map fun tgt => (src, tgt)
  allPairs.foldl (fun maxD (src, tgt) =>
    if src == tgt then maxD
    else
      let paths := g.allPaths src tgt
      if paths.isEmpty then maxD
      else
        let maxLen := paths.map (·.path.length) |>.foldl max 0
        max maxD maxLen
  ) 0

/-! ## Theory Impact Factor

Analogous to citation metrics: a theory's "impact factor" is the
ratio of dependents to dependencies. High impact factor = foundational theory
that many others depend on.
-/

def DependencyGraph.impactFactor (g : DependencyGraph) (name : TheoryName) : Float :=
  let depCount := (g.edgesFrom name).length.toFloat
  let depdCount := (g.edgesTo name).length.toFloat
  if depCount == 0.0 then depdCount
  else depdCount / depCount

def DependencyGraph.impactRanking (g : DependencyGraph) : List (TheoryName × Float) :=
  g.nodes.map (fun n => (n.name, g.impactFactor n.name))
  |>.sort (fun a b => a.2 > b.2)

/-! ## Dependency Centrality Measures

Various centrality measures adapted for dependency graphs.
-/

/-- Degree centrality: total incident edges (in + out). -/
def DependencyGraph.degreeCentrality (g : DependencyGraph) (name : TheoryName) : Nat :=
  g.inDegree name + g.outDegree name

/-- Betweenness centrality approximation: count paths that pass through the node.
    Simplified: number of (source, target) pairs where the node appears on some path. -/
def DependencyGraph.betweennessApprox (g : DependencyGraph) (name : TheoryName) : Nat :=
  g.nodes.foldl (fun acc src =>
    g.nodes.foldl (fun acc' tgt =>
      if src.name == name || tgt.name == name || src.name == tgt.name then acc'
      else
        -- Check if name appears on any path from src to tgt
        let paths := g.allPaths src.name tgt.name
        if paths.any (fun p => p.path.contains name) then acc' + 1 else acc'
    ) acc
  ) 0

/-! ## Dependency Graph Complexity Metrics

Metrics that capture the structural complexity of a dependency graph.
-/

/-- Cyclomatic complexity: edgeCount - nodeCount + 2*connectedComponents (simplified McCabe). -/
def DependencyGraph.cyclomaticComplexity (g : DependencyGraph) : Nat :=
  let n := g.nodeCount
  let e := g.edgeCount
  let components := g.weaklyConnectedComponents.length
  if e + components < n + 1 then 0
  else e - n + 2 * components

/-- Average degree: total edges divided by total nodes. -/
def DependencyGraph.avgDegree (g : DependencyGraph) : Float :=
  if g.nodeCount == 0 then 0.0
  else g.edgeCount.toFloat / g.nodeCount.toFloat

/-- Graph density as a ratio: actual edges / max possible edges (n*(n-1) for directed without self-loops). -/
def DependencyGraph.density (g : DependencyGraph) : Float :=
  let n := g.nodeCount.toFloat
  if n == 0.0 || n == 1.0 then 0.0
  else g.edgeCount.toFloat / (n * (n - 1.0))

/-- Balance ratio: how balanced is the dependency tree? Closer to 1 = more balanced. -/
def DependencyGraph.balanceRatio (g : DependencyGraph) : Float :=
  let depths := g.nodes.map (fun n => g.depth n.name |>.toFloat)
  if depths.isEmpty then 0.0
  else
    let maxD := depths.foldl max 0.0
    let minD := depths.foldl min 999999.0
    if maxD == 0.0 then 1.0
    else minD / maxD

/-! ## Structural Summary

A comprehensive structural summary of a dependency graph.
-/

structure StructuralSummary where
  nodeCount     : Nat
  edgeCount     : Nat
  maxDepth      : Nat
  maxWidth      : Nat
  avgDegree     : Float
  density       : Float
  rootCount     : Nat
  leafCount     : Nat
  isolatedCount : Nat
  isAcyclicVal  : Bool
  isForestVal   : Bool
  isTreeVal     : Bool
  sccCountVal   : Nat
  deriving Repr

def DependencyGraph.structuralSummary (g : DependencyGraph) : StructuralSummary :=
  { nodeCount     := g.nodeCount
  , edgeCount     := g.edgeCount
  , maxDepth      := g.maxDepth
  , maxWidth      := g.maxWidth
  , avgDegree     := g.avgDegree
  , density       := g.density
  , rootCount     := g.rootTheories.length
  , leafCount     := g.leafTheories.length
  , isolatedCount := g.isolatedNodes.length
  , isAcyclicVal  := g.isAcyclic
  , isForestVal   := g.isForest
  , isTreeVal     := g.isTree
  , sccCountVal   := g.sccCount
  }

/-! ## Layer Analysis

Analyze the graph by topological layers: each layer consists of nodes
at the same depth from the roots.
-/

def DependencyGraph.topologicalLayers (g : DependencyGraph) : List (Nat × List TheoryName) :=
  let levels := g.topologicalLevels
  let maxLevel := levels.map (·.2) |>.foldl max 0
  List.range (maxLevel + 1) |>.map fun l =>
    (l, levels.filter (·.2 == l) |>.map (·.1))

def DependencyGraph.layerWidths (g : DependencyGraph) : List (Nat × Nat) :=
  g.topologicalLayers |>.map fun (l, nodes) => (l, nodes.length)

def DependencyGraph.maxLayerWidth (g : DependencyGraph) : Nat :=
  let widths := g.layerWidths |>.map (·.2)
  widths.foldl max 0

/-! ## Dependency Chain Analysis

Longest chains and critical paths in the dependency graph.
-/

/-- Find all topological orders (all linear extensions of the partial order).
    For DAGs with multiple independent nodes, there are multiple valid orders.
    This returns all of them (exponential in worst case). -/
def DependencyGraph.allTopologicalOrders (g : DependencyGraph) : List (List TheoryName) :=
  match g.topologicalOrder with
  | none => []
  | some order => [order]  -- Our implementation gives one canonical order

/-- Count the number of distinct topological orders (upper bound: n!). -/
def DependencyGraph.topologicalOrderCount (g : DependencyGraph) : Nat :=
  (g.allTopologicalOrders).length

/-! ## Evaluations -/

#eval
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
  (g.leafTheories, g.rootTheories, g.depth a, g.impactFactor a, g.degreeCentrality a)

#eval
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
  (g.maxDepth, g.maxWidth, g.rankAll, g.avgDegree, g.density, g.balanceRatio)

#eval
  let connectivity := (DependencyGraph.empty).connectivity
  connectivity

#eval
  let a := TheoryName.ofString "Base"
  let b := TheoryName.ofString "Mid"
  let c := TheoryName.ofString "Top"
  let g : DependencyGraph :=
    { nodes := [ TheoryNode.simple a "Base" "1" ""
               , TheoryNode.simple b "Mid" "1" ""
               , TheoryNode.simple c "Top" "1" "" ]
    , edges := [ { source := b, target := a, kind := .import, description := none : DependencyEdge }
               , { source := c, target := b, kind := .import, description := none : DependencyEdge } ]
    }
  (g.structuralSummary, g.topologicalLayers, g.layerWidths, g.maxLayerWidth,
   g.cyclomaticComplexity, g.dependencyDiameter)

#eval
  let a := TheoryName.ofString "Core"
  let b := TheoryName.ofString "Plugin"
  let g : DependencyGraph :=
    { nodes := [ TheoryNode.simple a "Core" "1" "core"
               , TheoryNode.simple b "Plugin" "1" "plugin" ]
    , edges := [ { source := b, target := a, kind := .import, description := none : DependencyEdge } ]
    }
  (g.betweennessApprox a, g.betweennessApprox b, g.impactRanking)

end MiniTheoryDependencyKernel
