/-
# Dependency Kernel: Graph Algorithms

Operations on the theory dependency graph: topological ordering,
cycle detection, transitive closure, build order, impact analysis.
-/

import MiniTheoryDependencyKernel.Core.Basic

namespace MiniTheoryDependencyKernel

open MiniObjectKernel

def DependencyGraph.topologicalOrder (g : DependencyGraph) : Option (List TheoryName) :=
  let inDegree (name : TheoryName) : Nat :=
    g.edges.filter (·.target == name) |>.length
  let initQueue : List TheoryName :=
    g.nodes.filter (fun n => inDegree n.name == 0) |>.map (·.name)
  go (g.nodeCount + 1) initQueue [] (inDegree)
where
  go : Nat → List TheoryName → List TheoryName → (TheoryName → Nat) → Option (List TheoryName)
    | 0, _, _, _ => none
    | fuel + 1, [], order, _ =>
      if order.length == g.nodes.length then some order.reverse
      else none
    | fuel + 1, name :: rest, order, inDeg =>
      let dependents := g.edgesFrom name |>.map (·.target)
      let newInDeg (n : TheoryName) : Nat :=
        if dependents.contains n then inDeg n - 1 else inDeg n
      let newReady := dependents.filter fun n => newInDeg n == 0 && !(name :: order).contains n
      go fuel (rest ++ newReady) (name :: order) newInDeg

def DependencyGraph.isAcyclic (g : DependencyGraph) : Bool :=
  g.topologicalOrder.isSome

def DependencyGraph.isDAG (g : DependencyGraph) : Bool :=
  g.isAcyclic

def DependencyGraph.findCycle (g : DependencyGraph) : Option (List TheoryName) :=
  match g.topologicalOrder with
  | some _ => none
  | none =>
    g.nodes.findSome? fun start => dfs (g.nodeCount + 1) [start.name] start.name
where
  dfs : Nat → List TheoryName → TheoryName → Option (List TheoryName)
    | 0, _, _ => none
    | fuel + 1, path, current =>
      let neighbors := g.edgesFrom current |>.map (·.target)
      match neighbors.find? (· == path.headD current) with
      | some _ => some (path ++ [path.headD current])
      | none =>
        neighbors.findSome? fun next =>
          if path.contains next then none
          else dfs fuel (path ++ [next]) next

def DependencyGraph.transitiveDeps (g : DependencyGraph) (name : TheoryName) : List TheoryName :=
  go (g.nodeCount + 1) [name] []
where
  go : Nat → List TheoryName → List TheoryName → List TheoryName
    | 0, _, visited => visited
    | fuel + 1, [], visited => visited
    | fuel + 1, n :: rest, visited =>
      if visited.contains n then go fuel rest visited
      else
        let deps := g.depsOf n
        go fuel (rest ++ deps) (n :: visited)

def DependencyGraph.dependencyClosure (g : DependencyGraph) (name : TheoryName) : List TheoryName :=
  name :: g.transitiveDeps name

def DependencyGraph.transitiveDependents (g : DependencyGraph) (name : TheoryName) : List TheoryName :=
  go (g.nodeCount + 1) [name] []
where
  go : Nat → List TheoryName → List TheoryName → List TheoryName
    | 0, _, visited => visited
    | fuel + 1, [], visited => visited
    | fuel + 1, n :: rest, visited =>
      if visited.contains n then go fuel rest visited
      else
        let dependents := g.edgesTo n |>.map (·.source)
        go fuel (rest ++ dependents) (n :: visited)

def DependencyGraph.buildOrder (g : DependencyGraph) : Option (List TheoryName) :=
  g.topologicalOrder

def DependencyGraph.rebuildOrder (g : DependencyGraph) (name : TheoryName) : Option (List TheoryName) :=
  let affected := name :: g.transitiveDependents name
  match g.topologicalOrder with
  | none => none
  | some order => some (order.filter affected.contains)

structure GraphStats where
  nodeCount : Nat
  edgeCount : Nat
  maxDeps   : Nat
  maxDependents : Nat
  acyclic   : Bool
  deriving Repr

def DependencyGraph.stats (g : DependencyGraph) : GraphStats :=
  let maxDeps := g.nodes.map (fun n => (g.edgesFrom n.name).length) |>.foldl max 0
  let maxDependents := g.nodes.map (fun n => (g.edgesTo n.name).length) |>.foldl max 0
  { nodeCount     := g.nodeCount
    edgeCount     := g.edgeCount
    maxDeps       := maxDeps
    maxDependents := maxDependents
    acyclic       := g.topologicalOrder.isSome
  }

def kernelNode : TheoryNode :=
  { name        := TheoryName.ofString "MiniMathKernel"
    title       := "Math OS Kernel"
    version     := "0.1.0"
    path        := "0. mini-math-kernel"
    description := some "The foundational layer: syntax, logic, proof, axioms, objects, constructions, dependency"
    specialized := true
  }

def dependsOnKernel (pkgName : String) (kind : DependencyKind := .import) : DependencyEdge :=
  { source      := TheoryName.ofString pkgName
    target      := TheoryName.ofString "MiniMathKernel"
    kind        := kind
    description := some "All packages depend on the math kernel"
  }

/-! ## Strongly Connected Components (SCC) and Condensation -/

/-- Compute the condensation of a graph: contract each SCC to a single node.
    The resulting graph is guaranteed to be acyclic. -/
def DependencyGraph.condensation (g : DependencyGraph) : DependencyGraph :=
  let sccGroups := g.nodes.groupBy (fun a b =>
    (g.dependencyClosure a.name).contains b.name
    && (g.dependencyClosure b.name).contains a.name)
  let sccRepr : List (TheoryName × TheoryName) :=
    sccGroups.bind fun group =>
      match group with
      | [] => []
      | rep :: _ => group.map fun n => (n.name, rep.name)
  let sccLookup (name : TheoryName) : TheoryName :=
    (sccRepr.find? (fun (orig, _) => orig == name)).map (·.2) |>.getD name
  let condensedNodes : List TheoryNode :=
    sccGroups.filterMap fun group =>
      group.head?.map fun rep =>
        { rep with name := sccLookup rep.name
                 , title := s!"SCC({rep.title})"
                 , description := some s!"{group.length} nodes" }
  let edgeSet : List (TheoryName × TheoryName) :=
    g.edges.filterMap fun e =>
      let src := sccLookup e.source
      let tgt := sccLookup e.target
      if src == tgt then none
      else some (src, tgt)
  let edgeSet := edgeSet.eraseDups
  let condensedEdges : List DependencyEdge :=
    edgeSet.map fun (src, tgt) =>
      { source := src, target := tgt, kind := .import
      , description := some "condensed edge" }
  { nodes := condensedNodes, edges := condensedEdges }

/-- Find all strongly connected components (as list of node-name lists). -/
def DependencyGraph.sccs (g : DependencyGraph) : List (List TheoryName) :=
  g.nodes.groupBy (fun a b =>
    (g.dependencyClosure a.name).contains b.name
    && (g.dependencyClosure b.name).contains a.name)
  |>.map (·.map (·.name))

/-- Count the number of SCCs in the graph. -/
def DependencyGraph.sccCount (g : DependencyGraph) : Nat :=
  (g.sccs).length

/-! ## Graph Classification: Forest, Tree, Connected -/

/-- A dependency graph is a forest if every node has at most one incoming edge. -/
def DependencyGraph.isForest (g : DependencyGraph) : Bool :=
  g.nodes.all fun n => (g.edgesTo n.name).length ≤ 1

/-- Check if a graph is weakly connected (the undirected underlying graph is connected). -/
def DependencyGraph.isWeaklyConnected (g : DependencyGraph) : Bool :=
  match g.nodes with
  | [] => true
  | n :: _ =>
    let reachable := bfs (g.nodeCount + 1) [n.name] []
    reachable.length == g.nodeCount
where
  bfs : Nat → List TheoryName → List TheoryName → List TheoryName
    | 0, _, visited => visited
    | fuel + 1, [], visited => visited
    | fuel + 1, x :: rest, visited =>
      if visited.contains x then bfs fuel rest visited
      else
        let neighbors := (g.edgesFrom x).map (·.target) ++ (g.edgesTo x).map (·.source)
        bfs fuel (rest ++ neighbors) (x :: visited)

/-- Find weakly connected components. -/
def DependencyGraph.weaklyConnectedComponents (g : DependencyGraph) : List (List TheoryName) :=
  let allNames := g.nodes.map (·.name)
  go (g.nodeCount + 1) allNames []
where
  go : Nat → List TheoryName → List (List TheoryName) → List (List TheoryName)
    | 0, _, acc => acc
    | fuel + 1, [], acc => acc
    | fuel + 1, name :: rest, acc =>
      if acc.any (·.contains name) then go fuel rest acc
      else
        let comp := bfsComp (g.nodeCount + 1) [name] []
        go fuel rest (comp :: acc)
  bfsComp : Nat → List TheoryName → List TheoryName → List TheoryName
    | 0, _, visited => visited
    | fuel + 1, [], visited => visited
    | fuel + 1, x :: rest, visited =>
      if visited.contains x then bfsComp fuel rest visited
      else
        let neighbors := (g.edgesFrom x).map (·.target) ++ (g.edgesTo x).map (·.source)
        bfsComp fuel (rest ++ neighbors) (x :: visited)

/-- Check if two nodes are in the same weakly connected component. -/
def DependencyGraph.sameWeakComponent (g : DependencyGraph) (a b : TheoryName) : Bool :=
  g.weaklyConnectedComponents.any (fun comp => comp.contains a && comp.contains b)

/-! ## Connected Components of a DAG -/

/-- Check if the graph is strongly connected (every node can reach every other). -/
def DependencyGraph.isStronglyConnected (g : DependencyGraph) : Bool :=
  g.sccCount == 1

/-! ## Graph Analysis Helpers -/

/-- Get all paths of exactly `len` edges from `from` to `to_`. -/
def DependencyGraph.pathsOfLength (g : DependencyGraph) (src to_ : TheoryName) (len : Nat) : List (List TheoryName) :=
  go (len + 1) [src] len
where
  go : Nat → List TheoryName → Nat → List (List TheoryName)
    | 0, _, _ => []
    | fuel + 1, _, 0 => []
    | fuel + 1, path, remaining =>
      let current := path.headD src
      if remaining == 1 then
        let nextEdges := g.edgesFrom current
        nextEdges.filterMap fun e =>
          if e.target == to_ then some (path.reverse ++ [e.target])
          else none
      else
        let nextEdges := g.edgesFrom current
        nextEdges.bind fun e =>
          if path.contains e.target then []
          else go fuel (e.target :: path) (remaining - 1)

/-- Check if there is a path of length exactly n between two nodes. -/
def DependencyGraph.hasPathOfLength (g : DependencyGraph) (src to_ : TheoryName) (len : Nat) : Bool :=
  (g.pathsOfLength src to_ len).length > 0

/-- Find all ancestors (nodes that can reach the given node). -/
def DependencyGraph.ancestors (g : DependencyGraph) (name : TheoryName) : List TheoryName :=
  g.transitiveDependents name

/-- Find all descendants (nodes reachable from the given node). -/
def DependencyGraph.descendants (g : DependencyGraph) (name : TheoryName) : List TheoryName :=
  g.transitiveDeps name

/-! ## Graph Union and Intersection -/

/-- Union of two graphs: combine nodes and edges, deduplicating. -/
def DependencyGraph.union (g1 g2 : DependencyGraph) : DependencyGraph :=
  let allNodes := g1.nodes
  let newNodes := g2.nodes.filter (fun n => !allNodes.any (·.name == n.name))
  { nodes := allNodes ++ newNodes
  , edges := g1.edges ++ g2.edges
  }

/-- Intersection of two graphs: keep nodes and edges present in both. -/
def DependencyGraph.intersection (g1 g2 : DependencyGraph) : DependencyGraph :=
  let commonNodes := g1.nodes.filter (fun n => g2.nodes.any (·.name == n.name))
  let commonNames := commonNodes.map (·.name)
  let commonEdges := g1.edges.filter fun e =>
    g2.edges.any (fun e' => e'.source == e.source && e'.target == e.target)
    && commonNames.contains e.source && commonNames.contains e.target
  { nodes := commonNodes, edges := commonEdges }

/-! ## Graph Difference -/

/-- Remove all edges and nodes from g2 that appear in g1. -/
def DependencyGraph.difference (g1 g2 : DependencyGraph) : DependencyGraph :=
  let remainingNodes := g1.nodes.filter (fun n => !g2.nodes.any (·.name == n.name))
  let remainingNames := remainingNodes.map (·.name)
  let remainingEdges := g1.edges.filter fun e =>
    !g2.edges.any (fun e' => e'.source == e.source && e'.target == e.target)
    && remainingNames.contains e.source && remainingNames.contains e.target
  { nodes := remainingNodes, edges := remainingEdges }

/-! ## Evaluations for new operations -/

#eval
  let a := TheoryName.ofString "A"
  let b := TheoryName.ofString "B"
  let g : DependencyGraph :=
    { nodes := [ TheoryNode.simple a "A" "1" ""
               , TheoryNode.simple b "B" "1" "" ]
    , edges := [{ source := b, target := a, kind := .import, description := none }] }
  (g.isForest, g.isAcyclic, g.inDegree a, g.outDegree a)

#eval
  let a := TheoryName.ofString "A"
  let g : DependencyGraph :=
    { nodes := [ TheoryNode.simple a "A" "1" "" ], edges := [] }
  (g.condensation.nodeCount, g.sccCount, g.isWeaklyConnected)

#eval
  let a := TheoryName.ofString "A"
  let b := TheoryName.ofString "B"
  let c := TheoryName.ofString "C"
  let g : DependencyGraph :=
    { nodes := [ TheoryNode.simple a "A" "1" ""
               , TheoryNode.simple b "B" "1" ""
               , TheoryNode.simple c "C" "1" "" ]
    , edges := [ { source := b, target := a, kind := .import, description := none : DependencyEdge }
               , { source := c, target := a, kind := .import, description := none : DependencyEdge } ]
    }
  (g.sourceNodes, g.sinkNodes, g.isolatedNodes)

#eval
  let a := TheoryName.ofString "A"
  let b := TheoryName.ofString "B"
  let g1 : DependencyGraph :=
    { nodes := [TheoryNode.simple a "A" "1" ""], edges := [] }
  let g2 : DependencyGraph :=
    { nodes := [TheoryNode.simple b "B" "1" ""], edges := [] }
  let gu := g1.union g2
  let gi := g1.intersection g2
  (gu.nodeCount, gi.nodeCount)

end MiniTheoryDependencyKernel
