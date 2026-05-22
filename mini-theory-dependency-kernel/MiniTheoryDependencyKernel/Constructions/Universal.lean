/-
# Dependency Kernel: Graph Algorithms

Operations on the theory dependency graph: topological ordering,
cycle detection, transitive closure, build order, impact analysis.
-/

import MiniTheoryDependencyKernel.Core.Basic

namespace MiniTheoryDependencyKernel

def DependencyGraph.topologicalOrder (g : DependencyGraph) : Option (List TheoryName) :=
  let inDegree (name : TheoryName) : Nat :=
    g.edges.filter (·.target == name) |>.length
  let initQueue : List TheoryName :=
    g.nodes.filter (fun n => inDegree n.name == 0) |>.map (·.name)
  go initQueue [] (inDegree)
where
  go : List TheoryName → List TheoryName → (TheoryName → Nat) → Option (List TheoryName)
    | [], order, _ =>
      if order.length == g.nodes.length then some order.reverse
      else none
    | name :: rest, order, inDeg =>
      let dependents := g.edgesFrom name |>.map (·.target)
      let newInDeg (n : TheoryName) : Nat :=
        if dependents.contains n then inDeg n - 1 else inDeg n
      let newReady := dependents.filter fun n => newInDeg n == 0 && !(name :: order).contains n
      go (rest ++ newReady) (name :: order) newInDeg

def DependencyGraph.findCycle (g : DependencyGraph) : Option (List TheoryName) :=
  match g.topologicalOrder with
  | some _ => none
  | none =>
    g.nodes.findSome? fun start => dfs [start.name] start.name
where
  dfs : List TheoryName → TheoryName → Option (List TheoryName)
    | path, current =>
      let neighbors := g.edgesFrom current |>.map (·.target)
      match neighbors.find? (· == path.head?) with
      | some _ => some (path ++ [path.head?])
      | none =>
        neighbors.findSome? fun next =>
          if path.contains next then none
          else dfs (path ++ [next]) next

def DependencyGraph.transitiveDeps (g : DependencyGraph) (name : TheoryName) : List TheoryName :=
  go [name] []
where
  go : List TheoryName → List TheoryName → List TheoryName
    | [], visited => visited
    | n :: rest, visited =>
      if visited.contains n then go rest visited
      else
        let deps := g.depsOf n
        go (rest ++ deps) (n :: visited)

def DependencyGraph.transitiveDependents (g : DependencyGraph) (name : TheoryName) : List TheoryName :=
  go [name] []
where
  go : List TheoryName → List TheoryName → List TheoryName
    | [], visited => visited
    | n :: rest, visited =>
      if visited.contains n then go rest visited
      else
        let dependents := g.edgesTo n |>.map (·.source)
        go (rest ++ dependents) (n :: visited)

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

end MiniTheoryDependencyKernel
