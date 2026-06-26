/-
# Dependency Kernel: Theory Dependency Tracking

Tracks which theory depends on which — the "build system"
of the math kernel.
-/

import MiniObjectKernel.Core.Basic

open MiniObjectKernel

namespace MiniTheoryDependencyKernel

structure TheoryNode where
  name        : TheoryName
  title       : String
  version     : String
  path        : String
  description : Option String
  specialized : Bool := false
  deriving BEq, Repr, Inhabited

instance : ToString TheoryNode where
  toString n := s!"TheoryNode({n.name})"

def TheoryNode.simple (name : TheoryName) (title version path : String) : TheoryNode :=
  { name, title, version, path, description := none }

inductive DependencyKind
  | import | bridge | example | test
  deriving BEq, Repr, Inhabited

instance : ToString DependencyKind where
  toString
    | .import => "import"
    | .bridge => "bridge"
    | .example => "example"
    | .test => "test"

structure DependencyEdge where
  source : TheoryName
  target : TheoryName
  kind    : DependencyKind
  description : Option String
  deriving BEq, Repr, Inhabited

structure TheoryManifest where
  self         : TheoryNode
  dependencies : List DependencyEdge
  dependents   : List DependencyEdge
  deriving Repr, Inhabited

def TheoryManifest.ofDependencies (self : TheoryNode) (deps : List DependencyEdge) : TheoryManifest :=
  { self, dependencies := deps, dependents := [] }

def TheoryManifest.directDeps (m : TheoryManifest) : List TheoryName :=
  m.dependencies.map (·.target)

def TheoryManifest.importDeps (m : TheoryManifest) : List TheoryName :=
  m.dependencies.filter (·.kind == .import) |>.map (·.target)

structure DependencyGraph where
  nodes : List TheoryNode
  edges : List DependencyEdge
  deriving Repr, Inhabited

def DependencyGraph.empty : DependencyGraph := { nodes := [], edges := [] }

def DependencyGraph.addNode (g : DependencyGraph) (n : TheoryNode) : DependencyGraph :=
  if g.nodes.any (·.name == n.name) then g
  else { g with nodes := g.nodes ++ [n] }

def DependencyGraph.addEdge (g : DependencyGraph) (e : DependencyEdge) : DependencyGraph :=
  { g with edges := g.edges ++ [e] }

def DependencyGraph.findNode (g : DependencyGraph) (name : TheoryName) : Option TheoryNode :=
  g.nodes.find? (·.name == name)

def DependencyGraph.edgesFrom (g : DependencyGraph) (name : TheoryName) : List DependencyEdge :=
  g.edges.filter (·.source == name)

def DependencyGraph.edgesTo (g : DependencyGraph) (name : TheoryName) : List DependencyEdge :=
  g.edges.filter (·.target == name)

def DependencyGraph.depsOf (g : DependencyGraph) (name : TheoryName) : List TheoryName :=
  (g.edgesFrom name).map (·.target)

def DependencyGraph.nodeCount (g : DependencyGraph) : Nat := g.nodes.length
def DependencyGraph.edgeCount (g : DependencyGraph) : Nat := g.edges.length

/-! ## Node Degree Operations -/

/-- Compute the in-degree of a node. -/
def DependencyGraph.inDegree (g : DependencyGraph) (name : TheoryName) : Nat :=
  (g.edgesTo name).length

/-- Compute the out-degree of a node. -/
def DependencyGraph.outDegree (g : DependencyGraph) (name : TheoryName) : Nat :=
  (g.edgesFrom name).length

/-! ## Simple Graph Properties (self-contained) -/

/-- Get all edges of a specific dependency kind. -/
def DependencyGraph.edgesByKind (g : DependencyGraph) (kind : DependencyKind) : List DependencyEdge :=
  g.edges.filter (·.kind == kind)

/-- Check if the dependency graph has no duplicate edges. -/
def DependencyGraph.hasUniqueEdges (g : DependencyGraph) : Bool :=
  let edgePairs := g.edges.map fun e => (e.source, e.target)
  let deduped := edgePairs.eraseDups
  deduped.length == edgePairs.length

/-- Naive dedup for lists (preserving order, keeping first occurrence). -/
def List.eraseDups (xs : List α) [BEq α] : List α :=
  go xs []
where
  go : List α → List α → List α
    | [], acc => acc.reverse
    | x :: rest, acc =>
      if acc.contains x then go rest acc
      else go rest (x :: acc)

/-- Compute the adjacency matrix representation (as list of rows). -/
def DependencyGraph.adjacencyMatrix (g : DependencyGraph) : List (List Nat) :=
  let nameOrder := g.nodes.map (·.name)
  nameOrder.map fun src =>
    nameOrder.map fun tgt =>
      if g.edges.any (fun e => e.source == src && e.target == tgt) then 1 else 0

/-- Count all paths between two nodes (up to length bound to avoid infinite loops in cyclic graphs). -/
def DependencyGraph.countPaths (g : DependencyGraph) (src to_ : TheoryName) (maxLen : Nat) : Nat :=
  go [src] maxLen
where
  go (path : List TheoryName) : Nat → Nat
    | 0 => 0
    | fuel + 1 =>
      let current := path.headD src
      if current == to_ && path.length > 1 then 1
      else
        let nextEdges := g.edgesFrom current
        nextEdges.foldl (fun acc e =>
          if path.contains e.target then acc
          else acc + go (e.target :: path) fuel) 0

/-- Compute longest path length from a node (follows edges forward).
    Uses fuel parameter for structural termination — bounded by nodeCount. -/
def DependencyGraph.longestPathFrom (g : DependencyGraph) (name : TheoryName) : Nat :=
  go name (g.nodeCount)
where
  go (current : TheoryName) : Nat → Nat
    | 0 => 0
    | fuel + 1 =>
      let deps := g.depsOf current
      if deps.isEmpty then 0
      else 1 + (deps.map (fun d => go d fuel) |>.foldl max 0)

/-- Topological levels: assign each node its longest distance from a source. -/
def DependencyGraph.topologicalLevels (g : DependencyGraph) : List (TheoryName × Nat) :=
  g.nodes.map fun n => (n.name, g.longestPathFrom n.name)

/-- Check if a graph has a node with the given name. -/
def DependencyGraph.hasNode (g : DependencyGraph) (name : TheoryName) : Bool :=
  g.nodes.any (·.name == name)

/-- Get all nodes that have no outgoing edges (sink nodes / leaf theories). -/
def DependencyGraph.sinkNodes (g : DependencyGraph) : List TheoryName :=
  g.nodes.filter (fun n => g.edgesFrom n.name |>.isEmpty) |>.map (·.name)

/-- Get all nodes that have no incoming edges (source nodes / root theories). -/
def DependencyGraph.sourceNodes (g : DependencyGraph) : List TheoryName :=
  g.nodes.filter (fun n => g.edgesTo n.name |>.isEmpty) |>.map (·.name)

/-- Find all nodes that are both source and sink (isolated nodes). -/
def DependencyGraph.isolatedNodes (g : DependencyGraph) : List TheoryName :=
  g.nodes.filter (fun n =>
    (g.edgesFrom n.name).isEmpty && (g.edgesTo n.name).isEmpty) |>.map (·.name)

/-- Compute the minimum/maximum in-degree among all nodes. -/
def DependencyGraph.degreeStats (g : DependencyGraph) : Nat × Nat × Nat × Nat :=
  let inDegs := g.nodes.map (fun n => (g.edgesTo n.name).length)
  let outDegs := g.nodes.map (fun n => (g.edgesFrom n.name).length)
  (inDegs.foldl min 0, inDegs.foldl max 0,
   outDegs.foldl min 0, outDegs.foldl max 0)

/-- Check if the graph is empty (no nodes). -/
def DependencyGraph.isEmpty (g : DependencyGraph) : Bool :=
  g.nodes.isEmpty

/-- Get the subgraph containing only nodes that match a predicate. -/
def DependencyGraph.filterNodes (g : DependencyGraph) (p : TheoryNode → Bool) : DependencyGraph :=
  let filteredNodes := g.nodes.filter p
  let nameSet := filteredNodes.map (·.name)
  let filteredEdges := g.edges.filter (fun e => nameSet.contains e.source && nameSet.contains e.target)
  { nodes := filteredNodes, edges := filteredEdges }

/-- Remove a node and all its incident edges from the graph. -/
def DependencyGraph.removeNode (g : DependencyGraph) (name : TheoryName) : DependencyGraph :=
  { nodes := g.nodes.filter (·.name != name)
  , edges := g.edges.filter (fun e => e.source != name && e.target != name) }

/-- Remove all edges of a specific kind from the graph. -/
def DependencyGraph.removeEdgesOfKind (g : DependencyGraph) (kind : DependencyKind) : DependencyGraph :=
  { g with edges := g.edges.filter (·.kind != kind) }

/-- Compute the reverse graph (all edges reversed). -/
def DependencyGraph.reverse (g : DependencyGraph) : DependencyGraph :=
  { nodes := g.nodes
  , edges := g.edges.map fun e => { e with source := e.target, target := e.source } }

/-- Count the number of nodes with a given property. -/
def DependencyGraph.countNodesWhere (g : DependencyGraph) (p : TheoryNode → Bool) : Nat :=
  g.nodes.foldl (fun acc n => if p n then acc + 1 else acc) 0

/-- Grouping helper: partition elements by an equivalence relation. -/
def List.groupBy (xs : List α) (eq : α → α → Bool) : List (List α) :=
  match xs with
  | [] => []
  | x :: rest =>
    let group := x :: rest.filter (eq x)
    let others := rest.filter (λ y => ¬ eq x y)
    group :: others.groupBy eq

end MiniTheoryDependencyKernel
