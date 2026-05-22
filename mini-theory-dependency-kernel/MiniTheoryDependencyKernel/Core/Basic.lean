/-
# Dependency Kernel: Theory Dependency Tracking

Tracks which theory depends on which — the "build system"
of the math kernel.
-/

import MiniObjectKernel.Core.Basic

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

end MiniTheoryDependencyKernel
