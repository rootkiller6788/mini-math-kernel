/-
# Basic Dependency Graph Demo

Run: `lake env lean --run examples/BasicDemo.lean`
-/
import MiniTheoryDependencyKernel
open MiniTheoryDependencyKernel
open MiniObjectKernel

#eval "══ Theory Dependency Kernel — Basic Demo ══"

-- Create some theories
def kernel := TheoryNode.simple (TheoryName.ofString "MiniMathKernel") "Math Kernel" "0.1.0" "kernel"
def algebra := TheoryNode.simple (TheoryName.ofString "Algebra") "Abstract Algebra" "1.0" "algebra"
def analysis := TheoryNode.simple (TheoryName.ofString "Analysis") "Real Analysis" "1.0" "analysis"
def topology := TheoryNode.simple (TheoryName.ofString "Topology") "Point-Set Topology" "1.0" "topology"

-- Build a dependency graph
def g : DependencyGraph :=
  DependencyGraph.empty
    |>.addNode kernel
    |>.addNode algebra
    |>.addNode analysis
    |>.addNode topology
    |>.addEdge { source := algebra.name, target := kernel.name, kind := .import, description := none }
    |>.addEdge { source := analysis.name, target := kernel.name, kind := .import, description := none }
    |>.addEdge { source := topology.name, target := kernel.name, kind := .import, description := none }

#eval s!"Graph: {g.nodeCount} nodes, {g.edgeCount} edges"
#eval s!"Acyclic: {g.isAcyclic}"

-- Topological build order
#eval s!"Build order: {g.topologicalOrder}"

-- Transitive dependencies
#eval s!"Algebra transitively depends on: {g.transitiveDeps algebra.name}"

-- Find what depends on the kernel
#eval s!"Theories depending on kernel: {g.transitiveDependents kernel.name}"

-- Impact analysis
#eval s!"Kernel impact factor: {g.impactFactor kernel.name}"
#eval s!"Algebra impact factor: {g.impactFactor algebra.name}"

#eval "══ Demo Complete ══"
