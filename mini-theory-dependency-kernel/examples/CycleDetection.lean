/-
# Cycle Detection & SCC Demo

Run: `lake env lean --run examples/CycleDetection.lean`
-/
import MiniTheoryDependencyKernel
open MiniTheoryDependencyKernel
open MiniObjectKernel

#eval "══ Cycle Detection & SCC Analysis ══"

-- Build a graph with a mutual dependency pair
def a := TheoryNode.simple (TheoryName.ofString "MutualA") "A" "1" "a"
def b := TheoryNode.simple (TheoryName.ofString "MutualB") "B" "1" "b"
def c := TheoryNode.simple (TheoryName.ofString "NormalC") "C" "1" "c"

def cyclicGraph : DependencyGraph :=
  DependencyGraph.empty
    |>.addNode a |>.addNode b |>.addNode c
    |>.addEdge { source := a.name, target := b.name, kind := .import, description := none }
    |>.addEdge { source := b.name, target := a.name, kind := .import, description := none }
    |>.addEdge { source := c.name, target := a.name, kind := .import, description := none }

#eval s!"Graph: {cyclicGraph.nodeCount} nodes, {cyclicGraph.edgeCount} edges"
#eval s!"Is valid (acyclic + no self-dep): {cyclicGraph.isValid}"
#eval s!"Topological order exists: {cyclicGraph.topologicalOrder.isSome}"

-- Find the cycle
#eval s!"Cycle found: {cyclicGraph.findCycle}"

-- Compute SCCs
#eval s!"SCCs: {cyclicGraph.sccs}"
#eval s!"SCC count: {cyclicGraph.sccCount}"

-- Condensation (always acyclic)
def condensation := cyclicGraph.condensation
#eval s!"Condensation nodes: {condensation.nodeCount}"
#eval s!"Condensation is acyclic: {condensation.isAcyclic}"

-- Compare: non-cyclic counterpart
def acyclicGraph : DependencyGraph :=
  DependencyGraph.empty
    |>.addNode a |>.addNode b |>.addNode c
    |>.addEdge { source := b.name, target := a.name, kind := .import, description := none }
    |>.addEdge { source := c.name, target := a.name, kind := .import, description := none }

#eval s!"Acyclic graph valid: {acyclicGraph.isValid}"
#eval s!"Acyclic graph build order: {acyclicGraph.buildOrder}"

#eval "══ Detection Complete ══"
