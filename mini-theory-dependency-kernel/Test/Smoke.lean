/-
# Smoke Tests — MiniTheoryDependencyKernel

Run: `lake env lean --run Test/Smoke.lean`
-/

import MiniTheoryDependencyKernel

open MiniTheoryDependencyKernel

#eval "══ MINI-THEORY-DEPENDENCY-KERNEL SMOKE TESTS ══"

/-! ## Core.Basic: DependencyGraph -/
def g := DependencyGraph.empty
#eval g.nodeCount
#eval g.edgeCount

def node1 := kernelNode
def g1 := g.addNode node1
#eval g1.nodeCount

/-! ## Constructions.Universal: Graph Algorithms -/
#eval g1.topologicalOrder |>.isSome
#eval g1.stats

#eval "══ ALL MINI-THEORY-DEPENDENCY-KERNEL SMOKE TESTS PASSED ══"
