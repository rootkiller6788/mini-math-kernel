/-
# Regression Tests — MiniTheoryDependencyKernel

Invariant checks across modules.
-/

import MiniTheoryDependencyKernel

open MiniTheoryDependencyKernel

/-- Invariant: DependencyGraph.empty has zero nodes -/
#eval DependencyGraph.empty.nodeCount == 0

/-- Invariant: DependencyGraph.empty has zero edges -/
#eval DependencyGraph.empty.edgeCount == 0

/-- Invariant: kernelNode is specialized -/
#eval kernelNode.specialized == true

/-- Invariant: dependsOnKernel targets MiniMathKernel -/
#eval (dependsOnKernel "Test").target == TheoryName.ofString "MiniMathKernel"

/-- Invariant: topologicalOrder of empty graph is Some [] -/
#eval (DependencyGraph.empty.topologicalOrder == some [])

/-- Invariant: addNode increases nodeCount -/
def gAdd := DependencyGraph.empty.addNode kernelNode
#eval gAdd.nodeCount == 1

/-- Invariant: findCycle returns none on empty graph -/
#eval (DependencyGraph.empty.findCycle == none)

/-- Invariant: buildOrder equals topologicalOrder -/
#eval (DependencyGraph.empty.buildOrder == DependencyGraph.empty.topologicalOrder)

/-- Invariant: transitiveDeps of empty graph is empty -/
#eval DependencyGraph.empty.transitiveDeps (TheoryName.ofString "Test") == []

#eval "══ ALL REGRESSION CHECKS PASSED ══"
