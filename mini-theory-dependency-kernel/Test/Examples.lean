/-
# Step-by-Step Examples — MiniTheoryDependencyKernel

Building dependency graphs, detecting cycles, computing transitive closures.
-/

import MiniTheoryDependencyKernel

open MiniTheoryDependencyKernel

#eval "══ BUILDING DEPENDENCY GRAPHS ══"

/-! ### Step 1: Create a kernel node -/
#eval kernelNode.name
#eval kernelNode.title

/-! ### Step 2: Create a dependency edge -/
#eval dependsOnKernel "Algebra.GroupTheory" |>.kind

/-! ### Step 3: Build a dependency graph -/
def exampleGraph :=
  DependencyGraph.empty
    |>.addNode kernelNode
    |>.addNode (TheoryNode.simple (TheoryName.ofString "GroupTheory") "Group Theory" "0.1.0" "group-theory")
    |>.addEdge (dependsOnKernel "GroupTheory")

#eval exampleGraph.nodeCount
#eval exampleGraph.edgeCount

/-! ### Step 4: Compute topological order -/
#eval exampleGraph.topologicalOrder

/-! ### Step 5: Check for cycles -/
#eval exampleGraph.findCycle

/-! ### Step 6: Compute transitive dependencies -/
#eval exampleGraph.transitiveDeps (TheoryName.ofString "GroupTheory")

/-! ### Step 7: Compute build order -/
#eval exampleGraph.buildOrder

/-! ### Step 8: Graph statistics -/
#eval exampleGraph.stats

#eval "══ DEPENDENCY GRAPH BUILDING COMPLETE ══"
