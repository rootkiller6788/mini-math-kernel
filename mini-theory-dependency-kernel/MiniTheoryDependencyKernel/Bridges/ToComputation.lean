/-
# Dependency Kernel: Bridge to Computation

Computational dependency structures from build systems theory:
Make/Ninja dependency models, parallel build scheduling,
incremental rebuild computation, and the theory of
continuous integration dependency graphs.
-/

import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Laws
import MiniTheoryDependencyKernel.Constructions.Universal
import MiniTheoryDependencyKernel.Properties.Invariants
import MiniTheoryDependencyKernel.Theorems.Main

namespace MiniTheoryDependencyKernel

/-! ## Build System Model

A build system is a dependency graph where:
- Nodes are build targets (theories, modules, files)
- Edges are build dependencies (target A needs target B first)
- Topological order gives the build schedule.
-/

/-- Simulate a Make-like build with a dependency graph. -/
def simulateBuild (g : DependencyGraph) : String :=
  match g.buildOrder with
  | none => "BUILD FAILED: cyclic dependency detected"
  | some order =>
    s!"BUILD SUCCESS: {order.length} targets built in order: {", ".intercalate (order.map toString)}"

/-- Check if a graph represents a valid Makefile dependency structure. -/
def isValidMakeDependency (g : DependencyGraph) : Bool :=
  g.isValid && g.nodeCount > 0

/-! ## Parallel Build Scheduling

Given a dependency graph, compute how many parallel workers can be used
at each level of the build.

Level 0: targets with no dependencies
Level 1: targets whose deps are all in level 0
Level 2: targets whose deps are all in levels 0-1
etc.
-/

/-- Compute the maximum parallelism available at each build level. -/
def DependencyGraph.parallelism (g : DependencyGraph) : Option (List Nat) :=
  match g.topologicalOrder with
  | none => none
  | some order =>
    let levels : List (List TheoryName) :=
      go order [] []
    some (levels.map (·.length))
where
  go : List TheoryName → List TheoryName → List (List TheoryName) → List (List TheoryName)
    | [], _, acc => acc.reverse
    | name :: rest, built, acc =>
      let deps := g.depsOf name
      if deps.all built.contains then
        -- Put this in a new sub-list with others at the same level
        let (sameLevel, rest') := rest.span (fun n => (g.depsOf n).all built.contains)
        go rest' (name :: built) ((name :: sameLevel) :: acc)
      else
        go (rest ++ [name]) built acc

/-- Compute the critical path length (minimum build time with unlimited parallelism). -/
def DependencyGraph.criticalPath (g : DependencyGraph) : Option Nat :=
  match g.parallelism with
  | none => none
  | some levels => some levels.length

/-- Compute total work (sum of all build times, assuming 1 unit per target). -/
def DependencyGraph.totalWork (g : DependencyGraph) : Nat := g.nodeCount

/-- Speedup from parallelism: totalWork / criticalPath. -/
def DependencyGraph.parallelSpeedup (g : DependencyGraph) : Option Float :=
  match g.criticalPath with
  | none => none
  | some cp =>
    if cp == 0 then none
    else some (g.nodeCount.toFloat / cp.toFloat)

/-! ## Incremental Build Model

When a source node changes, compute what needs to be rebuilt.
-/

/-- Simulate a change: given a changed node, return what must be rebuilt. -/
def simulateChange (g : DependencyGraph) (changed : TheoryName) : Option (List TheoryName) :=
  g.rebuildOrder changed

/-- Estimate rebuild cost as fraction of total build. -/
def rebuildCost (g : DependencyGraph) (changed : TheoryName) : Option Float :=
  match g.rebuildOrder changed with
  | none => none
  | some order =>
    if g.nodeCount == 0 then none
    else some (order.length.toFloat / g.nodeCount.toFloat)

/-! ## Ninja-Style Dependency Model

Ninja uses a simpler dependency model: files depend on other files,
and the build system computes the minimal rebuild set.
-/

/-- Simulate a Ninja-like build: input a changed file, output rebuild plan. -/
def ninjaSimulate (g : DependencyGraph) (changedFile : TheoryName) : String :=
  match g.rebuildOrder changedFile with
  | none => s!"ninja: error: cycle detected, cannot build '{changedFile}'"
  | some order =>
    s!"ninja: building {order.length} targets after '{changedFile}' changed"

/-- Find all "dirty" targets: those transitively depending on any changed node. -/
def findDirtyTargets (g : DependencyGraph) (changed : List TheoryName) : List TheoryName :=
  changed.bind (fun name => g.transitiveDependents name) |>.eraseDups

/-- Naive dedup for lists (preserving order, keeping first occurrence). -/
def List.eraseDups (xs : List α) [BEq α] : List α :=
  go xs []
where
  go : List α → List α → List α
    | [], acc => acc.reverse
    | x :: rest, acc =>
      if acc.contains x then go rest acc
      else go rest (x :: acc)

/-! ## Continuous Integration Dependency Model

CI pipelines are dependency graphs:
- Each stage depends on previous stages
- Parallel stages can run concurrently
- Topological order gives the pipeline schedule
-/

structure CIPipeline where
  stages : List TheoryNode
  dependencies : List DependencyEdge
  name : String
  deriving Repr

def CIPipeline.toDependencyGraph (p : CIPipeline) : DependencyGraph :=
  { nodes := p.stages, edges := p.dependencies }

def CIPipeline.isBuildable (p : CIPipeline) : Bool :=
  (p.toDependencyGraph).isAcyclic

def CIPipeline.buildSchedule (p : CIPipeline) : Option (List TheoryName) :=
  (p.toDependencyGraph).buildOrder

/-! ## Evaluations -/

#eval do
  let a := TheoryName.ofString "Source"
  let b := TheoryName.ofString "Object"
  let c := TheoryName.ofString "Binary"
  let g : DependencyGraph :=
    { nodes := [ TheoryNode.simple a "Source" "1" "src"
               , TheoryNode.simple b "Object" "1" "obj"
               , TheoryNode.simple c "Binary" "1" "bin" ]
    , edges := [ { source := b, target := a, kind := .import, description := none : DependencyEdge }
               , { source := c, target := b, kind := .import, description := none : DependencyEdge } ]
    }
  (simulateBuild g, isValidMakeDependency g)

#eval do
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
  (g.parallelism, g.criticalPath, g.totalWork, g.parallelSpeedup)

#eval do
  let a := TheoryName.ofString "Kernel"
  let b := TheoryName.ofString "Lib"
  let c := TheoryName.ofString "App"
  let g : DependencyGraph :=
    { nodes := [ TheoryNode.simple a "Kernel" "1" ""
               , TheoryNode.simple b "Lib" "1" ""
               , TheoryNode.simple c "App" "1" "" ]
    , edges := [ { source := b, target := a, kind := .import, description := none : DependencyEdge }
               , { source := c, target := b, kind := .import, description := none : DependencyEdge } ]
    }
  (rebuildCost g a, ninjaSimulate g a)

end MiniTheoryDependencyKernel
