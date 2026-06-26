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

open MiniObjectKernel

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

/-! ## Makefile Dependency Analysis

Analyzing a dependency graph as if it were a Makefile. Each theory node
is a build target, and edges represent build dependencies.
-/

/-- Check which targets are "phony" (no build artifact, just a dependency group). -/
def phonyTargets (g : DependencyGraph) : List TheoryName :=
  g.nodes.filter (fun n =>
    g.edgesTo n.name |>.isEmpty && g.edgesFrom n.name |>.isNotEmpty
  ) |>.map (·.name)

/-- Find the "default target" — first node in topological order. -/
def defaultTarget (g : DependencyGraph) : Option TheoryName :=
  match g.topologicalOrder with
  | some (first :: _) => some first
  | _ => none

/-- Compute build levels for a Makefile-like build. Level 0 = no deps. -/
def DependencyGraph.makeBuildLevels (g : DependencyGraph) : Option (List (List TheoryName)) :=
  match g.topologicalOrder with
  | none => none
  | some order =>
    let reverseOrder := order.reverse
    some (go reverseOrder [])
where
  go : List TheoryName → List (List TheoryName) → List (List TheoryName)
    | [], acc => acc
    | n :: rest, acc =>
      let deps := g.depsOf n
      let level := deps.map (fun d =>
        match acc.findIdx? (·.contains d) with
        | none => 0
        | some idx => idx + 1
      ) |>.foldl max 0
      -- Insert n at the right level
      let (before, after) := acc.splitAt level
      let newAcc := before
      if after.isEmpty then
        newAcc ++ [[n]]
      else
        let thisLevel := after.headD []
        newAcc ++ [(thisLevel ++ [n])] ++ after.tailD
      go rest newAcc

/-- Estimate build time assuming unit time per target and perfect parallelism. -/
def estimateBuildTime (g : DependencyGraph) : Option Nat :=
  g.criticalPath

/-- Estimate build time with limited workers. -/
def estimateBuildTimeLimited (g : DependencyGraph) (workers : Nat) : Option Nat :=
  match g.parallelism with
  | none => none
  | some levels =>
    some (levels.foldl (fun acc levelSize =>
      -- With `workers` parallel workers, each level takes ceil(levelSize / workers)
      acc + ((levelSize + workers - 1) / workers)
    ) 0)

/-! ## Cache-Aware Dependency Analysis

In build systems like Bazel or Buck, caching determines whether a target
needs rebuilding. Cache invalidation propagates through the dependency graph.
-/

/-- Check if a target is "cacheable" — has no side effects (modeled as having no dependents of kind `test`). -/
def isCacheable (g : DependencyGraph) (name : TheoryName) : Bool :=
  !g.edges.any (fun e => e.source == name && e.kind == .test)

/-- Find all targets that would be invalidated if cache for `name` is cleared. -/
def cacheInvalidationSet (g : DependencyGraph) (name : TheoryName) : List TheoryName :=
  g.transitiveDependents name

/-- Compute cache hit probability (fraction of nodes that are cacheable). -/
def cacheHitRate (g : DependencyGraph) : Float :=
  if g.nodeCount == 0 then 0.0
  else
    let cacheable := g.nodes.filter (fun n => isCacheable g n.name) |>.length
    cacheable.toFloat / g.nodeCount.toFloat

/-! ## Package Manager Dependency Resolution

Simulate a package manager (like npm, cargo, apt) resolving dependencies.
-/

/-- Resolve transitive dependencies with version constraints.
    Returns Some (list of packages in install order) or None if conflict. -/
def resolveDependencies (g : DependencyGraph) (root : TheoryName) : Option (List TheoryName) :=
  -- In a valid graph, the topological order restricted to root's closure works
  if !g.isAcyclic then none
  else
    let closure := g.dependencyClosure root
    match g.topologicalOrder with
    | none => none
    | some order =>
      some (order.filter closure.contains)

/-- Check for diamond dependency conflicts: if two paths lead to different versions. -/
def hasDiamondConflict (g : DependencyGraph) (name : TheoryName) : Bool :=
  let paths := g.allPaths name name  -- self-paths indicate indirect diamond
  paths.length > 1

/-- List all theories that are transitively depended on (like `npm ls`). -/
def listDependencies (g : DependencyGraph) (root : TheoryName) : List (TheoryName × Nat) :=
  let deps := g.transitiveDeps root
  deps.map fun d => (d, g.depth d)

/-! ## Build Performance Analysis

Analyzing build performance from the dependency graph structure.
-/

/-- Identify bottleneck targets: those on the critical path with high dependents. -/
def bottleneckTargets (g : DependencyGraph) : List (TheoryName × Nat × Float) :=
  let maxDep := g.nodes.map (fun n => (g.edgesTo n.name).length) |>.foldl max 0
  g.nodes.filterMap fun n =>
    let depCount := (g.edgesTo n.name).length
    if depCount.toFloat >= (maxDep.toFloat * 0.5) then
      some (n.name, depCount, g.impactFactor n.name)
    else none

/-- Compute the total rebuild cost if each target has a build cost (approximated by its depth). -/
def totalRebuildCost (g : DependencyGraph) : Nat :=
  g.nodes.foldl (fun acc n => acc + g.depth n.name) 0

/-- Find targets that can be built in parallel (same topological level). -/
def parallelBuildGroups (g : DependencyGraph) : Option (List (List TheoryName)) :=
  match g.topologicalOrder with
  | none => none
  | some order =>
    let groups := go order [] []
    some groups
where
  go : List TheoryName → List TheoryName → List (List TheoryName) → List (List TheoryName)
    | [], _, acc => acc.reverse
    | n :: rest, built, acc =>
      let deps := g.depsOf n
      if deps.all built.contains then
        -- All deps built → can build n now along with others at this level
        let (sameLevel, rest') := rest.span (fun m =>
          (g.depsOf m).all (fun d => built.contains d || d == n))
        let group := n :: sameLevel
        go rest' (group.map id ++ built) (group :: acc)
      else
        go (rest ++ [n]) built acc

/-! ## Evaluations -/

#eval
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
  (simulateBuild g, isValidMakeDependency g, estimateBuildTime g,
   estimateBuildTimeLimited g 2, resolveDependencies g c)

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
  (g.parallelism, g.criticalPath, g.totalWork, g.parallelSpeedup,
   cacheHitRate g, phonyTargets g, defaultTarget g)

#eval
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
  (rebuildCost g a, ninjaSimulate g a, bottleneckTargets g, totalRebuildCost g)

#eval
  let a := TheoryName.ofString "Base"
  let b := TheoryName.ofString "Left"
  let c := TheoryName.ofString "Right"
  let d := TheoryName.ofString "Top"
  let g : DependencyGraph :=
    { nodes := [ TheoryNode.simple a "Base" "1" ""
               , TheoryNode.simple b "Left" "1" ""
               , TheoryNode.simple c "Right" "1" ""
               , TheoryNode.simple d "Top" "1" "" ]
    , edges := [ { source := b, target := a, kind := .import, description := none : DependencyEdge }
               , { source := c, target := a, kind := .import, description := none : DependencyEdge }
               , { source := d, target := b, kind := .import, description := none : DependencyEdge }
               , { source := d, target := c, kind := .import, description := none : DependencyEdge } ]
    }
  (hasDiamondConflict g d, cacheInvalidationSet g a, listDependencies g d,
   g.makeBuildLevels, parallelBuildGroups g)

end MiniTheoryDependencyKernel
