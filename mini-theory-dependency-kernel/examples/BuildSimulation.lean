/-
# Build System Simulation Demo

Run: `lake env lean --run examples/BuildSimulation.lean`

Demonstrates: Make-like build, parallel scheduling, incremental rebuild
-/
import MiniTheoryDependencyKernel
open MiniTheoryDependencyKernel
open MiniObjectKernel

#eval "══ Build System Simulation ══"

-- Create a realistic build graph: kernel → lib → app
def kernel := TheoryNode.simple (TheoryName.ofString "Kernel") "Kernel" "1.0" "src/kernel"
def lib    := TheoryNode.simple (TheoryName.ofString "Lib") "Library" "1.0" "src/lib"
def app    := TheoryNode.simple (TheoryName.ofString "App") "Application" "1.0" "src/app"

def buildGraph : DependencyGraph :=
  DependencyGraph.empty
    |>.addNode kernel
    |>.addNode lib
    |>.addNode app
    |>.addEdge { source := lib.name, target := kernel.name, kind := .import, description := none }
    |>.addEdge { source := app.name, target := lib.name, kind := .import, description := none }

-- Simulate a build
#eval simulateBuild buildGraph

-- Check validity
#eval s!"Valid Makefile dependency: {isValidMakeDependency buildGraph}"

-- Parallelism analysis
#eval s!"Parallel build widths: {buildGraph.parallelism}"
#eval s!"Critical path length: {buildGraph.criticalPath}"
#eval s!"Total work: {buildGraph.totalWork}"
#eval s!"Parallel speedup: {buildGraph.parallelSpeedup}"

-- Incremental rebuild: kernel changes → everything rebuilds
#eval s!"Rebuild after kernel change: {simulateChange buildGraph kernel.name}"
#eval s!"Rebuild cost (kernel): {rebuildCost buildGraph kernel.name}"

-- Incremental rebuild: app changes → only app rebuilds
#eval s!"Rebuild after app change: {simulateChange buildGraph app.name}"
#eval s!"Rebuild cost (app): {rebuildCost buildGraph app.name}"

-- Find bottleneck targets
#eval s!"Bottleneck targets: {bottleneckTargets buildGraph}"

-- Package manager: resolve dependencies for app
#eval s!"App dependencies: {resolveDependencies buildGraph app.name}"

#eval "══ Simulation Complete ══"
