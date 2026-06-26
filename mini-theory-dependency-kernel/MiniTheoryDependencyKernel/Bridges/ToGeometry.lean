/-
# Dependency Kernel: Bridge to Geometry

Geometric theories and their dependency structures: Euclidean geometry,
differential geometry, algebraic geometry, and their dependency
relationships in the mathematical theory landscape.
-/

import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects
import MiniTheoryDependencyKernel.Core.Laws
import MiniTheoryDependencyKernel.Constructions.Products
import MiniTheoryDependencyKernel.Properties.Invariants

namespace MiniTheoryDependencyKernel

/-! ## Geometric Theory Hierarchy

The standard geometric theory dependencies:
Set → Topology → DifferentialGeometry → RiemannianGeometry →
AlgebraicGeometry ← CommutativeAlgebra ← Ring.
-/

def geometricTheories : List FormalTheory :=
  let set := FormalTheory.simple (TheoryName.ofString "SetTheory")
  let top := FormalTheory.simple (TheoryName.ofString "Topology")
  let diffGeo := FormalTheory.simple (TheoryName.ofString "DifferentialGeometry")
                |>.addAxiom { name := "manifold", statement := "smooth manifold definition" }
                |>.addAxiom { name := "tangent", statement := "tangent bundle" }
  let riemGeo := FormalTheory.simple (TheoryName.ofString "RiemannianGeometry")
                |>.addAxiom { name := "metric_tensor", statement := "Riemannian metric" }
                |>.addAxiom { name := "curvature", statement := "curvature tensor" }
  let algGeo := FormalTheory.simple (TheoryName.ofString "AlgebraicGeometry")
               |>.addAxiom { name := "scheme", statement := "affine scheme definition" }
               |>.addAxiom { name := "sheaf", statement := "structure sheaf" }
  let commAlg := FormalTheory.simple (TheoryName.ofString "CommutativeAlgebra")
                |>.addAxiom { name := "ring", statement := "commutative ring" }
                |>.addAxiom { name := "ideal", statement := "ideal theory" }
  [set, top, diffGeo, riemGeo, algGeo, commAlg]

def geometryDependencyGraph : DependencyGraph :=
  let g := DependencyGraph.empty
  let g := geometricTheories.foldl
    (fun g t => g.addNode (t.toNode "1.0" s!"geometry/{t.theoryName}")) g
  let g := g.addEdge
    { source := TheoryName.ofString "Topology"
    , target := TheoryName.ofString "SetTheory"
    , kind := .import, description := none }
  let g := g.addEdge
    { source := TheoryName.ofString "DifferentialGeometry"
    , target := TheoryName.ofString "Topology"
    , kind := .import, description := some "manifolds are topological spaces" }
  let g := g.addEdge
    { source := TheoryName.ofString "RiemannianGeometry"
    , target := TheoryName.ofString "DifferentialGeometry"
    , kind := .import, description := none }
  let g := g.addEdge
    { source := TheoryName.ofString "AlgebraicGeometry"
    , target := TheoryName.ofString "Topology"
    , kind := .import, description := some "Zariski topology" }
  let g := g.addEdge
    { source := TheoryName.ofString "AlgebraicGeometry"
    , target := TheoryName.ofString "CommutativeAlgebra"
    , kind := .import, description := some "schemes via rings" }
  g

/-! ## Geometry Dependency Analysis

Analyzing the geometric theory hierarchy for structural properties.
-/

def geometryDependencyReport : String :=
  let g := geometryDependencyGraph
  let depth := g.maxDepth
  let leaves := g.leafTheories
  let roots := g.rootTheories
  s!"Geometry hierarchy: {g.nodeCount} theories, max depth {depth}, roots: {roots}, leaves: {leaves}"

def geometricTheoryRanking : List (TheoryName × Nat) :=
  let g := geometryDependencyGraph
  g.rankAll

/-! ## Cross-Domain Dependencies

Geometry depends on Topology and overlaps with Algebra in Algebraic Geometry.
-/

structure GeometricCrossReference where
  geometryTheory : TheoryName
  dependsOnCategory : String
  algebraicTheory : TheoryName
  deriving Repr

def geometryAlgebraIntersection : List GeometricCrossReference :=
  [ { geometryTheory := TheoryName.ofString "AlgebraicGeometry"
    , dependsOnCategory := "Algebra"
    , algebraicTheory := TheoryName.ofString "CommutativeAlgebra" }
  ]

def isGeometricTheory (name : TheoryName) : Bool :=
  let g := geometryDependencyGraph
  g.nodes.any (·.name == name)

/-! ## Evaluations -/

#eval do
  let g := geometryDependencyGraph
  (g.isAcyclic, g.nodeCount, g.edgeCount, g.maxDepth)

#eval do
  let theories := geometricTheories
  theories.length

#eval do
  let g := geometryDependencyGraph
  let algGeo := TheoryName.ofString "AlgebraicGeometry"
  let deps := g.transitiveDeps algGeo
  (g.depth algGeo, deps.length, deps)

#eval do
  let g := geometryDependencyGraph
  geometryDependencyReport

end MiniTheoryDependencyKernel
