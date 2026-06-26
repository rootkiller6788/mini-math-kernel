/-
# Dependency Kernel: Bridge to Algebra

Algebraic theories and their dependency structures: groups,
rings, fields, modules, vector spaces, and their interrelations.
Demonstrates how algebraic structures form a dependency hierarchy.
-/

import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects
import MiniTheoryDependencyKernel.Core.Laws
import MiniTheoryDependencyKernel.Constructions.Subobjects
import MiniTheoryDependencyKernel.Properties.Invariants

namespace MiniTheoryDependencyKernel

/-! ## Algebraic Theory Dependency Graph

The standard algebraic hierarchy: Set → Magma → Semigroup → Monoid → Group → AbelianGroup →
Ring → CommutativeRing → IntegralDomain → Field → VectorSpace → Module → Algebra.
-/

def algebraicTheories : List FormalTheory :=
  let set := FormalTheory.simple (TheoryName.ofString "Set")
  let magma := FormalTheory.simple (TheoryName.ofString "Magma")
               |>.addAxiom { name := "closure", statement := "x*y defined" }
  let semi := magma.addAxiom { name := "assoc", statement := "assoc" }
  let mono := semi.addAxiom { name := "ident", statement := "ident" }
  let group := mono.addAxiom { name := "inv", statement := "inv" }
  let abel := group.addAxiom { name := "comm", statement := "comm" }
  let ring := FormalTheory.simple (TheoryName.ofString "Ring")
              |>.addAxiom { name := "add_group", statement := "abelian additive group" }
              |>.addAxiom { name := "mul_monoid", statement := "multiplicative monoid" }
              |>.addAxiom { name := "distrib", statement := "distributivity" }
  let commRing := ring.addAxiom { name := "mul_comm", statement := "multiplication commutes" }
  let intDom := commRing.addAxiom { name := "no_zero_div", statement := "xy = 0 → x = 0 ∨ y = 0" }
  let field := intDom.addAxiom { name := "mul_inv", statement := "∀ x ≠ 0, ∃ x⁻¹" }
  let vecSpace := FormalTheory.simple (TheoryName.ofString "VectorSpace")
                 |>.addAxiom { name := "field_scalars", statement := "scalar field" }
                 |>.addAxiom { name := "ab_group_vectors", statement := "abelian group of vectors" }
  let module' := FormalTheory.simple (TheoryName.ofString "Module")
                |>.addAxiom { name := "ring_scalars", statement := "scalar ring" }
                |>.addAxiom { name := "ab_group_vectors", statement := "abelian group of vectors" }
  [set, magma, semi, mono, group, abel, ring, commRing, intDom, field, vecSpace, module']

def algebraicDependencyGraph : DependencyGraph :=
  let g := DependencyGraph.empty
  let theories := algebraicTheories
  let g := theories.foldl (fun g t => g.addNode (t.toNode "1.0" s!"algebra/{t.theoryName}")) g
  -- Add subtheory dependencies: each step in the hierarchy
  let g := g.addEdge { source := TheoryName.ofString "Magma", target := TheoryName.ofString "Set", kind := .import, description := none }
  let g := g.addEdge { source := TheoryName.ofString "Semigroup", target := TheoryName.ofString "Magma", kind := .import, description := none }
  let g := g.addEdge { source := TheoryName.ofString "Monoid", target := TheoryName.ofString "Semigroup", kind := .import, description := none }
  let g := g.addEdge { source := TheoryName.ofString "Group", target := TheoryName.ofString "Monoid", kind := .import, description := none }
  let g := g.addEdge { source := TheoryName.ofString "AbelianGroup", target := TheoryName.ofString "Group", kind := .import, description := none }
  let g := g.addEdge { source := TheoryName.ofString "Ring", target := TheoryName.ofString "AbelianGroup", kind := .import, description := none }
  let g := g.addEdge { source := TheoryName.ofString "CommutativeRing", target := TheoryName.ofString "Ring", kind := .import, description := none }
  let g := g.addEdge { source := TheoryName.ofString "IntegralDomain", target := TheoryName.ofString "CommutativeRing", kind := .import, description := none }
  let g := g.addEdge { source := TheoryName.ofString "Field", target := TheoryName.ofString "IntegralDomain", kind := .import, description := none }
  let g := g.addEdge { source := TheoryName.ofString "VectorSpace", target := TheoryName.ofString "Field", kind := .import, description := none }
  let g := g.addEdge { source := TheoryName.ofString "VectorSpace", target := TheoryName.ofString "AbelianGroup", kind := .import, description := none }
  let g := g.addEdge { source := TheoryName.ofString "Module", target := TheoryName.ofString "Ring", kind := .import, description := none }
  let g := g.addEdge { source := TheoryName.ofString "Module", target := TheoryName.ofString "AbelianGroup", kind := .import, description := none }
  g

/-! ## Algebra-Specific Dependency Analysis

Analyzing the algebraic theory hierarchy for structural properties.
-/

def algebraicDependencyReport : String :=
  let g := algebraicDependencyGraph
  let depth := g.maxDepth
  let leaves := g.leafTheories
  let roots := g.rootTheories
  s!"Algebra hierarchy: {g.nodeCount} theories, max depth {depth}, leaves: {leaves}, roots: {roots}"

def algebraicSubtheoryMap : List (TheoryName × List TheoryName) :=
  let g := algebraicDependencyGraph
  g.nodes.map fun n => (n.name, g.depsOf n.name)

def isAlgebraicTheory (name : TheoryName) : Bool :=
  let g := algebraicDependencyGraph
  g.nodes.any (·.name == name)

/-! ## Evaluations -/

#eval do
  let g := algebraicDependencyGraph
  (g.isAcyclic, g.nodeCount, g.edgeCount, g.maxDepth)

#eval do
  let theories := algebraicTheories
  theories.length

#eval do
  let g := algebraicDependencyGraph
  let vecSpace := TheoryName.ofString "VectorSpace"
  (g.depth vecSpace, g.depsOf vecSpace, g.edgesTo vecSpace |>.length)

#eval do
  let g := algebraicDependencyGraph
  algebraicDependencyReport

end MiniTheoryDependencyKernel
