/-
# Dependency Kernel: Counterexamples

Counterexamples demonstrating things that can go wrong in
theory dependency analysis: cyclic dependencies, inconsistent
theory combinations, and non-conservative extensions.
-/

import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects
import MiniTheoryDependencyKernel.Core.Laws
import MiniTheoryDependencyKernel.Constructions.Universal
import MiniTheoryDependencyKernel.Constructions.Products
import MiniTheoryDependencyKernel.Properties.Invariants

namespace MiniTheoryDependencyKernel

/-! ## Counterexample 1: Cyclic Dependency Graph

A dependency graph with a cycle: A depends on B, B depends on C,
C depends on A. This violates the acyclicity requirement.
-/

def cyclicDependencyGraph : DependencyGraph :=
  let a := TheoryNode.simple (TheoryName.ofString "A") "A" "1" "a"
  let b := TheoryNode.simple (TheoryName.ofString "B") "B" "1" "b"
  let c := TheoryNode.simple (TheoryName.ofString "C") "C" "1" "c"
  DependencyGraph.empty
    |>.addNode a |>.addNode b |>.addNode c
    |>.addEdge { source := a.name, target := b.name, kind := .import, description := none }
    |>.addEdge { source := b.name, target := c.name, kind := .import, description := none }
    |>.addEdge { source := c.name, target := a.name, kind := .import, description := none }

/-! ## Counterexample 2: Self-Dependency

A theory that depends on itself — an immediate violation of validity.
-/

def selfDependencyGraph : DependencyGraph :=
  let t := TheoryNode.simple (TheoryName.ofString "SelfRef") "Self-Referential" "1" "self"
  DependencyGraph.empty
    |>.addNode t
    |>.addEdge { source := t.name, target := t.name, kind := .import, description := none }

/-! ## Counterexample 3: Inconsistent Theory Combination

Combining two theories with conflicting axioms on overlapping
signatures can produce inconsistency.
-/

def inconsistentTheoryCombination : FormalTheory × FormalTheory :=
  let t1 := FormalTheory.simple (TheoryName.ofString "TheoryOfP")
            |>.addAxiom { name := "P_holds", statement := "P" }
  let t2 := FormalTheory.simple (TheoryName.ofString "TheoryOfNotP")
            |>.addAxiom { name := "notP_holds", statement := "¬P" }
  (t1, t2)

/-! ## Counterexample 4: Non-Conservative Extension

Adding a new axiom that is not provable in the original theory
but that changes the class of models: this is a proper (non-conservative)
extension.
-/

def nonConservativeExtension : FormalTheory × FormalTheory × TheoryExtension :=
  let semi := FormalTheory.simple (TheoryName.ofString "SemiGroup")
             |>.addAxiom { name := "assoc", statement := "assoc" }
  let commSemi := semi.addAxiom { name := "comm", statement := "commutativity" }
  let ext : TheoryExtension :=
    { original := semi, extended := commSemi
    , newConstants := [], newFunctions := [], newRelations := []
    , newAxioms := [{ name := "comm", statement := "commutativity" }]
    }
  (semi, commSemi, ext)

/-! ## Counterexample 5: Mutual Dependency (Cyclic Pair)

A pairs B and B depends on A — a 2-cycle.
-/

def mutualDependencyGraph : DependencyGraph :=
  let a := TheoryNode.simple (TheoryName.ofString "MutualA") "A" "1" "a"
  let b := TheoryNode.simple (TheoryName.ofString "MutualB") "B" "1" "b"
  DependencyGraph.empty
    |>.addNode a |>.addNode b
    |>.addEdge { source := a.name, target := b.name, kind := .import, description := none }
    |>.addEdge { source := b.name, target := a.name, kind := .import, description := none }

/-! ## Counterexample 6: Violated Transitive Closure

If the dependency graph is not transitively closed, build tools
may miss indirect dependencies.
-/

def missingTransitiveDependency : DependencyGraph :=
  let a := TheoryNode.simple (TheoryName.ofString "Top") "Top" "1" "top"
  let b := TheoryNode.simple (TheoryName.ofString "Middle") "Middle" "1" "mid"
  let c := TheoryNode.simple (TheoryName.ofString "Bottom") "Bottom" "1" "bot"
  -- Top → Middle, Middle → Bottom, but no Top → Bottom edge
  DependencyGraph.empty
    |>.addNode a |>.addNode b |>.addNode c
    |>.addEdge { source := a.name, target := b.name, kind := .import, description := none }
    |>.addEdge { source := b.name, target := c.name, kind := .import, description := none }

/-! ## Counterexample 7: Empty Dependency Graph

An empty graph with no theories is valid but degenerate.
-/

def emptyGraph : DependencyGraph := DependencyGraph.empty

/-! ## Counterexample 8: Disconnected Components

Two theories with no dependency between them cannot be ordered
relative to each other.
-/

def disconnectedComponents : DependencyGraph :=
  let a := TheoryNode.simple (TheoryName.ofString "ComponentA") "A" "1" "a"
  let b := TheoryNode.simple (TheoryName.ofString "ComponentB") "B" "1" "b"
  let c := TheoryNode.simple (TheoryName.ofString "DepC") "C" "1" "c"
  DependencyGraph.empty
    |>.addNode a |>.addNode b |>.addNode c
    |>.addEdge { source := c.name, target := a.name, kind := .import, description := none }

/-! ## Counterexample 9: Diamond Dependency

A diamond pattern: D depends on B and C, both of which depend on A.
This is valid but creates multiple dependency paths.
-/

def diamondDependency : DependencyGraph :=
  let a := TheoryNode.simple (TheoryName.ofString "Base") "Base" "1" "base"
  let b := TheoryNode.simple (TheoryName.ofString "Left") "Left" "1" "left"
  let c := TheoryNode.simple (TheoryName.ofString "Right") "Right" "1" "right"
  let d := TheoryNode.simple (TheoryName.ofString "Top") "Top" "1" "top"
  DependencyGraph.empty
    |>.addNode a |>.addNode b |>.addNode c |>.addNode d
    |>.addEdge { source := b.name, target := a.name, kind := .import, description := none }
    |>.addEdge { source := c.name, target := a.name, kind := .import, description := none }
    |>.addEdge { source := d.name, target := b.name, kind := .import, description := none }
    |>.addEdge { source := d.name, target := c.name, kind := .import, description := none }

/-! ## Evaluations -/

#eval do
  let g := cyclicDependencyGraph
  (g.isValid, g.isAcyclic, g.topologicalOrder)

#eval do
  let g := selfDependencyGraph
  (g.isValid, g.hasSelfDependency (TheoryName.ofString "SelfRef"))

#eval do
  let g := missingTransitiveDependency
  let top := TheoryName.ofString "Top"
  let bot := TheoryName.ofString "Bottom"
  let closure := g.transitiveClosure
  (g.hasPath top bot, closure.hasPath top bot)

#eval do
  let (t1, t2) := inconsistentTheoryCombination
  let union : TheoryUnion :=
    { theoryA := t1, theoryB := t2, unionName := TheoryName.ofString "Inconsistent" }
  (union.isDisjoint, union.combined.axioms.length)

end MiniTheoryDependencyKernel
