/-
# Dependency Kernel: Standard Examples

Standard examples of theory dependency graphs from real mathematics:
ZFC set theory, group/ring theory hierarchy, Peano arithmetic,
and their dependency relationships.
-/

import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects
import MiniTheoryDependencyKernel.Core.Laws
import MiniTheoryDependencyKernel.Constructions.Universal
import MiniTheoryDependencyKernel.Properties.Invariants
import MiniTheoryDependencyKernel.Morphisms.Equivalence

namespace MiniTheoryDependencyKernel

/-! ## Example 1: ZFC Dependency Graph

ZFC depends on first-order logic (FOL) and defines the foundation
for most of mathematics. Analysis, Algebra, and Topology all depend on ZFC.
-/

def zfcDependencyGraph : DependencyGraph :=
  let fol := TheoryNode.simple (TheoryName.ofString "FOL") "First-Order Logic" "1.0" "logic/fol"
  let zfc := TheoryNode.simple (TheoryName.ofString "ZFC") "Zermelo-Fraenkel Set Theory" "1.0" "foundations/zfc"
  let algebra := TheoryNode.simple (TheoryName.ofString "Algebra") "Abstract Algebra" "1.0" "algebra"
  let analysis := TheoryNode.simple (TheoryName.ofString "Analysis") "Real Analysis" "1.0" "analysis"
  let topology := TheoryNode.simple (TheoryName.ofString "Topology") "Point-Set Topology" "1.0" "topology"
  DependencyGraph.empty
    |>.addNode fol |>.addNode zfc |>.addNode algebra |>.addNode analysis |>.addNode topology
    |>.addEdge { source := zfc.name, target := fol.name, kind := .import, description := none }
    |>.addEdge { source := algebra.name, target := zfc.name, kind := .import, description := none }
    |>.addEdge { source := analysis.name, target := zfc.name, kind := .import, description := none }
    |>.addEdge { source := topology.name, target := zfc.name, kind := .import, description := none }

/-! ## Example 2: Group Theory Hierarchy

Building group theory and its subtheories: Magma → Semigroup → Monoid → Group → AbelianGroup.
-/

def groupTheoryHierarchy : FormalTheory × FormalTheory × FormalTheory × FormalTheory × FormalTheory :=
  let magma := FormalTheory.simple (TheoryName.ofString "Magma")
              |>.addAxiom { name := "closure", statement := "∀ x y, x*y is defined" }
  let semi := magma.addAxiom { name := "assoc", statement := "∀ x y z, (x*y)*z = x*(y*z)" }
  let mono := semi.addAxiom { name := "ident", statement := "∃ e, ∀ x, e*x = x ∧ x*e = x" }
  let group := mono.addAxiom { name := "inverse", statement := "∀ x, ∃ y, x*y = e ∧ y*x = e" }
  let abel := group.addAxiom { name := "comm", statement := "∀ x y, x*y = y*x" }
  (magma, semi, mono, group, abel)

/-! ## Example 3: Group-Ring-Field Hierarchy

Ring theory extends group theory (additive group) with multiplication;
Field theory extends ring theory with multiplicative inverses.
-/

def ringTheoryDependency : DependencyGraph × FormalTheory × FormalTheory × FormalTheory :=
  let group := FormalTheory.simple (TheoryName.ofString "GroupTheory")
              |>.addAxiom { name := "assoc", statement := "assoc" }
              |>.addAxiom { name := "ident", statement := "ident" }
              |>.addAxiom { name := "inv", statement := "inv" }
  let ring := FormalTheory.simple (TheoryName.ofString "RingTheory")
              |>.addAxiom { name := "add_group", statement := "additive group structure" }
              |>.addAxiom { name := "mul_assoc", statement := "mult associative" }
              |>.addAxiom { name := "distrib", statement := "distributive" }
  let field := FormalTheory.simple (TheoryName.ofString "FieldTheory")
              |>.addAxiom { name := "ring", statement := "ring structure" }
              |>.addAxiom { name := "mul_inv", statement := "multiplicative inverse" }
  let g := DependencyGraph.empty
    |>.addNode (group.toNode "1.0" "algebra/group")
    |>.addNode (ring.toNode "1.0" "algebra/ring")
    |>.addNode (field.toNode "1.0" "algebra/field")
    |>.addEdge { source := ring.theoryName, target := group.theoryName, kind := .import, description := none }
    |>.addEdge { source := field.theoryName, target := ring.theoryName, kind := .import, description := none }
  (g, group, ring, field)

/-! ## Example 4: Peano Arithmetic Dependencies

PA depends on first-order logic. Primitive recursive arithmetic (PRA)
is a subtheory of PA. Second-order arithmetic (Z2) extends PA.
-/

def paDependencyGraph : DependencyGraph :=
  let fol := TheoryNode.simple (TheoryName.ofString "FOL") "First-Order Logic" "1.0" "logic/fol"
  let pra := TheoryNode.simple (TheoryName.ofString "PRA") "Primitive Recursive Arithmetic" "1.0" "arithmetic/pra"
  let pa := TheoryNode.simple (TheoryName.ofString "PA") "Peano Arithmetic" "1.0" "arithmetic/pa"
  let z2 := TheoryNode.simple (TheoryName.ofString "Z2") "Second-Order Arithmetic" "1.0" "arithmetic/z2"
  DependencyGraph.empty
    |>.addNode fol |>.addNode pra |>.addNode pa |>.addNode z2
    |>.addEdge { source := pra.name, target := fol.name, kind := .import, description := none }
    |>.addEdge { source := pa.name, target := pra.name, kind := .import, description := some "PA extends PRA" }
    |>.addEdge { source := z2.name, target := pa.name, kind := .import, description := some "Z2 extends PA" }

/-! ## Example 5: Conservative Extension (Definitional)

Adding a defined symbol to a theory is a conservative extension.
Example: extending group theory with the definition of the commutator.
-/

def definitionalExtension : FormalTheory × FormalTheory :=
  let group := FormalTheory.simple (TheoryName.ofString "Group")
              |>.addAxiom { name := "assoc", statement := "∀ x y z, (x*y)*z = x*(y*z)" }
              |>.addAxiom { name := "ident", statement := "∃ e, ∀ x, e*x = x ∧ x*e = x" }
              |>.addAxiom { name := "inverse", statement := "∀ x, ∃ y, x*y = e ∧ y*x = e" }
  let groupWithComm := group.addAxiom
    { name := "commutator_def", statement := "comm(x,y) := x*y*x⁻¹*y⁻¹" }
  (group, groupWithComm)

/-! ## Example 6: Mutual Interpretability (PA and ZF-fin)

PA and ZF with the axiom of infinity negated (ZF-fin) are
mutually interpretable.
-/

def pa_zffin_mutualInterp : MutualInterpretability :=
  let pa := FormalTheory.simple (TheoryName.ofString "PA")
            |>.addAxiom { name := "induction", statement := "induction schema" }
  let zffin := FormalTheory.simple (TheoryName.ofString "ZF-fin")
              |>.addAxiom { name := "extensionality", statement := "extensionality" }
              |>.addAxiom { name := "neg_infinity", statement := "no infinite sets" }
  let mPA_ZFfin : TheoryMorphism :=
    { source := pa, target := zffin, symbolMap := SymbolMap.empty, axiomPreserving := true }
  let mZFfin_PA : TheoryMorphism :=
    { source := zffin, target := pa, symbolMap := SymbolMap.empty, axiomPreserving := true }
  { theoryA  := pa
  , theoryB  := zffin
  , interpAB := Interpretation.ofMorphism mPA_ZFfin
  , interpBA := Interpretation.ofMorphism mZFfin_PA
  }

/-! ## Evaluations -/

#eval do
  let g := zfcDependencyGraph
  (g.nodeCount, g.edgeCount, g.isAcyclic, g.topologicalOrder)

#eval do
  let (magma, semi, mono, group, abel) := groupTheoryHierarchy
  (magma.axioms.length, semi.axioms.length, mono.axioms.length,
   group.axioms.length, abel.axioms.length)

#eval do
  let (g, _, _, _) := ringTheoryDependency
  (g.depth (TheoryName.ofString "FieldTheory"), g.maxDepth)

#eval do
  let (group, _) := definitionalExtension
  let subRel := SubtheoryRelation.check group (group.addAxiom
    { name := "commutator_def", statement := "comm(x,y) := x*y*x⁻¹*y⁻¹" })
  (subRel.isSubtheory, ConservativityReport.check {
    original     := group
    extended     := group.addAxiom { name := "commutator_def", statement := "comm(x,y) := x*y*x⁻¹*y⁻¹" }
    newConstants := []
    newFunctions := []
    newRelations := []
    newAxioms    := [{ name := "commutator_def", statement := "comm(x,y) := x*y*x⁻¹*y⁻¹" }]
  }).isConserv

end MiniTheoryDependencyKernel
