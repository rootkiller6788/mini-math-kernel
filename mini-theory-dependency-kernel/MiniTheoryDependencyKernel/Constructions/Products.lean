/-
# Dependency Kernel: Products

Theory combination and products: union of signatures, theory
combination (Robinson-style), dependency graph products, and
free theory extensions.
-/

import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects

namespace MiniTheoryDependencyKernel

open MiniObjectKernel

/-! ## Theory Union

The union of two theories combines their signatures and axioms.
This is the simplest form of theory combination.
-/

structure TheoryUnion where
  theoryA    : FormalTheory
  theoryB    : FormalTheory
  unionName  : TheoryName
  deriving Repr, Inhabited

instance : ToString TheoryUnion where
  toString u := s!"Union({u.theoryA.theoryName} ∪ {u.theoryB.theoryName})"

def TheoryUnion.combined (u : TheoryUnion) : FormalTheory :=
  { theoryName := u.unionName
  , signature  := u.theoryA.signature.union u.theoryB.signature
  , axioms     := u.theoryA.axioms ++ u.theoryB.axioms
  }

def TheoryUnion.isDisjoint (u : TheoryUnion) : Bool :=
  -- Signatures share no non-logical symbols (excluding the overlap)
  u.theoryA.signature.constants.all (fun c => !u.theoryB.signature.constants.contains c)
  && u.theoryA.signature.functions.all (fun (f, _) => !u.theoryB.signature.functions.any (fun (g, _) => f == g))
  && u.theoryA.signature.relations.all (fun (r, _) => !u.theoryB.signature.relations.any (fun (s, _) => r == s))

/-! ## Theory Combination (Robinson-style)

Robinson's joint consistency theorem: if T1 and T2 are consistent
and their languages intersect only on a complete subtheory T0,
then T1 ∪ T2 is consistent.
-/

structure TheoryCombination where
  theory1    : FormalTheory
  theory2    : FormalTheory
  sharedTheory : FormalTheory  -- T0, the common subtheory
  combinedName : TheoryName
  deriving Repr, Inhabited

instance : ToString TheoryCombination where
  toString c := s!"Comb({c.theory1.theoryName} +_{shared} {c.theory2.theoryName})"

def TheoryCombination.combined (c : TheoryCombination) : FormalTheory :=
  { theoryName := c.combinedName
  , signature  := c.theory1.signature.union c.theory2.signature
  , axioms     := c.theory1.axioms ++ c.theory2.axioms
  }

def TheoryCombination.isRobinsonCompatible (c : TheoryCombination) : Bool :=
  -- Check that the shared theory is a subtheory of both
  let check1 := SubtheoryRelation.check c.sharedTheory c.theory1
  let check2 := SubtheoryRelation.check c.sharedTheory c.theory2
  check1.isSubtheory && check2.isSubtheory

/-! ## Dependency Graph Product

The cartesian product of two dependency graphs: nodes are pairs,
and an edge exists from (a1,b1) to (a2,b2) if there is an edge
in either component.
-/

def DependencyGraph.product (g1 g2 : DependencyGraph) : DependencyGraph :=
  let pairNodes : List TheoryNode :=
    g1.nodes.bind fun n1 =>
      g2.nodes.map fun n2 =>
        let pairedName := TheoryName.extend n1.name (toString n2.name)
        TheoryNode.simple pairedName
          (s!"{n1.title}×{n2.title}") "1.0" s!"product/{n1.path}+{n2.path}"
  let pairEdges : List DependencyEdge :=
    g1.edges.bind fun e1 =>
      g2.nodes.bind fun n2 =>
        g2.nodes.map fun _ =>
          { source      := TheoryName.extend e1.source (toString n2.name)
          , target      := TheoryName.extend e1.target (toString n2.name)
          , kind        := e1.kind
          , description := e1.description
          : DependencyEdge }
  { nodes := pairNodes, edges := pairEdges }

/-! ## Free Theory Extension

Given a signature, the free theory has no axioms — it is the
theory of all structures of that signature.
-/

structure FreeTheory where
  signature : Signature
  theoryName : TheoryName
  deriving Repr, Inhabited

def FreeTheory.toTheory (ft : FreeTheory) : FormalTheory :=
  { theoryName := ft.theoryName
  , signature := ft.signature
  , axioms := []
  }

def Signature.freeTheory (sig : Signature) (name : TheoryName) : FormalTheory :=
  { theoryName := name, signature := sig, axioms := [] }

/-! ## Theory Sum (Coproduct)

The disjoint union of two theories: their signatures are kept
separate (no identification of symbols).
-/

structure TheorySum where
  theoryA : FormalTheory
  theoryB : FormalTheory
  sumName : TheoryName
  deriving Repr, Inhabited

def TheorySum.theory (s : TheorySum) : FormalTheory :=
  -- Prefix symbols to avoid clashes
  let prefixedAxioms := s.theoryA.axioms.map fun a =>
    { a with name := s!"A.{a.name}" : Axiom }
  let prefixedBxioms := s.theoryB.axioms.map fun a =>
    { a with name := s!"B.{a.name}" : Axiom }
  { theoryName := s.sumName
  , signature  := s.theoryA.signature.union s.theoryB.signature
  , axioms     := prefixedAxioms ++ prefixedBxioms
  }

/-! ## Dependency Graph Merge

Merging two dependency graphs into one combined graph.
-/

def DependencyGraph.merge (g1 g2 : DependencyGraph) : DependencyGraph :=
  let allNodes := g1.nodes
  let newNodes := g2.nodes.filter (fun n => !g1.nodes.any (·.name == n.name))
  { nodes := allNodes ++ newNodes
  , edges := g1.edges ++ g2.edges
  }

def DependencyGraph.mergeWithBridge (g1 g2 : DependencyGraph)
    (bridgeSource bridgeTarget : TheoryName) : DependencyGraph :=
  let merged := g1.merge g2
  let bridgeEdge : DependencyEdge :=
    { source := bridgeSource, target := bridgeTarget, kind := .bridge
    , description := some "Cross-graph bridge" }
  merged.addEdge bridgeEdge

/-! ## Evaluations -/

#eval
  let t1 := FormalTheory.simple (TheoryName.ofString "Monoid")
            |>.addAxiom { name := "assoc", statement := "assoc" }
            |>.addAxiom { name := "ident", statement := "ident" }
  let t2 := FormalTheory.simple (TheoryName.ofString "CommMonoid")
            |>.addAxiom { name := "assoc", statement := "assoc" }
            |>.addAxiom { name := "ident", statement := "ident" }
            |>.addAxiom { name := "comm", statement := "comm" }
  let union : TheoryUnion := { theoryA := t1, theoryB := t2, unionName := TheoryName.ofString "Union" }
  union.combined.axioms.length

#eval
  let t1 := FormalTheory.simple (TheoryName.ofString "T1")
  let t2 := FormalTheory.simple (TheoryName.ofString "T2")
  let comb : TheoryCombination :=
    { theory1 := t1, theory2 := t2, sharedTheory := FormalTheory.simple (TheoryName.ofString "T0")
    , combinedName := TheoryName.ofString "Combined" }
  (toString comb, comb.isRobinsonCompatible)

#eval
  let sig : Signature := { constants := ["e"], functions := [("*", 2)], relations := [] }
  let freeT := Signature.freeTheory sig (TheoryName.ofString "FreeMagma")
  (freeT.signature.size, freeT.axioms.length)

end MiniTheoryDependencyKernel
