/-
# Dependency Kernel: Equivalence

Equivalence relations on dependency structures. Theory equivalence
via mutual interpretability, bisimulation of dependency graphs,
and equiconsistency relations.
-/

import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects
import MiniTheoryDependencyKernel.Morphisms.Hom
import MiniTheoryDependencyKernel.Morphisms.Iso

namespace MiniTheoryDependencyKernel

/-! ## Mutual Interpretability

Two theories are mutually interpretable if each can be interpreted
in the other. This is the fundamental notion of theory equivalence.
-/

structure MutualInterpretability where
  theoryA     : FormalTheory
  theoryB     : FormalTheory
  interpAB    : Interpretation
  interpBA    : Interpretation
  deriving Repr, Inhabited

instance : ToString MutualInterpretability where
  toString mi := s!"MutInterp({mi.theoryA.theoryName} ⟷ {mi.theoryB.theoryName})"

def MutualInterpretability.symmetric (mi : MutualInterpretability) : MutualInterpretability :=
  { theoryA  := mi.theoryB
  , theoryB  := mi.theoryA
  , interpAB := mi.interpBA
  , interpBA := mi.interpAB
  }

def MutualInterpretability.reflexive (t : FormalTheory) : MutualInterpretability :=
  let m := TheoryMorphism.id t
  { theoryA  := t
  , theoryB  := t
  , interpAB := Interpretation.ofMorphism m
  , interpBA := Interpretation.ofMorphism m
  }

/-! ## Equivalence of Formal Theories

The notion of equivalence goes beyond mutual interpretability:
we require the composed interpretations to be provably equivalent
to identity (categorical equivalence of theories).
-/

structure TheoryEquivalence where
  theoryA     : FormalTheory
  theoryB     : FormalTheory
  morphAB     : TheoryMorphism
  morphBA     : TheoryMorphism
  compAB_BA_eq_id : Bool  -- morphAB ∘ morphBA ~ id
  compBA_AB_eq_id : Bool  -- morphBA ∘ morphAB ~ id
  deriving Repr, Inhabited

instance : ToString TheoryEquivalence where
  toString eq := s!"Equiv({eq.theoryA.theoryName} ≈ {eq.theoryB.theoryName})"

def TheoryEquivalence.reflexive (t : FormalTheory) : TheoryEquivalence :=
  let m := TheoryMorphism.id t
  { theoryA := t, theoryB := t
  , morphAB := m, morphBA := m
  , compAB_BA_eq_id := true, compBA_AB_eq_id := true
  }

def TheoryEquivalence.symmetric (eq : TheoryEquivalence) : TheoryEquivalence :=
  { theoryA := eq.theoryB
  , theoryB := eq.theoryA
  , morphAB := eq.morphBA
  , morphBA := eq.morphAB
  , compAB_BA_eq_id := eq.compBA_AB_eq_id
  , compBA_AB_eq_id := eq.compAB_BA_eq_id
  }

/-! ## Dependency Graph Equivalence (Bisimulation)

Two dependency graphs are bisimilar if they have the same dependency
structure up to node renaming. This is weaker than isomorphism but
captures behavioral equivalence.
-/

structure DependencyBisimulation where
  graphA : DependencyGraph
  graphB : DependencyGraph
  relations : List (TheoryName × TheoryName)
  structuralMatch : Bool
  deriving Repr, Inhabited

instance : ToString DependencyBisimulation where
  toString b := s!"Bisim({b.graphA.nodeCount}⇌{b.graphB.nodeCount})"

def DependencyBisimulation.isReflexive (b : DependencyBisimulation) : Bool :=
  b.graphA.nodes.length == b.graphB.nodes.length
  && b.graphA.edges.length == b.graphB.edges.length

/-! ## Equiconsistency

Two theories are equiconsistent if the consistency of one implies
the consistency of the other. For first-order theories, mutual
interpretability implies equiconsistency.
-/

structure EquiconsistencyRelation where
  theoryA : FormalTheory
  theoryB : FormalTheory
  consistencyA_implies_B : Bool
  consistencyB_implies_A : Bool
  deriving Repr, Inhabited

instance : ToString EquiconsistencyRelation where
  toString r := s!"Equicons({r.theoryA.theoryName} ≡_con {r.theoryB.theoryName})"

def EquiconsistencyRelation.check (r : EquiconsistencyRelation) : Bool :=
  r.consistencyA_implies_B && r.consistencyB_implies_A

/-! ## Equivalence Classes

Partitioning the space of theories into equivalence classes
under mutual interpretability or equiconsistency.
-/

structure EquivalenceClass where
  representative : FormalTheory
  members        : List FormalTheory
  deriving Repr, Inhabited

def classifyBySignatureSize (theories : List FormalTheory) : List EquivalenceClass :=
  let groups := theories.groupBy (fun t1 t2 => t1.signature.size == t2.signature.size)
  groups.map fun ts =>
    { representative := ts.headD (FormalTheory.simple TheoryName.root)
    , members := ts
    }

def classifyByAxiomCount (theories : List FormalTheory) : List EquivalenceClass :=
  let groups := theories.groupBy (fun t1 t2 => t1.axioms.length == t2.axioms.length)
  groups.map fun ts =>
    { representative := ts.headD (FormalTheory.simple TheoryName.root)
    , members := ts
    }

/-! ## Grouping helper
-/

def List.groupBy (xs : List α) (eq : α → α → Bool) : List (List α) :=
  match xs with
  | [] => []
  | x :: rest =>
    let (group, others) := rest.partition (eq x)
    (x :: group) :: others.groupBy eq

/-! ## Evaluations -/

#eval do
  let t := FormalTheory.simple (TheoryName.ofString "Test")
  let mi := MutualInterpretability.reflexive t
  toString mi

#eval do
  let t := FormalTheory.simple (TheoryName.ofString "Test")
  let eq := TheoryEquivalence.reflexive t
  (toString eq, eq.symmetric |>.toString)

#eval do
  let t1 := FormalTheory.simple (TheoryName.ofString "T1")
  let t2 := FormalTheory.simple (TheoryName.ofString "T2")
  let t3 := FormalTheory.simple (TheoryName.ofString "T3")
  let ts := [t1, t2, t3]
  classifyByAxiomCount ts |>.length

end MiniTheoryDependencyKernel
