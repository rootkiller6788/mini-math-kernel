/-
# Dependency Kernel: Classification Data

Data structures for classifying theories by dependency structure,
consistency strength, axiomatizability, and computational complexity.
-/

import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects
import MiniTheoryDependencyKernel.Properties.Invariants

namespace MiniTheoryDependencyKernel

/-! ## Consistency Strength Classification

Theories are classified by their consistency strength: how much
mathematics they can encode. Measured here by the dependency
graph structure.
-/

inductive ConsistencyClass
  | weak
  | moderate
  | strong
  | veryStrong
  | maximal
  deriving BEq, Repr, Inhabited

instance : ToString ConsistencyClass where
  toString
    | .weak => "weak"
    | .moderate => "moderate"
    | .strong => "strong"
    | .veryStrong => "very strong"
    | .maximal => "maximal"

def ConsistencyClass.fromRank (rank : Nat) : ConsistencyClass :=
  if rank == 0 then .weak
  else if rank ≤ 2 then .moderate
  else if rank ≤ 5 then .strong
  else if rank ≤ 10 then .veryStrong
  else .maximal

/-! ## Axiomatizability Classification

Theories can be finitely axiomatizable, recursively axiomatizable,
or not effectively axiomatizable.
-/

inductive AxiomatizabilityClass
  | finite
  | recursive
  | nonEffective
  deriving BEq, Repr, Inhabited

instance : ToString AxiomatizabilityClass where
  toString
    | .finite => "finite"
    | .recursive => "recursive"
    | .nonEffective => "non-effective"

def AxiomatizabilityClass.ofTheory (t : FormalTheory) : AxiomatizabilityClass :=
  if t.axioms.length ≤ 10 then .finite
  else if t.axioms.length ≤ 100 then .recursive
  else .nonEffective

/-! ## Completeness Classification

-/

inductive CompletenessClass
  | complete
  | incomplete
  | essentiallyIncomplete
  deriving BEq, Repr, Inhabited

instance : ToString CompletenessClass where
  toString
    | .complete => "complete"
    | .incomplete => "incomplete"
    | .essentiallyIncomplete => "essentially incomplete"

/-! ## Decidability Classification

-/

inductive DecidabilityClass
  | decidable
  | undecidable
  | essentiallyUndecidable
  deriving BEq, Repr, Inhabited

instance : ToString DecidabilityClass where
  toString
    | .decidable => "decidable"
    | .undecidable => "undecidable"
    | .essentiallyUndecidable => "essentially undecidable"

/-! ## Theory Classification Record

A complete classification record for a formal theory.
-/

structure TheoryClassification where
  theoryName         : TheoryName
  consistencyClass   : ConsistencyClass
  axiomatizability   : AxiomatizabilityClass
  completeness       : CompletenessClass
  decidability       : DecidabilityClass
  depth              : Nat
  dependencyCount    : Nat
  dependentsCount    : Nat
  deriving Repr, Inhabited

instance : ToString TheoryClassification where
  toString c := s!"Classify({c.theoryName}: consist={c.consistencyClass}, ax={c.axiomatizability})"

def TheoryClassification.fromGraph (g : DependencyGraph) (name : TheoryName) : Option TheoryClassification :=
  match g.findNode name with
  | none => none
  | some n =>
    let rank := g.rank name
    let depCount := (g.edgesFrom name).length
    let depdCount := (g.edgesTo name).length
    some { theoryName       := name
         , consistencyClass := ConsistencyClass.fromRank rank
         , axiomatizability := .finite  -- default; could be refined
         , completeness     := .incomplete
         , decidability     := .undecidable
         , depth            := g.depth name
         , dependencyCount  := depCount
         , dependentsCount  := depdCount
         }

/-! ## Classification by Dependency Profile

Group theories by their dependency profile.
-/

structure DependencyProfile where
  name            : TheoryName
  directDeps      : Nat
  transitiveDeps  : Nat
  directDependents : Nat
  depth           : Nat
  deriving BEq, Repr, Inhabited

def DependencyProfile.ofGraph (g : DependencyGraph) (name : TheoryName) : Option DependencyProfile :=
  match g.findNode name with
  | none => none
  | some _ =>
    some { name            := name
         , directDeps      := (g.depsOf name).length
         , transitiveDeps  := (g.transitiveDeps name).length
         , directDependents := (g.edgesTo name).length
         , depth           := g.depth name
         }

def DependencyProfile.compare (a b : DependencyProfile) : Ordering :=
  compare a.depth b.depth

def classifyByProfile (g : DependencyGraph) : List DependencyProfile :=
  g.nodes.filterMap (fun n => DependencyProfile.ofGraph g n.name)

def mostFundamental (g : DependencyGraph) : Option TheoryName :=
  let profiles := classifyByProfile g
  profiles.sort DependencyProfile.compare |>.head? |>.map (·.name)

def mostDerived (g : DependencyGraph) : Option TheoryName :=
  let profiles := classifyByProfile g
  profiles.sort (fun a b => b.depth < a.depth) |>.head? |>.map (·.name)

/-! ## Classification Taxonomy

A hierarchical taxonomy of theories.
-/

structure Taxonomy where
  classes : List (String × List TheoryName)
  deriving Repr, Inhabited

def Taxonomy.empty : Taxonomy := { classes := [] }

def Taxonomy.addClass (tax : Taxonomy) (className : String) (theories : List TheoryName) : Taxonomy :=
  { tax with classes := tax.classes ++ [(className, theories)] }

def Taxonomy.findClass (tax : Taxonomy) (name : TheoryName) : Option String :=
  tax.classes.findSome? fun (className, theories) =>
    if theories.contains name then some className else none

/-! ## Evaluations -/

#eval do
  let a := TheoryName.ofString "Fundamental"
  let b := TheoryName.ofString "Derived"
  let g : DependencyGraph :=
    { nodes := [ TheoryNode.simple a "Fund" "1" ""
               , TheoryNode.simple b "Derived" "1" "" ]
    , edges := [ { source := b, target := a, kind := .import, description := none : DependencyEdge } ]
    }
  (mostFundamental g, mostDerived g)

#eval do
  let t := FormalTheory.simple (TheoryName.ofString "PA")
            |>.addAxiom { name := "ind", statement := "induction" }
  (AxiomatizabilityClass.ofTheory t, ConsistencyClass.fromRank 3)

#eval do
  let profiles := classifyByProfile DependencyGraph.empty
  let dc := DependencyProfile.compare
    { name := TheoryName.ofString "A", directDeps := 0, transitiveDeps := 0, directDependents := 1, depth := 1 }
    { name := TheoryName.ofString "B", directDeps := 2, transitiveDeps := 5, directDependents := 0, depth := 5 }
  dc

end MiniTheoryDependencyKernel
