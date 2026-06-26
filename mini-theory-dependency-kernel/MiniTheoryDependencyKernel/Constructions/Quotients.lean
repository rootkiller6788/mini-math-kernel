/-
# Dependency Kernel: Quotients

Quotient theory constructions: adding new axioms to an existing
theory, forming the deductive closure, and classifying extension
types (conservative, definitional, proper).
-/

import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects
import MiniTheoryDependencyKernel.Constructions.Subobjects

namespace MiniTheoryDependencyKernel

open MiniObjectKernel

/-! ## Quotient Theory

A quotient theory is formed by adding one or more axioms to an
existing theory. The resulting theory has the same signature but
additional axioms constraining the models.
-/

structure QuotientTheory where
  baseTheory   : FormalTheory
  newAxioms    : List Axiom
  quotientName : TheoryName
  deriving Repr, Inhabited

instance : ToString QuotientTheory where
  toString q := s!"Quotient({q.baseTheory.theoryName}/{q.newAxioms.length} axioms)"

def QuotientTheory.simple (base : FormalTheory) (newAx : Axiom) (name : TheoryName) : QuotientTheory :=
  { baseTheory := base, newAxioms := [newAx], quotientName := name }

def QuotientTheory.theory (q : QuotientTheory) : FormalTheory :=
  { theoryName := q.quotientName
  , signature  := q.baseTheory.signature
  , axioms     := q.baseTheory.axioms ++ q.newAxioms
  }

def QuotientTheory.isConservative (q : QuotientTheory) : Bool :=
  q.newAxioms.isEmpty  -- no new axioms → trivially conservative

def QuotientTheory.isProperExtension (q : QuotientTheory) : Bool :=
  q.newAxioms.length > 0

/-! ## Axiom Addition Operations

Adding axioms to a theory one at a time, tracking the chain of extensions.
-/

def FormalTheory.quotientBy (t : FormalTheory) (newAx : Axiom) (newName : TheoryName) : QuotientTheory :=
  { baseTheory := t, newAxioms := [newAx], quotientName := newName }

def FormalTheory.quotientByMany (t : FormalTheory) (newAxs : List Axiom) (newName : TheoryName) : QuotientTheory :=
  { baseTheory := t, newAxioms := newAxs, quotientName := newName }

/-! ## Extension Chain

A sequence of successive quotients forming an extension chain.
-/

structure ExtensionChain where
  theories : List FormalTheory
  steps    : List (Axiom × TheoryName)
  deriving Repr, Inhabited

def ExtensionChain.singleton (t : FormalTheory) : ExtensionChain :=
  { theories := [t], steps := [] }

def ExtensionChain.extend (chain : ExtensionChain) (ax : Axiom) (newName : TheoryName) : ExtensionChain :=
  let last := chain.theories.headD (FormalTheory.simple TheoryName.root)
  let q := last.quotientBy ax newName
  { theories := chain.theories ++ [q.theory]
  , steps    := chain.steps ++ [(ax, newName)]
  }

def ExtensionChain.length (chain : ExtensionChain) : Nat :=
  chain.steps.length

def ExtensionChain.lastTheory (chain : ExtensionChain) : Option FormalTheory :=
  chain.theories.reverse.head?

/-! ## Axiom Independence

An axiom is independent in a theory if removing it produces a
strictly weaker theory. An independent set of axioms means no
axiom is derivable from the others.
-/

structure AxiomIndependence where
  theory     : FormalTheory
  axField    : Axiom
  isIndependent : Bool
  deriving Repr, Inhabited

def checkIndependence (t : FormalTheory) (ax : Axiom) : AxiomIndependence :=
  -- Heuristic: an axiom is independent if it's not redundant with any other single axiom
  let others := t.axioms.filter (·.name != ax.name)
  let isRedundant := others.any (fun o => o.statement == ax.statement)
  { theory := t, axField := ax, isIndependent := !isRedundant }

def findIndependentAxioms (t : FormalTheory) : List Axiom :=
  t.axioms.filter fun ax =>
    (checkIndependence t ax).isIndependent

/-! ## Theory Completion

The deductive completion of a theory: adding a given sentence or
its negation to ensure completeness.
-/

structure TheoryCompletion where
  theory    : FormalTheory
  sentence  : String
  completed : FormalTheory  -- with sentence or ~sentence added
  deriving Repr, Inhabited

def TheoryCompletion.complete (t : FormalTheory) (sentence : String) (chooseAffirmative : Bool) : TheoryCompletion :=
  let ax := if chooseAffirmative then
    { name := "completion_aff", statement := sentence : Axiom }
  else
    { name := "completion_neg", statement := s!"¬({sentence})" : Axiom }
  let completedTheory := t.addAxiom ax
  { theory := t, sentence, completed := completedTheory }

/-! ## Dependency Impact of Quotienting

When we quotient a theory, the dependencies may change.
-/

def quotientDependencyImpact (baseName : TheoryName) (q : QuotientTheory)
    (originalDeps : List DependencyEdge) : List DependencyEdge :=
  let oldDepsForBase := originalDeps.filter (·.source == baseName)
  oldDepsForBase.map fun e =>
    { e with source := q.quotientName }

/-! ## Evaluations -/

#eval
  let t := FormalTheory.simple (TheoryName.ofString "SemiGroup")
  let q := t.quotientBy { name := "comm", statement := "∀ x y, x*y = y*x" }
                        (TheoryName.ofString "AbelianSemiGroup")
  (toString q, q.isProperExtension, q.isConservative)

#eval
  let t := FormalTheory.simple (TheoryName.ofString "Base")
            |>.addAxiom { name := "ax1", statement := "P" }
            |>.addAxiom { name := "ax2", statement := "Q" }
  findIndependentAxioms t |>.length

#eval
  let t := FormalTheory.simple (TheoryName.ofString "Incomplete")
  let completion := TheoryCompletion.complete t "∀ x, P(x)" true
  completion.completed.axioms.length

end MiniTheoryDependencyKernel
