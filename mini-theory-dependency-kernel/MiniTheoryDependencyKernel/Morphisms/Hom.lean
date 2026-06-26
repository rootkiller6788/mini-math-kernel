/-
# Dependency Kernel: Morphisms

Theory morphisms: structure-preserving maps between formal theories.
A theory morphism maps the signature of the source theory into the
target theory in a way that preserves the truth of axioms.
-/

import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects

namespace MiniTheoryDependencyKernel

open MiniObjectKernel

/-! ## Symbol Mapping

A symbol map specifies how each symbol in the source theory's
signature is translated to the target theory.
-/

structure SymbolMap where
  constants : List (String × String)
  functions : List (String × (String × Nat))
  relations : List (String × (String × Nat))
  deriving BEq, Repr, Inhabited

instance : ToString SymbolMap where
  toString m := s!"SymbolMap(c={m.constants.length}, f={m.functions.length}, r={m.relations.length})"

def SymbolMap.empty : SymbolMap :=
  { constants := [], functions := [], relations := [] }

def SymbolMap.addConstant (m : SymbolMap) (src tgt : String) : SymbolMap :=
  { m with constants := m.constants ++ [(src, tgt)] }

def SymbolMap.addFunction (m : SymbolMap) (src : String) (tgt : String) (arity : Nat) : SymbolMap :=
  { m with functions := m.functions ++ [(src, (tgt, arity))] }

def SymbolMap.isIdentity (m : SymbolMap) : Bool :=
  m.constants.all (fun (s, t) => s == t)
  && m.functions.all (fun (s, (t, _)) => s == t)
  && m.relations.all (fun (s, (t, _)) => s == t)

/-! ## Theory Morphism

A theory morphism from T to T' consists of:
- A mapping of the signature symbols of T into T'
- A verification that the translation of every axiom of T is
  provable in T' (axiomPreserving)
-/

structure TheoryMorphism where
  source : FormalTheory
  target : FormalTheory
  symbolMap : SymbolMap
  axiomPreserving : Bool  -- idealization: all source axioms translate to target theorems
  deriving Repr, Inhabited

instance : ToString TheoryMorphism where
  toString m := s!"Morphism({m.source.theoryName} → {m.target.theoryName})"

def TheoryMorphism.id (t : FormalTheory) : TheoryMorphism :=
  { source := t
  , target := t
  , symbolMap := SymbolMap.empty
  , axiomPreserving := true
  }

def TheoryMorphism.compose (m1 m2 : TheoryMorphism) : Option TheoryMorphism :=
  if m1.target.theoryName == m2.source.theoryName then
    some { source := m1.source
         , target := m2.target
         , symbolMap := SymbolMap.empty  -- simplified composition
         , axiomPreserving := m1.axiomPreserving && m2.axiomPreserving
         }
  else none

/-! ## Interpretation

A theory A is interpretable in theory B if there exists a
morphism from A to B. This is the fundamental relation in
relative consistency proofs.
-/

structure Interpretation where
  theoryA : FormalTheory
  theoryB : FormalTheory
  morphism : TheoryMorphism
  deriving Repr, Inhabited

instance : ToString Interpretation where
  toString i := s!"Interp({i.theoryA.theoryName} in {i.theoryB.theoryName})"

def Interpretation.ofMorphism (m : TheoryMorphism) : Interpretation :=
  { theoryA := m.source, theoryB := m.target, morphism := m }

/-! ## Relative Interpretation Graph

The graph of interpretability relations among theories.
-/

structure InterpretationGraph where
  theories      : List FormalTheory
  morphisms     : List TheoryMorphism
  deriving Repr, Inhabited

def InterpretationGraph.empty : InterpretationGraph :=
  { theories := [], morphisms := [] }

def InterpretationGraph.addTheory (ig : InterpretationGraph) (t : FormalTheory) : InterpretationGraph :=
  if ig.theories.any (·.theoryName == t.theoryName) then ig
  else { ig with theories := ig.theories ++ [t] }

def InterpretationGraph.addMorphism (ig : InterpretationGraph) (m : TheoryMorphism) : InterpretationGraph :=
  { ig with morphisms := ig.morphisms ++ [m] }

def InterpretationGraph.isMutuallyInterpretable (ig : InterpretationGraph) (a b : TheoryName) : Bool :=
  let ab := ig.morphisms.any (fun m => m.source.theoryName == a && m.target.theoryName == b)
  let ba := ig.morphisms.any (fun m => m.source.theoryName == b && m.target.theoryName == a)
  ab && ba

def InterpretationGraph.theoriesAbove (ig : InterpretationGraph) (threshold : TheoryName) : List FormalTheory :=
  ig.theories.filter fun t =>
    ig.morphisms.any (fun m => m.source.theoryName == threshold && m.target.theoryName == t.theoryName)

/-! ## Evaluations -/

#eval
  let t := FormalTheory.simple (TheoryName.ofString "EmptyTheory")
  let idMor := TheoryMorphism.id t
  toString idMor

#eval
  let source := FormalTheory.simple (TheoryName.ofString "SemiGroup")
            |>.addAxiom { name := "assoc", statement := "∀ x y z, (x*y)*z = x*(y*z)" }
  let target := FormalTheory.simple (TheoryName.ofString "Group")
            |>.addAxiom { name := "assoc", statement := "∀ x y z, (x*y)*z = x*(y*z)" }
            |>.addAxiom { name := "ident", statement := "∃ e, ∀ x, e*x = x" }
            |>.addAxiom { name := "inverse", statement := "∀ x, ∃ y, x*y = e" }
  let mor : TheoryMorphism :=
    { source := source, target := target,
      symbolMap := SymbolMap.empty, axiomPreserving := true }
  (toString mor, mor.axiomPreserving)

#eval
  let ig := InterpretationGraph.empty
  let semi := FormalTheory.simple (TheoryName.ofString "SemiGroup")
              |>.addAxiom { name := "assoc", statement := "assoc" }
  let group := semi.addAxiom { name := "ident", statement := "ident" }
              |>.addAxiom { name := "inv", statement := "inv" }
  let ig := ig.addTheory semi
  let ig := ig.addTheory group
  ig.isMutuallyInterpretable semi.theoryName group.theoryName

end MiniTheoryDependencyKernel
