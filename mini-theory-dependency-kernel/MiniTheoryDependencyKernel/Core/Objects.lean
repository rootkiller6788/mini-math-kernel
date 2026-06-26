/-
# Dependency Kernel: Objects

Object-level theory structures: signatures, axioms, formal theories,
and theory extensions that build on the dependency graph layer.
-/

import MiniTheoryDependencyKernel.Core.Basic

namespace MiniTheoryDependencyKernel

open MiniObjectKernel

/-! ## Theory Signature

A signature specifies the non-logical symbols of a formal theory:
constant symbols, function symbols (name + arity), and relation symbols.
-/

structure Signature where
  constants : List String
  functions : List (String × Nat)
  relations : List (String × Nat)
  deriving BEq, Repr, Inhabited

instance : ToString Signature where
  toString sig :=
    s!"Sig(cons={sig.constants.length}, fns={sig.functions.length}, rels={sig.relations.length})"

def Signature.empty : Signature :=
  { constants := [], functions := [], relations := [] }

def Signature.isEmpty (sig : Signature) : Bool :=
  sig.constants.isEmpty && sig.functions.isEmpty && sig.relations.isEmpty

def Signature.size (sig : Signature) : Nat :=
  sig.constants.length + sig.functions.length + sig.relations.length

def Signature.union (s1 s2 : Signature) : Signature :=
  { constants := s1.constants ++ s2.constants
  , functions := s1.functions ++ s2.functions
  , relations := s1.relations ++ s2.relations
  }

def Signature.isSubsig (sub sig : Signature) : Bool :=
  sub.constants.all sig.constants.contains
  && sub.functions.all sig.functions.contains
  && sub.relations.all sig.relations.contains

/-! ## Axioms

An axiom is a named logical statement (represented as a string).
Axiom schemes are parameterized axiom templates.
-/

structure Axiom where
  name : String
  statement : String
  deriving BEq, Repr, Inhabited

instance : ToString Axiom where
  toString a := s!"Axiom({a.name})"

structure AxiomScheme where
  name : String
  parameterCount : Nat
  template : String
  deriving BEq, Repr, Inhabited

/-! ## Formal Theory

A formal theory is a signature together with a set of axioms.
-/

structure FormalTheory where
  theoryName : TheoryName
  signature  : Signature
  axioms     : List Axiom
  deriving Repr, Inhabited

instance : ToString FormalTheory where
  toString t := s!"Theory({t.theoryName})"

def FormalTheory.simple (name : TheoryName) : FormalTheory :=
  { theoryName := name, signature := Signature.empty, axioms := [] }

def FormalTheory.addAxiom (t : FormalTheory) (a : Axiom) : FormalTheory :=
  { t with axioms := t.axioms ++ [a] }

def FormalTheory.addConstant (t : FormalTheory) (c : String) : FormalTheory :=
  { t with signature := { t.signature with constants := t.signature.constants ++ [c] } }

def FormalTheory.toNode (t : FormalTheory) (version path : String) : TheoryNode :=
  { name        := t.theoryName
  , title       := toString t.theoryName
  , version     := version
  , path        := path
  , description := some s!"Axioms: {t.axioms.length}, Sig size: {t.signature.size}"
  , specialized := false
  }

/-! ## Theory Extension

A theory T' extends T if it has the same or larger signature
and contains all axioms of T (possibly adding more).
-/

structure TheoryExtension where
  original : FormalTheory
  extended : FormalTheory
  newConstants : List String
  newFunctions : List (String × Nat)
  newRelations : List (String × Nat)
  newAxioms    : List Axiom
  deriving Repr, Inhabited

def TheoryExtension.isSignatureExtension (ext : TheoryExtension) : Bool :=
  ext.original.signature.isSubsig ext.extended.signature

def TheoryExtension.isAxiomExtension (ext : TheoryExtension) : Bool :=
  ext.original.axioms.all ext.extended.axioms.contains

def TheoryExtension.isExtension (ext : TheoryExtension) : Bool :=
  ext.isSignatureExtension && ext.isAxiomExtension

def TheoryExtension.isConservative (ext : TheoryExtension) : Bool :=
  -- A conservative extension adds no new theorems in the old language
  ext.isExtension && ext.newAxioms.isEmpty

/-! ## Evaluations -/

#eval
  let sig : Signature := { constants := [], functions := [("+", 2), ("*", 2)], relations := [("=", 2)] }
  sig.size

#eval
  let t := FormalTheory.simple (TheoryName.ofString "GroupTheory")
  t.addAxiom { name := "assoc", statement := "∀ x y z, (x*y)*z = x*(y*z)" }
  |>.addAxiom { name := "identity", statement := "∃ e, ∀ x, e*x = x ∧ x*e = x" }
  |>.addAxiom { name := "inverse", statement := "∀ x, ∃ y, x*y = e ∧ y*x = e" }
  |>.axioms.length

#eval
  let orig := FormalTheory.simple (TheoryName.ofString "SemiGroup")
            |>.addAxiom { name := "assoc", statement := "∀ x y z, (x*y)*z = x*(y*z)" }
  let extd := orig.addAxiom { name := "comm", statement := "∀ x y, x*y = y*x" }
  let ext : TheoryExtension :=
    { original     := orig
    , extended     := extd
    , newConstants := []
    , newFunctions := []
    , newRelations := []
    , newAxioms    := [{ name := "comm", statement := "∀ x y, x*y = y*x" }]
    }
  (ext.isExtension, ext.isConservative)

end MiniTheoryDependencyKernel
