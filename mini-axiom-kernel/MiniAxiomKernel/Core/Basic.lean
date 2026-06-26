/-
# Axioms Kernel: Axiom Declarations

Defines what an axiom is in the kernel: a named formula
asserted without proof.
-/

import MiniLogicKernel.Core.Basic

namespace MiniAxiomKernel

structure Axiom where
  name        : String
  statement   : Formula
  description : Option String
  deriving Repr, Inhabited

instance : ToString Axiom where
  toString a := s!"axiom {a.name} : {a.statement}"

def Axiom.simple (name : String) (statement : Formula) : Axiom :=
  { name, statement, description := none }

def Axiom.described (name : String) (statement : Formula) (desc : String) : Axiom :=
  { name, statement, description := some desc }

structure AxiomSet where
  axioms : List Axiom
  deriving Repr, Inhabited

instance : ToString AxiomSet where
  toString s := s!"AxiomSet ({s.axioms.length} axioms)"

def AxiomSet.empty : AxiomSet := { axioms := [] }
def AxiomSet.add (s : AxiomSet) (a : Axiom) : AxiomSet := { axioms := s.axioms ++ [a] }
def AxiomSet.addAll (s : AxiomSet) (as : List Axiom) : AxiomSet := { axioms := s.axioms ++ as }
def AxiomSet.containsName (s : AxiomSet) (name : String) : Bool :=
  s.axioms.any (·.name == name)
def AxiomSet.findByName (s : AxiomSet) (name : String) : Option Axiom :=
  s.axioms.find? (·.name == name)
def AxiomSet.statements (s : AxiomSet) : List Formula := s.axioms.map (·.statement)
def AxiomSet.asContext (s : AxiomSet) : List Formula := s.statements
def AxiomSet.size (s : AxiomSet) : Nat := s.axioms.length

end MiniAxiomKernel
