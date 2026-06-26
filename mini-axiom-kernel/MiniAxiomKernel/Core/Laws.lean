/-
# Axioms Kernel: Axiom Systems

Manages collections of axioms as coherent systems.
-/

import MiniAxiomKernel.Core.Basic

namespace MiniAxiomKernel

structure AxiomSystem where
  name        : String
  version     : String
  axioms      : AxiomSet
  description : Option String
  deriving Repr, Inhabited

instance : ToString AxiomSystem where
  toString s := s!"AxiomSystem {s.name} v{s.version} ({s.axioms.size} axioms)"

def AxiomSystem.empty (name version : String) : AxiomSystem :=
  { name, version, axioms := AxiomSet.empty, description := none }

def AxiomSystem.addAxiom (sys : AxiomSystem) (ax : Axiom) : AxiomSystem :=
  { sys with axioms := sys.axioms.add ax }

def AxiomSystem.addAxioms (sys : AxiomSystem) (axs : List Axiom) : AxiomSystem :=
  { sys with axioms := sys.axioms.addAll axs }

def isModel (assignment : Nat → Bool) (sys : AxiomSystem) : Prop :=
  ∀ ax ∈ sys.axioms.axioms, ax.statement.eval assignment = true

def isConsistent (sys : AxiomSystem) : Prop :=
  ∃ assignment : Nat → Bool, isModel assignment sys

def isInconsistent (sys : AxiomSystem) : Prop := ¬ isConsistent sys

def checkConsistent (sys : AxiomSystem) : Bool :=
  let allAtoms := dedup (sys.axioms.axioms.bind fun a => a.statement.atoms)
  let n := allAtoms.length
  if n > 16 then false
  else search allAtoms 0 (2 ^ n)
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  search (atoms : List Nat) (k : Nat) (remaining : Nat) : Bool :=
    if remaining == 0 then false
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then true
      else search atoms (k + 1) (remaining - 1)

def isIndependent (sys : AxiomSystem) (axName : String) : Option Bool :=
  match sys.axioms.findByName axName with
  | none => none
  | some target =>
    let others := sys.axioms.axioms.filter (·.name != axName)
    let allAtoms := dedup (others.bind fun a => a.statement.atoms ++ target.statement.atoms)
    let n := allAtoms.length
    if n > 16 then none
    else some (searchModel allAtoms 0 (2 ^ n) others target)
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  searchModel (atoms : List Nat) (k : Nat) (remaining : Nat) (others : List Axiom) (target : Axiom) : Bool :=
    if remaining == 0 then false
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      let othersOk := others.all fun ax => ax.statement.eval assign == true
      let targetFalse := target.statement.eval assign == false
      if othersOk && targetFalse then true
      else searchModel atoms (k + 1) (remaining - 1) others target

structure AxiomRegistry where
  systems : List AxiomSystem
  deriving Repr, Inhabited

def AxiomRegistry.empty : AxiomRegistry := { systems := [] }
def AxiomRegistry.register (reg : AxiomRegistry) (sys : AxiomSystem) : AxiomRegistry :=
  { systems := reg.systems ++ [sys] }
def AxiomRegistry.find (reg : AxiomRegistry) (name : String) : Option AxiomSystem :=
  reg.systems.find? (·.name == name)

end MiniAxiomKernel
