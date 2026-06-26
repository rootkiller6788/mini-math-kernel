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

/-! ## Fundamental Lemmas about addAxiom -/

/-- Membership in the axiom list after `addAxiom`: an axiom is in
    `sys.addAxiom ax` iff it was already in `sys` or equals `ax`. -/
lemma mem_addAxiom_iff (sys : AxiomSystem) (ax ax' : Axiom) :
    ax' ∈ (sys.addAxiom ax).axioms.axioms ↔ ax' ∈ sys.axioms.axioms ∨ ax' = ax := by
  simp [AxiomSystem.addAxiom, AxiomSet.add]

/-- `isModel` for a system with one added axiom decomposes
    into `isModel` of the original system plus the new axiom being true. -/
lemma isModel_addAxiom_iff (sys : AxiomSystem) (ax : Axiom) (assign : Nat → Bool) :
    isModel assign (sys.addAxiom ax) ↔
    isModel assign sys ∧ ax.statement.eval assign = true := by
  constructor
  · intro h
    have hModel : isModel assign sys := by
      intro ax' hax'
      exact h ax' (by simp [AxiomSystem.addAxiom, AxiomSet.add, hax'])
    have hAx : ax.statement.eval assign = true :=
      h ax (by simp [AxiomSystem.addAxiom, AxiomSet.add])
    exact ⟨hModel, hAx⟩
  · intro ⟨hModel, hAx⟩ ax' hax'
    simp [AxiomSystem.addAxiom, AxiomSet.add] at hax'
    rcases hax' with (h | h)
    · exact hModel ax' h
    · subst h; exact hAx

structure AxiomRegistry where
  systems : List AxiomSystem
  deriving Repr, Inhabited

def AxiomRegistry.empty : AxiomRegistry := { systems := [] }
def AxiomRegistry.register (reg : AxiomRegistry) (sys : AxiomSystem) : AxiomRegistry :=
  { systems := reg.systems ++ [sys] }
def AxiomRegistry.find (reg : AxiomRegistry) (name : String) : Option AxiomSystem :=
  reg.systems.find? (·.name == name)

end MiniAxiomKernel
