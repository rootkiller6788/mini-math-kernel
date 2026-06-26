/-
# Axioms Kernel: Completeness Properties

Defines and checks completeness of axiom systems. An axiom system is
syntactically complete if for every formula in its language, either
the formula or its negation is a logical consequence.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Constructions.Subobjects
import MiniAxiomKernel.Constructions.Quotients

namespace MiniAxiomKernel

/-! ## Syntactic Completeness -/

/-- An axiom system is (syntactically) complete over its signature
    if for every atom in the signature, either the atom or its negation
    is true in all models. This means the system decides every atomic
    formula. -/
def isSyntacticallyComplete (sys : AxiomSystem) : Bool :=
  let sig := signature sys
  let atoms := dedup (sys.axioms.statements.bind Formula.atoms ++ sig)
  let n := atoms.length
  if n > 16 then false
  else search atoms 0 (2 ^ n) sys sig
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  search (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sys : AxiomSystem) (sig : List Nat) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then
        let allModelsAgree := sig.all fun a =>
          let allAssignmentsMatch := allModels atoms 0 (2 ^ n) sys a (assign a)
          allAssignmentsMatch
        if allModelsAgree then search atoms (k + 1) (remaining - 1) sys sig
        else false
      else search atoms (k + 1) (remaining - 1) sys sig

  allModels (atoms : List Nat) (k' : Nat) (remaining' : Nat)
      (sys : AxiomSystem) (a : Nat) (val : Bool) : Bool :=
    if remaining' == 0 then true
    else
      let assign' (x : Nat) : Bool :=
        match atoms.findIdx? (· == x) with
        | some i => ((k' / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign' sys then
        if assign' a == val then
          allModels atoms (k' + 1) (remaining' - 1) sys a val
        else false
      else allModels atoms (k' + 1) (remaining' - 1) sys a val

/-! ## Completeness via Unique Model -/

/-- A system has a unique model up to the atoms in its signature
    if all models agree on all signature atoms. This is a stronger
    form of completeness (categoricity in the finite case). -/
def hasUniqueModel (sys : AxiomSystem) : Bool :=
  let atoms := dedup (sys.axioms.statements.bind Formula.atoms)
  let n := atoms.length
  if n > 16 then false
  else countModels atoms 0 (2 ^ n) sys ≤ 1
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  countModels (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sys : AxiomSystem) : Nat :=
    if remaining == 0 then 0
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then
        1 + countModels atoms (k + 1) (remaining - 1) sys
      else countModels atoms (k + 1) (remaining - 1) sys

/-- Count the number of models of an axiom system. -/
def modelCount (sys : AxiomSystem) : Option Nat :=
  let atoms := dedup (sys.axioms.statements.bind Formula.atoms)
  let n := atoms.length
  if n > 16 then none
  else some (cnt atoms 0 (2 ^ n) sys 0)
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  cnt (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sys : AxiomSystem) (acc : Nat) : Nat :=
    if remaining == 0 then acc
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then
        cnt atoms (k + 1) (remaining - 1) sys (acc + 1)
      else cnt atoms (k + 1) (remaining - 1) sys acc

/-! ## Completeness Classification -/

/-- The completeness class of an axiom system. -/
inductive CompletenessClass
  | complete     -- decides all formulas in its signature
  | incomplete   -- has undecided formulas
  | categorical  -- has a unique model
  | unknown      -- too many atoms to decide
  deriving Repr, DecidableEq

instance : ToString CompletenessClass where
  toString
    | .complete => "complete"
    | .incomplete => "incomplete"
    | .categorical => "categorical (unique model)"
    | .unknown => "unknown"

/-- Classify the completeness of a system. -/
def classifyCompleteness (sys : AxiomSystem) : CompletenessClass :=
  if hasUniqueModel sys then .categorical
  else
    let sig := signature sys
    let atoms := dedup (sys.axioms.statements.bind Formula.atoms ++ sig)
    let n := atoms.length
    if n > 16 then .unknown
    else if isSyntacticallyComplete sys then .complete
    else .incomplete
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

/-! ## Completing an Incomplete System -/

/-- Attempt to complete an incomplete system by adding enough atoms
    (either positively or negatively) to force a unique model. -/
def attemptCompletion (sys : AxiomSystem) : AxiomSystem :=
  let sig := signature sys
  let completions : List Axiom := sig.bind fun a =>
    let pos := Axiom.simple s!"complete-{a}" (.atom a)
    let neg := Axiom.simple s!"complete-{a}" (.not (.atom a))
    if modelCount sys == some 0 then []
    else [pos, neg]
  sys.addAxioms completions

/-- Check if the system is maximally consistent (no proper consistent
    extension over the same signature). Finite check. -/
def isMaximallyConsistent (sys : AxiomSystem) : Bool :=
  let sig := signature sys
  let atoms := dedup (sys.axioms.statements.bind Formula.atoms ++ sig)
  let n := atoms.length
  if n > 16 then false
  else checkMaximal atoms 0 (2 ^ n) sys sig
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  checkMaximal (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sys : AxiomSystem) (sig : List Nat) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then
        -- unique model up to signature atoms
        checkModels atoms 0 (2 ^ n) sys sig assign
      else checkMaximal atoms (k + 1) (remaining - 1) sys sig

  checkModels (atoms : List Nat) (k' : Nat) (remaining' : Nat)
      (sys : AxiomSystem) (sig : List Nat) (model : Nat → Bool) : Bool :=
    if remaining' == 0 then true
    else
      let assign' (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k' / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign' sys then
        let sameOnSig := sig.all fun a => assign' a == model a
        if sameOnSig then
          checkModels atoms (k' + 1) (remaining' - 1) sys sig model
        else false
      else checkModels atoms (k' + 1) (remaining' - 1) sys sig model

/-! ## #eval Examples -/

def completeSys : AxiomSystem :=
  AxiomSystem.empty "complete" "1.0"
    |>.addAxiom (Axiom.simple "ax1" (.atom 0))
    |>.addAxiom (Axiom.simple "ax2" (.atom 1))

#eval classifyCompleteness completeSys
#eval hasUniqueModel completeSys
#eval modelCount completeSys
#eval isMaximallyConsistent completeSys
#eval hasUniqueModel (AxiomSystem.empty "empty" "1.0")
#eval modelCount (AxiomSystem.empty "empty" "1.0")

end MiniAxiomKernel
