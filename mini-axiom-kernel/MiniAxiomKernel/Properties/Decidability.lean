/-
# Axioms Kernel: Decidability Properties

Defines and checks decidability of axiom systems. A theory is decidable
if there is an algorithm to determine whether any formula is a logical
consequence of the axioms.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Constructions.Subobjects

namespace MiniAxiomKernel

/-! ## Decidability via Finite Models -/

/-- Check if a formula is a logical consequence of an axiom system
    by exhaustive model search (up to 16 atoms). Returns `true` if
    the formula is true in all models, `false` if there is a
    countermodel, or `none` if there are too many atoms. -/
def isLogicalConsequence (sys : AxiomSystem) (f : Formula) : Option Bool :=
  let atoms := dedup (sys.axioms.statements.bind Formula.atoms ++ f.atoms)
  let n := atoms.length
  if n > 16 then none
  else some (search atoms 0 (2 ^ n) sys f)
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  search (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sys : AxiomSystem) (f : Formula) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then
        if f.eval assign == true then
          search atoms (k + 1) (remaining - 1) sys f
        else false
      else search atoms (k + 1) (remaining - 1) sys f

/-- Check if a formula is satisfiable modulo an axiom system. -/
def isSatisfiableMod (sys : AxiomSystem) (f : Formula) : Option Bool :=
  let atoms := dedup (sys.axioms.statements.bind Formula.atoms ++ f.atoms)
  let n := atoms.length
  if n > 16 then none
  else some (search atoms 0 (2 ^ n) sys f)
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  search (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sys : AxiomSystem) (f : Formula) : Bool :=
    if remaining == 0 then false
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys && f.eval assign == true then true
      else search atoms (k + 1) (remaining - 1) sys f

/-! ## Decidability Classification -/

/-- Decidability status of an axiom system (finite approximation). -/
inductive DecidabilityClass
  | decidable    -- finite model method works
  | undecidable  -- too many atoms for brute force
  | trivial      -- inconsistent (everything is a consequence)
  deriving Repr, DecidableEq

instance : ToString DecidabilityClass where
  toString
    | .decidable => "decidable (finite)"
    | .undecidable => "undecidable (too many atoms)"
    | .trivial => "trivial (inconsistent)"

/-- Classify the decidability of a system based on signature size. -/
def classifyDecidability (sys : AxiomSystem) : DecidabilityClass :=
  if not (sys.checkConsistent) then .trivial
  else
    let atoms := dedup (sys.axioms.statements.bind Formula.atoms)
    let n := atoms.length
    if n ≤ 16 then .decidable
    else .undecidable
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

/-! ## Axiom System Comparator (Entailment Checker) -/

/-- A decision procedure: check if one axiom system entails another
    (every model of sys1 is a model of sys2) by finite model search. -/
def entails (sys1 sys2 : AxiomSystem) : Option Bool :=
  let atoms := dedup (
    (sys1.axioms.statements.bind Formula.atoms) ++
    (sys2.axioms.statements.bind Formula.atoms))
  let n := atoms.length
  if n > 16 then none
  else some (search atoms 0 (2 ^ n) sys1 sys2)
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  search (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sys1 sys2 : AxiomSystem) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys1 then
        if isModel assign sys2 then
          search atoms (k + 1) (remaining - 1) sys1 sys2
        else false
      else search atoms (k + 1) (remaining - 1) sys1 sys2

/-! ## Theorem Enumeration -/

/-- Enumerate all formulas (up to a complexity bound) that are logical
    consequences of an axiom system. This simulates a theorem prover. -/
def enumerateTheorems (sys : AxiomSystem) (maxComplexity : Nat) : List Formula :=
  let sig := signature sys
  let candidates := generateFormulas sig maxComplexity
  candidates.filter fun f =>
    isLogicalConsequence sys f == some true
where
  generateFormulas (atoms : List Nat) (maxC : Nat) : List Formula :=
    let base := atoms.map (.atom ·) ++ [.true, .false]
    generateUpTo base maxC

  generateUpTo (seed : List Formula) (remaining : Nat) : List Formula :=
    if remaining == 0 then seed
    else
      let negated := seed.map (.not ·)
      let paired := seed.bind fun a =>
        seed.filterMap fun b =>
          if a != b then some [.and a b, .or a b, .impl a b, .equiv a b] else none
      let allNew := negated ++ paired.join
      generateUpTo (seed ++ allNew) (remaining - 1)

/-! ## Decidability for Propositional Axiom Systems -/

/-- For propositional axiom systems (finite signature), the theory
    of an axiom system is always decidable by truth tables. -/
def isFiniteSignature (sys : AxiomSystem) : Bool :=
  (signature sys).length ≤ 16

/-- Decision procedure: check entailment by enumerating all models. -/
def decideEntailment (sys : AxiomSystem) (f : Formula) : Option Bool :=
  isLogicalConsequence sys f

/-- Check if the axiom system has a finite model property (it always
    does in propositional logic). -/
def hasFiniteModelProperty (sys : AxiomSystem) : Bool :=
  let sig := signature sys
  sig.length ≤ 16

/-! ## #eval Examples -/

def decSys : AxiomSystem :=
  AxiomSystem.empty "dec" "1.0"
    |>.addAxiom (Axiom.simple "ax1" (.impl (.atom 0) (.atom 1)))
    |>.addAxiom (Axiom.simple "ax2" (.atom 0))

#eval classifyDecidability decSys
#eval isLogicalConsequence decSys (.atom 1)
#eval isSatisfiableMod decSys (.not (.atom 1))
#eval entails decSys decSys
#eval isFiniteSignature decSys
#eval (enumerateTheorems decSys 1).length
#eval hasFiniteModelProperty decSys

end MiniAxiomKernel
