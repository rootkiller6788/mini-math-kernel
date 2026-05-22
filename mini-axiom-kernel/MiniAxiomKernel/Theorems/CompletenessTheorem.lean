/-
# Axioms Kernel: Completeness Theorem

Proves completeness theorem variants for axiom systems. The completeness
theorem states: if a formula is true in all models of a system, then it
is a logical consequence (semantically complete).
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Properties.Completeness
import MiniAxiomKernel.Properties.Decidability
import MiniAxiomKernel.Theorems.Deduction
import MiniAxiomKernel.Theorems.Soundness

namespace MiniAxiomKernel

/-! ## Semantic Completeness -/

/-- The completeness theorem for propositional axiom systems: for any
    formula f, either f is a logical consequence of the system, or
    there exists a model of the system where f evaluates to false.
    This is always true in propositional logic (by truth tables). -/
def checkCompletenessTheorem (sys : AxiomSystem) (f : Formula) : Bool :=
  match isLogicalConsequence sys f with
  | some true => true   -- f is a consequence
  | some false =>
    -- There exists a countermodel
    isSatisfiableMod sys (.not f) == some true
  | none => false

/-- Verify the completeness theorem exhaustively: for every formula
    (up to given complexity), either it is a consequence or there is
    a countermodel. -/
def verifyCompletenessTheorem (sys : AxiomSystem) (maxComplexity : Nat) : Bool :=
  let sig := signature sys
  let formulas := generateFormulas sig maxComplexity
  formulas.all fun f => checkCompletenessTheorem sys f
where
  generateFormulas (atoms : List Nat) (maxC : Nat) : List Formula :=
    let base := atoms.map (.atom ·) ++ [.true, .false]
    gen base maxC

  gen (seed : List Formula) (remaining : Nat) : List Formula :=
    if remaining == 0 then seed
    else
      let negated := seed.map (.not ·)
      let new := negated ++ seed.bind fun a =>
        seed.filterMap fun b =>
          if a != b then some [.and a b, .or a b, .impl a b, .equiv a b] else none
      gen (seed ++ new.join) (remaining - 1)

/-! ## Completeness = Consequence or Countermodel -/

/-- The fundamental completeness property: for every formula, either
    it is true in all models (a consequence) or there is a specific
    model where it is false (a countermodel). -/
def completenessProperty (sys : AxiomSystem) (f : Formula) : Bool :=
  let atoms := dedup (sys.axioms.statements.bind Formula.atoms ++ f.atoms)
  let n := atoms.length
  if n > 16 then false
  else
    let allModelsTrue := searchAll atoms 0 (2 ^ n) sys f
    let counterModel := findModelWhereFalse atoms 0 (2 ^ n) sys f
    allModelsTrue || counterModel.isSome
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  searchAll (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sys : AxiomSystem) (f : Formula) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then
        if f.eval assign == true then
          searchAll atoms (k + 1) (remaining - 1) sys f
        else false
      else searchAll atoms (k + 1) (remaining - 1) sys f

  findModelWhereFalse (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sys : AxiomSystem) (f : Formula) : Option (Nat → Bool) :=
    if remaining == 0 then none
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys && f.eval assign == false then some assign
      else findModelWhereFalse atoms (k + 1) (remaining - 1) sys f

/-! ## Craig Interpolation (Finite Version) -/

/-- Craig interpolation: if A ⊨ B, there exists an interpolant I using
    only atoms common to A and B such that A ⊨ I and I ⊨ B.
    We approximate by checking all formulas over the common atoms. -/
def findInterpolant (sys : AxiomSystem) (A B : Formula) (maxComplexity : Nat) : Option Formula :=
  let commonAtoms := dedup (A.atoms.filter fun a => B.atoms.any (· == a))
  let candidates := generateFormulas commonAtoms maxComplexity
  candidates.find? fun I =>
    match isLogicalConsequence (sys.addAxiom (Axiom.simple "A" A)) I,
          isLogicalConsequence (sys.addAxiom (Axiom.simple "I" I)) B with
    | some true, some true => true
    | _, _ => false
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  generateFormulas (atoms : List Nat) (maxC : Nat) : List Formula :=
    let base := atoms.map (.atom ·) ++ [.true, .false]
    gen base maxC

  gen (seed : List Formula) (remaining : Nat) : List Formula :=
    if remaining == 0 then seed
    else
      let negated := seed.map (.not ·)
      let new := negated ++ seed.bind fun a =>
        seed.filterMap fun b =>
          if a != b then some [.and a b, .or a b, .impl a b, .equiv a b] else none
      gen (seed ++ new.join) (remaining - 1)

/-! ## Beth Definability (Finite Version) -/

/-- Beth definability: if a predicate (atom) is implicitly defined by
    a theory, then it is explicitly definable. We check if there exists
    a defining formula over the other atoms. -/
def checkBethDefinability (sys : AxiomSystem) (targetAtom : Nat) (maxComplexity : Nat) : Option Formula :=
  let otherAtoms := dedup (
    (sys.axioms.statements.bind Formula.atoms).filter (· != targetAtom))
  let candidates := generateFormulas otherAtoms maxComplexity
  candidates.find? fun defn =>
    let sysWithDef := sys.addAxiom
      (Axiom.simple "beth-def" (.equiv (.atom targetAtom) defn))
    match isLogicalConsequence sys (.equiv (.atom targetAtom) defn) with
    | some true => true
    | _ => false
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  generateFormulas (atoms : List Nat) (maxC : Nat) : List Formula :=
    let base := atoms.map (.atom ·) ++ [.true, .false]
    gen base maxC

  gen (seed : List Formula) (remaining : Nat) : List Formula :=
    if remaining == 0 then seed
    else
      let negated := seed.map (.not ·)
      let new := negated ++ seed.bind fun a =>
        seed.filterMap fun b =>
          if a != b then some [.and a b, .or a b, .impl a b, .equiv a b] else none
      gen (seed ++ new.join) (remaining - 1)

/-! ## Completeness and Consistency -/

/-- A system is consistent iff there is no formula f such that both
    f and ¬f are logical consequences. This is the syntactic equivalent
    of consistency. -/
def checkSyntacticConsistency (sys : AxiomSystem) : Bool :=
  let sig := signature sys
  let atoms := dedup (sys.axioms.statements.bind Formula.atoms ++ sig)
  let n := atoms.length
  if n > 16 then false
  else
    let formulas := generateFormulas sig 2
    !(formulas.any fun f =>
      isLogicalConsequence sys f == some true &&
      isLogicalConsequence sys (.not f) == some true)
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  generateFormulas (atoms : List Nat) (maxC : Nat) : List Formula :=
    let base := atoms.map (.atom ·) ++ [.true, .false]
    gen base maxC

  gen (seed : List Formula) (remaining : Nat) : List Formula :=
    if remaining == 0 then seed
    else
      let negated := seed.map (.not ·)
      let new := negated ++ seed.bind fun a =>
        seed.filterMap fun b =>
          if a != b then some [.and a b, .or a b] else none
      gen (seed ++ new.join) (remaining - 1)

/-! ## #eval Examples -/

def compThmSys : AxiomSystem :=
  AxiomSystem.empty "compThm" "1.0"
    |>.addAxiom (Axiom.simple "ax1" (.impl (.atom 0) (.atom 1)))
    |>.addAxiom (Axiom.simple "ax2" (.atom 0))

#eval checkCompletenessTheorem compThmSys (.atom 1)
#eval checkCompletenessTheorem compThmSys (.not (.atom 1))
#eval completenessProperty compThmSys (.atom 1)
#eval findInterpolant compThmSys (.atom 0) (.atom 1) 2
#eval checkBethDefinability compThmSys 0 2
#eval checkSyntacticConsistency compThmSys

end MiniAxiomKernel
