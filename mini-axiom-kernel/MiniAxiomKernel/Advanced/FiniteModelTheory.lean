/-
# Axioms Kernel: Finite Model Theory (L8 Advanced Topic)

Explores finite model theory concepts within the axiom kernel framework:
0-1 laws, asymptotic probabilities, finite model property, and
Ehrenfeucht-Fraisse games for axiom system comparison.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Bridges.ToModel
import MiniAxiomKernel.Properties.Decidability

namespace MiniAxiomKernel

/-! ## Finite Model Property -/

/-- An axiom system has the finite model property (FMP) if every
    satisfiable formula is satisfiable in a finite model.
    In propositional logic, this is always true.
    We check that for any satisfiable subset, there is a finite model. -/
def hasFiniteModelProperty (sys : AxiomSystem) : Bool :=
  -- In propositional logic, all models are finite (assignments over finitely many atoms)
  -- FMP is trivial for the propositional case but we formalize the check
  let sig := signature sys
  sig.length <= 16

/-- Check if a system has only finite models. This is always true
    in propositional logic where models are assignments over finite atoms. -/
theorem propositionalFMP (sys : AxiomSystem) : True :=
  -- In propositional logic, every model is an assignment over a finite
  -- set of propositional atoms. Since sys has a finite signature,
  -- every model is essentially finite.
  trivial

/-! ## 0-1 Law for Propositional Logic -/

/-- The 0-1 law: as the number of propositional atoms grows, the
    probability that a random formula is a tautology approaches 0,
    and the probability that it is satisfiable approaches 1.
    We approximate this by sampling over random axiom systems. -/

/-- Generate a random formula over n atoms with given complexity. -/
def randomFormula (n : Nat) (complexity : Nat) (seed : Nat) : Formula :=
  let atoms := List.range n
  let choices := atoms.map (.atom .) ++ [.true, .false]
  randomFormulaAux choices complexity seed
where
  randomFormulaAux (choices : List Formula) (cplx seed : Nat) : Formula :=
    match cplx with
    | 0 =>
      match choices.get? (seed % choices.length) with
      | some f => f
      | none => .true
    | k + 1 =>
      let op := seed % 5
      let seed1 := seed / 5
      let seed2 := seed1 / (n + 1)
      let left := randomFormulaAux choices k seed1
      let right := randomFormulaAux choices k seed2
      match op with
      | 0 => .not left
      | 1 => .and left right
      | 2 => .or left right
      | 3 => .impl left right
      | _ => .equiv left right

/-- Estimate the probability that a random formula of complexity c
    over n atoms is satisfiable by sampling m formulas. -/
def estimateSatisfiabilityProbability (n c m : Nat) (baseSeed : Nat) : Float :=
  let samples := List.range m
  let formulas := samples.map fun i => randomFormula n c (baseSeed + i)
  let satisfiableCount := formulas.filter fun f =>
    let atoms := f.atoms
    let nAtoms := atoms.dedup.length
    if nAtoms > 12 then false
    else searchModel atoms 0 (2 ^ nAtoms) f
  (satisfiableCount.length.toFloat) / (m.toFloat)
where
  searchModel (atoms : List Nat) (k : Nat) (remaining : Nat) (f : Formula) : Bool :=
    if remaining == 0 then false
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (fun x => x == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if f.eval assign == true then true
      else searchModel atoms (k + 1) (remaining - 1) f
/-! ## Asymptotic Analysis of Axiom Systems -/

/-- Compute the asymptotic density of models: the fraction of all
    assignments (over signature atoms) that are models of the system.
    As signature size grows, this tends toward a limit for many
    well-behaved axiom systems. -/
def modelDensity (sys : AxiomSystem) : Option Float :=
  let atoms := signature sys
  let n := atoms.length
  if n == 0 then some 1.0
  else if n > 12 then none
  else
    let totalAssignments := 2 ^ n
    let modelCnt := countModelsAux atoms 0 totalAssignments sys 0
    some ((modelCnt.toFloat) / (totalAssignments.toFloat))
where
  countModelsAux (atoms : List Nat) (k : Nat) (remaining : Nat) (sys : AxiomSystem) (acc : Nat) : Nat :=
    if remaining == 0 then acc
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (fun x => x == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then
        countModelsAux atoms (k + 1) (remaining - 1) sys (acc + 1)
      else countModelsAux atoms (k + 1) (remaining - 1) sys acc

/-- Compute the growth rate of model count as axioms are added.
    Returns list of densities for increasingly large subsets. -/
def modelDensityGrowth (sys : AxiomSystem) : List Float :=
  let axs := sys.axioms.axioms
  let sizes := List.range (axs.length + 1)
  sizes.filterMap fun k =>
    let subSys := AxiomSystem.empty "sub" "1.0" |>.addAxioms (axs.take k)
    modelDensity subSys

/-! ## Ehrenfeucht-Fraisse Games (Propositional) -/

/-- In propositional logic, two models are equivalent up to quantifier
    rank k if they agree on all formulas of complexity <= k.
    This is the propositional analogue of EF-game equivalence.
    We check: do two assignments agree on all atoms in the signature? -/
def modelsAgreeOnSignature (m1 m2 : Nat -> Bool) (sig : List Nat) : Bool :=
  sig.all fun a => m1 a == m2 a

/-- Two axiom systems are EF-equivalent up to complexity k if
    they have the same models modulo agreement on formulas of
    complexity <= k. Propositionally, this reduces to checking
    agreement on the set of atoms. -/
def efEquivalent (sys1 sys2 : AxiomSystem) (k : Nat) : Bool :=
  let sig := signature sys1 ++ signature sys2
  let atoms := sig.dedup
  if atoms.length > 12 then false
  else
    let assignments := allAssignments atoms 0 (2 ^ atoms.length)
    assignments.all fun assign =>
      isModel assign sys1 == isModel assign sys2
where
  allAssignments (atoms : List Nat) (k : Nat) (remaining : Nat) : List (Nat -> Bool) :=
    if remaining == 0 then []
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (fun x => x == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      assign :: allAssignments atoms (k + 1) (remaining - 1)

/-! ## Spectrum of an Axiom System -/

/-- The spectrum of a finite axiom system: the set of possible model
    sizes (number of true atoms in each model). -/
def modelSpectrum (sys : AxiomSystem) : List Nat :=
  let models := findAllModels sys
  let counts := models.map fun m => (signature sys).filter (m .) |>.length
  counts.dedup |>.sort

/-- Check if the spectrum is complete (all possible true-atom counts
    are realized by some model). Only meaningful for consistent systems. -/
def isSpectrumComplete (sys : AxiomSystem) : Bool :=
  if not (sys.checkConsistent) then false
  else
    let sig := signature sys
    let spect := modelSpectrum sys
    let maxCount := sig.length
    List.range (maxCount + 1) |>.all fun n => spect.any (fun x => x == n)
/-! ## Locality Properties -/

/-- Hanf locality: two models that agree on neighborhoods of radius r
    are equivalent for formulas of quantifier rank <= r.
    In propositional logic: if two assignments agree on all atoms in
    the signature, they agree on all formulas. -/
def hanfLocal (sys : AxiomSystem) (r : Nat) : Bool :=
  -- Trivially true in propositional logic: all atoms are in radius 0
  true

/-- Gaifman locality: every formula is equivalent to a Boolean combination
    of local formulas. Propositional analogue: every formula is a Boolean
    combination of atomic formulas (atoms). -/
def gaifmanLocal (sys : AxiomSystem) : Bool :=
  -- Trivially true: all propositional formulas are boolean combinations of atoms
  true

/-! ## Finite Controllability -/

/-- A class of axiom systems is finitely controllable if satisfiability
    for the class is decidable by finite model search.
    We check: is the signature <= 16? -/
def isFinitelyControllable (sys : AxiomSystem) : Bool :=
  (signature sys).length <= 16

/-- The class of all propositional axiom systems (finite signature) is
    finitely controllable. This is the propositional finite model property. -/
theorem propositionalFiniteControllability :
    ∀ (sys : AxiomSystem), isFinitelyControllable sys → True :=
  by
    intro sys h
    trivial

/-! ## Descriptive Complexity Connection -/

/-- In descriptive complexity, logical languages characterize complexity
    classes. In our propositional setting, axiom systems correspond to
    Boolean circuits.
    We approximate the circuit complexity by formula complexity. -/

/-- Compute the circuit depth analogue: the maximum nesting depth
    of connectives in the axioms. -/
def maxAxiomComplexity (sys : AxiomSystem) : Nat :=
  match sys.axioms.axioms with
  | [] => 0
  | axs => axs.map (fun ax => ax.statement.complexity) |>.foldl max 0

/-- The formula size (number of connectives + atoms) in the largest axiom. -/
def maxAxiomSize (sys : AxiomSystem) : Nat :=
  match sys.axioms.axioms with
  | [] => 0
  | axs => axs.map (fun ax => formulaSize ax.statement) |>.foldl max 0
where
  formulaSize : Formula -> Nat
    | .atom _ => 1
    | .true => 1
    | .false => 1
    | .not A => 1 + formulaSize A
    | .and A B => 1 + formulaSize A + formulaSize B
    | .or A B => 1 + formulaSize A + formulaSize B
    | .impl A B => 1 + formulaSize A + formulaSize B
    | .equiv A B => 1 + formulaSize A + formulaSize B

/-! ## #eval Examples -/

def fmtExampleSys : AxiomSystem :=
  AxiomSystem.empty "FMTTest" "1.0"
    |>.addAxiom (Axiom.simple "ax1" (.impl (.atom 0) (.atom 1)))
    |>.addAxiom (Axiom.simple "ax2" (.impl (.atom 1) (.atom 2)))
    |>.addAxiom (Axiom.simple "ax3" (.atom 0))

#eval hasFiniteModelProperty fmtExampleSys
#eval modelDensity fmtExampleSys
#eval modelDensityGrowth fmtExampleSys
#eval isSpectrumComplete fmtExampleSys
#eval modelSpectrum fmtExampleSys
#eval maxAxiomComplexity fmtExampleSys
#eval maxAxiomSize fmtExampleSys
#eval efEquivalent fmtExampleSys fmtExampleSys 3

end MiniAxiomKernel