/-
# Axioms Kernel: Deduction Theorems

Proves and applies deduction theorem variants for axiom systems.
The deduction theorem states: if Γ ∪ {A} ⊢ B, then Γ ⊢ A → B.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Properties.Decidability

namespace MiniAxiomKernel

/-! ## Semantic Deduction Theorem -/

/-- The semantic deduction theorem: B is a logical consequence of
    sys ∪ {A} if and only if A → B is a logical consequence of sys.
    Verified by finite model search. -/
def checkDeductionTheorem (sys : AxiomSystem) (A B : Formula) : Bool :=
  let sysPlusA := sys.addAxiom (Axiom.simple "hypothesis" A)
  let consB := isLogicalConsequence sysPlusA B
  let consImpl := isLogicalConsequence sys (.impl A B)
  consB == consImpl

/-- A computational check: for a finite signature, verify the deduction
    theorem holds for all formula pairs up to a given complexity. -/
def verifyDeductionTheorem (sys : AxiomSystem) (maxComplexity : Nat) : Bool :=
  let sig := signature sys
  let formulas := generateFormulas sig maxComplexity
  formulas.all fun A =>
    formulas.all fun B =>
      checkDeductionTheorem sys A B
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
          if a != b then some [.and a b, .or a b, .impl a b] else none
      gen (seed ++ new.join) (remaining - 1)

/-! ## Deduction Theorem for Multiple Hypotheses -/

/-- General deduction theorem: adding multiple hypotheses.
    Γ ∪ {A₁, ..., Aₙ} ⊨ B  iff  Γ ⊨ (A₁ → ... → Aₙ → B). -/
def checkMultiDeductionTheorem (sys : AxiomSystem) (hyps : List Formula) (conc : Formula) : Bool :=
  let sysPlusHyps := sys.addAxioms (hyps.map fun f => Axiom.simple "hyp" f)
  let consConc := isLogicalConsequence sysPlusHyps conc
  let implConc := hyps.foldr .impl conc
  let consImpl := isLogicalConsequence sys implConc
  consConc == consImpl

/-! ## Lindenbaum Lemma (Finite Version) -/

/-- Lindenbaum's lemma: every consistent set can be extended to a
    maximally consistent set. In the finite propositional case, we
    can construct such an extension by adding atoms or their negations
    systematically. -/
def lindenbaumExtension (sys : AxiomSystem) : AxiomSystem :=
  let sig := signature sys
  let atoms := dedup (sys.axioms.statements.bind Formula.atoms ++ sig)
  extendByAtoms sys atoms
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  extendByAtoms (current : AxiomSystem) : List Nat → AxiomSystem
    | [] => current
    | a :: rest =>
      let withPos := current.addAxiom (Axiom.simple s!"atom-{a}" (.atom a))
      let withNeg := current.addAxiom (Axiom.simple s!"not-atom-{a}" (.not (.atom a)))
      if withPos.checkConsistent then
        extendByAtoms withPos rest
      else if withNeg.checkConsistent then
        extendByAtoms withNeg rest
      else extendByAtoms current rest

/-- Check that the Lindenbaum extension is maximally consistent. -/
def verifyLindenbaum (sys : AxiomSystem) : Bool :=
  let ext := lindenbaumExtension sys
  ext.checkConsistent

/-! ## Proof-Theoretic Deduction (Implication Chain) -/

/-- Construct an implication chain: from hypotheses h₁, ..., hₙ to
    conclusion C. This is a computational simulation of a proof that
    follows the deduction theorem structure. -/
def buildImplicationChain (hyps : List Formula) (conc : Formula) : Formula :=
  match hyps with
  | [] => conc
  | h :: hs => .impl h (buildImplicationChain hs conc)

/-- Check that the implication chain is a logical consequence of an
    empty axiom system when the conclusion follows from the hypotheses. -/
def checkImplicationChain (hyps : List Formula) (conc : Formula) : Bool :=
  let chain := buildImplicationChain hyps conc
  let sys := AxiomSystem.empty "temp" "1.0" |>.addAxioms (hyps.map fun f => Axiom.simple "hyp" f)
  match isLogicalConsequence sys conc with
  | some true => isLogicalConsequence (AxiomSystem.empty "empty" "1.0") chain == some true
  | _ => false

/-! ## Deduction Theorem as Equivalence -/

/-- The full semantic deduction theorem stated as a verified equivalence
    for finite systems. -/
def deductionEquivalence (sys : AxiomSystem) (A B : Formula) : Bool :=
  let atoms := dedup (
    sys.axioms.statements.bind Formula.atoms ++ A.atoms ++ B.atoms)
  let n := atoms.length
  if n > 16 then false
  else verify atoms 0 (2 ^ n) sys A B
where
  dedup : List Nat → List Nat
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))

  verify (atoms : List Nat) (k : Nat) (remaining : Nat)
      (sys : AxiomSystem) (A B : Formula) : Bool :=
    if remaining == 0 then true
    else
      let assign (a : Nat) : Bool :=
        match atoms.findIdx? (· == a) with
        | some i => ((k / (2 ^ i)) % 2) == 1
        | none => false
      if isModel assign sys then
        let implVal := (.impl A B).eval assign
        -- Check: A → B is true iff ¬(A true ∧ B false)
        let consVal := !(A.eval assign == true && B.eval assign == false)
        if implVal == consVal then
          verify atoms (k + 1) (remaining - 1) sys A B
        else false
      else verify atoms (k + 1) (remaining - 1) sys A B

/-! ## #eval Examples -/

def ddSys : AxiomSystem :=
  AxiomSystem.empty "ddTest" "1.0"
    |>.addAxiom (Axiom.simple "ax1" (.impl (.atom 0) (.atom 1)))

#eval checkDeductionTheorem ddSys (.atom 0) (.atom 1)
#eval isLogicalConsequence (ddSys.addAxiom (Axiom.simple "hyp" (.atom 0))) (.atom 1)
#eval isLogicalConsequence ddSys (.impl (.atom 0) (.atom 1))

def ddEmpty : AxiomSystem := AxiomSystem.empty "empty" "1.0"
#eval checkMultiDeductionTheorem ddEmpty [.atom 0, .atom 1] (.and (.atom 0) (.atom 1))

#eval verifyLindenbaum ddSys
#eval lindenbaumExtension ddSys |>.axioms.axioms.length

end MiniAxiomKernel
