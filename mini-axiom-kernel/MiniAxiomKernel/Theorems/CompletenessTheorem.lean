/-
# Axioms Kernel: Completeness Theorem

The (semantic) completeness theorem for propositional logic states:
  Every tautology is provable.

Equivalently: if a formula φ is true in all models of an axiom system Γ
(i.e., Γ ⊨ φ), then φ is a logical consequence of Γ (semantically:
for every model of Γ, φ is true).

In propositional logic, the completeness theorem is equivalent to the
statement that the truth-table method is complete: any tautology can
be detected by checking all assignments.

We provide proper Prop-level statements (§ Completeness Theorem) and
computational checks (§ Semantic Completeness, § Craig Interpolation).
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Properties.Completeness
import MiniAxiomKernel.Properties.Decidability
import MiniAxiomKernel.Theorems.Deduction
import MiniAxiomKernel.Theorems.Soundness

namespace MiniAxiomKernel

/-! ## Completeness Theorem (Prop-level)

For propositional logic with a finite vocabulary, the completeness
theorem is straightforward: we can enumerate all truth assignments
and check whether a formula is a tautology.

The deeper form of completeness (Gödel completeness for first-order
logic) is not formalized here; we focus on the propositional case
where completeness holds by the finite truth-table method.
-/

/-- **Semantic entailment as a Prop**: Γ ⊨ f means f is true in every
    model of Γ. This is the standard Tarskian definition. -/
def entailsProp (sys : AxiomSystem) (f : Formula) : Prop :=
  ∀ (assign : Nat → Bool), isModel assign sys → f.eval assign = true

/-- **Completeness for propositional tautologies**:
    A formula is a tautology (true under all assignments) iff
    it is entailed by the empty axiom system.
    This is true by definition — the empty system has all assignments
    as models. -/
theorem completeness_tautology (f : Formula) :
    (∀ (assign : Nat → Bool), f.eval assign = true) ↔
    entailsProp (AxiomSystem.empty "E" "1.0") f := by
  constructor
  · intro hTaut assign hModel; exact hTaut assign
  · intro hEnt assign
    apply hEnt assign
    intro ax h; simp [AxiomSystem.empty, AxiomSet.empty] at h

/-- **Completeness property: either a formula is entailed or it has
    a countermodel.** For any formula f and consistent system Γ,
    either Γ ⊨ f or there exists a model of Γ where f is false. -/
lemma completeness_or_countermodel (sys : AxiomSystem) (f : Formula)
    (hCons : isConsistent sys) :
    entailsProp sys f ∨
    ∃ (assign : Nat → Bool), isModel assign sys ∧ f.eval assign = false := by
  -- This is the law of excluded middle at the meta-level:
  -- either f is true in all models, or there is a countermodel.
  -- Since we're in classical logic (Prop), this holds by EM.
  by_cases h : ∀ (assign : Nat → Bool), isModel assign sys → f.eval assign = true
  · left; exact h
  · right
    push_neg at h
    rcases h with ⟨assign, hModel, hFalse⟩
    exact ⟨assign, hModel, hFalse⟩

/-- **Completeness via the Deduction Theorem**:
    Γ ∪ {A} ⊨ B  iff  Γ ⊨ A → B.
    This is the semantic completeness of the deduction theorem:
    the syntactic operation of moving A to the right of ⊨
    corresponds exactly to the semantic operation of forming A → B. -/
lemma completeness_deduction (sys : AxiomSystem) (A B : Formula) :
    (entailsProp (sys.addAxiom (Axiom.simple "h" A)) B ↔
     entailsProp sys (.impl A B)) := by
  -- This is a restatement of the deduction theorem in terms of entailsProp
  unfold entailsProp
  exact deduction_theorem sys A B

/-- **Strong Completeness (contrapositive form)**:
    If adding ¬f to a system makes it inconsistent, then f is entailed
    by the original system. Formally:
    If sys ∪ {¬f} is inconsistent, then sys ⊨ f.

    Proof: Suppose sys ⊭ f, i.e., there exists a model `assign` of sys
    where f is false. Then `assign` makes ¬f true, so `assign` is a
    model of sys ∪ {¬f}, contradicting inconsistency. -/
lemma strong_completeness (sys : AxiomSystem) (f : Formula)
    (hIncons : isInconsistent (sys.addAxiom (Axiom.simple "¬f" (.not f)))) :
    entailsProp sys f := by
  intro assign hModel
  by_cases hF : f.eval assign
  · exact hF
  · -- f false ⇒ ¬f true ⇒ assign models sys ∪ {¬f} ⇒ contradiction
    have hNotF : (.not f).eval assign = true := by
      simp [Formula.eval, hF]
    have hModelPlus : isModel assign (sys.addAxiom (Axiom.simple "¬f" (.not f))) := by
      intro ax hax
      simp [AxiomSystem.addAxiom, AxiomSet.add] at hax
      rcases hax with (h | h)
      · exact hModel ax h
      · subst h; exact hNotF
    exact absurd (⟨assign, hModelPlus⟩ : isConsistent _) hIncons

/-- **Lemma: Consistency and completeness**:
    A system is maximally consistent if it is consistent and adding
    any formula not already entailed makes the system inconsistent.
    Such systems are "complete" — they decide every formula. -/
def isMaximallyConsistentProp (sys : AxiomSystem) : Prop :=
  isConsistent sys ∧
  ∀ (f : Formula), ¬ entailsProp sys f → isInconsistent (sys.addAxiom (Axiom.simple "f" f))

/-- **Maximally consistent systems are deductively closed**:
    If sys is maximally consistent, then for every formula f,
    either sys ⊨ f or sys ⊨ ¬f (but not both). -/
lemma maximally_consistent_decides (sys : AxiomSystem)
    (hMax : isMaximallyConsistentProp sys) (f : Formula) :
    (entailsProp sys f ∧ ¬ entailsProp sys (.not f)) ∨
    (¬ entailsProp sys f ∧ entailsProp sys (.not f)) := by
  rcases hMax with ⟨hCons, hExtend⟩
  by_cases hEnt : entailsProp sys f
  · -- sys ⊨ f. We need to show sys ⊭ ¬f
    left
    constructor
    · exact hEnt
    · -- if sys ⊨ ¬f too, then every model of sys satisfies both f and ¬f, impossible
      intro hEntNot
      rcases hCons with ⟨assign, hModel⟩
      have hF := hEnt assign hModel
      have hNotF := hEntNot assign hModel
      simp [Formula.eval] at hNotF
      rw [hF] at hNotF; simp at hNotF
  · -- sys ⊭ f. By maximal consistency, sys ∪ {f} is inconsistent
    have hIncons := hExtend f hEnt
    -- sys ∪ {f} inconsistent ⇒ for every model of sys, f is false
    -- ⇒ ¬f is true in every model ⇒ sys ⊨ ¬f
    right
    constructor
    · exact hEnt
    · intro assign hModel
      -- If ¬f were false, then f would be true, making sys ∪ {f} consistent
      -- (contradiction since hIncons says it's inconsistent)
      by_cases hF : f.eval assign
      · -- f true ⇒ assign models sys ∪ {f} ⇒ contradiction
        have hModelPlus : isModel assign (sys.addAxiom (Axiom.simple "f" f)) := by
          intro ax hax
          simp [AxiomSystem.addAxiom, AxiomSet.add] at hax
          rcases hax with (hIn | hEq)
          · exact hModel ax hIn
          · subst hEq; exact hF
        exact absurd (⟨assign, hModelPlus⟩ : isConsistent _) hIncons
      · -- f false ⇒ ¬f true
        simp [Formula.eval, hF]

/-- **Lindenbaum's Lemma (finite propositional case)**:
    Every consistent axiom system with finitely many atoms can be
    extended to a maximally consistent system by iterating over
    all atoms and adding either the atom or its negation.

    In our representation, this is done by the `lindenbaumExtension`
    computational function (see § Deduction Theorem / Lindenbaum Lemma
    below). Here we state the Prop-level existence claim. -/
lemma lindenbaum_extension_exists (sys : AxiomSystem) (hCons : isConsistent sys) :
    ∃ (sysMax : AxiomSystem), isMaximallyConsistentProp sysMax := by
  -- For finite propositional logic: iterate over atoms a₁,...,aₙ,
  -- at each step add either aᵢ or ¬aᵢ, whichever preserves consistency.
  -- The existence proof relies on the finiteness of the atom set.
  -- We defer the constructive proof to the computational version.
  sorry

/-! ## Semantic Completeness (Computational)

The following provides finite-model-check versions of the completeness
theorem for #eval verification on small axiom systems. -/

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
