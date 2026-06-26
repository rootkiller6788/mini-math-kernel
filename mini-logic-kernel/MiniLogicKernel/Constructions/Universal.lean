/-
# Logic Kernel: Universal Constructions

Universal properties in logic: free Boolean algebras,
universal models, and Henkin constructions.
-/

import MiniLogicKernel.Core.Basic
import MiniLogicKernel.Core.Objects

namespace MiniLogicKernel

/-! ## Free Boolean Algebra on Generators -/

/-- The set of generators for a free Boolean algebra on n atoms:
    atom 0, atom 1, ..., atom (n-1). -/
def generators (n : Nat) : List Formula :=
  (List.range n).map Formula.atom

/-- A formula uses atoms only from the set {0, ..., n-1}. -/
def usesAtoms (f : Formula) (n : Nat) : Bool :=
  listAll f.atoms fun a => a < n

/-- The free Boolean algebra on n generators consists of all formulas
    built from those atoms, up to logical equivalence. -/
def freeFormulaOn (n : Nat) : Type :=
  { f : Formula // usesAtoms f n }

instance : Repr (freeFormulaOn n) where
  reprPrec s _ := repr s.val

/-! ## Universal Mapping Property -/

/-- Given a map from atom indices to arbitrary formulas,
    extend it homomorphically to all formulas.
    This is the universal map from the free Boolean algebra
    on countably many generators to any formula algebra. -/
def extendMap (f : Formula) (mapping : Nat → Formula) : Formula :=
  match f with
  | .atom n    => mapping n
  | .true      => .true
  | .false     => .false
  | .not A     => .not (extendMap A mapping)
  | .and A B   => .and (extendMap A mapping) (extendMap B mapping)
  | .or A B    => .or (extendMap A mapping) (extendMap B mapping)
  | .impl A B  => .impl (extendMap A mapping) (extendMap B mapping)
  | .equiv A B => .equiv (extendMap A mapping) (extendMap B mapping)

/-- The universal mapping property: evaluation of the homomorphic extension
    equals evaluation of the original formula under the pushed-forward assignment.
    That is, `(extendMap f φ).eval σ = f.eval (λ n => (φ n).eval σ)`. -/
theorem extendMap_eval (f : Formula) (mapping : Nat → Formula) (assignment : Nat → Bool) :
    (extendMap f mapping).eval assignment = f.eval (fun n => (mapping n).eval assignment) := by
  induction f with
  | atom n => rfl
  | true => rfl
  | false => rfl
  | not A ih =>
    simp [extendMap, Formula.eval, ih]
  | and A B ihA ihB =>
    simp [extendMap, Formula.eval, ihA, ihB]
  | or A B ihA ihB =>
    simp [extendMap, Formula.eval, ihA, ihB]
  | impl A B ihA ihB =>
    simp [extendMap, Formula.eval, ihA, ihB]
  | equiv A B ihA ihB =>
    simp [extendMap, Formula.eval, ihA, ihB]

/-- If the mapping is the identity (atom constructor), then
    `extendMap` returns the original formula. -/
theorem extendMap_id (f : Formula) : extendMap f Formula.atom = f := by
  induction f with
  | atom n => rfl
  | true => rfl
  | false => rfl
  | not A ih =>
    simp [extendMap, ih]
  | and A B ihA ihB =>
    simp [extendMap, ihA, ihB]
  | or A B ihA ihB =>
    simp [extendMap, ihA, ihB]
  | impl A B ihA ihB =>
    simp [extendMap, ihA, ihB]
  | equiv A B ihA ihB =>
    simp [extendMap, ihA, ihB]

/-- Composition of homomorphisms: extending by `m1` then by `m2`
    is equivalent to extending by the composition `m2 ∘ m1` (applied pointwise). -/
theorem extendMap_comp (f : Formula) (m1 m2 : Nat → Formula) :
    extendMap (extendMap f m1) m2 = extendMap f (fun n => extendMap (m1 n) m2) := by
  induction f with
  | atom n => rfl
  | true => rfl
  | false => rfl
  | not A ih =>
    simp [extendMap, ih]
  | and A B ihA ihB =>
    simp [extendMap, ihA, ihB]
  | or A B ihA ihB =>
    simp [extendMap, ihA, ihB]
  | impl A B ihA ihB =>
    simp [extendMap, ihA, ihB]
  | equiv A B ihA ihB =>
    simp [extendMap, ihA, ihB]

/-! ## Initial Object: Formulas with Zero Atoms -/

/-- A formula with no atoms (i.e. built only from true/false).
    Up to logical equivalence, there are exactly two such formulas:
    true and false. This makes the set a 2-element Boolean algebra,
    which is the initial object in the category of Boolean algebras. -/
def hasNoAtoms (f : Formula) : Prop := f.atoms = []

/-- Lemma: if the concatenation of two lists is empty, then each list is empty. -/
private lemma append_nil_of_append_nil {α : Type} {l1 l2 : List α} (h : l1 ++ l2 = []) : l1 = [] ∧ l2 = [] := by
  constructor
  · cases l1 with
    | nil => rfl
    | cons x xs =>
      have : (x :: xs) ++ l2 ≠ [] := by
        simp
      exact absurd h this
  · cases l2 with
    | nil => rfl
    | cons y ys =>
      have : l1 ++ (y :: ys) ≠ [] := by
        induction l1 with
        | nil => simp
        | cons z zs ih => simp
      exact absurd h this

/-- Any two formulas with no atoms are logically equivalent
    iff they have the same evaluation under any single assignment.
    Since there are no atoms, evaluation is independent of assignment. -/
theorem noAtoms_eval_independent (f : Formula) (h : hasNoAtoms f)
    (σ1 σ2 : Nat → Bool) : f.eval σ1 = f.eval σ2 := by
  induction f with
  | atom n =>
    unfold hasNoAtoms Formula.atoms at h
    simp at h
  | true => rfl
  | false => rfl
  | not A ih =>
    unfold hasNoAtoms Formula.atoms at h
    have hA : hasNoAtoms A := by
      unfold hasNoAtoms; simpa using h
    simp [Formula.eval, ih hA σ1 σ2]
  | and A B ihA ihB =>
    unfold hasNoAtoms Formula.atoms at h
    have hAB := append_nil_of_append_nil h
    rcases hAB with ⟨hA_nil, hB_nil⟩
    have hA : hasNoAtoms A := by unfold hasNoAtoms; exact hA_nil
    have hB : hasNoAtoms B := by unfold hasNoAtoms; exact hB_nil
    simp [Formula.eval, ihA hA σ1 σ2, ihB hB σ1 σ2]
  | or A B ihA ihB =>
    unfold hasNoAtoms Formula.atoms at h
    have hAB := append_nil_of_append_nil h
    rcases hAB with ⟨hA_nil, hB_nil⟩
    have hA : hasNoAtoms A := by unfold hasNoAtoms; exact hA_nil
    have hB : hasNoAtoms B := by unfold hasNoAtoms; exact hB_nil
    simp [Formula.eval, ihA hA σ1 σ2, ihB hB σ1 σ2]
  | impl A B ihA ihB =>
    unfold hasNoAtoms Formula.atoms at h
    have hAB := append_nil_of_append_nil h
    rcases hAB with ⟨hA_nil, hB_nil⟩
    have hA : hasNoAtoms A := by unfold hasNoAtoms; exact hA_nil
    have hB : hasNoAtoms B := by unfold hasNoAtoms; exact hB_nil
    simp [Formula.eval, ihA hA σ1 σ2, ihB hB σ1 σ2]
  | equiv A B ihA ihB =>
    unfold hasNoAtoms Formula.atoms at h
    have hAB := append_nil_of_append_nil h
    rcases hAB with ⟨hA_nil, hB_nil⟩
    have hA : hasNoAtoms A := by unfold hasNoAtoms; exact hA_nil
    have hB : hasNoAtoms B := by unfold hasNoAtoms; exact hB_nil
    simp [Formula.eval, ihA hA σ1 σ2, ihB hB σ1 σ2]

/-- Representative initial objects: formulas built only from true/false. -/
def initialFormula : Formula := .false

def initialFormula_alt : Formula := .true

/-- The initial object has no atoms. -/
theorem initial_hasNoAtoms : hasNoAtoms initialFormula := by
  unfold initialFormula hasNoAtoms; rfl

/-- In the initial Boolean algebra, the only two equivalence classes
    are [true] and [false]. -/
theorem initial_only_two_classes (f : Formula) (h : hasNoAtoms f) :
    (∀ σ, f.eval σ = true) ∨ (∀ σ, f.eval σ = false) := by
  -- Evaluate f under an arbitrary assignment (e.g., all false)
  let σ0 : Nat → Bool := fun _ => false
  have h0 : f.eval σ0 = true ∨ f.eval σ0 = false := by
    cases h0' : f.eval σ0
    · right; exact h0'
    · left; exact h0'
  rcases h0 with (hT | hF)
  · left
    intro σ
    have := noAtoms_eval_independent f h σ0 σ
    rw [hT] at this
    exact this.symm
  · right
    intro σ
    have := noAtoms_eval_independent f h σ0 σ
    rw [hF] at this
    exact this.symm

/-! ## Terminal Object: The Trivial Formula -/

/-- The terminal object in the formula category is `.true`.
    For any formula A, there is exactly one morphism A → true
    (represented by `.impl A .true`), and it is always a tautology. -/
def terminalFormula : Formula := .true

/-- For any formula A, `A → true` is a tautology. -/
theorem terminal_unique (A : Formula) : isTautology (.impl A .true) := by
  intro assignment
  simp [Formula.eval]

/-- `true` is the unique (up to logical equivalence) formula such that
    `A → X` is a tautology for all A when A itself is a tautology. -/
theorem terminal_characterization (A X : Formula)
    (h : isTautology (.impl A X)) (hA : isTautology A) : isTautology X := by
  intro assignment
  have hAe := hA assignment
  have hIe := h assignment
  simp [Formula.eval] at hAe hIe ⊢
  simp [hAe, hIe]

/-! ## #eval Tests -/

-- Test the universal mapping property with concrete examples
def sampleMapping : Nat → Formula
  | 0 => .not (.atom 1)
  | 1 => .and (.atom 0) (.atom 2)
  | _ => .true

def testFormula : Formula := .impl (.and (.atom 0) (.atom 1)) (.or (.atom 0) (.atom 2))

#eval testFormula
#eval extendMap testFormula sampleMapping

-- Test eval under a concrete assignment
def testAssignment (n : Nat) : Bool := n % 2 = 0
#eval testFormula.eval testAssignment
#eval (extendMap testFormula sampleMapping).eval testAssignment

-- Verify the universal property: LHS = RHS
#eval (extendMap testFormula sampleMapping).eval testAssignment ==
      testFormula.eval (fun n => (sampleMapping n).eval testAssignment)

-- Test generators
#eval generators 3
#eval usesAtoms testFormula 3
#eval usesAtoms testFormula 2

-- Test that the identity map is respected
#eval extendMap testFormula Formula.atom == testFormula

-- Terminal formula tests
def testImplTrue : Formula := .impl (.atom 0) .true
#eval testImplTrue.eval (fun _ => false)
#eval testImplTrue.eval (fun _ => true)
#eval terminalFormula

-- Initial formula tests
#eval initialFormula
#eval initialFormula.eval (fun _ => false)
#eval initialFormula.eval (fun _ => true)

end MiniLogicKernel
