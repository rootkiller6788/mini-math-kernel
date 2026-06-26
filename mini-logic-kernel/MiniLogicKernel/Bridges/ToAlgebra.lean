/-
# Logic Kernel: Bridge to Algebra

Connections between logic and algebra:
Boolean algebras, Heyting algebras, and algebraic logic.
-/

import MiniLogicKernel.Core.Basic
import MiniLogicKernel.Morphisms.Equivalence

namespace MiniLogicKernel

open FormulaQuot

/-! ## Lindenbaum-Tarski Algebra

The quotient of propositional formulas by logical equivalence
forms a Boolean algebra. This is the Lindenbaum-Tarski construction.

The carriers are equivalence classes of formulas; operations are
lifted from the logical connectives.
-/

/-- The Lindenbaum-Tarski algebra type. -/
def LTAlg : Type := FormulaQuot

instance : Inhabited LTAlg :=
  ⟨top⟩

/-! ### Commutativity -/

theorem and_comm (x y : FormulaQuot) : and x y = and y x := by
  apply Quotient.induction_on₂ x y
  intro A B
  apply Quotient.sound
  intro a
  simp [Formula.eval, Bool.and_comm]

theorem or_comm (x y : FormulaQuot) : or x y = or y x := by
  apply Quotient.induction_on₂ x y
  intro A B
  apply Quotient.sound
  intro a
  simp [Formula.eval, Bool.or_comm]

/-! ### Associativity -/

theorem and_assoc (x y z : FormulaQuot) : and (and x y) z = and x (and y z) := by
  apply Quotient.induction_on₃ x y z
  intro A B C
  apply Quotient.sound
  intro a
  simp [Formula.eval, Bool.and_assoc]

theorem or_assoc (x y z : FormulaQuot) : or (or x y) z = or x (or y z) := by
  apply Quotient.induction_on₃ x y z
  intro A B C
  apply Quotient.sound
  intro a
  simp [Formula.eval, Bool.or_assoc]

/-! ### Distributivity -/

theorem and_over_or (x y z : FormulaQuot) : and x (or y z) = or (and x y) (and x z) := by
  apply Quotient.induction_on₃ x y z
  intro A B C
  apply Quotient.sound
  intro a
  -- Using the Boolean distributive law: A ∧ (B ∨ C) = (A ∧ B) ∨ (A ∧ C)
  cases hA : A.eval a
  · simp [Formula.eval, hA]
  · simp [Formula.eval, hA]

theorem or_over_and (x y z : FormulaQuot) : or x (and y z) = and (or x y) (or x z) := by
  apply Quotient.induction_on₃ x y z
  intro A B C
  apply Quotient.sound
  intro a
  cases hA : A.eval a
  · simp [Formula.eval, hA]
  · simp [Formula.eval, hA]

/-! ### Identity Laws -/

theorem and_true (x : FormulaQuot) : and x top = x := by
  apply Quotient.induction_on x
  intro A
  apply Quotient.sound
  intro a
  simp [Formula.eval, top, FormulaQuot.top]

theorem true_and (x : FormulaQuot) : and top x = x := by
  rw [and_comm, and_true]

theorem or_false (x : FormulaQuot) : or x bot = x := by
  apply Quotient.induction_on x
  intro A
  apply Quotient.sound
  intro a
  simp [Formula.eval, bot, FormulaQuot.bot]

theorem false_or (x : FormulaQuot) : or bot x = x := by
  rw [or_comm, or_false]

/-! ### Complement Laws -/

theorem and_not (x : FormulaQuot) : and x (not x) = bot := by
  apply Quotient.induction_on x
  intro A
  apply Quotient.sound
  intro a
  simp [Formula.eval, bot, FormulaQuot.bot, not, FormulaQuot.not]

theorem or_not (x : FormulaQuot) : or x (not x) = top := by
  apply Quotient.induction_on x
  intro A
  apply Quotient.sound
  intro a
  simp [Formula.eval, top, FormulaQuot.top, not, FormulaQuot.not]

/-! ### Idempotence -/

theorem and_idem (x : FormulaQuot) : and x x = x := by
  apply Quotient.induction_on x
  intro A
  apply Quotient.sound
  intro a
  simp [Formula.eval]

theorem or_idem (x : FormulaQuot) : or x x = x := by
  apply Quotient.induction_on x
  intro A
  apply Quotient.sound
  intro a
  simp [Formula.eval]

/-! ### Absorption Laws -/

theorem and_absorb_or (x y : FormulaQuot) : and x (or x y) = x := by
  apply Quotient.induction_on₂ x y
  intro A B
  apply Quotient.sound
  intro a
  cases h : A.eval a
  · simp [Formula.eval, h]
  · simp [Formula.eval, h]

theorem or_absorb_and (x y : FormulaQuot) : or x (and x y) = x := by
  apply Quotient.induction_on₂ x y
  intro A B
  apply Quotient.sound
  intro a
  cases h : A.eval a
  · simp [Formula.eval, h]
  · simp [Formula.eval, h]

/-! ### De Morgan's Laws -/

theorem not_and (x y : FormulaQuot) : not (and x y) = or (not x) (not y) := by
  apply Quotient.induction_on₂ x y
  intro A B
  apply Quotient.sound
  intro a
  simp [Formula.eval, not, FormulaQuot.not, and, FormulaQuot.and, or, FormulaQuot.or]

theorem not_or (x y : FormulaQuot) : not (or x y) = and (not x) (not y) := by
  apply Quotient.induction_on₂ x y
  intro A B
  apply Quotient.sound
  intro a
  simp [Formula.eval, not, FormulaQuot.not, and, FormulaQuot.and, or, FormulaQuot.or]

/-! ### Double Negation -/

theorem not_not (x : FormulaQuot) : not (not x) = x := by
  apply Quotient.induction_on x
  intro A
  apply Quotient.sound
  intro a
  simp [Formula.eval, not, FormulaQuot.not]

/-! ## Partial Order from Implication

Define x ≤ y iff x → y is logically true (i.e., the equivalence class
of x → y equals top). This makes LTAlg a Boolean algebra with the
standard order.
-/

/-- Partial order: x ≤ y iff (x → y) is a tautology.
    In the quotient, this means impl x y = top. -/
def le (x y : FormulaQuot) : Prop := impl x y = top

/-- The partial order relation is well-defined on the quotient. -/
theorem le_iff_logEquiv_impl (A B : Formula) : le (FormulaQuot.mk A) (FormulaQuot.mk B) ↔ isTautology (.impl A B) := by
  constructor
  · intro h
    have h_eq := Quotient.exact h
    -- h_eq: logEquiv (.impl A B) .true
    intro a
    have h_a := h_eq a
    simp [Formula.eval] at h_a ⊢
    exact h_a
  · intro h_taut
    apply Quotient.sound
    intro a
    simp [Formula.eval, h_taut a]

-- Reflexivity
theorem le_refl (x : FormulaQuot) : le x x := by
  apply Quotient.induction_on x
  intro A
  rw [le_iff_logEquiv_impl]
  intro a; simp [Formula.eval]

-- Antisymmetry
theorem le_antisymm (x y : FormulaQuot) (h1 : le x y) (h2 : le y x) : x = y := by
  apply Quotient.induction_on₂ x y
  intro A B
  rw [le_iff_logEquiv_impl] at h1 h2
  apply Quotient.sound
  intro a
  have hA_impl_B := h1 a
  have hB_impl_A := h2 a
  simp [Formula.eval] at hA_impl_B hB_impl_A
  -- hA_impl_B: !(A.eval a) || B.eval a = true
  -- hB_impl_A: !(B.eval a) || A.eval a = true
  -- This implies A.eval a = B.eval a
  have hA := A.eval a
  have hB := B.eval a
  -- From the two conditions using Boolean logic:
  -- If A.eval a = true then hA_impl_B gives B.eval a = true
  -- If A.eval a = false then hB_impl_A gives !(B.eval a) = true, so B.eval a = false
  -- Thus A.eval a = B.eval a
  revert hA_impl_B hB_impl_A
  cases hA : A.eval a
  · simp [Formula.eval, hA]
  · simp [Formula.eval, hA]

-- Transitivity
theorem le_trans (x y z : FormulaQuot) (h1 : le x y) (h2 : le y z) : le x z := by
  apply Quotient.induction_on₃ x y z
  intro A B C
  rw [le_iff_logEquiv_impl, le_iff_logEquiv_impl] at h1 h2
  rw [le_iff_logEquiv_impl]
  intro a
  have hAB := h1 a
  have hBC := h2 a
  simp [Formula.eval] at hAB hBC ⊢
  -- hAB: !A.eval a || B.eval a = true
  -- hBC: !B.eval a || C.eval a = true
  -- Need: !A.eval a || C.eval a = true
  cases hA : A.eval a
  · simp [Formula.eval, hA]
  · simp [Formula.eval, hA] at hAB ⊢
    exact hBC

/-! ## Boolean Algebra Structure

The LTAlg with operations top, bot, not, and, or, impl and the
le partial order forms a Boolean algebra. All required laws are
proved above.
-/

/-- The characteristic property of implication: x ∧ y ≤ z iff x ≤ y → z -/
theorem impl_adjunction (x y z : FormulaQuot) : le (and x y) z ↔ le x (impl y z) := by
  apply Quotient.induction_on₃ x y z
  intro A B C
  simp [le_iff_logEquiv_impl]
  constructor
  · intro h a
    have ha := h a
    simp [Formula.eval] at ha ⊢
    -- ha: !(A.eval a && B.eval a) || C.eval a = true
    -- Goal: !(A.eval a) || (!(B.eval a) || C.eval a) = true
    -- These are logically equivalent (exportation law)
    cases hA : A.eval a
    · simp [Formula.eval, hA]
    · simp [Formula.eval, hA] at ha ⊢
      -- ha: !(B.eval a) || C.eval a = true
      -- Goal same
      exact ha
  · intro h a
    have ha := h a
    simp [Formula.eval] at ha ⊢
    cases hA : A.eval a
    · simp [Formula.eval, hA]
    · simp [Formula.eval, hA] at ha ⊢
      exact ha

/-! ## #eval Examples -/

-- Demonstrate Boolean equivalence via direct evaluations
-- The Lindenbaum-Tarski algebra identifies logically equivalent formulas
#eval (.and (.atom 0) (.atom 1)).eval (λ _ => true)
#eval (.or (.not (.atom 0)) (.atom 0)).eval (λ _ => true)
#eval (.impl (.atom 0) (.atom 0)).eval (λ _ => false)
#eval (.and (.atom 0) (.not (.atom 0))).eval (λ _ => true)

-- Check the adjunction: (A ∧ B) → C is equivalent to A → (B → C)
def f_impl_adjunction : Formula :=
  .equiv (.impl (.and (.atom 0) (.atom 1)) (.atom 2))
         (.impl (.atom 0) (.impl (.atom 1) (.atom 2)))
#eval f_impl_adjunction.eval (λ _ => true)
#eval f_impl_adjunction.eval (λ n => n == 0)

-- Verify Boolean identities
#eval (.and (.atom 0) (.true)).eval (λ _ => true)
#eval (.or (.atom 0) (.false)).eval (λ _ => true)

end MiniLogicKernel

end MiniLogicKernel
