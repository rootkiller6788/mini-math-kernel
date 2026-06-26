/-
# Logic Kernel: Equivalence

Logical equivalence relations, formula equivalence classes,
and equivalence reasoning infrastructure.
-/

import MiniLogicKernel.Core.Basic

namespace MiniLogicKernel

/-! ## Logical Equivalence

Two formulas are logically equivalent if they evaluate to the same
truth value under every Boolean assignment.
-/

def logEquiv (A B : Formula) : Prop :=
  ∀ (a : Nat → Bool), A.eval a = B.eval a

theorem logEquiv_refl (A : Formula) : logEquiv A A := by
  intro a; rfl

theorem logEquiv_symm {A B : Formula} (h : logEquiv A B) : logEquiv B A := by
  intro a; rw [h a]

theorem logEquiv_trans {A B C : Formula} (hAB : logEquiv A B) (hBC : logEquiv B C) : logEquiv A C := by
  intro a; rw [hAB a, hBC a]

theorem logEquiv_iff_equiv_taut (A B : Formula) : logEquiv A B ↔ isTautology (.equiv A B) := by
  constructor
  · intro h a
    simp [Formula.eval, h a]
  · intro h a
    have h' := h a
    simp [Formula.eval] at h'
    have hA := Formula.eval A a
    have hB := Formula.eval B a
    exact Bool.eq_of_beq_eq_true h'

theorem logEquiv_preserves_tautology {A B : Formula} (hEq : logEquiv A B) :
    isTautology A ↔ isTautology B := by
  constructor
  · intro hA a
    rw [← hEq a, hA a]
  · intro hB a
    rw [hEq a, hB a]

theorem logEquiv_preserves_satisfiability {A B : Formula} (hEq : logEquiv A B) :
    isSatisfiable A ↔ isSatisfiable B := by
  constructor
  · intro ⟨a, h⟩; exact ⟨a, by rw [← hEq a, h]⟩
  · intro ⟨a, h⟩; exact ⟨a, by rw [hEq a, h]⟩

theorem not_logEquiv_not {A B : Formula} (h : logEquiv A B) : logEquiv (.not A) (.not B) := by
  intro a; simp [Formula.eval, h a]

theorem and_logEquiv_and {A B C D : Formula} (hAB : logEquiv A B) (hCD : logEquiv C D) :
    logEquiv (.and A C) (.and B D) := by
  intro a; simp [Formula.eval, hAB a, hCD a]

theorem or_logEquiv_or {A B C D : Formula} (hAB : logEquiv A B) (hCD : logEquiv C D) :
    logEquiv (.or A C) (.or B D) := by
  intro a; simp [Formula.eval, hAB a, hCD a]

theorem impl_logEquiv_impl {A B C D : Formula} (hAB : logEquiv A B) (hCD : logEquiv C D) :
    logEquiv (.impl A C) (.impl B D) := by
  intro a; simp [Formula.eval, hAB a, hCD a]

/-! ## Equivalence Classes

The set of all formulas logically equivalent to a given formula.
-/

def EquivClass (A : Formula) : Set Formula :=
  {B | logEquiv A B}

theorem EquivClass.mem_self (A : Formula) : A ∈ EquivClass A :=
  logEquiv_refl A

theorem EquivClass.ext {A B : Formula} (h : logEquiv A B) : EquivClass A = EquivClass B := by
  ext C; constructor
  · intro hAC; exact logEquiv_trans (logEquiv_symm h) hAC
  · intro hBC; exact logEquiv_trans h hBC

theorem EquivClass.mem_of_mem_equiv {A B C : Formula} (hAB : logEquiv A B) (hBC : B ∈ EquivClass C) :
    A ∈ EquivClass C :=
  logEquiv_trans (logEquiv_symm hAB) hBC

/-! ## Setoid Instance

The logical equivalence relation forms a setoid on formulas, enabling
quotient constructions.
-/

instance Formula.setoid : Setoid Formula where
  r := logEquiv
  iseqv := ⟨logEquiv_refl, logEquiv_symm, logEquiv_trans⟩

/-- The quotient of formulas by logical equivalence (Lindenbaum-Tarski algebra). -/
def FormulaQuot : Type := Quotient Formula.setoid

def FormulaQuot.mk (f : Formula) : FormulaQuot :=
  Quotient.mk Formula.setoid f

def FormulaQuot.lift (f : Formula → α) (h : ∀ A B, logEquiv A B → f A = f B) : FormulaQuot → α :=
  Quotient.lift f h

/-! ## Operations on Equivalence Classes

Logical connectives lift to the quotient, making it a Boolean algebra.
-/

def FormulaQuot.top : FormulaQuot := FormulaQuot.mk .true
def FormulaQuot.bot : FormulaQuot := FormulaQuot.mk .false

def FormulaQuot.not (x : FormulaQuot) : FormulaQuot :=
  Quotient.liftOn x (λ A => FormulaQuot.mk (.not A))
    (by
      intro A B h
      apply Quotient.sound
      exact not_logEquiv_not h)

def FormulaQuot.and (x y : FormulaQuot) : FormulaQuot :=
  Quotient.lift₂ (λ A B => FormulaQuot.mk (.and A B))
    (by
      intro A1 A2 B1 B2 hA hB
      apply Quotient.sound
      exact and_logEquiv_and hA hB)
    x y

def FormulaQuot.or (x y : FormulaQuot) : FormulaQuot :=
  Quotient.lift₂ (λ A B => FormulaQuot.mk (.or A B))
    (by
      intro A1 A2 B1 B2 hA hB
      apply Quotient.sound
      exact or_logEquiv_or hA hB)
    x y

def FormulaQuot.impl (x y : FormulaQuot) : FormulaQuot :=
  Quotient.lift₂ (λ A B => FormulaQuot.mk (.impl A B))
    (by
      intro A1 A2 B1 B2 hA hB
      apply Quotient.sound
      exact impl_logEquiv_impl hA hB)
    x y

/-! ## #eval Examples -/

def A0 : Formula := .atom 0
def A1 : Formula := .atom 1
def formA : Formula := .and A0 A1
def formB : Formula := .not (.or (.not A0) (.not A1))

-- Check that De Morgan duals agree on concrete assignments
#eval formA.eval (λ _ => true)
#eval formB.eval (λ _ => true)
#eval formA.eval (λ n => n == 0)
#eval formB.eval (λ n => n == 0)

-- Check equivalence by evaluating under specific assignments
-- Equivalent formulas have the same truth value under every assignment
#eval (.equiv formA formB).eval (λ _ => true)
#eval (.equiv formA formB).eval (λ n => n == 0)
#eval (.equiv formA formB).eval (λ n => n == 1)

-- Tautology check via universal quantifier over small domains
-- (excluded middle is true under all assignments)
#eval (.or A0 (.not A0)).eval (λ _ => true)
#eval (.or A0 (.not A0)).eval (λ _ => false)
#eval (.or A0 (.not A0)).eval (λ n => n % 2 == 0)

end MiniLogicKernel
