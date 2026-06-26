/-
# Logic Kernel: Equivalence

Logical equivalence relations, formula equivalence classes,
and equivalence reasoning infrastructure.

Knowledge coverage: L2 (Equivalence relations), L3 (Lindenbaum-Tarski algebra)
-/

import MiniLogicKernel.Core.Basic

namespace MiniLogicKernel

/-! ## Additional Properties of Logical Equivalence

The basic definitions (logEquiv, logEquiv_refl, logEquiv_symm, logEquiv_trans,
logEquiv_iff_equiv_taut, not_logEquiv_not, and_logEquiv_and, or_logEquiv_or,
impl_logEquiv_impl, Formula.setoid, EquivClass) are in Core/Basic.

This file adds preservation properties and higher-level operations.
-/

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

theorem logEquiv_preserves_unsatisfiability {A B : Formula} (hEq : logEquiv A B) :
    isUnsatisfiable A ↔ isUnsatisfiable B := by
  constructor
  · intro h a
    rw [← hEq a]; exact h a
  · intro h a
    rw [hEq a]; exact h a

theorem EquivClass.mem_of_mem_equiv {A B C : Formula} (hAB : logEquiv A B) (hBC : B ∈ EquivClass C) :
    A ∈ EquivClass C :=
  logEquiv_trans (logEquiv_symm hAB) hBC

/-! ## The FormulaQuot Type

The quotient of formulas by logical equivalence (Lindenbaum-Tarski algebra).
Uses the Setoid instance from Core/Basic.
-/

def FormulaQuot : Type := Quotient Formula.setoid

namespace FormulaQuot

def mk (f : Formula) : FormulaQuot := Quotient.mk _ f

def lift (f : Formula → α) (h : ∀ A B, logEquiv A B → f A = f B) : FormulaQuot → α :=
  Quotient.lift f h

/-! ## Boolean Algebra Operations -/

def top : FormulaQuot := mk .true
def bot : FormulaQuot := mk .false

def not (x : FormulaQuot) : FormulaQuot :=
  Quotient.liftOn x (λ A => mk (.not A))
    (by intro A B h; apply Quotient.sound; exact not_logEquiv_not h)

def and (x y : FormulaQuot) : FormulaQuot :=
  Quotient.lift₂ (λ A B => mk (.and A B))
    (by intro A1 A2 B1 B2 hA hB; apply Quotient.sound; exact and_logEquiv_and hA hB)
    x y

def or (x y : FormulaQuot) : FormulaQuot :=
  Quotient.lift₂ (λ A B => mk (.or A B))
    (by intro A1 A2 B1 B2 hA hB; apply Quotient.sound; exact or_logEquiv_or hA hB)
    x y

def impl (x y : FormulaQuot) : FormulaQuot :=
  Quotient.lift₂ (λ A B => mk (.impl A B))
    (by intro A1 A2 B1 B2 hA hB; apply Quotient.sound; exact impl_logEquiv_impl hA hB)
    x y

end FormulaQuot

/-! ## Logical Strength Comparison

Define a relation "A is at most as strong as B" meaning A → B is a tautology.
This gives a preorder that becomes a partial order after quotienting.
-/

def leStrength (A B : Formula) : Prop := isTautology (.impl A B)

theorem leStrength_refl (A : Formula) : leStrength A A := by
  intro a; simp [Formula.eval]

theorem leStrength_trans {A B C : Formula} (hAB : leStrength A B) (hBC : leStrength B C) :
    leStrength A C := by
  intro a; have haB := hAB a; have hbC := hBC a
  simp [Formula.eval] at haB hbC ⊢
  cases h : A.eval a
  · simp [Formula.eval, h]
  · simp [Formula.eval, h] at haB ⊢; exact hbC

theorem leStrength_antisymm_equiv {A B : Formula} (hAB : leStrength A B) (hBA : leStrength B A) :
    logEquiv A B := by
  intro a
  have hABa := hAB a; have hBAa := hBA a
  simp [Formula.eval] at hABa hBAa
  cases hA : A.eval a
  · simp [Formula.eval, hA]; exact hBAa
  · simp [Formula.eval, hA] at hABa; exact hABa

theorem leStrength_impl_iff (A B : Formula) : leStrength A B ↔ logEquiv (.impl A B) .true := by
  constructor
  · intro h a; simp [logEquiv, Formula.eval, h a]
  · intro h a; have ha := h a; simp [logEquiv, Formula.eval] at ha; exact ha

/-! ## Substitution Preserving Equivalence -/

theorem logEquiv_subst {A B : Formula} (hEq : logEquiv A B) (n : Nat) (g : Formula) :
    logEquiv (A.subst n g) (B.subst n g) := by
  intro a
  rw [Formula.eval_subst A n g a, Formula.eval_subst B n g a]
  apply hEq

/-! ## #eval Examples -/

def A0 : Formula := .atom 0
def A1 : Formula := .atom 1
def formA : Formula := .and A0 A1
def formB : Formula := .not (.or (.not A0) (.not A1))

#eval formA.eval (λ _ => true)
#eval formB.eval (λ _ => true)
#eval formA.eval (λ n => n == 0)
#eval formB.eval (λ n => n == 0)

#eval (.equiv formA formB).eval (λ _ => true)
#eval (.equiv formA formB).eval (λ n => n == 0)
#eval (.equiv formA formB).eval (λ n => n == 1)

#eval (.or A0 (.not A0)).eval (λ _ => true)
#eval (.or A0 (.not A0)).eval (λ _ => false)
#eval (.or A0 (.not A0)).eval (λ n => n % 2 == 0)

end MiniLogicKernel
