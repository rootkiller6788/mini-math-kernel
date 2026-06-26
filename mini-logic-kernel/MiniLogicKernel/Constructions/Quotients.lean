/-
# Logic Kernel: Quotient Constructions

Quotienting formulas by logical equivalence,
Lindenbaum-Tarski algebra constructions.
-/

import MiniLogicKernel.Core.Basic

namespace MiniLogicKernel

/-! ## Helper: List Operations -/

/-- Check if all elements of a list satisfy a predicate. -/
def listAll {α : Type} (l : List α) (p : α → Bool) : Bool :=
  match l with
  | [] => true
  | x :: xs => p x && listAll xs p

/-! ## Logical Equivalence -/

/-- Two formulas are logically equivalent if they agree under every assignment. -/
def logicallyEquivalent (A B : Formula) : Prop :=
  ∀ (assignment : Nat → Bool), A.eval assignment = B.eval assignment

theorem logicallyEquivalent.refl (A : Formula) : logicallyEquivalent A A := by
  intro _; rfl

theorem logicallyEquivalent.symm {A B : Formula} (h : logicallyEquivalent A B) :
    logicallyEquivalent B A := by
  intro assignment; rw [h assignment]

theorem logicallyEquivalent.trans {A B C : Formula}
    (hAB : logicallyEquivalent A B) (hBC : logicallyEquivalent B C) :
    logicallyEquivalent A C := by
  intro assignment; rw [hAB assignment, hBC assignment]

/-- Logical equivalence is an equivalence relation, giving a `Setoid` instance. -/
instance : Setoid Formula where
  r := logicallyEquivalent
  iseqv := {
    refl := logicallyEquivalent.refl
    symm := logicallyEquivalent.symm
    trans := logicallyEquivalent.trans
  }

/-! ## The Lindenbaum Algebra (Quotient Type) -/

/-- The Lindenbaum-Tarski algebra: formulas modulo logical equivalence.
    This is a Boolean algebra where `⊤` = [true], `⊥` = [false]. -/
def FormulaQuotient : Type := Quotient (inferInstance : Setoid Formula)

namespace FormulaQuotient

/-- Embed a formula into its equivalence class. -/
def mk (f : Formula) : FormulaQuotient := Quotient.mk _ f

/-- Extract a representative from an equivalence class. -/
def out (q : FormulaQuotient) : Formula := Quotient.out q

/-- The equivalence class of `true`. -/
def top : FormulaQuotient := mk .true

/-- The equivalence class of `false`. -/
def bot : FormulaQuotient := mk .false

/-- Complement (negation) lifted to the quotient. -/
def compl : FormulaQuotient → FormulaQuotient :=
  Quotient.lift (fun f => mk (.not f)) (by
    intro a b h
    apply Quotient.sound
    intro assignment
    have h_eq := h assignment
    simp [Formula.eval, h_eq])

/-- Conjunction lifted to the quotient. -/
def inf : FormulaQuotient → FormulaQuotient → FormulaQuotient :=
  Quotient.lift₂ (fun a b => mk (.and a b)) (by
    intro a₁ a₂ h₁ b₁ b₂ h₂
    apply Quotient.sound
    intro assignment
    have h₁_eq := h₁ assignment
    have h₂_eq := h₂ assignment
    simp [Formula.eval, h₁_eq, h₂_eq])

/-- Disjunction lifted to the quotient. -/
def sup : FormulaQuotient → FormulaQuotient → FormulaQuotient :=
  Quotient.lift₂ (fun a b => mk (.or a b)) (by
    intro a₁ a₂ h₁ b₁ b₂ h₂
    apply Quotient.sound
    intro assignment
    have h₁_eq := h₁ assignment
    have h₂_eq := h₂ assignment
    simp [Formula.eval, h₁_eq, h₂_eq])

/-- Implication lifted to the quotient. -/
def imp : FormulaQuotient → FormulaQuotient → FormulaQuotient :=
  Quotient.lift₂ (fun a b => mk (.impl a b)) (by
    intro a₁ a₂ h₁ b₁ b₂ h₂
    apply Quotient.sound
    intro assignment
    have h₁_eq := h₁ assignment
    have h₂_eq := h₂ assignment
    simp [Formula.eval, h₁_eq, h₂_eq])

end FormulaQuotient

/-! ## Equivalence Class Operations -/

/-- Two equivalence classes are equal if their representatives are logically equivalent. -/
theorem quotient_eq_iff (x y : Formula) :
    FormulaQuotient.mk x = FormulaQuotient.mk y ↔ logicallyEquivalent x y := by
  constructor
  · intro h
    have := Quotient.exact h
    exact this
  · intro h
    apply Quotient.sound
    exact h

/-! ## Boolean Algebra Laws in the Lindenbaum Algebra -/

/-- Double-negation elimination in the Lindenbaum algebra: ¬¬x = x. -/
theorem quotient_double_neg (q : FormulaQuotient) :
    FormulaQuotient.compl (FormulaQuotient.compl q) = q := by
  refine Quotient.inductionOn q (fun f => ?_)
  dsimp [FormulaQuotient.compl, FormulaQuotient.mk]
  apply Quotient.sound
  intro assignment
  simp [Formula.eval]

/-- De Morgan law in the Lindenbaum algebra: ¬(x ∧ y) = ¬x ∨ ¬y. -/
theorem quotient_de_morgan_and (q r : FormulaQuotient) :
    FormulaQuotient.compl (FormulaQuotient.inf q r) =
    FormulaQuotient.sup (FormulaQuotient.compl q) (FormulaQuotient.compl r) := by
  refine Quotient.inductionOn₂ q r (fun f g => ?_)
  dsimp [FormulaQuotient.compl, FormulaQuotient.inf, FormulaQuotient.sup, FormulaQuotient.mk]
  apply Quotient.sound
  intro assignment
  simp [Formula.eval]

/-- Idempotence of conjunction in the Lindenbaum algebra: x ∧ x = x. -/
theorem quotient_and_idempotent (q : FormulaQuotient) :
    FormulaQuotient.inf q q = q := by
  refine Quotient.inductionOn q (fun f => ?_)
  dsimp [FormulaQuotient.inf, FormulaQuotient.mk]
  apply Quotient.sound
  intro assignment
  simp [Formula.eval]

/-- Identity: x ∨ false = x in the Lindenbaum algebra. -/
theorem quotient_or_bot (q : FormulaQuotient) :
    FormulaQuotient.sup q FormulaQuotient.bot = q := by
  refine Quotient.inductionOn q (fun f => ?_)
  dsimp [FormulaQuotient.sup, FormulaQuotient.bot, FormulaQuotient.mk]
  apply Quotient.sound
  intro assignment
  simp [Formula.eval]

/-! ## #eval Tests -/

-- Some representative formulas
def fA : Formula := .atom 0
def fB : Formula := .atom 1
def fNotNotA : Formula := .not (.not (.atom 0))
def fExcludedMiddle : Formula := .or (.atom 0) (.not (.atom 0))

-- Test: ¬¬A has the same eval as A under all test assignments
def testAssignments : List (Nat → Bool) := [
  fun _ => false,
  fun _ => true,
  fun n => n = 0
]

#eval testAssignments.map (fun σ => fNotNotA.eval σ)
#eval testAssignments.map (fun σ => fA.eval σ)

-- Verify double-negation equivalence for all test assignments
#eval listAll testAssignments (fun σ => fNotNotA.eval σ == fA.eval σ)

-- Verify excluded middle is always true
#eval listAll testAssignments (fun σ => fExcludedMiddle.eval σ == true)

end MiniLogicKernel
