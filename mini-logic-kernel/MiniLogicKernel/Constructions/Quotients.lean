/-
# Logic Kernel: Quotient Constructions

Quotienting formulas by logical equivalence,
Lindenbaum-Tarski algebra constructions.

Knowledge coverage: L3 (Quotient constructions), L4 (Boolean algebra completeness)
-/

import MiniLogicKernel.Core.Basic

namespace MiniLogicKernel

/-! ## The Lindenbaum Algebra (Quotient Type) -/

/-- The Lindenbaum-Tarski algebra: formulas modulo logical equivalence.
    This is a Boolean algebra where ⊤ = [true], ⊥ = [false].
    Uses the Setoid instance from Core/Basic. -/
def FormulaQuotient : Type := Quotient Formula.setoid

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
    exact not_logEquiv_not h)

/-- Conjunction lifted to the quotient. -/
def inf : FormulaQuotient → FormulaQuotient → FormulaQuotient :=
  Quotient.lift₂ (fun a b => mk (.and a b)) (by
    intro a₁ a₂ h₁ b₁ b₂ h₂
    apply Quotient.sound
    exact and_logEquiv_and h₁ h₂)

/-- Disjunction lifted to the quotient. -/
def sup : FormulaQuotient → FormulaQuotient → FormulaQuotient :=
  Quotient.lift₂ (fun a b => mk (.or a b)) (by
    intro a₁ a₂ h₁ b₁ b₂ h₂
    apply Quotient.sound
    exact or_logEquiv_or h₁ h₂)

/-- Implication lifted to the quotient. -/
def imp : FormulaQuotient → FormulaQuotient → FormulaQuotient :=
  Quotient.lift₂ (fun a b => mk (.impl a b)) (by
    intro a₁ a₂ h₁ b₁ b₂ h₂
    apply Quotient.sound
    exact impl_logEquiv_impl h₁ h₂)

end FormulaQuotient

/-! ## Equivalence Class Operations -/

theorem quotient_eq_iff (x y : Formula) :
    FormulaQuotient.mk x = FormulaQuotient.mk y ↔ logEquiv x y := by
  constructor
  · intro h; exact Quotient.exact h
  · intro h; apply Quotient.sound; exact h

/-! ## Boolean Algebra Laws in the Lindenbaum Algebra -/

theorem quotient_double_neg (q : FormulaQuotient) :
    FormulaQuotient.compl (FormulaQuotient.compl q) = q := by
  refine Quotient.inductionOn q (fun f => ?_)
  dsimp [FormulaQuotient.compl, FormulaQuotient.mk]
  apply Quotient.sound
  intro assignment; simp [Formula.eval]

theorem quotient_de_morgan_and (q r : FormulaQuotient) :
    FormulaQuotient.compl (FormulaQuotient.inf q r) =
    FormulaQuotient.sup (FormulaQuotient.compl q) (FormulaQuotient.compl r) := by
  refine Quotient.inductionOn₂ q r (fun f g => ?_)
  dsimp [FormulaQuotient.compl, FormulaQuotient.inf, FormulaQuotient.sup, FormulaQuotient.mk]
  apply Quotient.sound
  intro assignment; simp [Formula.eval]

theorem quotient_and_idempotent (q : FormulaQuotient) :
    FormulaQuotient.inf q q = q := by
  refine Quotient.inductionOn q (fun f => ?_)
  dsimp [FormulaQuotient.inf, FormulaQuotient.mk]
  apply Quotient.sound
  intro assignment; simp [Formula.eval]

theorem quotient_or_bot (q : FormulaQuotient) :
    FormulaQuotient.sup q FormulaQuotient.bot = q := by
  refine Quotient.inductionOn q (fun f => ?_)
  dsimp [FormulaQuotient.sup, FormulaQuotient.bot, FormulaQuotient.mk]
  apply Quotient.sound
  intro assignment; simp [Formula.eval]

theorem quotient_and_top (q : FormulaQuotient) :
    FormulaQuotient.inf q FormulaQuotient.top = q := by
  refine Quotient.inductionOn q (fun f => ?_)
  dsimp [FormulaQuotient.inf, FormulaQuotient.top, FormulaQuotient.mk]
  apply Quotient.sound
  intro assignment; simp [Formula.eval]

theorem quotient_or_top (q : FormulaQuotient) :
    FormulaQuotient.sup q FormulaQuotient.top = FormulaQuotient.top := by
  refine Quotient.inductionOn q (fun f => ?_)
  dsimp [FormulaQuotient.sup, FormulaQuotient.top, FormulaQuotient.mk]
  apply Quotient.sound
  intro assignment; simp [Formula.eval]

theorem quotient_and_bot (q : FormulaQuotient) :
    FormulaQuotient.inf q FormulaQuotient.bot = FormulaQuotient.bot := by
  refine Quotient.inductionOn q (fun f => ?_)
  dsimp [FormulaQuotient.inf, FormulaQuotient.bot, FormulaQuotient.mk]
  apply Quotient.sound
  intro assignment; simp [Formula.eval]

theorem quotient_de_morgan_or (q r : FormulaQuotient) :
    FormulaQuotient.compl (FormulaQuotient.sup q r) =
    FormulaQuotient.inf (FormulaQuotient.compl q) (FormulaQuotient.compl r) := by
  refine Quotient.inductionOn₂ q r (fun f g => ?_)
  dsimp [FormulaQuotient.compl, FormulaQuotient.inf, FormulaQuotient.sup, FormulaQuotient.mk]
  apply Quotient.sound
  intro assignment; simp [Formula.eval]

theorem quotient_distrib_and_over_or (q r s : FormulaQuotient) :
    FormulaQuotient.inf q (FormulaQuotient.sup r s) =
    FormulaQuotient.sup (FormulaQuotient.inf q r) (FormulaQuotient.inf q s) := by
  refine Quotient.inductionOn₃ q r s (fun f g h => ?_)
  dsimp [FormulaQuotient.inf, FormulaQuotient.sup, FormulaQuotient.mk]
  apply Quotient.sound
  intro assignment
  cases hf : f.eval assignment
  · simp [Formula.eval, hf]
  · simp [Formula.eval, hf]

theorem quotient_distrib_or_over_and (q r s : FormulaQuotient) :
    FormulaQuotient.sup q (FormulaQuotient.inf r s) =
    FormulaQuotient.inf (FormulaQuotient.sup q r) (FormulaQuotient.sup q s) := by
  refine Quotient.inductionOn₃ q r s (fun f g h => ?_)
  dsimp [FormulaQuotient.inf, FormulaQuotient.sup, FormulaQuotient.mk]
  apply Quotient.sound
  intro assignment
  cases hf : f.eval assignment
  · simp [Formula.eval, hf]
  · simp [Formula.eval, hf]

/-! ## Partial Order from Implication -/

/-- x ≤ y iff x.impl y = top in the Lindenbaum algebra. -/
def FormulaQuotient.le (x y : FormulaQuotient) : Prop :=
  FormulaQuotient.imp x y = FormulaQuotient.top

theorem FormulaQuotient.le_refl (x : FormulaQuotient) : FormulaQuotient.le x x := by
  refine Quotient.inductionOn x (fun f => ?_)
  dsimp [FormulaQuotient.le, FormulaQuotient.imp, FormulaQuotient.top, FormulaQuotient.mk]
  apply Quotient.sound
  intro a; simp [Formula.eval]

theorem FormulaQuotient.le_antisymm (x y : FormulaQuotient)
    (h1 : FormulaQuotient.le x y) (h2 : FormulaQuotient.le y x) : x = y := by
  refine Quotient.inductionOn₂ x y (fun f g h1 h2 => ?_)
  dsimp [FormulaQuotient.le, FormulaQuotient.imp, FormulaQuotient.top, FormulaQuotient.mk] at h1 h2
  have h_eq1 := Quotient.exact h1
  have h_eq2 := Quotient.exact h2
  apply Quotient.sound
  intro a
  have h1a := h_eq1 a
  have h2a := h_eq2 a
  simp [Formula.eval] at h1a h2a
  cases hf : f.eval a
  · simp [Formula.eval, hf]
    have := h2a; simp [Formula.eval, hf] at this
    exact this.symm
  · simp [Formula.eval, hf] at h1a
    exact h1a

theorem FormulaQuotient.le_trans (x y z : FormulaQuotient)
    (h1 : FormulaQuotient.le x y) (h2 : FormulaQuotient.le y z) : FormulaQuotient.le x z := by
  refine Quotient.inductionOn₃ x y z (fun f g h h1 h2 => ?_)
  dsimp [FormulaQuotient.le, FormulaQuotient.imp, FormulaQuotient.top, FormulaQuotient.mk] at h1 h2 ⊢
  have h_eq1 := Quotient.exact h1
  have h_eq2 := Quotient.exact h2
  apply Quotient.sound
  intro a
  have h1a := h_eq1 a; have h2a := h_eq2 a
  simp [Formula.eval] at h1a h2a ⊢
  cases hf : f.eval a
  · simp [Formula.eval, hf]
  · simp [Formula.eval, hf] at h1a ⊢; exact h2a

/-! ## #eval Tests -/

def fA : Formula := .atom 0
def fB : Formula := .atom 1
def fNotNotA : Formula := .not (.not (.atom 0))
def fExcludedMiddle : Formula := .or (.atom 0) (.not (.atom 0))

def testAssignments : List (Nat → Bool) := [
  fun _ => false,
  fun _ => true,
  fun n => n = 0
]

#eval listAll testAssignments (fun σ => fNotNotA.eval σ == fA.eval σ)
#eval listAll testAssignments (fun σ => fExcludedMiddle.eval σ == true)

end MiniLogicKernel
