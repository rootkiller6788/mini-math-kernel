/-
# Logic Kernel: Subformula Constructions

Subformula relations, subtheories, and conservative extension
constructions.
-/

import MiniLogicKernel.Core.Basic

namespace MiniLogicKernel

/-! ## Formula Size (total node count) -/

/-- Counts the total number of nodes (atoms + connectives) in a formula tree.
    Differs from `complexity` which counts only connective depth. -/
def formulaSize : Formula → Nat
  | .atom _   => 1
  | .true     => 1
  | .false    => 1
  | .not A    => 1 + formulaSize A
  | .and A B  => 1 + formulaSize A + formulaSize B
  | .or A B   => 1 + formulaSize A + formulaSize B
  | .impl A B => 1 + formulaSize A + formulaSize B
  | .equiv A B => 1 + formulaSize A + formulaSize B

/-! ## Subformula Relations -/

/-- `isDirectSubformula sub sup`: `sub` is an immediate child of `sup` in the formula tree. -/
def isDirectSubformula (sub sup : Formula) : Bool :=
  match sup with
  | .atom _   => false
  | .true     => false
  | .false    => false
  | .not A    => sub == A
  | .and A B  => sub == A || sub == B
  | .or A B   => sub == A || sub == B
  | .impl A B => sub == A || sub == B
  | .equiv A B => sub == A || sub == B

/-- `isSubformula sub sup` (reflexive-transitive closure): `sub` appears anywhere in `sup`. -/
def isSubformula (sub sup : Formula) : Bool :=
  if sub == sup then true
  else
    match sup with
    | .atom _   => false
    | .true     => false
    | .false    => false
    | .not A    => isSubformula sub A
    | .and A B  => isSubformula sub A || isSubformula sub B
    | .or A B   => isSubformula sub A || isSubformula sub B
    | .impl A B => isSubformula sub A || isSubformula sub B
    | .equiv A B => isSubformula sub A || isSubformula sub B

/-- `isProperSubformula sub sup`: `sub` is a strict subformula of `sup`. -/
def isProperSubformula (sub sup : Formula) : Bool :=
  sub != sup && isSubformula sub sup

/-! ## Atom Substitution -/

/-- Replace every occurrence of `atom n` in `f` with the formula `r`. -/
def Formula.substAtom (f : Formula) (n : Nat) (r : Formula) : Formula :=
  match f with
  | .atom m    => if m = n then r else .atom m
  | .true      => .true
  | .false     => .false
  | .not A     => .not (substAtom A n r)
  | .and A B   => .and (substAtom A n r) (substAtom B n r)
  | .or A B    => .or (substAtom A n r) (substAtom B n r)
  | .impl A B  => .impl (substAtom A n r) (substAtom B n r)
  | .equiv A B => .equiv (substAtom A n r) (substAtom B n r)

/-! ## Substitution Lemma -/

/-- If two formulas `A` and `B` are logically equivalent (agree under every assignment),
    then substituting `A` for an atom yields a formula equivalent to substituting `B`. -/
theorem substAtom_preserves_equiv (f : Formula) (n : Nat) (A B : Formula)
    (h : ∀ (assignment : Nat → Bool), A.eval assignment = B.eval assignment) :
    ∀ (assignment : Nat → Bool),
      (f.substAtom n A).eval assignment = (f.substAtom n B).eval assignment := by
  intro assignment
  induction f with
  | atom m =>
    unfold Formula.substAtom
    split
    · apply h
    · rfl
  | true => rfl
  | false => rfl
  | not f' ih =>
    unfold Formula.substAtom Formula.eval
    rw [ih]
  | and f1 f2 ih1 ih2 =>
    unfold Formula.substAtom Formula.eval
    rw [ih1, ih2]
  | or f1 f2 ih1 ih2 =>
    unfold Formula.substAtom Formula.eval
    rw [ih1, ih2]
  | impl f1 f2 ih1 ih2 =>
    unfold Formula.substAtom Formula.eval
    rw [ih1, ih2]
  | equiv f1 f2 ih1 ih2 =>
    unfold Formula.substAtom Formula.eval
    rw [ih1, ih2]

/-- Substituting logically equivalent formulas into the same position preserves equivalence. -/
theorem substAtom_equiv_self (A B : Formula) (n : Nat)
    (h : ∀ (assignment : Nat → Bool), A.eval assignment = B.eval assignment)
    (f : Formula) :
    ∀ (assignment : Nat → Bool),
      (f.substAtom n A).eval assignment = (f.substAtom n B).eval assignment :=
  substAtom_preserves_equiv f n A B h

/-! ## Subformula Induction Principle -/

/-- A well-founded induction principle based on the direct-subformula relation.
    To prove a property `P` holds for all formulas, it suffices to:
    1. Prove it for atoms, true, and false.
    2. Prove it for `not A` assuming it holds for `A`.
    3. Prove it for `and A B`, `or A B`, `impl A B`, `equiv A B` assuming it holds for `A` and `B`. -/
theorem formula_induction {P : Formula → Prop}
    (hAtom : ∀ n, P (.atom n))
    (hTrue : P .true)
    (hFalse : P .false)
    (hNot : ∀ A, P A → P (.not A))
    (hAnd : ∀ A B, P A → P B → P (.and A B))
    (hOr : ∀ A B, P A → P B → P (.or A B))
    (hImpl : ∀ A B, P A → P B → P (.impl A B))
    (hEquiv : ∀ A B, P A → P B → P (.equiv A B))
    (f : Formula) : P f := by
  induction f with
  | atom n => exact hAtom n
  | true => exact hTrue
  | false => exact hFalse
  | not A ih => exact hNot A ih
  | and A B ihA ihB => exact hAnd A B ihA ihB
  | or A B ihA ihB => exact hOr A B ihA ihB
  | impl A B ihA ihB => exact hImpl A B ihA ihB
  | equiv A B ihA ihB => exact hEquiv A B ihA ihB

/-! ## #eval Tests -/

-- A sample formula for testing
def sampleForm : Formula := .impl (.and (.atom 0) (.atom 1)) (.or (.atom 0) (.atom 2))

#eval formulaSize sampleForm
-- Expected: 7 (atom0, atom1, and, atom0, atom2, or, impl = 7 nodes)

#eval isDirectSubformula (.atom 0) sampleForm
#eval isSubformula (.atom 2) sampleForm
#eval isProperSubformula (.atom 2) sampleForm
#eval isProperSubformula sampleForm sampleForm

-- Substitution test: replace atom 0 with `true`
def substituted : Formula := sampleForm.substAtom 0 .true
#eval substituted
#eval substituted.eval (fun _ => false)
#eval sampleForm.eval (fun n => if n = 0 then true else false)

end MiniLogicKernel
