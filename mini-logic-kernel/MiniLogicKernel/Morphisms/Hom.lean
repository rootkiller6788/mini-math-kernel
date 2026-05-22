/-
# Logic Kernel: Homomorphisms

Formula homomorphisms and structure-preserving maps
between logical theories.
-/

import MiniLogicKernel.Core.Basic
import MiniLogicKernel.Core.Objects

namespace MiniLogicKernel

/-! ## Formula Translation -/

/-- Translate atom indices via a mapping function -/
def Formula.translate (f : Formula) (atomMap : Nat → Nat) : Formula :=
  match f with
  | .atom n => .atom (atomMap n)
  | .true => .true
  | .false => .false
  | .not A => .not (translate A atomMap)
  | .and A B => .and (translate A atomMap) (translate B atomMap)
  | .or A B => .or (translate A atomMap) (translate B atomMap)
  | .impl A B => .impl (translate A atomMap) (translate B atomMap)
  | .equiv A B => .equiv (translate A atomMap) (translate B atomMap)

/-- Rename atoms by adding an offset -/
def Formula.prefixAtoms (f : Formula) (n : Nat) : Formula :=
  f.translate fun k => k + n

/-- Substitute a formula for a specific atom index -/
def Formula.subst (f : Formula) (n : Nat) (g : Formula) : Formula :=
  match f with
  | .atom m => if m == n then g else .atom m
  | .true => .true
  | .false => .false
  | .not A => .not (subst A n g)
  | .and A B => .and (subst A n g) (subst B n g)
  | .or A B => .or (subst A n g) (subst B n g)
  | .impl A B => .impl (subst A n g) (subst B n g)
  | .equiv A B => .equiv (subst A n g) (subst B n g)

/-- Simultaneous substitution of multiple atoms -/
def Formula.substMany (f : Formula) (substs : List (Nat × Formula)) : Formula :=
  match f with
  | .atom m => match substs.lookup m with
    | some g => g
    | none => .atom m
  | .true => .true
  | .false => .false
  | .not A => .not (substMany A substs)
  | .and A B => .and (substMany A substs) (substMany B substs)
  | .or A B => .or (substMany A substs) (substMany B substs)
  | .impl A B => .impl (substMany A substs) (substMany B substs)
  | .equiv A B => .equiv (substMany A substs) (substMany B substs)

/-! ## Evaluation under Translation -/

/-- Evaluation after translation corresponds to evaluation with transformed assignment -/
theorem Formula.eval_translate (f : Formula) (atomMap : Nat → Nat) (assignment : Nat → Bool) :
    (f.translate atomMap).eval assignment = f.eval (assignment ∘ atomMap) := by
  induction f with
  | atom n => rfl
  | true => rfl
  | false => rfl
  | not A ih => simp [translate, eval, ih]
  | and A B ihA ihB => simp [translate, eval, ihA, ihB]
  | or A B ihA ihB => simp [translate, eval, ihA, ihB]
  | impl A B ihA ihB => simp [translate, eval, ihA, ihB]
  | equiv A B ihA ihB => simp [translate, eval, ihA, ihB]

/-! ## Structure Homomorphisms -/

/-- Homomorphism between first-order structures -/
structure PredHom (S T : Structure) where
  domMap : S.domain → T.domain
  predCompat : ∀ (p : Nat) (args : List S.domain),
    S.predInterp p args → T.predInterp p (args.map domMap)
  constCompat : ∀ (n : Nat), domMap (S.constInterp n) = T.constInterp n

/-- Identity homomorphism -/
def PredHom.id (S : Structure) : PredHom S S where
  domMap := id
  predCompat := by intro p args h; exact h
  constCompat := by intro n; rfl

/-- Composition of homomorphisms -/
def PredHom.comp (f : PredHom S T) (g : PredHom T U) : PredHom S U where
  domMap := g.domMap ∘ f.domMap
  predCompat := by
    intro p args h
    have hT := f.predCompat p args h
    simpa [List.map_map] using g.predCompat p (args.map f.domMap) hT
  constCompat := by
    intro n
    simp [Function.comp, f.constCompat, g.constCompat]

/-! ## Tests -/

#eval Formula.translate (Formula.and (.atom 0) (.atom 1)) (fun k => k + 5)
#eval Formula.subst (Formula.or (.atom 0) (.atom 1)) 0 (Formula.atom 42)
#eval Formula.prefixAtoms (Formula.impl (.atom 0) (.atom 3)) 10
#eval Formula.substMany (Formula.and (.atom 0) (.atom 1)) [(0, Formula.true), (1, Formula.false)]

end MiniLogicKernel
