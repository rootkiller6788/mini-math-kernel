/-
# Logic Kernel: Isomorphisms

Logical isomorphisms: formula equivalence
and structure isomorphisms.
-/

import MiniLogicKernel.Core.Basic
import MiniLogicKernel.Core.Objects

namespace MiniLogicKernel

/-! ## Atom Translation

Translate all atom indices in a formula by a given mapping.
-/

def Formula.translate (f : Formula) (σ : Nat → Nat) : Formula :=
  match f with
  | .atom n => .atom (σ n)
  | .true => .true
  | .false => .false
  | .not A => .not (translate A σ)
  | .and A B => .and (translate A σ) (translate B σ)
  | .or A B => .or (translate A σ) (translate B σ)
  | .impl A B => .impl (translate A σ) (translate B σ)
  | .equiv A B => .equiv (translate A σ) (translate B σ)

theorem Formula.translate_eval (f : Formula) (σ : Nat → Nat) (a : Nat → Bool) :
    (f.translate σ).eval a = f.eval (a ∘ σ) := by
  induction f with
  | atom n => rfl
  | true => rfl
  | false => rfl
  | not A ih => simp [Formula.translate, Formula.eval, ih]
  | and A B ihA ihB => simp [Formula.translate, Formula.eval, ihA, ihB]
  | or A B ihA ihB => simp [Formula.translate, Formula.eval, ihA, ihB]
  | impl A B ihA ihB => simp [Formula.translate, Formula.eval, ihA, ihB]
  | equiv A B ihA ihB => simp [Formula.translate, Formula.eval, ihA, ihB]

/-! ## Formula Isomorphism

A formula isomorphism is a bijective renaming of atom indices.
Two formulas related by an isomorphism have identical logical properties
(tautology, satisfiability, unsatisfiability).
-/

structure FormulaIso where
  atomMap : Nat → Nat
  bijective : Function.Bijective atomMap

/-- The identity formula isomorphism. -/
def FormulaIso.id : FormulaIso where
  atomMap := id
  bijective := ⟨λ a b h => h, λ b => ⟨b, rfl⟩⟩

/-- Compose two formula isomorphisms. -/
def FormulaIso.comp (g f : FormulaIso) : FormulaIso where
  atomMap := g.atomMap ∘ f.atomMap
  bijective := Function.Bijective.comp g.bijective f.bijective

/-- Extract a two-sided inverse from a bijective map. -/
def FormulaIso.inverse (φ : FormulaIso) : Nat → Nat :=
  let ⟨_, hsurj⟩ := φ.bijective
  λ y => Classical.choose (hsurj y)

theorem FormulaIso.leftInv (φ : FormulaIso) (x : Nat) :
    φ.inverse (φ.atomMap x) = x := by
  let ⟨hinj, hsurj⟩ := φ.bijective
  apply hinj
  rw [Classical.choose_spec (hsurj (φ.atomMap x))]

theorem FormulaIso.rightInv (φ : FormulaIso) (y : Nat) :
    φ.atomMap (φ.inverse y) = y :=
  Classical.choose_spec (φ.bijective.right y)

theorem FormulaIso.preserves_tautology (φ : FormulaIso) (f : Formula) :
    isTautology f ↔ isTautology (f.translate φ.atomMap) := by
  constructor
  · intro htaut assignment
    rw [Formula.translate_eval f φ.atomMap assignment]
    apply htaut
  · intro htaut assignment
    have := htaut (assignment ∘ φ.inverse)
    rw [Formula.translate_eval f φ.atomMap (assignment ∘ φ.inverse)] at this
    have h_eq : (assignment ∘ φ.inverse) ∘ φ.atomMap = assignment := by
      funext x
      simp [Function.comp, φ.leftInv x]
    rw [h_eq] at this
    exact this

theorem FormulaIso.preserves_satisfiability (φ : FormulaIso) (f : Formula) :
    isSatisfiable f ↔ isSatisfiable (f.translate φ.atomMap) := by
  constructor
  · intro ⟨a, hsat⟩
    refine ⟨a ∘ φ.inverse, ?_⟩
    rw [Formula.translate_eval f φ.atomMap (a ∘ φ.inverse)]
    have h_eq : (a ∘ φ.inverse) ∘ φ.atomMap = a := by
      funext x; simp [Function.comp, φ.leftInv x]
    rw [h_eq, hsat]
  · intro ⟨a, hsat⟩
    refine ⟨a ∘ φ.atomMap, ?_⟩
    rw [← Formula.translate_eval f φ.atomMap a, hsat]

/-! ## Structure Isomorphism

A structure isomorphism is a bijection between domains that preserves
predicate interpretation and constant interpretation.
-/

structure StructureIso (S T : Structure) where
  domMap : S.domain → T.domain
  invMap : T.domain → S.domain
  leftInv : ∀ x, invMap (domMap x) = x
  rightInv : ∀ y, domMap (invMap y) = y
  predCompat : ∀ (p : Nat) (args : List S.domain),
    S.predInterp p args ↔ T.predInterp p (args.map domMap)
  constCompat : ∀ (c : Nat), domMap (S.constInterp c) = T.constInterp c

/-- Identity structure isomorphism. -/
def StructureIso.refl (S : Structure) : StructureIso S S where
  domMap := id
  invMap := id
  leftInv := λ _ => rfl
  rightInv := λ _ => rfl
  predCompat := λ _ _ => by simp
  constCompat := λ _ => rfl

/-- Symmetry of structure isomorphism. -/
def StructureIso.symm {S T : Structure} (iso : StructureIso S T) : StructureIso T S where
  domMap := iso.invMap
  invMap := iso.domMap
  leftInv := iso.rightInv
  rightInv := iso.leftInv
  predCompat := by
    intro p args
    have h := iso.predCompat p (args.map iso.invMap)
    have h_map : (args.map iso.invMap).map iso.domMap = args := by
      calc
        (args.map iso.invMap).map iso.domMap = args.map (iso.domMap ∘ iso.invMap) := by simp
        _ = args.map (λ x => x) := by
          simp [iso.rightInv, Function.funext_iff]
        _ = args := by simp
    simpa [h_map] using h
  constCompat := by
    intro c
    calc
      iso.invMap (T.constInterp c) = iso.invMap (iso.domMap (S.constInterp c)) := by rw [iso.constCompat c]
      _ = S.constInterp c := by rw [iso.leftInv]

/-- Transitivity of structure isomorphism. -/
def StructureIso.trans {S T U : Structure} (iso1 : StructureIso S T) (iso2 : StructureIso T U) :
    StructureIso S U where
  domMap := iso2.domMap ∘ iso1.domMap
  invMap := iso1.invMap ∘ iso2.invMap
  leftInv := by
    intro x
    simp [iso1.leftInv, iso2.leftInv]
  rightInv := by
    intro y
    simp [iso1.rightInv, iso2.rightInv]
  predCompat := by
    intro p args
    have h1 := iso1.predCompat p args
    have h2 := iso2.predCompat p (args.map iso1.domMap)
    have h_map : (args.map iso1.domMap).map iso2.domMap = args.map (iso2.domMap ∘ iso1.domMap) := by simp
    simpa [h_map] using ⟨λ h => h2.mp (h1.mp h), λ h => h1.mpr (h2.mpr h)⟩
  constCompat := by
    intro c
    simp [iso1.constCompat c, iso2.constCompat c]

/-- An isomorphism preserves satisfiability of predicate formulas. -/
theorem StructureIso.preserves_satisfies {S T : Structure} (iso : StructureIso S T)
    (φ : PredFormula) (env : List S.domain) :
    S.satisfies φ env ↔ T.satisfies φ (env.map iso.domMap) := by
  induction φ generalizing env with
  | prop f => simp [Structure.satisfies]
  | pred p ts =>
    -- Key lemma: evaluating ts in T with mapped env equals mapping the
    -- evaluation of ts in S with original env, because T.constInterp = domMap ∘ S.constInterp
    have h_map : (ts.map fun n =>
        match (env.map iso.domMap).get? n with | some x => x | none => T.constInterp n) =
      (ts.map fun n =>
        match env.get? n with | some x => x | none => S.constInterp n).map iso.domMap := by
      simp [iso.constCompat]
    have h_pred := iso.predCompat p (ts.map fun n =>
      match env.get? n with | some x => x | none => S.constInterp n)
    simpa [Structure.satisfies, h_map] using h_pred
  | eq t1 t2 => simp [Structure.satisfies, iso.constCompat]
  | not A ih => simp [Structure.satisfies, ih]
  | and A B ihA ihB => simp [Structure.satisfies, ihA, ihB]
  | or A B ihA ihB => simp [Structure.satisfies, ihA, ihB]
  | impl A B ihA ihB => simp [Structure.satisfies, ihA, ihB]
  | equiv A B ihA ihB => simp [Structure.satisfies, ihA, ihB]
  | all P ih =>
    simp [Structure.satisfies]
    constructor
    · intro h y
      let x := iso.invMap y
      have hx := h x
      have h_ih := ih (x :: env)
      have h_forward := h_ih.mp hx
      simpa [iso.rightInv y] using h_forward
    · intro h x
      have h_ih := ih (x :: env)
      apply h_ih.mpr
      simpa using h (iso.domMap x)
  | ex P ih =>
    simp [Structure.satisfies]
    constructor
    · intro ⟨x, hx⟩
      refine ⟨iso.domMap x, ?_⟩
      exact (ih (x :: env)).mp hx
    · intro ⟨y, hy⟩
      refine ⟨iso.invMap y, ?_⟩
      exact (ih (iso.invMap y :: env)).mpr hy

/-! ## #eval Examples -/

-- Swap atoms 0 and 1 and evaluate
def swap01 : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n => n

#eval (.atom 0).translate swap01
#eval (.and (.atom 0) (.not (.atom 1))).translate swap01
#eval (.impl (.atom 0) (.atom 1)).translate swap01

-- Check that translate_eval holds for a specific assignment
def sampleAssign : Nat → Bool := λ n => n % 2 == 0
#eval ((.and (.atom 0) (.atom 1)).translate swap01).eval sampleAssign
#eval (.and (.atom 0) (.atom 1)).eval (sampleAssign ∘ swap01)
#eval ((.and (.atom 0) (.atom 1)).translate swap01).eval sampleAssign ==
      (.and (.atom 0) (.atom 1)).eval (sampleAssign ∘ swap01)

end MiniLogicKernel
