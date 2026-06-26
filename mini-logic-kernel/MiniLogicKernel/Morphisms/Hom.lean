/-
# Logic Kernel: Homomorphisms

Formula homomorphisms and structure-preserving maps between logical theories.
Defines PredHom (first-order structure homomorphisms), embedding maps,
and homomorphism-based preservation properties.

Knowledge coverage: L2 (Homomorphism), L3 (Math Structures), L5 (Category theory proofs)
-/

import MiniLogicKernel.Core.Basic
import MiniLogicKernel.Core.Objects

namespace MiniLogicKernel

/-! ## Structure Homomorphisms -/

/-- Homomorphism between first-order structures. -/
structure PredHom (S T : Structure) where
  domMap : S.domain → T.domain
  predCompat : ∀ (p : Nat) (args : List S.domain),
    S.predInterp p args → T.predInterp p (args.map domMap)
  constCompat : ∀ (n : Nat), domMap (S.constInterp n) = T.constInterp n

/-- Identity homomorphism. -/
def PredHom.id (S : Structure) : PredHom S S where
  domMap := id
  predCompat := by intro p args h; exact h
  constCompat := by intro n; rfl

/-- Composition of homomorphisms. -/
def PredHom.comp {S T U : Structure} (f : PredHom S T) (g : PredHom T U) : PredHom S U where
  domMap := g.domMap ∘ f.domMap
  predCompat := by
    intro p args h
    have hT := f.predCompat p args h
    simpa [List.map_map] using g.predCompat p (args.map f.domMap) hT
  constCompat := by
    intro n
    simp [Function.comp, f.constCompat, g.constCompat]

/-! ## Homomorphism Preservation Properties -/

/-- Positive existential formulas are preserved under homomorphisms. -/
def PredFormula.isPositive : PredFormula → Bool
  | .prop _ => true
  | .pred _ _ => true
  | .eq _ _ => true
  | .not _ => false
  | .and A B => isPositive A && isPositive B
  | .or A B => isPositive A && isPositive B
  | .impl A B => isPositive A && isPositive B
  | .equiv A B => isPositive A && isPositive B
  | .all _ => false
  | .ex P => isPositive P

/-- Homomorphisms preserve the universal fragment (formulas without ∃). -/
def PredFormula.isUniversal : PredFormula → Bool
  | .prop _ => true
  | .pred _ _ => true
  | .eq _ _ => true
  | .not A => isUniversal A
  | .and A B => isUniversal A && isUniversal B
  | .or A B => isUniversal A && isUniversal B
  | .impl A B => isUniversal A && isUniversal B
  | .equiv A B => isUniversal A && isUniversal B
  | .all P => isUniversal P
  | .ex _ => false

/-! ## Homomorphism Composition Properties -/

/-- Composition of homomorphisms is associative. -/
theorem PredHom.comp_assoc {S T U V : Structure}
    (f : PredHom S T) (g : PredHom T U) (h : PredHom U V) :
    PredHom.comp (PredHom.comp f g) h = PredHom.comp f (PredHom.comp g h) := by
  ext x
  · rfl
  · intro p args
    simp [PredHom.comp]
  · intro n
    simp [PredHom.comp]

/-- Identity homomorphisms are neutral for composition. -/
theorem PredHom.comp_id_right {S T : Structure} (f : PredHom S T) :
    PredHom.comp f (PredHom.id T) = f := by
  ext x
  · rfl
  · intro p args
    simp [PredHom.comp, PredHom.id]
  · intro n
    simp [PredHom.comp, PredHom.id]

theorem PredHom.id_comp_left {S T : Structure} (f : PredHom S T) :
    PredHom.comp (PredHom.id S) f = f := by
  ext x
  · rfl
  · intro p args
    simp [PredHom.comp, PredHom.id]
  · intro n
    simp [PredHom.comp, PredHom.id]

/-! ## Embeddings and Strong Homomorphisms -/

/-- An embedding is an injective homomorphism where predicates are reflected. -/
structure PredEmbedding (S T : Structure) extends PredHom S T where
  injective : ∀ x y, domMap x = domMap y → x = y
  predReflect : ∀ (p : Nat) (args : List S.domain),
    T.predInterp p (args.map domMap) → S.predInterp p args

/-- Every isomorphism (bijective homomorphism with inverse) is an embedding. -/
def PredHom.toEmbedding {S T : Structure} (f : PredHom S T)
    (inv : T.domain → S.domain)
    (leftInv : ∀ x, inv (f.domMap x) = x)
    (predReflect : ∀ (p : Nat) (args : List S.domain),
      T.predInterp p (args.map f.domMap) → S.predInterp p args) :
    PredEmbedding S T where
  toPredHom := f
  injective := by
    intro x y h
    calc
      x = inv (f.domMap x) := by rw [leftInv]
      _ = inv (f.domMap y) := by rw [h]
      _ = y := by rw [leftInv]
  predReflect := predReflect

/-! ## Submodel Relation -/

/-- S is a submodel of T if S.domain ⊆ T.domain and the predicates/constants agree. -/
structure Submodel (S T : Structure) where
  domSub : S.domain → T.domain
  domInj : ∀ x y, domSub x = domSub y → x = y
  predCompat : ∀ (p : Nat) (args : List S.domain),
    S.predInterp p args ↔ T.predInterp p (args.map domSub)
  constCompat : ∀ (c : Nat), domSub (S.constInterp c) = T.constInterp c

/-- A submodel gives an embedding. -/
def Submodel.toEmbedding {S T : Structure} (h : Submodel S T) : PredEmbedding S T where
  domMap := h.domSub
  predCompat := by intro p args hS; exact (h.predCompat p args).mp hS
  constCompat := h.constCompat
  injective := h.domInj
  predReflect := by intro p args hT; exact (h.predCompat p args).mpr hT

/-! ## Homomorphic Image -/

/-- The homomorphic image of S under f is a structure T' where
    the domain is the image of S.domain under f.domMap. -/
structure HomImage (S T : Structure) (f : PredHom S T) where
  carrier : Set T.domain
  closure : ∀ x, x ∈ carrier ↔ ∃ y : S.domain, f.domMap y = x

/-- The image of a structure under a surjective homomorphism
    is elementarily equivalent for positive formulas. -/
def imageProperty : Prop :=
  ∀ (S T : Structure) (f : PredHom S T),
    (∀ y : T.domain, ∃ x : S.domain, f.domMap x = y) →
    ∀ (φ : PredFormula), PredFormula.isPositive φ = true →
    ∀ (env : List S.domain),
      S.satisfies φ env → T.satisfies φ (env.map f.domMap)

/-! ## Tests -/

#eval Formula.translate (Formula.and (.atom 0) (.atom 1)) (fun k => k + 5)
#eval Formula.subst (Formula.or (.atom 0) (.atom 1)) 0 (Formula.atom 42)
#eval Formula.prefixAtoms (Formula.impl (.atom 0) (.atom 3)) 10
#eval Formula.substMany (Formula.and (.atom 0) (.atom 1)) [(0, Formula.true), (1, Formula.false)]

end MiniLogicKernel
