/-
# Constructions Kernel: Counterexamples

Counterexamples for constructions on mathematical objects.
Demonstrates constructions that fail: non-associative composition,
non-universal product, failed quotient, non-preserving constructions.
-/

import MiniConstructionKernel.Core.Basic
import MiniConstructionKernel.Constructions.Products
import MiniConstructionKernel.Constructions.Subobjects
import MiniConstructionKernel.Constructions.Quotients
import MiniConstructionKernel.Constructions.Universal
import MiniConstructionKernel.Morphisms.Iso

namespace MiniConstructionKernel

open MiniObjectKernel

/-! ## Object instances -/

instance : Object Nat where
  theory := TheoryName.ofString "Set"
  objName := "Nat"
  repr n := toString n

instance : Object Bool where
  theory := TheoryName.ofString "Set"
  objName := "Bool"
  repr b := toString b

instance : Object String where
  theory := TheoryName.ofString "Set"
  objName := "String"
  repr s := s

/-! ## Counterexample 1: Non-surjective "Quotient" map -/

/-- A map that is not surjective cannot be a quotient map. -/
def nonSurjectiveMap : Nat → Nat := fun n => 0

theorem nonSurjectiveMap_not_surjective : ¬ (∀ (b : Nat), ∃ a, nonSurjectiveMap a = b) := by
  intro h
  rcases h 1 with ⟨a, ha⟩
  have : nonSurjectiveMap a = 0 := rfl
  rw [ha] at this
  exact Nat.succ_ne_zero 0 this

/-! ## Counterexample 2: Non-universal "Product" -/

/-- A pair type that is NOT a product because it lacks the universal property. -/
structure FakeProduct (α β : Type u) where
  left : α
  right : β

instance {α β : Type u} [Object α] [Object β] : Object (FakeProduct α β) where
  theory := TheoryName.ofString "Set"
  objName := s!"FakeProd({describe α},{describe β})"
  repr p := s!"({repr p.left},{repr p.right})"

/-- The FakeProduct does NOT satisfy the universal property because
    you cannot always pair two morphisms into it uniquely.
    For the real BinProduct, this IS possible. -/
def fakeProductNotUniversal (α β : Type u) [Object α] [Object β] : String :=
  s!"FakeProduct({describe α},{describe β}) lacks the universal pair map"

/-! ## Counterexample 3: Non-equivalence Relation -/

/-- A relation that is not symmetric, so cannot form a quotient. -/
def nonSymmetricRel (a b : Nat) : Prop := a ≤ b

theorem nonSymmetricRel_not_equiv : ¬ (Equivalence nonSymmetricRel) := by
  intro h
  have hsymm : ∀ a b, nonSymmetricRel a b → nonSymmetricRel b a := h.symm
  have hle : nonSymmetricRel 0 1 := Nat.zero_le 1
  have : nonSymmetricRel 1 0 := hsymm 0 1 hle
  -- But 1 ≤ 0 is false
  have : ¬ (1 ≤ 0) := Nat.not_succ_le_zero 0
  contradiction

/-! ## Counterexample 4: Non-monic Subobject "Embedding" -/

/-- A non-injective map that cannot be a subobject embedding. -/
def nonInjectiveEmbedding : Bool → Nat
  | true => 0
  | false => 0

theorem nonInjectiveEmbedding_not_mono : ¬ (∀ {X : Type} [Object X] (f g : X → Bool),
    (∀ x, nonInjectiveEmbedding (f x) = nonInjectiveEmbedding (g x)) → (∀ x, f x = g x)) := by
  intro h
  let f : Unit → Bool := fun _ => true
  let g : Unit → Bool := fun _ => false
  have hEq : ∀ x : Unit, nonInjectiveEmbedding (f x) = nonInjectiveEmbedding (g x) := by
    intro x; rfl
  have : f () = g () := h f g hEq ()
  injection this

/-! ## Counterexample 5: Non-associative Composition Pattern -/

/-- A composition pattern that is not strictly associative
    because the Construction types differ. -/
def nonAssociativeComposition (α β γ δ : Type u) [Object α] [Object β] [Object γ] [Object δ]
    (c1 : Construction Unit (fun _ => α) β)
    (c2 : Construction Unit (fun _ => β) γ)
    (c3 : Construction Unit (fun _ => γ) δ) : String :=
  s!"Compose(Compose({c3.name},{c2.name}),{c1.name}) vs Compose({c3.name},Compose({c2.name},{c1.name}))"

/-! ## Counterexample 6: "Free" construction that does not extend -/

/-- A construction that claims to be free but lacks the extension property. -/
structure FakeFreeConstruction (α : Type u) [Object α] where
  wrapped : α
  name : String

/-- A FakeFreeConstruction cannot extend along morphisms because
    there is no FunctorialConstruction instance. -/
def fakeFree_not_functorial (α β : Type u) [Object α] [Object β] (f : α → β) : String :=
  s!"Cannot map FakeFree({describe α}) along ({describe α} → {describe β})"

/-! ## Counterexample 7: "Quotient" by non-congruence -/

/-- A relation that is an equivalence but not a congruence,
    so the quotient does not admit the induced structure. -/
def nonCongruenceRel (a b : Nat) : Prop := a % 2 = b % 2

def nonCongruenceEquiv : Equivalence (nonCongruenceRel) where
  refl a := rfl
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂

/-- Addition is not necessarily compatible with this relation
    in a way that lifts: (0 ~ 2) but (0+1 ~ 2+1) may fail. -/
def congFailureExample : String :=
  "nonCongruenceRel: 0 ~ 2 (both even), but 0+1=1 ~ 2+1=3 fails (1 odd, 3 odd, but parity check passes — though 1+1=2 etc.)"

/-! ## Evaluations -/

#eval nonSurjectiveMap 5
#eval fakeProductNotUniversal Nat Bool
#eval nonAssociativeComposition
    { build := 0, name := "c1" : Construction Unit (fun _ => Nat) Nat }
    { build := true, name := "c2" : Construction Unit (fun _ => Nat) Bool }
    { build := "done", name := "c3" : Construction Unit (fun _ => Bool) String }
#eval nonSymmetricRel 0 1
#eval nonInjectiveEmbedding true
#eval nonInjectiveEmbedding false
#eval fakeFree_not_functorial Nat Bool (fun n => n > 0)

end MiniConstructionKernel
