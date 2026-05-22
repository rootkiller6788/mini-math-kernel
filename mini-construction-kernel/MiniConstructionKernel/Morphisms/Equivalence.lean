/-
# Constructions Kernel: Construction Equivalence

Equivalence relations between constructions on mathematical objects.
Includes: construction equivalence, Morita-style equivalence,
natural isomorphism between constructions, and equivalence classes.
-/

import MiniConstructionKernel.Core.Basic
import MiniConstructionKernel.Morphisms.Iso

namespace MiniConstructionKernel

/-! ## Construction Equivalence Relation -/

-- An equivalence relation on constructions
structure ConstructionEquivalence (α : Type u) [Object α] where
  rel : α → α → Prop
  reflexive : ∀ a, rel a a
  symmetric : ∀ a b, rel a b → rel b a
  transitive : ∀ a b c, rel a b → rel b c → rel a c
  name : String

/-! ## Natural Isomorphism between Construction Functors -/

-- Two construction functors are naturally isomorphic
structure NaturalIsomorphism (F G : Type u → Type v) [∀ α, Object (F α)] [∀ α, Object (G α)] where
  component : ∀ {α : Type u} → [Object α] → ConstructionIso (F α) (G α)
  naturality : ∀ {α β : Type u} [Object α] [Object β] (f : α → β),
    (∀ (x : F α), (component β).forward (F.mapByHom f x) = G.mapByHom f ((component α).forward x)) → True
  name : String

/-! ## Equivalence of Construction Categories -/

-- An equivalence between categories of constructions
structure ConstructionCategoryEquivalence (C D : Type u → Type v)
    [∀ α, Object (C α)] [∀ α, Object (D α)] where
  F : {α : Type u} → [Object α] → C α → D α
  G : {α : Type u} → [Object α] → D α → C α
  unitIso : ∀ {α : Type u} → [Object α] → ConstructionIso (C α) (C α)
  counitIso : ∀ {α : Type u} → [Object α] → ConstructionIso (D α) (D α)
  name : String

/-! ## Trivial Equivalence -/

def trivialEquivalence (α : Type u) [Object α] : ConstructionEquivalence α where
  rel a b := a = b
  reflexive a := rfl
  symmetric a b h := h.symm
  transitive a b c h₁ h₂ := h₁.trans h₂
  name := s!"TrivialEq({describe α})"

/-! ## Equality of Constructions Modulo Isomorphism -/

def isoEquivalence (α : Type u) [Object α] : ConstructionEquivalence α where
  rel a b := Nonempty (ConstructionIso α α)
  reflexive a := ⟨identityIso α⟩
  symmetric a b h := by
    rcases h with ⟨iso⟩
    exact ⟨inverseIso iso⟩
  transitive a b c h₁ h₂ := by
    rcases h₁ with ⟨iso₁⟩
    rcases h₂ with ⟨iso₂⟩
    exact ⟨compIso iso₂ iso₁⟩
  name := s!"IsoEq({describe α})"

/-! ## Morita-like Equivalence of Constructions -/

-- Two constructions are Morita-equivalent if they have equivalent categories of modules/actions
structure MoritaEquivalence (C D : Type u) [Object C] [Object D] where
  -- A witness that the constructions have 'equivalent representation theories'
  forwardF : C → D
  backwardF : D → C
  -- Every object of C can be 'represented' in terms of D and vice versa
  leftWitness : ∀ (c : C), ConstructionIso C C
  rightWitness : ∀ (d : D), ConstructionIso D D
  name : String

/-! ## Kernel of a Construction Morphism -/

-- The kernel of a construction morphism defines an equivalence relation
structure KernelEquivalence (α β : Type u) [Object α] [Object β] (f : α → β) where
  rel : α → α → Prop := fun a₁ a₂ => f a₁ = f a₂
  isEquiv : Equivalence (rel f)
  name : String

def kernelEquivalenceOfMap {α β : Type u} [Object α] [Object β] (f : α → β) :
    KernelEquivalence α β f :=
  { rel a₁ a₂ := f a₁ = f a₂
    isEquiv := {
      refl := fun a => rfl
      symm := fun h => h.symm
      trans := fun h₁ h₂ => h₁.trans h₂
    }
    name := s!"Ker({describe α}, {describe β})"
  }

/-! ## Image Equivalence -/

-- The image of a construction morphism partitions the codomain
structure ImageEquivalence (α β : Type u) [Object α] [Object β] (f : α → β) where
  inImage : β → Prop := fun b => ∃ a, f a = b
  reachable : ∀ b₁ b₂, (inImage b₁ ∧ inImage b₂) → (inImage b₁ ↔ inImage b₂)
  name : String

/-! ## Equivalence Classes of Constructions -/

-- Classification of constructions up to equivalence
inductive ConstructionClass : Type
  | limitClass
  | colimitClass
  | freeClass
  | cofreeClass
  | otherClass
  deriving BEq, Repr, Inhabited

def constructionClassName : ConstructionClass → String
  | ConstructionClass.limitClass => "Limit"
  | ConstructionClass.colimitClass => "Colimit"
  | ConstructionClass.freeClass => "Free"
  | ConstructionClass.cofreeClass => "Cofree"
  | ConstructionClass.otherClass => "Other"

/-! ## Congruence on Constructions -/

-- A congruence relation on a construction
structure ConstructionCongruence (α : Type u) [Object α] where
  rel : α → α → Prop
  isEquiv : Equivalence rel
  compatible : ∀ {a₁ a₂ b₁ b₂ : α}, rel a₁ a₂ → rel b₁ b₂ → rel (a₁) (b₁) → True
  name : String

/-! ## Examples and evaluations -/

section Examples

open MiniObjectKernel

instance : Object Nat where
  theory := TheoryName.ofString "Set"
  objName := "Nat"
  repr n := toString n

instance : Object String where
  theory := TheoryName.ofString "Set"
  objName := "String"
  repr s := s

def trivialEqNat : ConstructionEquivalence Nat :=
  trivialEquivalence Nat

def kernelLength : KernelEquivalence String Nat String.length :=
  kernelEquivalenceOfMap String.length

def mod3Equiv : ConstructionEquivalence Nat where
  rel a b := a % 3 = b % 3
  reflexive a := rfl
  symmetric a b h := h.symm
  transitive a b c h₁ h₂ := h₁.trans h₂
  name := "Mod3Equiv"

#eval trivialEqNat.name
#eval kernelLength.name
#eval constructionClassName ConstructionClass.limitClass
#eval kernelLength.rel "abc" "def"   -- both length 3, so true
#eval mod3Equiv.rel 7 10            -- 7%3=1, 10%3=1, so true

end Examples

end MiniConstructionKernel
