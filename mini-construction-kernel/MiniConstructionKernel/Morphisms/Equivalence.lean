/-
# Constructions Kernel: Construction Equivalence

Equivalence relations between constructions on mathematical objects.
Includes: construction equivalence, Morita-style equivalence,
natural isomorphism between constructions, and equivalence classes.
-/

import MiniConstructionKernel.Core.Basic
import MiniConstructionKernel.Core.Objects
import MiniConstructionKernel.Core.Laws
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
structure NaturalIsomorphism (F G : Type u → Type v) [∀ α, Object (F α)] [∀ α, Object (G α)]
    [ff : FunctorialConstruction F] [fg : FunctorialConstruction G] where
  component : ∀ {α : Type u} → [Object α] → ConstructionIso (F α) (G α)
  naturality : ∀ {α β : Type u} [Object α] [Object β] (f : α → β) (x : F α),
    (component β).forward (ff.map f x) = fg.map f ((component α).forward x)
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
  compatible : ∀ {a₁ a₂ b₁ b₂ : α}, rel a₁ a₂ → rel b₁ b₂ → rel a₁ b₁ → rel a₂ b₂
  name : String

/-! ## Examples and evaluations -/

section Examples

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

/-! ## Equivalence of Constructions via Natural Isomorphism -/

theorem natural_iso_implies_equivalence {F G : Type u → Type u} [∀ α, Object (F α)] [∀ α, Object (G α)]
    [ff : FunctorialConstruction F] [fg : FunctorialConstruction G]
    (η : NaturalIsomorphism F G) : ∀ {α : Type u} [Object α], Nonempty (ConstructionIso (F α) (G α)) := by
  intro α
  exact ⟨η.component α⟩

/-! ## Induced Equivalence on Quotients -/

structure QuotientEquivalence (α : Type u) [Object α] where
  rel₁ : α → α → Prop
  rel₂ : α → α → Prop
  isEquiv₁ : Equivalence rel₁
  isEquiv₂ : Equivalence rel₂
  equivalence : rel₁ ↔ rel₂
  name : String

/-! ## Two equivalence relations that are equivalent induce iso quotients -/

theorem equivalent_relations_iso_quotients {α : Type u} [Object α] (qe : QuotientEquivalence α) :
    Nonempty (ConstructionIso (Quot qe.rel₁) (Quot qe.rel₂)) := by
  let fwd : Quot qe.rel₁ → Quot qe.rel₂ :=
    Quot.lift (Quot.mk qe.rel₂) fun a b h =>
      Quot.sound (qe.equivalence.mp h)
  let bwd : Quot qe.rel₂ → Quot qe.rel₁ :=
    Quot.lift (Quot.mk qe.rel₁) fun a b h =>
      Quot.sound (qe.equivalence.mpr h)
  have left_inv : ∀ x, bwd (fwd x) = x := by
    intro x; apply Quot.inductionOn x; intro a; rfl
  have right_inv : ∀ x, fwd (bwd x) = x := by
    intro x; apply Quot.inductionOn x; intro a; rfl
  exact ⟨constructionIsoOfBijection fwd bwd left_inv right_inv "QuotEquivIso"⟩

/-! ## Weak Equivalence of Constructions -/

structure WeakEquivalence (α β : Type u) [Object α] [Object β] where
  f : α → β
  essentiallySurjective : ∀ (b : β), ∃ a, f a = b
  fullyFaithful : ∀ (a₁ a₂ : α), (f a₁ = f a₂) ↔ (a₁ = a₂)
  name : String

theorem weak_equivalence_to_iso {α β : Type u} [Object α] [Object β] (we : WeakEquivalence α β) :
    Nonempty (ConstructionIso α β) := by
  let g (b : β) : α := Classical.choose (we.essentiallySurjective b)
  have hg : ∀ b, we.f (g b) = b := fun b => Classical.choose_spec (we.essentiallySurjective b)
  have left_inv : ∀ a, g (we.f a) = a := by
    intro a
    have : we.f (g (we.f a)) = we.f a := hg (we.f a)
    exact ((we.fullyFaithful (g (we.f a)) a).mp this)
  have right_inv : ∀ b, we.f (g b) = b := hg
  exact ⟨constructionIsoOfBijection we.f g left_inv right_inv "WeakEquivIso"⟩

/-! ## Construction Retract -/

structure ConstructionRetract (α β : Type u) [Object α] [Object β] where
  inclusion : α → β
  retraction : β → α
  retract_left : ∀ a, retraction (inclusion a) = a
  name : String

/-! ## Section-Retraction Pair -/

structure SectionRetraction (α β : Type u) [Object α] [Object β] where
  section' : α → β
  retraction : β → α
  section_retraction : ∀ a, retraction (section' a) = a
  name : String

theorem section_is_mono {α β : Type u} [Object α] [Object β] (sr : SectionRetraction α β) :
    ∀ {X : Type u} [Object X] (f g : X → α), (∀ x, sr.section' (f x) = sr.section' (g x)) → (∀ x, f x = g x) := by
  intro X _ f g h x
  have := h x
  have : sr.retraction (sr.section' (f x)) = sr.retraction (sr.section' (g x)) := by rw [this]
  rw [sr.section_retraction, sr.section_retraction] at this
  exact this

theorem retraction_is_epi {α β : Type u} [Object α] [Object β] (sr : SectionRetraction α β) :
    ∀ {X : Type u} [Object X] (f g : β → X), (∀ b, f (sr.retraction b) = g (sr.retraction b)) → (∀ b, f b = g b) := by
  intro X _ f g h b
  have : ∀ a, f (sr.retraction (sr.section' a)) = g (sr.retraction (sr.section' a)) :=
    fun a => h (sr.section' a)
  simp [sr.section_retraction] at this
  exact this b

/-! ## Isomorphism theorems for constructions -/

-- If F is fully faithful and essentially surjective, then the categories are equivalent
structure CategoricalEquivalence (F : Type u → Type v) (G : Type v → Type u)
    [∀ α, Object (F α)] [∀ β, Object (G β)] where
  unitIso : ∀ {α : Type u} [Object α], Nonempty (ConstructionIso α (G (F α)))
  counitIso : ∀ {β : Type v} [Object β], Nonempty (ConstructionIso (F (G β)) β)
  name : String

end MiniConstructionKernel
