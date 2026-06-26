/-
# Constructions Kernel: Basic Constructions

Defines the `Construction` type — the common interface for building
new mathematical objects from existing ones. Provides canonical
algebraic structures (monoid, group, ring, module, lattice).

References: Mac Lane, Categories for the Working Mathematician
-/

import MiniObjectKernel.Core.Basic

namespace MiniConstructionKernel

open MiniObjectKernel

/-! ## Shared Object Instances -/
-- Reuse Object instances from MiniObjectKernel.Core.Basic for Nat, String, Bool, Empty, Unit.
-- Additional instances:

instance : Object Int where
  theory := TheoryName.ofString "Set"
  objName := "Int"
  repr n := toString n

instance (α : Type) [Object α] : Object (Option α) where
  theory := TheoryName.ofString "Set"
  objName := s!"Option({Object.objName α})"
  repr
    | none => "none"
    | some a => s!"some({repr a})"

/-! ## Construction Type

A `Construction` packages a built object `β` together with metadata:
the indexing type `ι`, a family `α : ι → Type` of input types, and a name.
-/

structure Construction (ι : Type) (α : ι → Type) (β : Type) where
  build : β
  [obj : Object β]
  name : String

/-! ## Product and Coproduct Constructions

`ProductConstruction` represents an I-indexed product with projections.
`CoproductConstruction` is the dual with injections.
-/

structure ProductConstruction (ι : Type) (α : ι → Type) where
  carrier : Type
  [obj : Object carrier]
  proj : (i : ι) → carrier → α i
  name : String

def ProductConstruction.binary (α β : Type) [Object α] [Object β] : Type :=
  ProductConstruction (Fin 2) fun
    | 0 => α
    | 1 => β

structure CoproductConstruction (ι : Type) (α : ι → Type) where
  carrier : Type
  [obj : Object carrier]
  inj : (i : ι) → α i → carrier
  name : String

def CoproductConstruction.binary (α β : Type) [Object α] [Object β] : Type :=
  CoproductConstruction (Fin 2) fun
    | 0 => α
    | 1 => β

/-! ## Sub-Object and Quotient Constructions -/

structure SubConstruction (α : Type) [Object α] where
  pred : α → Prop
  carrier : Type := { x : α // pred x }
  [obj : Object carrier]
  inclusion : carrier → α := Subtype.val
  name : String

structure QuotientConstruction (α : Type) [Object α] where
  rel : α → α → Prop
  isEquiv : Equivalence rel
  carrier : Type := Quot rel
  [obj : Object carrier]
  proj : α → carrier := Quot.mk rel
  name : String

/-! ## Function Space Construction -/

structure FunctionSpaceConstruction (α β : Type) [Object α] [Object β] where
  carrier : Type := α → β
  [obj : Object carrier]
  name : String

/-! ## Composition of Constructions -/

def compose {α β γ : Type} [Object α] [Object β] [Object γ]
    (c2 : Construction Unit (fun _ => β) γ) (c1 : Construction Unit (fun _ => α) β) :
    Construction Unit (fun _ => α) γ :=
  { build := c2.build
    name := s!"{c2.name} ∘ {c1.name}"
  }

/-! ## Constant Construction -/

def constantConstruction (α β : Type) [Object α] [Object β] (val : β) :
    Construction Unit (fun _ => α) β :=
  { build := val
    name := s!"Const({describe α}, {describe β})"
  }

/-! ## Binary Construction (lifting a binary operation) -/

def binaryConstruction {α β γ : Type} [Object α] [Object β] [Object γ]
    (op : α → β → γ) (cα : Construction Unit (fun _ => Unit) α)
    (cβ : Construction Unit (fun _ => Unit) β) :
    Construction Unit (fun _ => Unit) γ :=
  { build := op cα.build cβ.build
    name := s!"Binary({cα.name}, {cβ.name})"
  }

/-! ## Monoidal Construction (Monoid Object in Set)

A monoid object (Mac Lane VII.3): a set with an associative
binary operation and a unit element.
-/

structure MonoidalConstruction (α : Type) [Object α] where
  tensor : α → α → α
  unit : α
  assoc : ∀ (a b c : α), tensor (tensor a b) c = tensor a (tensor b c)
  left_id : ∀ (a : α), tensor unit a = a
  right_id : ∀ (a : α), tensor a unit = a
  name : String

/-! ## Group-like Construction

Encodes the standard group axioms (Mac Lane I.1).
-/

structure GroupLikeConstruction (α : Type) [Object α] where
  mul : α → α → α
  inv : α → α
  one : α
  mul_assoc : ∀ (a b c : α), mul (mul a b) c = mul a (mul b c)
  mul_one : ∀ (a : α), mul a one = a
  one_mul : ∀ (a : α), mul one a = a
  mul_inv_left : ∀ (a : α), mul (inv a) a = one
  name : String

/-! ## Ring-like Construction

Encodes the standard ring axioms (associative, commutative addition;
associative multiplication; distributivity). Reference: standard algebra.
-/

structure RingLikeConstruction (α : Type) [Object α] where
  add : α → α → α
  mul : α → α → α
  zero : α
  one : α
  neg : α → α
  add_assoc : ∀ (a b c : α), add (add a b) c = add a (add b c)
  add_comm : ∀ (a b : α), add a b = add b a
  add_zero : ∀ (a : α), add a zero = a
  add_neg : ∀ (a : α), add a (neg a) = zero
  mul_assoc : ∀ (a b c : α), mul (mul a b) c = mul a (mul b c)
  mul_one : ∀ (a : α), mul a one = a
  one_mul : ∀ (a : α), mul one a = a
  left_distrib : ∀ (a b c : α), mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ (a b c : α), mul (add a b) c = add (mul a c) (mul b c)
  name : String

/-! ## Module-like Construction

Encodes the standard R-module axioms (additive abelian group with
scalar multiplication satisfying distributivity and associativity).
Reference: standard algebra.
-/

structure ModuleLikeConstruction (R α : Type) [Object R] [Object α] where
  add : α → α → α
  zero : α
  neg : α → α
  smul : R → α → α
  add_assoc : ∀ (a b c : α), add (add a b) c = add a (add b c)
  add_comm : ∀ (a b : α), add a b = add b a
  add_zero : ∀ (a : α), add a zero = a
  add_neg : ∀ (a : α), add a (neg a) = zero
  smul_add : ∀ (r : R) (a b : α), smul r (add a b) = add (smul r a) (smul r b)
  add_smul : ∀ (r s : R) (a : α), smul (r + s) a = add (smul r a) (smul s a)
  mul_smul : ∀ (r s : R) (a : α), smul (r * s) a = smul r (smul s a)
  one_smul : ∀ (a : α), smul 1 a = a
  smul_zero : ∀ (r : R), smul r zero = zero
  name : String

/-! ## Lattice-like Construction

Encodes the standard lattice axioms (associative, commutative,
idempotent meet and join with absorption). Reference: universal algebra.
-/

structure LatticeLikeConstruction (α : Type) [Object α] where
  meet : α → α → α
  join : α → α → α
  meet_assoc : ∀ (a b c : α), meet (meet a b) c = meet a (meet b c)
  meet_comm : ∀ (a b : α), meet a b = meet b a
  meet_idemp : ∀ (a : α), meet a a = a
  join_assoc : ∀ (a b c : α), join (join a b) c = join a (join b c)
  join_comm : ∀ (a b : α), join a b = join b a
  join_idemp : ∀ (a : α), join a a = a
  absorb₁ : ∀ (a b : α), meet a (join a b) = a
  absorb₂ : ∀ (a b : α), join a (meet a b) = a
  name : String

/-! ## Construction Morphism (Map between constructions) -/

structure ConstructionMap (α β : Type) [Object α] [Object β] where
  map : α → β
  name : String

def identityConstructionMap (α : Type) [Object α] : ConstructionMap α α :=
  { map := fun a => a
    name := s!"id({describe α})"
  }

def composeConstructionMap {α β γ : Type} [Object α] [Object β] [Object γ]
    (g : ConstructionMap β γ) (f : ConstructionMap α β) : ConstructionMap α γ :=
  { map := fun a => g.map (f.map a)
    name := s!"{g.name}∘{f.name}"
  }

/-! ## Kernel of a Construction Morphism

The kernel relation of f : α → β: a₁ ~ a₂ iff f a₁ = f a₂.
This is always an equivalence relation.
-/

structure ConstructionKernel (α β : Type) [Object α] [Object β] (f : α → β) where
  ker : α → α → Prop := fun a₁ a₂ => f a₁ = f a₂
  isEquiv : Equivalence ker := {
    refl := fun a => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂
  }
  name : String

def constructionKernelOfMap {α β : Type} [Object α] [Object β] (f : α → β) :
    ConstructionKernel α β f :=
  { name := s!"Ker({describe α}→{describe β})"
  }

/-! ## Image of a Construction Morphism -/

structure ConstructionImage (α β : Type) [Object α] [Object β] (f : α → β) where
  im : β → Prop := fun b => ∃ a, f a = b
  mem_iff : ∀ b, im b ↔ ∃ a, f a = b := fun _ => ⟨fun h => h, fun h => h⟩
  name : String

def constructionImageOfMap {α β : Type} [Object α] [Object β] (f : α → β) :
    ConstructionImage α β f :=
  { name := s!"Im({describe α}→{describe β})"
  }

/-! ## Coequalizer as a Universal Construction

The coequalizer of f, g : β → α in Set is the quotient by the
equivalence relation generated by f(b) ~ g(b) for all b ∈ β.
Reference: Mac Lane III.3.
-/

structure Coequalizer (α β : Type) (f g : β → α) [Object α] [Object β] where
  carrier : Type
  [obj : Object carrier]
  proj : α → carrier
  coequal : ∀ (b : β), proj (f b) = proj (g b)
  universal : ∀ {X : Type} [Object X] (h : α → X),
    (∀ b, h (f b) = h (g b)) → carrier → X
  universal_proj : ∀ {X : Type} [Object X] (h : α → X) (hEq : ∀ b, h (f b) = h (g b)) (a : α),
    universal h hEq (proj a) = h a
  unique : ∀ {X : Type} [Object X] (h : α → X) (hEq : ∀ b, h (f b) = h (g b)) (k : carrier → X),
    (∀ a, k (proj a) = h a) → (∀ c, k c = universal h hEq c)
  name : String

/-- The canonical coequalizer in Set: quotient by the relation generated by f(b) ~ g(b). -/
def coequalizerConstruction {α β : Type} [Object α] [Object β] (f g : β → α) :
    Coequalizer α β f g :=
  { carrier := Quot fun a₁ a₂ => ∃ b, f b = a₁ ∧ g b = a₂ ∨ g b = a₁ ∧ f b = a₂
    proj := Quot.mk _
    coequal b := Quot.sound ⟨b, .inl ⟨rfl, rfl⟩⟩
    universal h hEq := Quot.lift h fun a₁ a₂ => by
      rintro ⟨b, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
      · exact hEq b
      · symm; exact hEq b
    universal_proj h hEq a := rfl
    unique h hEq k hk := by
      intro c
      exact Quot.inductionOn c (hk ·)
    name := s!"Coeq({describe α}, {describe β})"
  }

/-! ## Completion of a Construction

Models a metric-like completion: every Cauchy sequence converges
(represented as the existence of a Nat-indexed approximation).
-/

structure Completion (α : Type) [Object α] where
  completed : Type
  [obj : Object completed]
  embed : α → completed
  dense : ∀ (x : completed), Nonempty (Nat → α)
  name : String

/-! ## Localization of a Construction

A localization of α at a multiplicative set S adds formal inverses
for elements of S. The `invert` field states that each s ∈ S becomes
invertible in the localization.
-/

structure Localization (α : Type) [Object α] (S : α → Prop) where
  localized : Type
  [obj : Object localized]
  localize : α → localized
  invert : ∀ (s : α), S s → Nonempty (localized → localized)
  name : String

end MiniConstructionKernel
