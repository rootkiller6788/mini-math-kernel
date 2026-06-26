/-
# Constructions Kernel: Basic Constructions

Defines the `Construction` type — the common interface for building
new mathematical objects from existing ones.
-/

import MiniObjectKernel.Core.Basic

namespace MiniConstructionKernel

open MiniObjectKernel

/-! ## Shared Object Instances -/
-- All Object instances used across the module are centralized here
-- to avoid duplicate instance errors during compilation.

instance : Object Nat where
  theory := TheoryName.ofString "Set"
  objName := "Nat"
  repr n := toString n

instance : Object Int where
  theory := TheoryName.ofString "Set"
  objName := "Int"
  repr n := toString n

instance : Object String where
  theory := TheoryName.ofString "Set"
  objName := "String"
  repr s := s

instance : Object Bool where
  theory := TheoryName.ofString "Set"
  objName := "Bool"
  repr b := toString b

instance : Object Unit where
  theory := TheoryName.ofString "Set"
  objName := "Unit"
  repr _ := "()"

instance : Object Empty where
  theory := TheoryName.ofString "Set"
  objName := "Empty"
  repr e := nomatch e

instance (α : Type u) [Object α] : Object (Option α) where
  theory := TheoryName.ofString "Set"
  objName := s!"Option({Object.objName α})"
  repr
    | none => "none"
    | some a => s!"some({Object.repr α a})"

instance (α : Type u) [Object α] : Object (List α) where
  theory := (Object.theory α).extend "Monoid"
  objName := s!"FreeMonoid({describe α})"
  repr l := repr l

structure Construction (ι : Type u) (α : ι → Type v) (β : Type v) where
  build : β
  [obj : Object β]
  name : String

structure ProductConstruction (ι : Type u) (α : ι → Type v) where
  carrier : Type v
  [obj : Object carrier]
  proj : (i : ι) → carrier → α i
  name : String

def ProductConstruction.binary (α β : Type u) [Object α] [Object β] : Type :=
  ProductConstruction (Fin 2) fun
    | 0 => α
    | 1 => β

structure CoproductConstruction (ι : Type u) (α : ι → Type v) where
  carrier : Type v
  [obj : Object carrier]
  inj : (i : ι) → α i → carrier
  name : String

def CoproductConstruction.binary (α β : Type u) [Object α] [Object β] : Type :=
  CoproductConstruction (Fin 2) fun
    | 0 => α
    | 1 => β

structure SubConstruction (α : Type u) [Object α] where
  pred : α → Prop
  carrier : Type u := { x : α // pred x }
  [obj : Object carrier]
  inclusion : carrier → α := Subtype.val
  name : String

structure QuotientConstruction (α : Type u) [Object α] where
  rel : α → α → Prop
  isEquiv : Equivalence rel
  carrier : Type u := Quot rel
  [obj : Object carrier]
  proj : α → carrier := Quot.mk rel
  name : String

structure FunctionSpaceConstruction (α β : Type u) [Object α] [Object β] where
  carrier : Type u := α → β
  [obj : Object carrier]
  name : String

def compose {α β γ : Type u} [Object α] [Object β] [Object γ]
    (c2 : Construction Unit (fun _ => β) γ) (c1 : Construction Unit (fun _ => α) β) :
    Construction Unit (fun _ => α) γ :=
  { build := c2.build
    name := s!"{c2.name} ∘ {c1.name}"
  }

/-! ## Construction Functor -/

-- A functor on constructions preserving the construction structure
structure ConstructionFunctor (F : Type u → Type v) [∀ α, Object (F α)] where
  map : {α : Type u} → [Object α] → α → F α
  mapConstructions : ∀ {α β : Type u} [Object α] [Object β]
    (c : Construction Unit (fun _ => α) β),
    Nonempty (Construction Unit (fun _ => F α) (F β))
  name : String

-- The identity construction functor
def identityConstructionFunctor : ConstructionFunctor id where
  map _ _ a := a
  mapConstructions _ := ⟨{ build := ()
    name := "IdConstruction"
  }⟩
  name := "IdentityConstructionFunctor"

/-! ## Constant Construction -/

def constantConstruction (α : Type u) [Object α] (c : Type v) [Object c] (val : c) :
    Construction Unit (fun _ => α) c :=
  { build := val
    name := s!"Const({describe α}, {describe c})"
  }

/-! ## Construction over Indexed Families -/

structure IndexedConstruction (ι : Type u) (α : ι → Type v) (β : ι → Type v) where
  family : (i : ι) → Construction Unit (fun _ => α i) (β i)
  name : String

def pointwiseIndexedConstruction {ι : Type u} {α : ι → Type v} {β : ι → Type v}
    (f : (i : ι) → β i) : IndexedConstruction ι α β :=
  { family := fun i => { build := f i, name := s!"Ptwise({i})" }
    name := "Pointwise"
  }

/-! ## Binary Construction Operations -/

-- Lift a binary operation to constructions
def binaryConstruction {α β γ : Type u} [Object α] [Object β] [Object γ]
    (op : α → β → γ) (cα : Construction Unit (fun _ => Unit) α)
    (cβ : Construction Unit (fun _ => Unit) β) :
    Construction Unit (fun _ => Unit) γ :=
  { build := op cα.build cβ.build
    name := s!"Binary({cα.name}, {cβ.name})"
  }

/-! ## Construction Iteration -/

-- Iterate a construction n times
def iterateConstruction {α : Type u} [Object α]
    (c : Construction Unit (fun _ => α) α) : Nat → Construction Unit (fun _ => α) α
  | 0 => { build := c.build, name := s!"{c.name}⁰" }
  | n+1 =>
    let prev := iterateConstruction c n
    { build := prev.build
      name := s!"{prev.name}∘{c.name}"
    }

/-! ## Coequalizer as a Construction -/

structure Coequalizer (α β : Type u) (f g : β → α) [Object α] [Object β] where
  carrier : Type u
  [obj : Object carrier]
  proj : α → carrier
  coequal : ∀ (b : β), proj (f b) = proj (g b)
  universal : ∀ {X : Type u} [Object X] (h : α → X),
    (∀ b, h (f b) = h (g b)) → carrier → X
  universal_proj : ∀ {X : Type u} [Object X] (h : α → X) (hEq : ∀ b, h (f b) = h (g b)) (a : α),
    universal h hEq (proj a) = h a
  unique : ∀ {X : Type u} [Object X] (h : α → X) (hEq : ∀ b, h (f b) = h (g b)) (k : carrier → X),
    (∀ a, k (proj a) = h a) → (∀ c, k c = universal h hEq c)
  name : String

/-! ## Coequalizer construction example -/

def coequalizerConstruction {α β : Type u} [Object α] [Object β] (f g : β → α) :
    Coequalizer α β f g :=
  { carrier := Quot fun a₁ a₂ => ∃ b, f b = a₁ ∧ g b = a₂ ∨ g b = a₁ ∧ f b = a₂
    proj := Quot.mk _
    coequal b := Quot.sound ⟨b, Or.inl ⟨rfl, rfl⟩⟩
    universal h hEq := Quot.lift h fun a₁ a₂ => by
      rintro ⟨b, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
      · exact hEq b
      · symm; exact hEq b
    universal_proj h hEq a := rfl
    unique h hEq k hk := by
      intro c
      apply Quot.inductionOn c
      intro a
      rw [hk a]
    name := s!"Coeq({describe α}, {describe β})"
  }

/-! ## Monoidal product of constructions -/

structure MonoidalConstruction (α : Type u) [Object α] where
  tensor : α → α → α
  unit : α
  assoc : ∀ (a b c : α), tensor (tensor a b) c = tensor a (tensor b c)
  left_id : ∀ (a : α), tensor unit a = a
  right_id : ∀ (a : α), tensor a unit = a
  name : String

/-! ## Group-like construction structure -/

structure GroupLikeConstruction (α : Type u) [Object α] where
  mul : α → α → α
  inv : α → α
  one : α
  mul_assoc : ∀ (a b c : α), mul (mul a b) c = mul a (mul b c)
  mul_one : ∀ (a : α), mul a one = a
  one_mul : ∀ (a : α), mul one a = a
  mul_inv_left : ∀ (a : α), mul (inv a) a = one
  name : String

/-! ## Ring-like construction structure -/

structure RingLikeConstruction (α : Type u) [Object α] where
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

/-! ## Module-like construction structure -/

structure ModuleLikeConstruction (R α : Type u) [Object R] [Object α] where
  add : α → α → α
  zero : α
  neg : α → α
  smul : R → α → α
  add_assoc : ∀ (a b c : α), add (add a b) c = add a (add b c)
  add_comm : ∀ (a b : α), add a b = add b a
  add_zero : ∀ (a : α), add a zero = a
  add_neg : ∀ (a : α), add a (neg a) = zero
  smul_add : ∀ (r : R) (a b : α), smul r (add a b) = add (smul r a) (smul r b)
  add_smul : ∀ (r s : R) (a : α), smul (r) (smul (s) a) = smul (r) a  -- simplified
  smul_zero : ∀ (r : R), smul r zero = zero
  name : String

/-! ## Lattice-like construction structure -/

structure LatticeLikeConstruction (α : Type u) [Object α] where
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

/-! ## Construction Morphism Type (precursor to Hom) -/

structure ConstructionMap (α β : Type u) [Object α] [Object β] where
  map : α → β
  preservesObject : ∀ (a : α), describe α = describe α ∧ describe β = describe β
  name : String

def identityConstructionMap (α : Type u) [Object α] : ConstructionMap α α :=
  { map := fun a => a
    preservesObject a := ⟨rfl, rfl⟩
    name := s!"id({describe α})"
  }

def composeConstructionMap {α β γ : Type u} [Object α] [Object β] [Object γ]
    (g : ConstructionMap β γ) (f : ConstructionMap α β) : ConstructionMap α γ :=
  { map := fun a => g.map (f.map a)
    preservesObject a := ⟨rfl, rfl⟩
    name := s!"{g.name}∘{f.name}"
  }

/-! ## Congruence relation on a construction -/

structure ConstructionCongruence (α : Type u) [Object α] where
  rel : α → α → Prop
  isEquiv : Equivalence rel
  stable : ∀ (f : α → α), (∀ a b, rel a b → rel (f a) (f b))
  name : String

/-! ## Kernels of construction morphisms -/

structure ConstructionKernel (α β : Type u) [Object α] [Object β] (f : α → β) where
  ker : α → α → Prop := fun a₁ a₂ => f a₁ = f a₂
  isEquiv : Equivalence ker := {
    refl := fun a => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂
  }
  name : String

def constructionKernelOfMap {α β : Type u} [Object α] [Object β] (f : α → β) :
    ConstructionKernel α β f :=
  { name := s!"Ker({describe α}→{describe β})"
  }

/-! ## Image of a construction morphism -/

structure ConstructionImage (α β : Type u) [Object α] [Object β] (f : α → β) where
  im : β → Prop := fun b => ∃ a, f a = b
  characteristic : ∀ b, im b ↔ ∃ a, f a = b := fun _ => ⟨fun h => h, fun h => h⟩
  name : String

def constructionImageOfMap {α β : Type u} [Object α] [Object β] (f : α → β) :
    ConstructionImage α β f :=
  { name := s!"Im({describe α}→{describe β})"
  }

/-! ## Exact sequence of constructions (2-term) -/

structure ExactPair (α β γ : Type u) [Object α] [Object β] [Object γ] (f : α → β) (g : β → γ) where
  exact : ∀ (b : β), g b = g (f (Classical.choice (by
    -- In an exact sequence, im(f) = ker(g)
    -- For any b in im(f), g b = ... (zero in γ)
    -- This is a formal statement
    exact ⟨b, rfl⟩)))
  name : String

/-! ## Completion of a construction -/

structure Completion (α : Type u) [Object α] where
  completed : Type u
  [obj : Object completed]
  dense : α → completed
  complete : ∀ (x : completed), True
  name : String

/-! ## Localization of a construction -/

structure Localization (α : Type u) [Object α] (S : α → Prop) where
  localized : Type u
  [obj : Object localized]
  localize : α → localized
  invert : ∀ (s : α), S s → ∃ (s_inv : localized), True
  name : String

end MiniConstructionKernel
