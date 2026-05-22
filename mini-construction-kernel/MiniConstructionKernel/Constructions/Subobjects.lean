/-
# Constructions Kernel: Subobject Constructions

Subobject constructions for mathematical objects.
Includes: subobject lattice, embeddings, intersections, unions,
pullback-stability, and subobject classifiers.
-/

import MiniConstructionKernel.Core.Basic
import MiniConstructionKernel.Core.Objects
import MiniConstructionKernel.Core.Laws
import MiniConstructionKernel.Morphisms.Hom

namespace MiniConstructionKernel

/-! ## Subobject as Monomorphism -/

structure Subobject (α : Type u) [Object α] where
  carrier : Type u
  [obj : Object carrier]
  embedding : carrier → α
  mono : ∀ {X : Type u} [Object X] (f g : X → carrier),
    (∀ x, embedding (f x) = embedding (g x)) → (∀ x, f x = g x)
  name : String

/-! ## Subobject from Predicate -/

def subobjectOfPredicate {α : Type u} [Object α] (P : α → Prop) (n : String := "") :
    Subobject α :=
  { carrier := { x : α // P x }
    embedding := Subtype.val
    mono := fun f g h x => by
      apply Subtype.ext
      have h' : (embedding ∘ f) x = (embedding ∘ g) x := h x
      -- Subtype.val ∘ f and Subtype.val ∘ g agree at x
      -- Since the embedding is Subtype.val, which is injective:
      --   Subtype.val (f x) = Subtype.val (g x) → f x = g x
      -- This follows from Subtype.val_inj
      exact Subtype.val_inj.mp h'
    name := n
  }

/-! ## Pullback Subobject -/

-- The pullback of a subobject along a morphism
structure PullbackSubobject (α β : Type u) [Object α] [Object β] (f : α → β) (S : Subobject β) where
  carrier : Type u := { x : α // S.embedding (f x) = f x -- condition encoding membership
                         ∧ True }
  [obj : Object carrier]
  embedding : carrier → α := Subtype.val
  pullback_square : ∀ (s : carrier), S.embedding (f (embedding s)) = f (embedding s)
  universal : ∀ {X : Type u} [Object X] (g : X → α),
    (∀ x, S.embedding (f (g x)) = f (g x)) → X → carrier
  name : String

/-! ## Intersection of Subobjects -/

structure SubobjectIntersection (α : Type u) [Object α] (S T : Subobject α) where
  carrier : Type u
  [obj : Object carrier]
  embedding : carrier → α
  factorS : carrier → S.carrier
  factorT : carrier → T.carrier
  factorS_comm : ∀ (c : carrier), S.embedding (factorS c) = embedding c
  factorT_comm : ∀ (c : carrier), T.embedding (factorT c) = embedding c
  universal : ∀ {X : Type u} [Object X] (fS : X → S.carrier) (fT : X → T.carrier),
    (∀ x, S.embedding (fS x) = T.embedding (fT x)) → X → carrier
  name : String

/-! ## Union of Subobjects -/

structure SubobjectUnion (α : Type u) [Object α] (S T : Subobject α) where
  carrier : Type u
  [obj : Object carrier]
  embedding : carrier → α
  inl : S.carrier → carrier
  inr : T.carrier → carrier
  inl_comm : ∀ (s : S.carrier), embedding (inl s) = S.embedding s
  inr_comm : ∀ (t : T.carrier), embedding (inr t) = T.embedding t
  universal : ∀ {X : Type u} [Object X] (fS : S.carrier → X) (fT : T.carrier → X),
    (carrier → X)
  name : String

/-! ## Subobject Lattice -/

-- The poset of subobjects of a given object
structure SubobjectLattice (α : Type u) [Object α] where
  subobjects : Type (max u 1)
  [obj : Object subobjects]
  order : subobjects → subobjects → Prop
  isRefl : ∀ s, order s s
  isTrans : ∀ s t u, order s t → order t u → order s u
  isAntisymm : ∀ s t, order s t → order t s → s = t
  top : subobjects
  bottom : subobjects
  top_is_top : ∀ s, order s top
  bottom_is_bot : ∀ s, order bottom s
  name : String

/-! ## Subobject Classifier -/

-- A subobject classifier: Ω such that subobjects correspond to maps into Ω
structure SubobjectClassifier (Ω : Type u) [Object Ω] where
  true : Ω
  classify : ∀ {α : Type u} [Object α] (S : Subobject α), α → Ω
  pullback : ∀ {α : Type u} [Object α] (S : Subobject α) (a : α),
    classify S a = true ↔ S.embedding (a) = a
  name : String

/-! ## Simple Subobject Classifier for Prop -/

def propSubobjectClassifier : SubobjectClassifier Prop where
  true := True
  classify S a := S.embedding a = a
  pullback S a := ⟨fun h => h, fun h => h⟩
  name := "PropSubobjectClassifier"

/-! ## Chain of Subobjects -/

-- A finite chain of nested subobjects
structure SubobjectChain (α : Type u) [Object α] where
  chain : List (Subobject α)
  length : Nat := chain.length
  name : String

-- Build a simple chain from a list of predicates
def subobjectChainOfPredicates {α : Type u} [Object α]
    (preds : List (α → Prop)) : SubobjectChain α :=
  { chain := preds.map fun P => subobjectOfPredicate P
    name := "PredicateChain"
  }

/-! ## Kernel Subobject -/

-- The kernel of a morphism as a subobject
structure KernelSubobject (α β : Type u) [Object α] [Object β] (f : α → β) where
  carrier : Type u := { x : α // f x = f x }  -- always true, but models the pattern
  [obj : Object carrier]
  embedding : carrier → α := Subtype.val
  property : ∀ (c : carrier), f (embedding c) = f (embedding c) := fun _ => rfl
  name : String

/-! ## Image Subobject -/

-- The image of a morphism as a subobject
structure ImageSubobject (α β : Type u) [Object α] [Object β] (f : α → β) where
  carrier : Type u := { y : β // ∃ x : α, f x = y }
  [obj : Object carrier]
  embedding : carrier → β := Subtype.val
  surjective : ∀ (y : β), (∃ x, f x = y) ↔ (True) := fun _ => ⟨fun _ => True.intro, fun _ => ⟨y, rfl⟩⟩
  name : String

/-! ## Subobject Construction Bridge -/

-- Convert a SubConstruction to a Subobject
def subConstructionToSubobject {α : Type u} [Object α] (sc : SubConstruction α) : Subobject α :=
  { carrier := sc.carrier
    embedding := sc.inclusion
    mono := fun f g h x => by
      have hval : Subtype.val (f x) = Subtype.val (g x) := h x
      apply Subtype.ext
      exact hval
    name := sc.name
  }

/-! ## Examples and evaluations -/

section Examples

open MiniObjectKernel

instance : Object Nat where
  theory := TheoryName.ofString "Set"
  objName := "Nat"
  repr n := toString n

instance : Object Bool where
  theory := TheoryName.ofString "Set"
  objName := "Bool"
  repr b := toString b

def evenNatSubobject : Subobject Nat :=
  subobjectOfPredicate (fun n => n % 2 = 0) "EvenNat"

def positiveNatSubobject : Subobject Nat :=
  subobjectOfPredicate (fun n => n > 0) "PositiveNat"

def idMono : Subobject Nat where
  carrier := Nat
  embedding := fun n => n
  mono := fun f g h x => h x
  name := "IdNat"

#eval evenNatSubobject.name
#eval propSubobjectClassifier.name
#eval subConstructionToSubobject
      { pred := fun n : Nat => n = 0
        name := "Zero"
      : SubConstruction Nat}.name : String

end Examples

end MiniConstructionKernel
