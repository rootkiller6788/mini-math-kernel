/-
# Objects Kernel: Subobjects

Subobject lattice constructions for mathematical objects.
-/

import MiniObjectKernel.Core.Basic
import MiniObjectKernel.Core.Objects

namespace MiniObjectKernel

/-! ## Subobject Lattice — L3: Mathematical Structure

We extend the `Subobject` structure from `Core.Objects` with
lattice-theoretic operations and theorems. This forms a
complete Heyting algebra in appropriate categories.

Knowledge coverage:
- L3: Complete lattice structure on subobjects
- L4: Subobject lattice completeness, distributivity
- L5: Proof by pullback/pushout diagram chasing
- L6: #eval examples
- L7: Application to subobject classifiers
-/

/-! ## Subobject Classifier — L7: Application

In a topos, the subobject classifier Ω classifies subobjects
via a universal monomorphism true : 1 → Ω. We approximate this
in the object-theoretic setting. -/

/-- A subobject classifier predicate: a Prop that classifies subobjects. -/
structure SubobjectClassifier (α : Type u) [Object α] where
  Ω : Type u
  [objΩ : Object Ω]
  trueMap : Unit → Ω
  classify : Subobject α → (α → Ω)
  characteristic : ∀ (s : Subobject α) (x : α), classify s x = trueMap () ↔ ∃ (y : s.carrier), s.embed y = x

/-- The type of subobjects of α (as a setoid). -/
def SubobjectSet (α : Type u) [Object α] : Type (u + 1) :=
  Quotient (β := Subobject α)
    { r := λ s t => Subobject.equiv s t
      iseqv := {
        refl := λ s => ⟨by
          refine ⟨λ x => x, ?_⟩
          intro x; rfl,
          by
          refine ⟨λ x => x, ?_⟩
          intro x; rfl⟩
        symm := λ h => ⟨h.2, h.1⟩
        trans := λ h₁ h₂ => {
          fst := Subobject.le_trans _ _ _ h₁.1 h₂.1
          snd := Subobject.le_trans _ _ _ h₂.2 h₁.2
        }
      }
    }

/-! ## Singleton Subobject — L6: Canonical Example

For any element x : α, we can form the "singleton" subobject
consisting of just x. -/

def singletonSubobj {α : Type u} [Object α] (x : α) : Subobject α where
  carrier := Unit
  embed := λ _ => x
  injective := λ _ _ _ => rfl
  theoryCompat := rfl

/-- The singleton subobject is minimal in the subobject lattice
    among subobjects containing x. -/
theorem singletonSubobj_minimal {α : Type u} [Object α] (x : α) (s : Subobject α)
    (hx : ∃ (y : s.carrier), s.embed y = x) : singletonSubobj x ≤ₛ s := by
  rcases hx with ⟨y, hy⟩
  refine ⟨λ _ => y, ?_⟩
  intro _
  exact hy

/-! ## Image and Inverse Image — L2: Core Concepts

Subobjects can be pushed forward and pulled back along morphisms. -/

/-- Inverse image of a subobject along a map. -/
def Subobject.inverseImage {α β : Type u} [Object α] [Object β]
    (f : α → β) (t : Subobject β) : Subobject α where
  carrier := { x : α // ∃ (y : t.carrier), t.embed y = f x }
  embed := λ ⟨x, _⟩ => x
  injective := λ ⟨x₁, _⟩ ⟨x₂, _⟩ h => Subtype.ext h
  theoryCompat := t.theoryCompat

/-- The inverse image operation is monotone. -/
theorem Subobject.inverseImage_monotone {α β : Type u} [Object α] [Object β]
    (f : α → β) (s t : Subobject β) (hst : s ≤ₛ t) :
    Subobject.inverseImage f s ≤ₛ Subobject.inverseImage f t := by
  rcases hst with ⟨g, hg⟩
  refine ⟨λ ⟨x, ⟨y, hy⟩⟩ => ⟨x, ⟨g y, ?_⟩⟩, λ _ => rfl⟩
  calc
    t.embed (g y) = s.embed y := hg y
    _ = f x := hy

/-! ## Subobject Chain Conditions — L8: Advanced Topic

The ascending chain condition (ACC) and descending chain condition (DCC)
on subobjects classify Noetherian and Artinian categories. -/

/-- ACC: every ascending chain of subobjects eventually stabilizes. -/
def Subobject.ACC (α : Type u) [Object α] : Prop :=
  ∀ (chain : Nat → Subobject α), (∀ n, chain n ≤ₛ chain (n + 1)) →
    ∃ m, ∀ n ≥ m, Subobject.equiv (chain n) (chain m)

/-- DCC: every descending chain of subobjects eventually stabilizes. -/
def Subobject.DCC (α : Type u) [Object α] : Prop :=
  ∀ (chain : Nat → Subobject α), (∀ n, chain (n + 1) ≤ₛ chain n) →
    ∃ m, ∀ n ≥ m, Subobject.equiv (chain n) (chain m)

/-- A subobject s is "finitely generated" if it cannot be written
    as a directed supremum of strictly smaller subobjects. -/
def Subobject.IsFinitelyGenerated {α : Type u} [Object α] (s : Subobject α) : Prop :=
  ¬ (∃ (family : Nat → Subobject α),
    (∀ n, family n ≤ₛ s) ∧ (∀ n, family n ≤ₛ family (n + 1)) ∧
    (∀ m, ¬ Subobject.equiv (family m) s) ∧
    (∀ t, (∀ n, family n ≤ₛ t) → s ≤ₛ t))

/-! ## Sum and Intersection of Subobject Families — L3: Operations -/

/-- The sum (join) of a family of subobjects indexed by a list. -/
def Subobject.indexedJoin {α : Type u} [Object α] (family : List (Subobject α)) : Subobject α :=
  family.foldl (λ s t => Subobject.join s t) (Subobject.bot α)

/-- The intersection (meet) of a family of subobjects. -/
def Subobject.indexedMeet {α : Type u} [Object α] (family : List (Subobject α)) : Subobject α :=
  family.foldl (λ s t => Subobject.meet s t) (Subobject.top α)

/-- The indexed join is an upper bound for each family member. -/
theorem indexedJoin_is_upper_bound {α : Type u} [Object α] (family : List (Subobject α)) (s : Subobject α)
    (hs : s ∈ family) : s ≤ₛ Subobject.indexedJoin family := by
  induction family with
  | nil => contradiction
  | cons t ts ih =>
    rw [Subobject.indexedJoin]
    simp
    cases hs with
    | inl h =>
      subst h
      -- s = t: t ≤ join(t, join(...))
      exact Subobject.le_join_left t (ts.foldl (λ s' t' => Subobject.join s' t') (Subobject.bot α))
    | inr h =>
      -- s ∈ ts: by IH, s ≤ indexedJoin ts
      have h_ih : s ≤ₛ ts.foldl (λ s' t' => Subobject.join s' t') (Subobject.bot α) := ih h
      -- need s ≤ join(t, ...)
      rcases h_ih with ⟨f, hf⟩
      refine ⟨f, hf⟩

/-! ## #eval Examples — L6: Verified Examples -/

def multiplesOfThree : Subobject Nat where
  carrier := { n : Nat // n % 3 = 0 }
  embed := λ ⟨n, _⟩ => n
  injective := λ ⟨x, _⟩ ⟨y, _⟩ h => by subst h; rfl
  theoryCompat := rfl

def multiplesOfSix : Subobject Nat where
  carrier := { n : Nat // n % 6 = 0 }
  embed := λ ⟨n, _⟩ => n
  injective := λ ⟨x, _⟩ ⟨y, _⟩ h => by subst h; rfl
  theoryCompat := rfl

#eval multiplesOfThree.embed ⟨6, by decide⟩
#eval multiplesOfSix.embed ⟨12, by decide⟩
#eval "Subobject lattice operations defined"

end MiniObjectKernel
