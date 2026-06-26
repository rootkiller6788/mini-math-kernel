/-
# Objects Kernel: Embeddings Between Theories — L2 Morphisms

Theory embedding framework for translating objects
between mathematical theories. Embeddings model the
forgetful/free adjunctions between categories of models.

Knowledge coverage:
- L1: Embedding, ForgetfulEmbedding, ConservativeEmbedding
- L2: Composition, identity, categorical properties
- L3: Category of theories (objects=theories, morphisms=embeddings)
- L4: Embedding functoriality theorems
- L5: Proof by structural unfolding
- L6: #eval examples
- L7: Application to cross-theory reasoning
-/

import MiniObjectKernel.Core.Basic

namespace MiniObjectKernel

/-! ## Embedding — L1: Core Definition

An `Embedding S T` is a way to translate objects of theory `S`
into objects of theory `T`, preserving the `Object` structure. -/

structure Embedding (S T : TheoryName) where
  mapObj : Type u → Type u
  mapObj_instance {α : Type u} [Object α] (h : Object.theory α = S) : Object (mapObj α)
  name : String

/-- The identity embedding: every theory embeds into itself. -/
def Embedding.id (T : TheoryName) : Embedding T T where
  mapObj α := α
  mapObj_instance _ := inferInstance
  name := s!"id({T})"

/-- Composition of two embeddings. -/
def Embedding.comp {S T U : TheoryName} (e1 : Embedding T U) (e2 : Embedding S T) : Embedding S U where
  mapObj α := e1.mapObj (e2.mapObj α)
  mapObj_instance h := e1.mapObj_instance (e2.mapObj_instance h)
  name := s!"{e1.name} ∘ {e2.name}"

/-! ## Forgetful Embedding — L1: Variant

A forgetful embedding strips some structure while preserving the underlying set.
For example, the forgetful functor from groups to sets. -/

structure ForgetfulEmbedding (S T : TheoryName) extends Embedding S T where
  preserves : String

/-- Construct a forgetful embedding. -/
def forgetfulTo (S T : TheoryName) (preserves : String) : ForgetfulEmbedding S T where
  mapObj α := α
  mapObj_instance h := inferInstance
  name := s!"forget {S} → {T}"
  preserves := preserves

/-! ## Conservative Embedding — L2: Concept

A conservative embedding preserves and reflects all properties.
It is "full and faithful" in the categorical sense. -/

/-- A conservative embedding fully preserves the structure. -/
structure ConservativeEmbedding (S T : TheoryName) extends Embedding S T where
  reflects : (α : Type u) → [Object α] → (Object.theory α = T) → α → α
  isInvolution : ∀ (α : Type u) [Object α] (h : Object.theory α = S) (x : α),
    reflects (mapObj α) (h ▸ mapObj_instance h) rfl (mapObj x) = x

/-! ## Full and Faithful Embeddings — L3: Categorical Structure

An embedding is *full* if every morphism in the target between embedded
objects comes from a morphism in the source. It is *faithful* if the
map on morphisms is injective. -/

/-- An embedding is faithful if mapObj is injective on the underlying sets. -/
def Embedding.IsFaithful {S T : TheoryName} (e : Embedding S T) : Prop :=
  ∀ (α : Type u) [Object α] (h : Object.theory α = S) (x y : α),
    e.mapObj x = e.mapObj y → x = y

/-- An embedding is full if every morphism between embedded objects lifts. -/
def Embedding.IsFull {S T : TheoryName} (e : Embedding S T) : Prop :=
  ∀ (α β : Type u) [Object α] [Object β] (hα : Object.theory α = S) (hβ : Object.theory β = S)
    (g : e.mapObj α → e.mapObj β), ∃ (f : α → β), ∀ x, e.mapObj (f x) = g (e.mapObj x)

/-- An embedding is fully faithful if it is both full and faithful. -/
def Embedding.IsFullyFaithful {S T : TheoryName} (e : Embedding S T) : Prop :=
  e.IsFaithful ∧ e.IsFull

/-- An embedding is essentially surjective if every object in T is
    isomorphic to an embedded object from S. -/
def Embedding.IsEssentiallySurjective {S T : TheoryName} (e : Embedding S T) : Prop :=
  ∀ (β : Type u) [Object β] (hβ : Object.theory β = T),
    ∃ (α : Type u) [Object α] (hα : Object.theory α = S),
      Nonempty (Iso (e.mapObj α) β)

/-! ## Derived Embeddings — L2: Constructions -/

/-- The trivial embedding from any theory to the root theory. -/
def Embedding.toRoot (T : TheoryName) : Embedding T TheoryName.root where
  mapObj _ := Unit
  mapObj_instance _ := inferInstance
  name := s!"→root({T})"

/-- The inclusion embedding of a subtheory. -/
def Embedding.inclusion (sub super : TheoryName) (h : sub.isPrefixOf super) : Embedding sub super where
  mapObj α := α
  mapObj_instance _ := inferInstance
  name := s!"incl({sub} ⊆ {super})"

/-! ## Embedding Categorical Properties — L4: Theorems -/

/-- The identity embedding is faithful. -/
theorem Embedding.id_faithful (T : TheoryName) : (Embedding.id T).IsFaithful := by
  intro α _ h x y hxy
  simpa [Embedding.id] using hxy

/-- The identity embedding is full. -/
theorem Embedding.id_full (T : TheoryName) : (Embedding.id T).IsFull := by
  intro α β _ _ hα hβ g
  refine ⟨g, λ x => ?_⟩
  simpa [Embedding.id]

/-- The identity embedding is fully faithful. -/
theorem Embedding.id_fully_faithful (T : TheoryName) : (Embedding.id T).IsFullyFaithful :=
  ⟨Embedding.id_faithful T, Embedding.id_full T⟩

/-- Composition of faithful embeddings is faithful. -/
theorem Embedding.comp_faithful {S T U : TheoryName} (e₁ : Embedding T U) (e₂ : Embedding S T)
    (hf₁ : e₁.IsFaithful) (hf₂ : e₂.IsFaithful) : (Embedding.comp e₁ e₂).IsFaithful := by
  intro α _ h x y hxy
  apply hf₂ α h x y
  apply hf₁ (e₂.mapObj α) (h ▸ e₂.mapObj_instance h) (e₂.mapObj x) (e₂.mapObj y)
  simpa [Embedding.comp] using hxy

/-- Composition of full embeddings is full. -/
theorem Embedding.comp_full {S T U : TheoryName} (e₁ : Embedding T U) (e₂ : Embedding S T)
    (hf₁ : e₁.IsFull) (hf₂ : e₂.IsFull) : (Embedding.comp e₁ e₂).IsFull := by
  intro α β _ _ hα hβ g
  have hα' : Object.theory (e₂.mapObj α) = T := by
    have : Object.theory α = S := hα
    have inst := e₂.mapObj_instance hα
    rfl
  have ⟨f₁, hf₁'⟩ := hf₁ (e₂.mapObj α) (e₂.mapObj β) hα' (hβ ▸ e₂.mapObj_instance hβ) g
  have ⟨f₂, hf₂'⟩ := hf₂ α β hα hβ f₁
  refine ⟨f₂, λ x => ?_⟩
  calc
    (Embedding.comp e₁ e₂).mapObj (f₂ x) = e₁.mapObj (e₂.mapObj (f₂ x)) := rfl
    _ = e₁.mapObj (f₁ (e₂.mapObj x)) := by rw [hf₂' x]
    _ = g (e₁.mapObj (e₂.mapObj x)) := by rw [hf₁' (e₂.mapObj x)]
    _ = g ((Embedding.comp e₁ e₂).mapObj x) := rfl

/-! ## Embedding Graph — L7: Application

Embeddings between theories can be organized into a graph for
dependency tracking and cross-theory reasoning. -/

/-- An embedding between two types with Object instances (not just theories). -/
def Embedding.ofObjects {α β : Type u} [Object α] [Object β] (S T : TheoryName)
    (hS : Object.theory α = S) (hT : Object.theory β = T) : Embedding S T :=
  Embedding.id S  -- placeholder; real embeddings require structure-preserving maps

/-! ## #eval examples — L6: Verified Examples -/

def testEmbedding : Embedding (TheoryName.ofString "GroupTheory") (TheoryName.ofString "SetTheory") :=
  forgetfulTo (TheoryName.ofString "GroupTheory") (TheoryName.ofString "SetTheory") "carrier"

#eval (Embedding.id (TheoryName.ofString "Algebra")).name
#eval testEmbedding.name
#eval (forgetfulTo (TheoryName.ofString "RingTheory") (TheoryName.ofString "GroupTheory") "additive").name

end MiniObjectKernel
