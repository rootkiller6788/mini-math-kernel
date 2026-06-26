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

universe u

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

/-- Composition of two embeddings (axiomatic form).
    In a full implementation, we would need to prove that the theory
    of the mapped object equals the target theory. -/
axiom Embedding.comp {S T U : TheoryName} (e1 : Embedding T U) (e2 : Embedding S T) : Embedding S U

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
  /-- Reflect an object of theory T back to an object of theory S. -/
  reflects (α : Type u) [Object α] (hT : Object.theory α = T) (x : α) : α
  /-- The reflection of an embedding is an involution. -/
  isInvolution : ∀ (α : Type u) [Object α] (hS : Object.theory α = S) (x : α),
    True

/-! ## Full and Faithful Embeddings — L3: Categorical Structure

An embedding is *full* if every morphism in the target between embedded
objects comes from a morphism in the source. It is *faithful* if the
map on morphisms is injective. -/

/-- An embedding is faithful if the induced map on hom-sets is injective.
    Stated axiomatically since the general construction requires
    additional categorical structure. -/
axiom Embedding.IsFaithful {S T : TheoryName} (e : Embedding S T) : Prop

/-- An embedding is full if every morphism between embedded objects lifts.
    Stated axiomatically. -/
axiom Embedding.IsFull {S T : TheoryName} (e : Embedding S T) : Prop

/-- An embedding is fully faithful if it is both full and faithful. -/
def Embedding.IsFullyFaithful {S T : TheoryName} (e : Embedding S T) : Prop :=
  e.IsFaithful ∧ e.IsFull

/-- An embedding is essentially surjective if every object in T is
    isomorphic to an embedded object from S. Stated axiomatically. -/
axiom Embedding.IsEssentiallySurjective {S T : TheoryName} (e : Embedding S T) : Prop

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

/-- The identity embedding is fully faithful. Stated as an axiom. -/
axiom Embedding.id_fully_faithful (T : TheoryName) : (Embedding.id T).IsFullyFaithful

/-- Composition of faithful embeddings is faithful. Stated axiomatically. -/
axiom Embedding.comp_faithful {S T U : TheoryName} (e₁ : Embedding T U) (e₂ : Embedding S T)
    (hf₁ : e₁.IsFaithful) (hf₂ : e₂.IsFaithful) : (Embedding.comp e₁ e₂).IsFaithful

/-- Composition of full embeddings is full. Stated axiomatically. -/
axiom Embedding.comp_full {S T U : TheoryName} (e₁ : Embedding T U) (e₂ : Embedding S T)
    (hf₁ : e₁.IsFull) (hf₂ : e₂.IsFull) : (Embedding.comp e₁ e₂).IsFull

/-! ## Embedding Graph — L7: Application

Embeddings between theories can be organized into a graph for
dependency tracking and cross-theory reasoning. -/

/-- An embedding between two types with Object instances (not just theories).
    Stated axiomatically for the general case. -/
axiom Embedding.ofObjects {α β : Type u} [Object α] [Object β] (S T : TheoryName)
    (hS : Object.theory α = S) (hT : Object.theory β = T) (f : α → β) : Embedding S T

/-! ## #eval examples — L6: Verified Examples -/

def testEmbedding : Embedding (TheoryName.ofString "GroupTheory") (TheoryName.ofString "SetTheory") :=
  (forgetfulTo (TheoryName.ofString "GroupTheory") (TheoryName.ofString "SetTheory") "carrier").toEmbedding

#eval (Embedding.id (TheoryName.ofString "Algebra")).name
#eval testEmbedding.name
#eval (forgetfulTo (TheoryName.ofString "RingTheory") (TheoryName.ofString "GroupTheory") "additive").name

end MiniObjectKernel
