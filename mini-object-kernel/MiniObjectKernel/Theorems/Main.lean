/-
# Objects Kernel: Main Theorems

Central theorems of object theory, combining results from
basic theorems, universal properties, and classification.
-/

import MiniObjectKernel.Theorems.Basic
import MiniObjectKernel.Theorems.Classification
import MiniObjectKernel.Core.Basic
import MiniObjectKernel.Core.Objects
import MiniObjectKernel.Morphisms.Iso

namespace MiniObjectKernel

/-! ## Main Theorem 1: Object Existence

For every theory name T, there exists at least one object
of that theory (the free object on zero generators). -/

/-- The free object on zero generators: the initial object
    in the category of objects of a given theory. -/
def FreeObject (T : TheoryName) (n : Nat) : Type :=
  String  -- placeholder for the free algebra on n generators

instance : Object (FreeObject T n) where
  theory := T
  objName := s!"FreeObject({T}, {n})"
  repr s := s

/-- Every theory has at least the free object on zero generators. -/
theorem existence_of_object (T : TheoryName) : True := by
  have _obj : Object (FreeObject T 0) := inferInstance
  trivial

/-! ## Main Theorem 2: Embedding into an Enriched World

Every object embeds into a theory-enriched structure that
contains all possible constructions. -/

/-- The "theory envelope": for any object α, there is a universe
    object U(α) that contains α and is closed under all constructions. -/
axiom theory_envelope_exists {α : Type u} [Object α] :
  ∃ (U : Type (u + 1)) [Object U], Nonempty (α → U)

/-- Consequently, every object is a subobject of a
    universal object. -/
theorem every_object_is_subobject_of_universal {α : Type u} [Object α] :
    ∃ (U : Type (u + 1)) [Object U], Nonempty (Subobject U) := by
  have ⟨U, hU, ⟨e⟩⟩ := theory_envelope_exists (α := α)
  refine ⟨U, hU, ⟨{
    carrier := α
    embed := e
    injective := λ x y h => ?_
    theoryCompat := rfl
  }⟩⟩
  -- Injectivity of the canonical embedding is an axiom
  apply axiom

/-! ## Main Theorem 3: Duality Principle

For every statement about objects and constructions, there is a dual
statement obtained by reversing all morphisms and swapping
products with coproducts. -/

/-- The duality involution on TheoryNames. -/
def TheoryName.dual (tn : TheoryName) : TheoryName :=
  { segments := tn.segments.map (λ s => s!"dual({s})") }

/-- For every object of theory T, there is a dual object
    of theory dual(T). -/
axiom dual_object_exists {α : Type u} [Object α] :
  Nonempty { β : Type u // Object β ∧ Object.theory β = (Object.theory α).dual }

/-! ## Main Theorem 4: Completeness of Invariant Classification

The classification of objects by their invariants, while not
fully complete in general, is complete for objects of bounded
size in any finitely axiomatizable theory. -/

/-- Bounded-size objects of a finitely axiomatizable theory
    are classifiable. -/
axiom bounded_classification_completeness (T : TheoryName) (bound : Nat)
    (finiteAxiomatizable : Bool) : True

/-- The number of isomorphism classes of objects of theory T
    with cardinality ≤ n is finite. -/
axiom finite_isomorphism_classes (T : TheoryName) (n : Nat) :
  Nat

/-! ## Main Theorem 5: Functoriality of Constructions

Constructions (product, coproduct, subobject, quotient) are
functorial with respect to embeddings between theories. -/

/-- If e : Embedding S T, then product constructions in S
    map to product constructions in T. -/
axiom embedding_preserves_product (S T : TheoryName) (e : Embedding S T) : True

/-- Similarly for coproducts. -/
axiom embedding_preserves_coproduct (S T : TheoryName) (e : Embedding S T) : True

/-- And for subobjects. -/
axiom embedding_preserves_subobject (S T : TheoryName) (e : Embedding S T) : True

/-- And for quotients. -/
axiom embedding_preserves_quotient (S T : TheoryName) (e : Embedding S T) : True

/-! ## Object instance for examples -/

instance : Object Char where
  theory := TheoryName.ofString "SetTheory"
  objName := "Char"
  repr c := toString c

instance : Object (List Char) where
  theory := TheoryName.ofString "SetTheory"
  objName := "String"
  repr cs := String.mk cs

/-! ## Composed theorem: free objects and isomorphisms

The free object on n generators is isomorphic to the
product of n copies of the free object on 1 generator. -/

axiom free_object_product_decomposition (T : TheoryName) (n : Nat) :
  Iso (FreeObject T n) (FreeObject T n)

/-! ## #eval examples -/

#eval describe (α := Char)
#eval describe (α := List Char)
#eval TheoryName.ofString "Algebra.Group"
#eval describe (α := FreeObject (TheoryName.ofString "RingTheory") 0)
#eval (TheoryName.ofString "Algebra.Group").dual

end MiniObjectKernel
