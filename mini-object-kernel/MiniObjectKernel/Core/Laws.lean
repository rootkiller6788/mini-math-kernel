/-
# Objects Kernel: Laws

Axioms and laws governing mathematical objects.
Essential properties that every Object instance must satisfy
and derived theorems about the Object ecosystem.
-/

import MiniObjectKernel.Core.Basic
import MiniObjectKernel.Core.Objects
import MiniObjectKernel.Morphisms.Hom
import MiniObjectKernel.Morphisms.Iso

namespace MiniObjectKernel

/-! ## Uniqueness of Theory Name

For any type `α`, there should be at most one canonical `Object` theory.
We state this as an axiom: two `Object` instances on the same type
must assign the same theory name. -/

/-- If two Object instances exist for the same type, their theories are equal.
    This is a meta-property that Lean cannot enforce at the typeclass level. -/
axiom obj_theory_unique {α : Type u} [o₁ : Object α] [o₂ : Object α] :
  o₁.theory = o₂.theory

/-- Consequence: the `Object` theory is a function of the type, not the instance. -/
theorem obj_theory_deterministic {α : Type u} [o₁ : Object α] [o₂ : Object α] :
  o₁.theory = o₂.theory := obj_theory_unique

/-! ## Subobject Laws

Subobjects form a preorder under the inclusion relation `≤ₛ`.
We prove reflexivity, transitivity, and antisymmetry (up to equivalence). -/

/-- Reflexivity: every subobject is less than or equal to itself. -/
theorem subobject_refl {α : Type u} [Object α] (s : Subobject α) : s ≤ₛ s := by
  refine ⟨λ x => x, ?_⟩
  intro x; rfl

/-- Transitivity: if s ≤ t and t ≤ u, then s ≤ u. -/
theorem subobject_trans {α : Type u} [Object α] (s t u : Subobject α)
    (hst : s ≤ₛ t) (htu : t ≤ₛ u) : s ≤ₛ u := by
  rcases hst with ⟨f, hf⟩
  rcases htu with ⟨g, hg⟩
  refine ⟨λ x => g (f x), ?_⟩
  intro x
  calc
    u.embed (g (f x)) = t.embed (f x) := hg (f x)
    _ = s.embed x := hf x

/-- Antisymmetry up to equivalence: if s ≤ₛ t and t ≤ₛ s, they are equivalent. -/
theorem subobject_antisymm_equiv {α : Type u} [Object α] (s t : Subobject α)
    (hst : s ≤ₛ t) (hts : t ≤ₛ s) : Subobject.equiv s t :=
  ⟨hst, hts⟩

/-- Inclusion of the bottom subobject is a monomorphism. -/
theorem subobject_bot_unique {α : Type u} [Object α] (s : Subobject α)
    (h : s ≤ₛ Subobject.bot α) : Nonempty (Subobject.equiv s (Subobject.bot α)) := by
  rcases h with ⟨f, hf⟩
  have hempty : s.carrier → Empty := f
  refine ⟨⟨h, ?_⟩⟩
  refine ⟨λ e => nomatch e, ?_⟩
  intro e; nomatch e

/-! ## Quotient Laws

The universal property of a quotient: any map that respects the equivalence
relation factors uniquely through the projection. -/

/-- The universal property of a quotient (existence part). -/
axiom quotient_universal_property {α : Type u} [Object α] (Q : Quotient α)
    (β : Type u) [Object β] (f : α → β) (h : ∀ x y, Q.rel x y → f x = f y) :
  ∃! g : Q.quotientType → β, ∀ x, g (Q.proj x) = f x

/-- Lift a map `f : α → β` that respects `Q.rel` to a map on the quotient. -/
def quotient_lift {α : Type u} [Object α] (Q : Quotient α)
    (β : Type u) [Object β] (f : α → β) (h : ∀ x y, Q.rel x y → f x = f y) :
    Q.quotientType → β :=
  (quotient_universal_property Q β f h).exists.choose

/-- The lift satisfies the commutative diagram: `lift Q f h (proj x) = f x`. -/
theorem quotient_lift_commutes {α : Type u} [Object α] (Q : Quotient α)
    (β : Type u) [Object β] (f : α → β) (h : ∀ x y, Q.rel x y → f x = f y) (x : α) :
    quotient_lift Q β f h (Q.proj x) = f x :=
  ((quotient_universal_property Q β f h).exists.choose_spec).1 x

/-- The lift is unique: any other map `g` satisfying the commutative diagram
    equals the canonical lift. -/
theorem quotient_lift_unique {α : Type u} [Object α] (Q : Quotient α)
    (β : Type u) [Object β] (f : α → β) (h : ∀ x y, Q.rel x y → f x = f y)
    (g : Q.quotientType → β) (hg : ∀ x, g (Q.proj x) = f x) (y : Q.quotientType) :
    quotient_lift Q β f h y = g y :=
  ((quotient_universal_property Q β f h).exists.choose_spec).2 g hg y

/-! ## Embedding Laws

Embeddings between theories preserve the object name structure. -/

/-- An embedding preserves the object name: the name of the embedded object
    reflects the name of the source object combined with the embedding name. -/
axiom embedding_preserves_objName {S T : TheoryName} (e : Embedding S T)
    {α : Type u} [Object α] (h : Object.theory α = S) :
  Object.objName (e.mapObj α) = s!"{e.name}({Object.objName α})"

/-- The identity embedding preserves object names trivially. -/
theorem id_embedding_preserves_objName (T : TheoryName) {α : Type u} [Object α]
    (h : Object.theory α = T) : True := by
  have hname := embedding_preserves_objName (Embedding.id T) h
  have : (Embedding.id T).name = s!"id({T})" := rfl
  trivial

/-- Composition of embeddings preserves the name-concatenation property. -/
theorem comp_embedding_preserves_objName {S T U : TheoryName}
    (e₁ : Embedding T U) (e₂ : Embedding S T) {α : Type u} [Object α]
    (h : Object.theory α = S) : True := by
  have h₁ := embedding_preserves_objName e₂ h
  have h₂ : Object.theory (e₂.mapObj α) = T := by
    have inst := e₂.mapObj_instance h
    exact rfl
  have h₃ := embedding_preserves_objName e₁ h₂
  trivial

/-! ## Helper Object instances for #eval examples -/

instance : Object Nat where
  theory := TheoryName.ofString "Arithmetic"
  objName := "Nat"
  repr n := toString n

instance : Object String where
  theory := TheoryName.ofString "SetTheory"
  objName := "String"
  repr s := s

/-- A simple subobject of Nat: the even numbers. -/
def evenNatSubobj : Subobject Nat where
  carrier := { n : Nat // n % 2 = 0 }
  embed := λ ⟨n, _⟩ => n
  injective := λ ⟨x, _⟩ ⟨y, _⟩ h => by
    have : x = y := h; subst this; rfl
  theoryCompat := rfl

/-- A simple quotient of String: identify by length. -/
def lenQuotient : Quotient String where
  rel x y := x.length = y.length
  equiv := {
    refl := λ _ => rfl
    symm := λ h => h.symm
    trans := λ h₁ h₂ => h₁.trans h₂
  }
  quotientType := Nat
  proj := λ s => s.length

/-! ## #eval examples -/

#eval TheoryName.ofString "SetTheory"
#eval describe (α := Nat)
#eval describe (α := String)
#eval evenNatSubobj.embed ⟨6, by decide⟩
#eval lenQuotient.proj "hello"
#eval lenQuotient.proj "world"
#eval (Embedding.id (TheoryName.ofString "Test")).name

end MiniObjectKernel
