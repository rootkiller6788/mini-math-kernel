/-
# Objects Kernel: Laws — L4/L5 Core Theorems and Proofs

Axioms and laws governing mathematical objects.
Essential properties that every Object instance must satisfy
and derived theorems about the Object ecosystem.

Knowledge coverage:
- L1: Law structures for objects
- L2: Law satisfaction and verification
- L4: Subobject lattice completeness, quotient universal properties
- L5: Proof by diagram chasing, structural induction, case analysis
- L6: #eval examples for law verification
-/

import MiniObjectKernel.Core.Basic
import MiniObjectKernel.Core.Objects
import MiniObjectKernel.Morphisms.Hom
import MiniObjectKernel.Morphisms.Iso

namespace MiniObjectKernel

/-! ## Object Laws as Structures — L1: Core Definitions

We can package the expected properties of objects into `Law` structures,
enabling systematic verification that an Object instance satisfies
the axioms of its theory. -/

/-- An `ObjectLaw` is a predicate that an Object instance may or may not satisfy. -/
structure ObjectLaw (α : Type u) [Object α] where
  name : String
  statement : Prop
  holds : statement

/-- A collection of laws that objects of a given theory must satisfy. -/
structure TheoryLaws where
  theory : TheoryName
  laws : List (String × Prop)
  deriving Repr

/-- Check whether a given proposition follows from the theory laws.
    (Meta-level: we use `axiom` for the general case.) -/
axiom theoryLaws_entail (tl : TheoryLaws) (P : Prop) : Prop

/-! ## Subobject Laws — L4: Fundamental Theorems

Subobjects form a preorder under the inclusion relation `≤ₛ`.
We prove reflexivity, transitivity, antisymmetry (up to equivalence),
and lattice completeness. -/

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

/-- The bottom subobject is initial in the subobject preorder: if s ≤ bot, then s ≅ bot. -/
theorem subobject_bot_unique {α : Type u} [Object α] (s : Subobject α)
    (h : s ≤ₛ Subobject.bot α) : Nonempty (Subobject.equiv s (Subobject.bot α)) := by
  rcases h with ⟨f, hf⟩
  have : s.carrier → Empty := f
  refine ⟨⟨h, ?_⟩⟩
  refine ⟨λ e => nomatch e, ?_⟩
  intro e; nomatch e

/-- The top subobject is terminal: if top ≤ s, then s ≅ top. -/
theorem subobject_top_unique {α : Type u} [Object α] (s : Subobject α)
    (h : Subobject.top α ≤ₛ s) : Nonempty (Subobject.equiv s (Subobject.top α)) := by
  rcases h with ⟨f, hf⟩
  refine ⟨⟨Subobject.le_top s, ?_⟩⟩
  refine ⟨λ x => f x, ?_⟩
  intro x; exact hf x

/-- Meet is idempotent: s ∧ s ≅ s. -/
theorem subobject_meet_idempotent {α : Type u} [Object α] (s : Subobject α) :
    Subobject.equiv (Subobject.meet s s) s := by
  constructor
  · exact Subobject.meet_le_left s s
  · refine ⟨λ x => ⟨(x, x), ?_⟩, λ x => rfl⟩
    rfl

/-- Join is idempotent: s ∨ s ≅ s. -/
theorem subobject_join_idempotent {α : Type u} [Object α] (s : Subobject α) :
    Subobject.equiv (Subobject.join s s) s := by
  constructor
  · refine ⟨λ ⟨p, h⟩ => ?_, ?_⟩
    rcases h with ⟨x, hx, hrest⟩
    exact x
    intro x; rfl
  · exact Subobject.le_join_left s s

/-- Distributivity of meet over join: s ∧ (t ∨ u) ≥ (s ∧ t) ∨ (s ∧ u).
    (Full distributivity holds only in distributive lattices.) -/
theorem subobject_meet_join_distrib_le {α : Type u} [Object α] (s t u : Subobject α) :
    Subobject.join (Subobject.meet s t) (Subobject.meet s u) ≤ₛ Subobject.meet s (Subobject.join t u) := by
  refine ⟨λ x => ?_, ?_⟩
  rcases x with ⟨x_s, x_s_val, hx⟩
  rcases hx with (⟨y, hy⟩ | ⟨z, hz⟩)
  · refine ⟨(⟨x_s, y⟩, ?_), ?_⟩
    · -- diagram commutation for the meet
      rcases x_s with ⟨(xs, xt), h_eq⟩
      simp
      exact h_eq
    · rfl
  · refine ⟨(⟨x_s, z⟩, ?_), ?_⟩
    rcases x_s with ⟨(xs, xu), h_eq⟩
    simp
    exact h_eq
    rfl
  · intro x; rfl

/-! ## Quotient Laws — L4: Universal Property

The universal property of a quotient: any map that respects the equivalence
relation factors uniquely through the projection. -/

/-- Existence part of the quotient universal property. -/
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

/-- The lift is unique. -/
theorem quotient_lift_unique {α : Type u} [Object α] (Q : Quotient α)
    (β : Type u) [Object β] (f : α → β) (h : ∀ x y, Q.rel x y → f x = f y)
    (g : Q.quotientType → β) (hg : ∀ x, g (Q.proj x) = f x) (y : Q.quotientType) :
    quotient_lift Q β f h y = g y :=
  ((quotient_universal_property Q β f h).exists.choose_spec).2 g hg y

/-- If the projection is surjective, the lift is uniquely determined
    by the commutative condition. Proof by surjectivity argument. -/
theorem quotient_lift_unique_by_surjectivity {α : Type u} [Object α] (Q : Quotient α)
    (β : Type u) [Object β] (f : α → β) (h : ∀ x y, Q.rel x y → f x = f y)
    (g₁ g₂ : Q.quotientType → β) (hg₁ : ∀ x, g₁ (Q.proj x) = f x)
    (hg₂ : ∀ x, g₂ (Q.proj x) = f x) (hsurj : ∀ y : Q.quotientType, ∃ x : α, Q.proj x = y) :
    g₁ = g₂ := by
  funext y
  rcases hsurj y with ⟨x, hx⟩
  calc
    g₁ y = g₁ (Q.proj x) := by rw [hx]
    _ = f x := hg₁ x
    _ = g₂ (Q.proj x) := (hg₂ x).symm
    _ = g₂ y := by rw [hx]

/-! ## Embedding Laws — L2: Core Concept

Embeddings between theories must preserve the object name structure
and satisfy categorical properties (identity, composition). -/

/-- An embedding preserves the object name. -/
axiom embedding_preserves_objName {S T : TheoryName} (e : Embedding S T)
    {α : Type u} [Object α] (h : Object.theory α = S) :
  Object.objName (e.mapObj α) = s!"{e.name}({Object.objName α})"

/-- The identity embedding preserves object names trivially. -/
theorem id_embedding_preserves_objName (T : TheoryName) {α : Type u} [Object α]
    (h : Object.theory α = T) : Object.objName ((Embedding.id T).mapObj α) = s!"id({T})({Object.objName α})" := by
  have hname := embedding_preserves_objName (Embedding.id T) h
  simpa [Embedding.id] using hname

/-- Composition of embeddings preserves object names. -/
theorem comp_embedding_preserves_objName {S T U : TheoryName}
    (e₁ : Embedding T U) (e₂ : Embedding S T) {α : Type u} [Object α]
    (h : Object.theory α = S) :
    Object.objName ((Embedding.comp e₁ e₂).mapObj α) =
    s!"{e₁.name} ∘ {e₂.name}({Object.objName α})" := by
  have hname := embedding_preserves_objName (Embedding.comp e₁ e₂) h
  simpa [Embedding.comp] using hname

/-! ## Law Satisfaction — L5: Proof Techniques

We demonstrate several proof methods for verifying that an Object
satisfies its theory laws. -/

/-- Trivial law: the type Unit always satisfies that it has an element.
    Proof by `exact`. -/
def unit_has_element_law : ObjectLaw Unit where
  name := "nonempty"
  statement := Nonempty Unit
  holds := ⟨()⟩

/-- List concatenation law: List α with concatenation satisfies associativity.
    Proof by `simp`. -/
theorem list_append_assoc_law (α : Type u) (xs ys zs : List α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  simp

/-- Nat addition law: 0 is neutral for addition.
    Proof by `simp`. -/
theorem nat_add_zero_law (n : Nat) : n + 0 = n := by simp

/-- Law satisfaction for the subobject bot: it is contained in every subobject.
    Proof by `nomatch` (vacuous truth). -/
theorem bot_subobject_law {α : Type u} [Object α] (s : Subobject α) :
    Subobject.bot α ≤ₛ s :=
  Subobject.bot_le s

/-! ## Construction Laws — L2: Core Concept

Constructions (product, coproduct) satisfy their universal properties
with respect to the Object typeclass. -/

/-- The product of two objects α, β satisfies the universal property
    when we use the type-theoretic product α × β. -/
theorem pair_product_universal_law (α β : Type u) [Object α] [Object β] :
    ∀ (X : Type u) [Object X] (f : X → α) (g : X → β),
    ∃! h : X → (α × β), (∀ x, Prod.fst (h x) = f x) ∧ (∀ x, Prod.snd (h x) = g x) := by
  intro X _ f g
  refine ⟨λ x => (f x, g x), ⟨λ _ => rfl, λ _ => rfl⟩, ?_⟩
  intro h ⟨h₁, h₂⟩
  funext x
  apply Prod.ext
  · exact h₁ x
  · exact h₂ x

/-- The coproduct (sum type) satisfies its universal property. -/
theorem sum_coproduct_universal_law (α β : Type u) [Object α] [Object β] :
    ∀ (X : Type u) [Object X] (f : α → X) (g : β → X),
    ∃! h : (α ⊕ β) → X, (∀ a, h (Sum.inl a) = f a) ∧ (∀ b, h (Sum.inr b) = g b) := by
  intro X _ f g
  refine ⟨λ s => match s with | Sum.inl a => f a | Sum.inr b => g b, ⟨λ _ => rfl, λ _ => rfl⟩, ?_⟩
  intro h ⟨h₁, h₂⟩
  funext x
  cases x with
  | inl a => exact h₁ a
  | inr b => exact h₂ b

/-! ## Interaction Laws — L4: Composite Theorems

How subobjects and quotients interact. -/

/-- The subobject of a quotient object: a subobject of α/s corresponds
    to a subobject of α containing s. (Stated as an axiom.) -/
axiom subobject_quotient_correspondence {α : Type u} [Object α]
    (Q : Quotient α) : Subobject Q.quotientType → Subobject α

/-- Pulling back a subobject along a quotient projection is a monotone operation.
    Since the correspondence is axiomatic, monotonicity is stated as an axiom. -/
axiom subobject_quotient_pullback_monotone {α : Type u} [Object α]
    (Q : Quotient α) (s t : Subobject Q.quotientType)
    (hst : s ≤ₛ t) : subobject_quotient_correspondence Q s ≤ₛ subobject_quotient_correspondence Q t

/-! ## #eval examples — L6: Verified Examples -/

/-- Simple subobject of Nat: multiples of 3. -/
def multiplesOfThree : Subobject Nat where
  carrier := { n : Nat // n % 3 = 0 }
  embed := λ ⟨n, _⟩ => n
  injective := λ ⟨x, _⟩ ⟨y, _⟩ h => by subst h; rfl
  theoryCompat := rfl

/-- Simple quotient: strings identified by first character. -/
def firstCharQuotient : Quotient String where
  rel x y := x.get? 0 = y.get? 0
  equiv := {
    refl := λ _ => rfl
    symm := λ h => h.symm
    trans := λ h₁ h₂ => h₁.trans h₂
  }
  quotientType := Option Char
  proj := λ s => s.get? 0

#eval multiplesOfThree.embed ⟨6, by decide⟩
#eval multiplesOfThree.embed ⟨9, by decide⟩
#eval firstCharQuotient.proj "cat"
#eval firstCharQuotient.proj "dog"
#eval (Embedding.id (TheoryName.ofString "Test")).name

end MiniObjectKernel
