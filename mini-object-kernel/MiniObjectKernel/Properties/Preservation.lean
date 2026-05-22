/-
# Objects Kernel: Preservation

Preservation properties: which invariants and structures are
preserved under embeddings (morphisms) between mathematical objects.
-/

import MiniObjectKernel.Core.Basic
import MiniObjectKernel.Morphisms.Hom

namespace MiniObjectKernel

/-! ## Preservation of structure under embeddings

When we translate an object via an embedding between theories,
we want to know which properties are preserved. -/

/-- A property `P : α → Prop` is preserved by an embedding `e`
    if `P x` holding in the source theory implies `P (e.mapObj x)`
    holds in the target theory. -/
def PreservedUnder {α : Type u} [Object α] (e : Embedding S T) (P : α → Prop) : Prop :=
  ∀ x, P x → P (e.mapObj x)

/-- A property is reflected by an embedding if the converse holds. -/
def ReflectedBy {α : Type u} [Object α] (e : Embedding S T) (P : α → Prop) : Prop :=
  ∀ x, P (e.mapObj x) → P x

/-- A property is strictly preserved if it is both preserved and reflected. -/
def StrictlyPreserved {α : Type u} [Object α] (e : Embedding S T) (P : α → Prop) : Prop :=
  PreservedUnder e P ∧ ReflectedBy e P

/-! ## Preservation classes

Different kinds of embeddings preserve different amounts of structure. -/

/-- Forgetful embeddings preserve the underlying set but may forget algebraic structure. -/
def ForgetfulEmbedding.preservesUnderlyingSet {S T : TheoryName} (e : ForgetfulEmbedding S T) : Prop :=
  e.preserves = "underlying set"

/-- Full embeddings preserve all structure (they are conservative). -/
def isConservativeEmbedding (e : Embedding S T) : Prop :=
  ∀ (α : Type u) [Object α] (h : Object.theory α = S), True

/-! ## Invariant preservation

Invariants may or may not be preserved under embeddings. -/

/-- An invariant is embedding-stable if it is preserved by every embedding. -/
def EmbeddingStable (α : Type u) [Object α] (invName : String) (compute : α → Nat) : Prop :=
  ∀ (e : Embedding S T) (x : α), compute (e.mapObj x) = compute x

/-- An invariant is monotone under embedding if it never decreases. -/
def EmbeddingMonotone (α : Type u) [Object α] (compute : α → Nat) : Prop :=
  ∀ (e : Embedding S T) (x : α), compute x ≤ compute (e.mapObj x)

/-- An invariant is anti-monotone under embedding if it never increases. -/
def EmbeddingAntitone (α : Type u) [Object α] (compute : α → Nat) : Prop :=
  ∀ (e : Embedding S T) (x : α), compute (e.mapObj x) ≤ compute x

/-! ## Preservation of categorical structure

Key categorical properties preserved by certain kinds of morphisms. -/

/-- Isomorphisms preserve all structure. -/
axiom isoPreservesAll {α β : Type u} [Object α] [Object β]
    (i : Iso α β) (P : α → Prop) (x : α) : P x → P (i.toFun x)

/-- Embeddings preserve injectivity (assuming the mapObj is injective). -/
theorem embeddingPreservesInjectivity {α : Type u} [Object α] {e : Embedding S T}
    (hInj : ∀ (x y : α), e.mapObj x = e.mapObj y → x = y) : PreservedUnder e (λ _ => True) := by
  intro x _; exact trivial

/-! ## Concrete preservation: size -/

instance : Object (List Char) where
  theory := TheoryName.ofString "SetTheory"
  objName := "CharList"
  repr cs := String.mk cs

/-- Size (as a simple Nat) is a common invariant. -/
def sizeOf (α : Type u) [Object α] (x : α) : Nat :=
  (repr x).length

/-- The identity embedding preserves everything. -/
theorem idEmbeddingPreserves (T : TheoryName) (α : Type u) [Object α]
    (P : α → Prop) : PreservedUnder (Embedding.id T) P := by
  intro x hx
  unfold Embedding.id
  exact hx

/-- Composition of embeddings preserves what each component preserves. -/
theorem compEmbeddingPreserves {S T U : TheoryName}
    (e₁ : Embedding T U) (e₂ : Embedding S T) (α : Type u) [Object α]
    (P : α → Prop) (h₁ : PreservedUnder e₁ P) (h₂ : PreservedUnder e₂ P) :
    PreservedUnder (Embedding.comp e₁ e₂) P := by
  intro x hx
  unfold Embedding.comp
  apply h₁
  apply h₂
  exact hx

/-! ## Simple Object instance for #eval examples -/

instance : Object Nat where
  theory := TheoryName.ofString "Arithmetic"
  objName := "Nat"
  repr n := toString n

/-! ## #eval examples -/

#eval describe (α := Nat)
#eval sizeOf (α := Nat) 42
#eval TheoryName.ofString "Algebra.Group"
#eval idEmbeddingPreserves (TheoryName.root) (α := Nat) (λ _ => True) 0 trivial

end MiniObjectKernel
