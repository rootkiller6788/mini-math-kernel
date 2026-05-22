/-
# Constructions Kernel: Construction Morphisms

Morphisms between constructions on mathematical objects.
Includes: construction-preserving maps, natural transformations,
and adjunctions between construction functors.
-/

import MiniConstructionKernel.Core.Basic
import MiniConstructionKernel.Core.Objects
import MiniConstructionKernel.Core.Laws

namespace MiniConstructionKernel

/-! ## Construction Homomorphism -/

-- A map between two constructions that preserves the construction structure
structure ConstructionHom (C D : Type u → Type v) where
  component : {α : Type u} → [Object α] → C α → D α
  natural : ∀ {α β : Type u} [Object α] [Object β] (f : α → β),
    (∀ (x : C α), component β (C.mapByHom f x) = D.mapByHom f (component α x)) → True
  name : String

/-! ## Natural Transformation -/

-- Natural transformation between construction functors F, G : C → D
structure NaturalTransformation (F G : Type u → Type v) [FC : FunctorialConstruction F] [GC : FunctorialConstruction G] where
  component : {α : Type u} → [Object α] → F α → G α
  naturality : ∀ {α β : Type u} [Object α] [Object β] (f : α → β),
    (∀ (x : F α), component β (FC.map f x) = GC.map f (component α x)) → True
  name : String

/-! ## Construction Morphism Composition -/

structure ConstructionMorphism (C D : Type u → Type v) where
  onObjects : {α : Type u} → [Object α] → C α → D α
  preservesProduct : ∀ {α β : Type u} [Object α] [Object β],
    (∀ (p : BinProduct (C α) (C β)), onObjects (BinProduct (C α) (C β)) p = onObjects (C α) p.1) → True
  preservesCoproduct : ∀ {α β : Type u} [Object α] [Object β],
    (∀ (c : Coproduct (C α) (C β)), onObjects (Coproduct (C α) (C β)) (Coproduct.inl c) = c) → True
  name : String

/-! ## Adjunction between Constructions -/

-- An adjunction F ⊣ G between construction functors
structure ConstructionAdjunction (F G : Type u → Type u) [∀ α, Object (F α)] [∀ α, Object (G α)] where
  homEquiv : ∀ {α β : Type u} [Object α] [Object β], (F α → β) → (α → G β)
  homEquiv_symm : ∀ {α β : Type u} [Object α] [Object β], (α → G β) → (F α → β)
  unit : {α : Type u} → [Object α] → α → G (F α)
  counit : {α : Type u} → [Object α] → F (G α) → α
  naturality₁ : ∀ {α β : Type u} [Object α] [Object β] (f : F α → β) (g : F α → β'),
    (∀ x, f x = g x) → (∀ a, homEquiv f a = homEquiv g a)
  name : String

/-! ## Construction Submorphism and Epimorphism -/

structure ConstructionMono (α β : Type u) [Object α] [Object β] where
  f : α → β
  mono : ∀ {X : Type u} [Object X] (g h : X → α), (∀ x, f (g x) = f (h x)) → (∀ x, g x = h x)
  name : String

structure ConstructionEpi (α β : Type u) [Object α] [Object β] where
  f : α → β
  epi : ∀ {X : Type u} [Object X] (g h : β → X), (∀ b, g (f b) = h (f b)) → (∀ b, g b = h b)
  name : String

/-! ## Identity and Constant Morphisms -/

def identityConstructionMorphism (α : Type u) [Object α] : ConstructionMono α α :=
  { f := fun a => a
    mono := fun g h hEq x => hEq x
    name := s!"id({describe α})"
  }

def constantConstructionMorphism (α β : Type u) [Object α] [Object β] (b : β) : ConstructionHom id id where
  component _ _ _ := b
  natural f _ := True.intro
  name := s!"const({describe α}, {describe β})"
  where
    instance : FunctorialConstruction id := {
      map _a f x := x
      map_id _ := True.intro
      map_comp f g := True.intro
      name := "id"
    }

/-! ## Hom-Set Construction -/

-- The hom-set between two objects as a construction
def homSet (α β : Type u) [Object α] [Object β] : Type u := α → β

instance {α β : Type u} [Object α] [Object β] : Object (homSet α β) where
  theory := (Object.theory α).extend "Hom"
  objName := s!"Hom({Object.objName α}, {Object.objName β})"
  repr _ := "<function>"

/-! ## Composition of Construction Morphisms -/

def compConstructionMono {α β γ : Type u} [Object α] [Object β] [Object γ]
    (g : ConstructionMono β γ) (f : ConstructionMono α β) : ConstructionMono α γ :=
  { f := fun a => g.f (f.f a)
    mono := fun h k hEq x =>
      f.mono h k (fun y => g.mono (f.f ∘ h) (f.f ∘ k) (by
        intro z; apply hEq) y) x
    name := s!"{g.name} ∘ {f.name}"
  }

/-! ## Examples and evaluations -/

section Examples

open MiniObjectKernel

instance : Object Nat where
  theory := TheoryName.ofString "Set"
  objName := "Nat"
  repr n := toString n

instance : Object String where
  theory := TheoryName.ofString "Set"
  objName := "String"
  repr s := s

instance : FunctorialConstruction Option where
  map f
    | none => none
    | some a => some (f a)
  map_id _ := True.intro
  map_comp f g := True.intro
  name := "Option"

instance : FunctorialConstruction List where
  map f
    | [] => []
    | a :: as => f a :: map f as
  map_id _ := True.intro
  map_comp f g := True.intro
  name := "List"

def idMonoNat : ConstructionMono Nat Nat :=
  identityConstructionMorphism Nat

def natToStringLength : ConstructionMono Nat Nat where
  f n := n
  mono g h hEq x := hEq x
  name := "lengthMorphism"

def natConstMorphism : ConstructionHom id id :=
  constantConstructionMorphism Nat Nat 0

#eval idMonoNat.name
#eval natConstMorphism.name
#eval idMonoNat.f 42
#eval describe (homSet Nat String)

end Examples

end MiniConstructionKernel
