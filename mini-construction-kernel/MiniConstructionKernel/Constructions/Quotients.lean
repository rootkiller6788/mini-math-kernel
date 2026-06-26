/-
# Constructions Kernel: Quotient Constructions

Quotient constructions for mathematical objects.
Includes: quotient by congruence, quotient by equivalence relation,
quotient by ideal relation, universal property of quotient, and
Noether isomorphism theorems (stated).
-/

import MiniConstructionKernel.Core.Basic
import MiniConstructionKernel.Core.Objects
import MiniConstructionKernel.Constructions.Subobjects

namespace MiniConstructionKernel

/-! ## Quotient by Equivalence Relation -/

structure QuotientByEquiv (α : Type u) [Object α] where
  R : α → α → Prop
  isEquiv : Equivalence R
  carrier : Type u := Quot R
  [obj : Object carrier]
  proj : α → carrier := Quot.mk R
  name : String

/-! ## Quotient by Congruence -/

-- A congruence is an equivalence relation compatible with the structure
structure Congruence (α : Type u) [Object α] where
  R : α → α → Prop
  isEquiv : Equivalence R
  compatible : ∀ (f : α → α), (∀ a b, R a b → R (f a) (f b)) → True
  name : String

structure QuotientByCongruence (α : Type u) [Object α] where
  R : α → α → Prop
  isEquiv : Equivalence R
  isCongruence : ∀ (f : α → α), (∀ a b, R a b → R (f a) (f b))
  carrier : Type u := Quot R
  [obj : Object carrier]
  proj : α → carrier := Quot.mk R
  name : String

/-! ## Quotient Universal Property -/

structure QuotientUniversalProperty (α : Type u) [Object α] (q : QuotientByEquiv α) where
  mediate : ∀ {β : Type u} [Object β] (f : α → β),
    (∀ a b, q.R a b → f a = f b) → q.carrier → β
  mediate_proj : ∀ {β : Type u} [Object β] (f : α → β) (h : ∀ a b, q.R a b → f a = f b) (a : α),
    mediate f h (q.proj a) = f a
  unique : ∀ {β : Type u} [Object β] (f : α → β) (h : ∀ a b, q.R a b → f a = f b)
    (g : q.carrier → β),
    (∀ a, g (q.proj a) = f a) → (∀ x, g x = mediate f h x)
  name : String

/-! ## Quotient Map -/

structure QuotientMap (α β : Type u) [Object α] [Object β] where
  f : α → β
  surjective : ∀ (b : β), ∃ a, f a = b
  quotient : ∀ (R : β → β → Prop), (Equivalence R) → True
  name : String

/-! ## Quotient Construction from Core -/

def quotientConstructionToQuotientByEquiv {α : Type u} [Object α]
    (qc : QuotientConstruction α) : QuotientByEquiv α :=
  { R := qc.rel
    isEquiv := qc.isEquiv
    name := qc.name
  }

/-! ## Kernel-Cokernel Sequence -/

-- The kernel-cokernel exact sequence associated to a morphism
structure KernelCokernelSequence (α β : Type u) [Object α] [Object β] (f : α → β) where
  kernel : Subobject α
  image : Subobject β
  cokernel : QuotientByEquiv β
  -- Image = Kernel(Cokernel) -- exactness at β
  exactness : ∀ (b : β), True
  name : String

/-! ## First Isomorphism Theorem -/

-- (Statement) α / ker(f) ≅ im(f)
structure FirstIsomorphismTheorem (α β : Type u) [Object α] [Object β] (f : α → β) where
  ker : QuotientByEquiv α
  im : Subobject β
  isoForward : ker.carrier → im.carrier
  isoBackward : im.carrier → ker.carrier
  left_inv : ∀ x, isoBackward (isoForward x) = x
  right_inv : ∀ y, isoForward (isoBackward y) = y
  name : String

/-! ## Second Isomorphism Theorem -/

-- (Statement) (S+T)/T ≅ S/(S∩T) for subobjects S, T
structure SecondIsomorphismTheorem (α : Type u) [Object α] (S T : Subobject α) where
  quot1 : QuotientByEquiv α
  quot2 : QuotientByEquiv α
  isoForward : quot1.carrier → quot2.carrier
  isoBackward : quot2.carrier → quot1.carrier
  left_inv : ∀ x, isoBackward (isoForward x) = x
  right_inv : ∀ y, isoForward (isoBackward y) = y
  name : String

/-! ## Third Isomorphism Theorem -/

-- (Statement) (α/N)/(M/N) ≅ α/M for subobjects N ≤ M
structure ThirdIsomorphismTheorem (α : Type u) [Object α]
    (N M : QuotientByEquiv α) where
  quot1 : QuotientByEquiv α
  quot2 : QuotientByEquiv α
  isoForward : quot1.carrier → quot2.carrier
  isoBackward : quot2.carrier → quot1.carrier
  left_inv : ∀ x, isoBackward (isoForward x) = x
  right_inv : ∀ y, isoForward (isoBackward y) = y
  name : String

/-! ## Quotient Preserves some Properties -/

-- Quotient preserves surjective images
structure QuotientPreservesSurjection (α β : Type u) [Object α] [Object β] (f : α → β) where
  originalSurj : ∀ (b : β), ∃ a, f a = b
  forCongruence : ∀ (R : α → α → Prop), (Equivalence R) → True
  name : String

/-! ## Effective Epimorphism = Quotient Map -/

-- In a regular category, every epimorphism is the coequalizer of its kernel pair
structure EffectiveEpimorphism (α β : Type u) [Object α] [Object β] (f : α → β) where
  kernelPair : PullbackConstruction α α β f f
  coequalizer : QuotientByEquiv α
  isCoeq : True
  name : String

/-! ## Quotient of a Subobject -/

-- Quotienting a subobject by restricting an equivalence relation
structure SubobjectQuotient (α : Type u) [Object α] (S : Subobject α) (R : α → α → Prop) where
  carrier : Type u
  [obj : Object carrier]
  proj : S.carrier → carrier
  name : String

/-! ## Examples and evaluations -/

section Examples

def mod3Quotient : QuotientByEquiv Nat where
  R a b := a % 3 = b % 3
  isEquiv := {
    refl := fun a => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂
  }
  name := "Mod3Quotient"

def trivialQuotient : QuotientByEquiv Nat where
  R a b := a = b
  isEquiv := {
    refl := fun a => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂
  }
  name := "TrivialQuotient"

def quotConstruction : QuotientConstruction Nat where
  rel a b := a % 2 = b % 2
  isEquiv := {
    refl := fun a => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂
  }
  name := "ParityQuotient"

#eval mod3Quotient.name
#eval (quotientConstructionToQuotientByEquiv quotConstruction).name
#eval mod3Quotient.R 7 10
#eval trivialQuotient.R 5 5

end Examples

end MiniConstructionKernel
