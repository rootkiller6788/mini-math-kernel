/-
# Constructions Kernel: Basic Constructions

Defines the `Construction` type — the common interface for building
new mathematical objects from existing ones.
-/

import MiniObjectKernel.Core.Basic

namespace MiniConstructionKernel

structure Construction (ι : Type u) (α : ι → Type v) (β : Type v) where
  build : β
  [obj : Object β]
  name : String

structure ProductConstruction (ι : Type u) (α : ι → Type v) where
  carrier : Type v
  [obj : Object carrier]
  proj : (i : ι) → carrier → α i
  name : String

def ProductConstruction.binary (α β : Type u) [Object α] [Object β] : Type :=
  ProductConstruction (Fin 2) fun
    | 0 => α
    | 1 => β

structure CoproductConstruction (ι : Type u) (α : ι → Type v) where
  carrier : Type v
  [obj : Object carrier]
  inj : (i : ι) → α i → carrier
  name : String

def CoproductConstruction.binary (α β : Type u) [Object α] [Object β] : Type :=
  CoproductConstruction (Fin 2) fun
    | 0 => α
    | 1 => β

structure SubConstruction (α : Type u) [Object α] where
  pred : α → Prop
  carrier : Type u := { x : α // pred x }
  [obj : Object carrier]
  inclusion : carrier → α := Subtype.val
  name : String

structure QuotientConstruction (α : Type u) [Object α] where
  rel : α → α → Prop
  isEquiv : Equivalence rel
  carrier : Type u := Quot rel
  [obj : Object carrier]
  proj : α → carrier := Quot.mk rel
  name : String

structure FunctionSpaceConstruction (α β : Type u) [Object α] [Object β] where
  carrier : Type u := α → β
  [obj : Object carrier]
  name : String

def compose {α β γ : Type u} [Object α] [Object β] [Object γ]
    (c2 : Construction Unit (fun _ => β) γ) (c1 : Construction Unit (fun _ => α) β) :
    Construction Unit (fun _ => α) γ :=
  { build := c2.build
    name := s!"{c2.name} ∘ {c1.name}"
  }

end MiniConstructionKernel
