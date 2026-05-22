/-
# Constructions Kernel: Product and Coproduct

Concrete implementations of product and coproduct constructions.
-/

import MiniConstructionKernel.Core.Basic
import MiniConstructionKernel.Constructions.Universal

namespace MiniConstructionKernel

structure Product (α : Type u) (β : α → Type v) where
  fst : α
  snd : β fst

abbrev BinProduct (α β : Type u) := Product α fun _ => β
infixr:70 " ×ₖ " => BinProduct

def Product.mk (a : α) (b : β a) : Product α β := { fst := a, snd := b }
def Product.fst' (p : Product α β) : α := p.fst
def Product.snd' (p : Product α β) : β p.fst := p.snd

def binProductUniversal (α β : Type u) [Object α] [Object β] :
    ProductUniversal α β (BinProduct α β) where
  fst p := p.fst
  snd p := p.snd
  pair p q x := { fst := p x, snd := q x }
  pair_fst p q x := rfl
  pair_snd p q x := rfl
  unique p q h hFst hSnd x := by
    cases h x; constructor <;> assumption

inductive Coproduct (α β : Type u) : Type u where
  | inl : α → Coproduct α β
  | inr : β → Coproduct α β

infixr:60 " +ₖ " => Coproduct

def binCoproductUniversal (α β : Type u) [Object α] [Object β] :
    CoproductUniversal α β (Coproduct α β) where
  inl := Coproduct.inl
  inr := Coproduct.inr
  cases f g
    | Coproduct.inl a => f a
    | Coproduct.inr b => g b
  cases_inl f g a := rfl
  cases_inr f g b := rfl
  unique f g h hInl hInr c :=
    match c with
    | Coproduct.inl a => hInl a
    | Coproduct.inr b => hInr b

def buildProduct (α β : Type u) [Object α] [Object β] :
    ProductConstruction (Fin 2) fun
      | 0 => α
      | 1 => β :=
  { carrier := BinProduct α β
    proj := fun
      | 0 => Product.fst'
      | 1 => Product.snd'
    name := s!"Product({describe α}, {describe β})"
  }

def buildCoproduct (α β : Type u) [Object α] [Object β] :
    CoproductConstruction (Fin 2) fun
      | 0 => α
      | 1 => β :=
  { carrier := Coproduct α β
    inj := fun
      | 0 => Coproduct.inl
      | 1 => Coproduct.inr
    name := s!"Coproduct({describe α}, {describe β})"
  }

end MiniConstructionKernel
