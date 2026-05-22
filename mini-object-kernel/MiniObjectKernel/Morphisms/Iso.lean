/-
# Objects Kernel: Isomorphisms

Isomorphism structure and reasoning for mathematical objects.
-/

import MiniObjectKernel.Core.Basic

namespace MiniObjectKernel

abbrev ObjEq (α : Type u) (x y : α) : Prop := x = y

structure Iso (α β : Type u) [Object α] [Object β] where
  toFun    : α → β
  invFun   : β → α
  leftInv  : ∀ x, invFun (toFun x) = x
  rightInv : ∀ y, toFun (invFun y) = y

def congrArg {α β : Type u} {a b : α} (f : α → β) (h : a = b) : f a = f b := h ▸ rfl

def Iso.toEq {α β : Type u} [Object α] [Object β] (i : Iso α β) (x y : α) :
    x = y ↔ i.toFun x = i.toFun y :=
  ⟨congrArg i.toFun, fun h =>
    calc
      x = i.invFun (i.toFun x) := (i.leftInv x).symm
      _ = i.invFun (i.toFun y) := congrArg i.invFun h
      _ = y := i.leftInv y
  ⟩

end MiniObjectKernel
