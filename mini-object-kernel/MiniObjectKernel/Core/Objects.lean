/-
# Objects Kernel: Subobjects and Quotients

Subobject and quotient constructions for mathematical objects.
-/

import MiniObjectKernel.Core.Basic

namespace MiniObjectKernel

/-! ## Subobject -/

structure Subobject (α : Type u) [Object α] where
  carrier : Type u
  [obj : Object carrier]
  embed : carrier → α
  injective : ∀ x y, embed x = embed y → x = y
  theoryCompat : obj.theory = Object.theory α

structure SubobjectPredicate (α : Type u) [Object α] where
  pred : α → Prop
  nonempty : ∃ x, pred x

/-! ## Quotient -/

structure Quotient (α : Type u) [Object α] where
  rel : α → α → Prop
  equiv : Equivalence rel
  quotientType : Type u
  [quotObj : Object quotientType]
  proj : α → quotientType

end MiniObjectKernel
