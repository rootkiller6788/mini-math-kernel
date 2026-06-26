/-
# Objects Kernel: Mathematical Objects

Defines the `Object` typeclass — the common interface for
every mathematical structure in the mini-everything-math ecosystem.
-/

namespace MiniObjectKernel

/-! ## Theory Name -/

structure TheoryName where
  segments : List String
  deriving BEq, Hashable, Repr, Inhabited

instance : ToString TheoryName where
  toString tn := String.intercalate "." tn.segments

def TheoryName.ofString (s : String) : TheoryName := { segments := s.splitOn "." }
def TheoryName.root : TheoryName := { segments := [] }
def TheoryName.extend (tn : TheoryName) (sub : String) : TheoryName :=
  { segments := tn.segments ++ [sub] }

/-! ## The Object Typeclass -/

class Object (α : Type u) where
  theory : TheoryName
  objName : String
  repr : α → String

export Object (theory objName repr)

def describe (α : Type u) [Object α] : String :=
  s!"[{theory α}] {objName α}"

end MiniObjectKernel
