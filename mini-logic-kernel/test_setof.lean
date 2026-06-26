
namespace Test
def Set (α : Type) := α → Prop
def Set.setOf {α : Type} (p : α → Prop) : Set α := p
#check {x : Nat | x = 0}
end Test

