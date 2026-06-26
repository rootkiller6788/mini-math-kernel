/-
# Objects Kernel: Mathematical Objects — L1 Core Definitions

Defines the `Object` typeclass — the common interface for
every mathematical structure in the mini-everything-math ecosystem.
-/

namespace MiniObjectKernel

/-! ## Theory Name — L1: Core Definition

A `TheoryName` is a hierarchical dotted-path identifier for
mathematical theories (e.g. "Algebra.GroupTheory.AbelianGroup").
Segments are ordered from most general to most specific. -/

structure TheoryName where
  segments : List String
  deriving BEq, Hashable, Repr, Inhabited

instance : ToString TheoryName where
  toString tn := String.intercalate "." tn.segments

/-- Parse a dotted string into a TheoryName. -/
def TheoryName.ofString (s : String) : TheoryName := { segments := s.splitOn "." }

/-- The root (empty) theory name. -/
def TheoryName.root : TheoryName := { segments := [] }

/-- Extend a theory name with a sub-theory segment. -/
def TheoryName.extend (tn : TheoryName) (sub : String) : TheoryName :=
  { segments := tn.segments ++ [sub] }

/-- The depth (number of segments) of a theory name. -/
def TheoryName.depth (tn : TheoryName) : Nat := tn.segments.length

/-- Whether `tn` is a prefix of `tn'` (i.e., `tn'` extends `tn`).
    Note: recursion on the segments lists. -/
def TheoryName.isPrefixOf (tn tn' : TheoryName) : Bool :=
  let rec go (l₁ l₂ : List String) : Bool :=
    match l₁, l₂ with
    | [], _ => true
    | _::_, [] => false
    | s₁::ss₁, s₂::ss₂ => (s₁ == s₂) && go ss₁ ss₂
  termination_by l₁.length
  decreasing_by
    simp [InvImage, WellFoundedRelation.rel]
    apply Nat.lt_succ_self
  go tn.segments tn'.segments

/-- Whether two theory names share a common prefix. -/
def TheoryName.commonPrefix (tn₁ tn₂ : TheoryName) : TheoryName :=
  { segments := aux tn₁.segments tn₂.segments }
where
  aux : List String → List String → List String
    | [], _ => []
    | _, [] => []
    | s₁::ss₁, s₂::ss₂ => if s₁ == s₂ then s₁ :: aux ss₁ ss₂ else []

/-- The parent theory (removing the last segment). -/
def TheoryName.parent (tn : TheoryName) : TheoryName :=
  match tn.segments with
  | [] => { segments := [] }
  | _ :: [] => { segments := [] }
  | xs => { segments := xs.dropLast }

/-- Lexicographic comparison of theory names. -/
def TheoryName.lt (tn₁ tn₂ : TheoryName) : Bool := tn₁.segments < tn₂.segments

/-- Number of segments in the longest common prefix. -/
def TheoryName.commonPrefixLength (tn₁ tn₂ : TheoryName) : Nat :=
  (TheoryName.commonPrefix tn₁ tn₂).depth

/-! ## The Object Typeclass — L1: Core Definition

An `Object` is any type with an associated theory, name, and
human-readable representation. This is the foundational typeclass
for all mathematical structures in the ecosystem. -/

class Object (α : Type) where
  theory : TheoryName
  objName : String
  repr : α → String

export Object (theory objName repr)

/-- Produce a description string for a type with an Object instance. -/
def describe (α : Type) [Object α] : String :=
  s!"[{theory α}] {objName α}"

/-- Get the fully qualified name of an object. -/
def Object.qualifiedName (α : Type) [Object α] : String :=
  s!"{theory α}.{objName α}"

/-- An object is "primitive" if it belongs to a root-level theory. -/
def Object.isPrimitive (α : Type) [Object α] : Bool :=
  (theory α).depth == 0

/-- An object is "derived" if it belongs to a multi-segment theory. -/
def Object.isDerived (α : Type) [Object α] : Bool :=
  (theory α).depth > 1

/-! ## Canonical Object Instances — L6: Standard Examples -/

instance : Object Nat where
  theory := TheoryName.ofString "SetTheory"
  objName := "ℕ"
  repr n := toString n

instance : Object String where
  theory := TheoryName.ofString "SetTheory"
  objName := "String"
  repr s := s

instance : Object Char where
  theory := TheoryName.ofString "SetTheory"
  objName := "Char"
  repr c := toString c

instance : Object Bool where
  theory := TheoryName.ofString "SetTheory"
  objName := "𝔹"
  repr b := toString b

instance : Object Empty where
  theory := TheoryName.root
  objName := "∅"
  repr e := nomatch e

instance : Object Unit where
  theory := TheoryName.root
  objName := "∗"
  repr _ := "∗"

instance : Object (List Nat) where
  theory := TheoryName.ofString "SetTheory"
  objName := "List(ℕ)"
  repr xs := toString xs

instance : Object (List String) where
  theory := TheoryName.ofString "SetTheory"
  objName := "List(String)"
  repr xs := toString xs

instance : Object (List Char) where
  theory := TheoryName.ofString "SetTheory"
  objName := "List(Char)"
  repr cs := String.mk cs

/-! ## #eval examples — L6: Verified Examples -/

#eval TheoryName.ofString "SetTheory"
#eval TheoryName.ofString "Algebra.GroupTheory"
#eval describe (α := Nat)
#eval describe (α := String)
#eval describe (α := Bool)
#eval Object.qualifiedName (α := Nat)
#eval TheoryName.commonPrefix (TheoryName.ofString "Algebra.Group.Abelian")
    (TheoryName.ofString "Algebra.Ring.Commutative")
#eval TheoryName.depth (TheoryName.ofString "Algebra.Group.Abelian")

end MiniObjectKernel
