/-
# Objects Kernel: Classification Data

Data structures for classifying mathematical objects by their invariants.
-/

import MiniObjectKernel.Core.Basic
import MiniObjectKernel.Properties.Invariants

namespace MiniObjectKernel

/-! ## Classification schemes

A classification scheme assigns each object a "class" based on
its invariants. We model classification data as a map from
invariant-space to class labels. -/

/-- A classification class: a named category into which objects can be sorted. -/
structure ObjectClass where
  name : String
  description : String
  typicalExample : String
  deriving BEq, Hashable, Repr, Inhabited

/-- The classification data for an object is a list of
    (invariantName, value) pairs plus an assigned class. -/
structure ClassificationData (α : Type u) [Object α] where
  obj : α
  invariants : List (String × String)
  assignedClass : ObjectClass
  deriving Repr

/-- A classification rule maps invariant values to a class. -/
structure ClassificationRule where
  condition : String  -- pattern to match in invariant data
  outputClass : ObjectClass
  priority : Nat
  deriving Repr

/-- A classifier is a collection of rules applied in priority order. -/
structure Classifier where
  rules : List ClassificationRule
  defaultClass : ObjectClass
  deriving Repr

/-- Apply a classifier to invariant data, returning the assigned class. -/
def Classifier.classify (c : Classifier) (invariants : List (String × String)) : ObjectClass :=
  match c.rules.find? (λ r =>
    invariants.any (λ (k, v) => k == r.condition)) with
  | some rule => rule.outputClass
  | none => c.defaultClass

/-! ## Example invariant-value representation -/

/-- Represent an invariant value as a tagged union (for classification). -/
inductive InvariantValue where
  | natVal (n : Nat)
  | boolVal (b : Bool)
  | stringVal (s : String)
  | cardVal (c : Cardinality)
  deriving BEq, Repr, Inhabited

/-- A classification profile: a map from invariant names to values. -/
structure InvariantProfile where
  data : List (String × InvariantValue)
  deriving Repr

/-- Look up an invariant value by name in a profile. -/
def InvariantProfile.lookup (p : InvariantProfile) (name : String) : Option InvariantValue :=
  match p.data.find? (λ (n, _) => n == name) with
  | some (_, v) => some v
  | none => none

/-- Check if two profiles agree on all listed invariant names. -/
def InvariantProfile.agreeOn (p q : InvariantProfile) (names : List String) : Bool :=
  names.all (λ n => p.lookup n == q.lookup n)

/-! ## Classification by cardinality: the simplest classification scheme. -/

def classifyByCardinality (card : Cardinality) : ObjectClass :=
  match card with
  | Cardinality.finite 0 => { name := "Empty", description := "No elements", typicalExample := "Empty set" }
  | Cardinality.finite 1 => { name := "Singleton", description := "One element", typicalExample := "Unit type" }
  | Cardinality.finite n => { name := s!"Finite{n}", description := s!"{n} elements", typicalExample := s!"Set of {n} elements" }
  | Cardinality.infinite => { name := "CountablyInfinite", description := "Countably infinite", typicalExample := "Natural numbers" }
  | Cardinality.uncountable => { name := "Uncountable", description := "Uncountably infinite", typicalExample := "Real numbers" }

/-! ## Object instance for examples — uses canonical instances from Core.Basic -/

/-- Build a classification profile from a list. -/
def listProfile (xs : List String) : InvariantProfile :=
  { data := [
      ("length", InvariantValue.natVal xs.length),
      ("sorted", InvariantValue.boolVal (match xs with
        | [] => true
        | [x] => true
        | x :: y :: _ => x ≤ y)
      )
    ] }

/-- Example classifier: classify lists by length. -/
def listLengthClassifier : Classifier :=
  { rules := [
      { condition := "length"
        , outputClass := { name := "HasLength", description := "Has a length invariant", typicalExample := "[1,2,3]" }
        , priority := 1
      }
    ],
    defaultClass := { name := "LongList", description := "Multiple elements", typicalExample := "[1,2,3]" }
  }

/-! ## #eval examples -/

#eval describe (α := List String)
#eval classifyByCardinality (Cardinality.finite 3)
#eval classifyByCardinality Cardinality.infinite
#eval "Classification framework defined for Object typeclass"

end MiniObjectKernel
