/-
# Constructions Kernel: Classification Data

Classification data for constructions on mathematical objects.
Structures for classifying constructions by their universal property type:
limit, colimit, free, cofree.
-/

import MiniConstructionKernel.Core.Basic
import MiniConstructionKernel.Core.Objects
import MiniConstructionKernel.Constructions.Universal

namespace MiniConstructionKernel

/-! ## Universal Property Classification -/

-- Enumeration of universal property types
inductive UniversalPropertyType : Type
  | limit
  | colimit
  | free
  | cofree
  | initialObject
  | terminalObject
  | product
  | coproduct
  | equalizer
  | coequalizer
  | pullback
  | pushout
  | other
  deriving BEq, Repr, Inhabited

def universalPropertyTypeName : UniversalPropertyType → String
  | UniversalPropertyType.limit => "Limit"
  | UniversalPropertyType.colimit => "Colimit"
  | UniversalPropertyType.free => "Free"
  | UniversalPropertyType.cofree => "Cofree"
  | UniversalPropertyType.initialObject => "Initial Object"
  | UniversalPropertyType.terminalObject => "Terminal Object"
  | UniversalPropertyType.product => "Product"
  | UniversalPropertyType.coproduct => "Coproduct"
  | UniversalPropertyType.equalizer => "Equalizer"
  | UniversalPropertyType.coequalizer => "Coequalizer"
  | UniversalPropertyType.pullback => "Pullback"
  | UniversalPropertyType.pushout => "Pushout"
  | UniversalPropertyType.other => "Other"

/-! ## Classified Construction -/

-- A construction annotated with its universal property type
structure ClassifiedConstruction (α : Type u) [Object α] where
  constructionType : UniversalPropertyType
  carrier : Type u
  [obj : Object carrier]
  description : String

/-! ## Classification Database -/

-- A collection of classified constructions
structure ClassificationDatabase where
  entries : List (Σ (α : Type), ClassifiedConstruction α)
  name : String

def emptyClassificationDatabase : ClassificationDatabase :=
  { entries := []
    name := "Empty"
  }

def addClassificationEntry (db : ClassificationDatabase)
    {α : Type u} (entry : ClassifiedConstruction α) : ClassificationDatabase :=
  { entries := ⟨α, entry⟩ :: db.entries
    name := db.name
  }

/-! ## Has Universal Property -/

-- Records that a type satisfies a specific universal property
structure HasUniversalProperty (α : Type u) [Object α] where
  upType : UniversalPropertyType
  data : Type u
  witness : data
  name : String

/-! ## Limit Type Classification -/

-- Classification data for limit-type constructions
structure LimitClassification (J : Type u) (D : J → Type v) where
  limitType : UniversalPropertyType := UniversalPropertyType.limit
  shape : Type u := J
  diagram : J → Type v := D
  name : String

/-! ## Colimit Type Classification -/

-- Classification data for colimit-type constructions
structure ColimitClassification (J : Type u) (D : J → Type v) where
  colimitType : UniversalPropertyType := UniversalPropertyType.colimit
  shape : Type u := J
  diagram : J → Type v := D
  name : String

/-! ## Free Type Classification -/

-- Classification data for free-type constructions
structure FreeClassification (F : Type u → Type v) [∀ α, Object (F α)] where
  freeType : UniversalPropertyType := UniversalPropertyType.free
  forgetfulCodomain : Type
  name : String

/-! ## Adjunction Classification -/

-- Classification data for adjoint constructions
inductive AdjunctionType : Type
  | leftAdjoint
  | rightAdjoint
  | idempotentAdjunction
  deriving BEq, Repr, Inhabited

structure AdjunctionClassification (F G : Type u → Type u) [∀ α, Object (F α)] [∀ α, Object (G α)] where
  adjunctionType : AdjunctionType
  isFree : Bool := true
  isForgetful : Bool := false
  name : String

/-! ## Product Classification -/

-- Classification data for product constructions
structure ProductClassification (α β : Type u) [Object α] [Object β] where
  productType : UniversalPropertyType := UniversalPropertyType.product
  leftObject : Type u := α
  rightObject : Type u := β
  isBinary : Bool := true
  name : String

/-! ## Coproduct Classification -/

-- Classification data for coproduct constructions
structure CoproductClassification (α β : Type u) [Object α] [Object β] where
  coproductType : UniversalPropertyType := UniversalPropertyType.coproduct
  leftObject : Type u := α
  rightObject : Type u := β
  isBinary : Bool := true
  name : String

/-! ## Equalizer Classification -/

-- Classification data for equalizer constructions
structure EqualizerClassification (α β : Type u) [Object α] [Object β] (f g : α → β) where
  equalizerType : UniversalPropertyType := UniversalPropertyType.equalizer
  f : α → β := f
  g : α → β := g
  name : String

/-! ## Coequalizer Classification -/

-- Classification data for coequalizer constructions
structure CoequalizerClassification (α β : Type u) [Object α] [Object β] (f g : β → α) where
  coequalizerType : UniversalPropertyType := UniversalPropertyType.coequalizer
  f : β → α := f
  g : β → α := g
  name : String

/-! ## Classification by Diagram Shape -/

-- The shape of the indexing diagram determines the construction type
inductive DiagramShape : Type
  | empty
  | discrete (n : Nat)
  | parallelPair
  | span
  | cospan
  | general
  deriving BEq, Repr, Inhabited

structure DiagramClassification (J : Type u) where
  shape : DiagramShape
  category : Type u := J
  name : String

def classifyDiagramShape {J : Type u} (dj : J) : DiagramClassification J where
  shape := DiagramShape.general
  name := s!"Diagram(J)"

/-! ## Classification Table -/

-- A table mapping construction names to their universal property types
structure ClassificationTable where
  table : List (String × UniversalPropertyType)
  name : String

def emptyClassificationTable : ClassificationTable :=
  { table := []
    name := "Empty"
  }

def classifyConstruction (table : ClassificationTable) (name : String) : UniversalPropertyType :=
  match table.table.find? fun (n, _) => n == name with
  | some (_, t) => t
  | none => UniversalPropertyType.other

/-! ## Examples and evaluations -/

section Examples

def productClass : ProductClassification Nat Bool :=
  { name := "Nat×Bool" }

def coproductClass : CoproductClassification Nat Bool :=
  { name := "Nat+Bool" }

def classTable : ClassificationTable :=
  { table := [
      ("Nat×Bool", UniversalPropertyType.product),
      ("Nat+Bool", UniversalPropertyType.coproduct)
    ]
    name := "ExampleTable"
  }

#eval universalPropertyTypeName UniversalPropertyType.product
#eval universalPropertyTypeName UniversalPropertyType.colimit
#eval productClass.name
#eval classifyConstruction classTable "Nat×Bool"
#eval coproductClass.coproductType

end Examples

end MiniConstructionKernel
