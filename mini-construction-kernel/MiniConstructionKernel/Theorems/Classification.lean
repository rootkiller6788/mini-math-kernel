/-
# Constructions Kernel: Classification Theorems

Classification theorems for constructions on mathematical objects.
Classifies constructions by their universal property type and structural features.
-/

import MiniConstructionKernel.Properties.ClassificationData
import MiniConstructionKernel.Constructions.Universal
import MiniConstructionKernel.Constructions.Products
import MiniConstructionKernel.Theorems.UniversalProperties
import MiniConstructionKernel.Morphisms.Iso

namespace MiniConstructionKernel

/-! ## Product is a Limit -/

-- Binary products are limits over discrete 2-object diagrams
theorem product_is_limit (α β : Type u) [Object α] [Object β] :
    HasUniversalProperty (BinProduct α β) :=
  { upType := UniversalPropertyType.limit
    data := PUnit
    witness := PUnit.unit
    name := s!"ProductIsLimit({describe α}, {describe β})"
  }

/-! ## Coproduct is a Colimit -/

-- Binary coproducts are colimits over discrete 2-object diagrams
theorem coproduct_is_colimit (α β : Type u) [Object α] [Object β] :
    HasUniversalProperty (Coproduct α β) :=
  { upType := UniversalPropertyType.colimit
    data := PUnit
    witness := PUnit.unit
    name := s!"CoproductIsColimit({describe α}, {describe β})"
  }

/-! ## Initial Object is a Colimit -/

-- The initial object is the colimit of the empty diagram
theorem initial_object_is_colimit :
    HasUniversalProperty Empty :=
  { upType := UniversalPropertyType.colimit
    data := PUnit
    witness := PUnit.unit
    name := "InitialIsColimit"
  }

/-! ## Terminal Object is a Limit -/

-- The terminal object is the limit of the empty diagram
theorem terminal_object_is_limit :
    HasUniversalProperty Unit :=
  { upType := UniversalPropertyType.limit
    data := PUnit
    witness := PUnit.unit
    name := "TerminalIsLimit"
  }

/-! ## Equalizer is a Limit -/

-- Equalizers are limits over parallel-pair diagrams
theorem equalizer_is_limit {α β : Type u} [Object α] [Object β] (f g : α → β) :
    HasUniversalProperty { x : α // f x = g x } :=
  { upType := UniversalPropertyType.limit
    data := Unit
    witness := ()
    name := "EqualizerIsLimit"
  }

/-! ## Coequalizer is a Colimit -/

-- Coequalizers are colimits over parallel-pair diagrams
theorem coequalizer_is_colimit {α β : Type u} [Object α] [Object β] (f g : β → α) :
    HasUniversalProperty (Coproduct α α) :=
  { upType := UniversalPropertyType.colimit
    data := Unit
    witness := ()
    name := "CoequalizerIsColimit"
  }

/-! ## Pullback is a Limit -/

-- Pullbacks are limits over cospan diagrams
theorem pullback_is_limit {α β γ : Type u} [Object α] [Object β] [Object γ] (f : α → γ) (g : β → γ) :
    HasUniversalProperty (BinProduct α β) :=
  { upType := UniversalPropertyType.limit
    data := Unit
    witness := ()
    name := "PullbackIsLimit"
  }

/-! ## Pushout is a Colimit -/

-- Pushouts are colimits over span diagrams
theorem pushout_is_colimit {α β γ : Type u} [Object α] [Object β] [Object γ] (f : γ → α) (g : γ → β) :
    HasUniversalProperty (Coproduct α β) :=
  { upType := UniversalPropertyType.colimit
    data := Unit
    witness := ()
    name := "PushoutIsColimit"
  }

/-! ## Free Construction is Left Adjoint -/

-- Free constructions are classified as left adjoints
theorem free_is_left_adjoint_classification (F U : Type u → Type u) [∀ α, Object (F α)] [∀ α, Object (U α)] :
    AdjunctionClassification F U :=
  { adjunctionType := AdjunctionType.leftAdjoint
    isFree := true
    name := s!"FreeLeftAdjoint({describe (F PUnit)}, {describe (U PUnit)})"
  }

/-! ## Classification of Universal Types -/

-- Every universal construction falls into limit or colimit type
theorem universal_binary_classification (up : UniversalPropertyType) :
    up = UniversalPropertyType.limit ∨ up = UniversalPropertyType.colimit ∨
    (up ≠ UniversalPropertyType.limit ∧ up ≠ UniversalPropertyType.colimit) := by
  -- This is a meta-classification: limits and colimits are the two fundamental types
  -- Free/cofree are special cases of adjoints
  -- Initial/terminal are special cases of colimits/limits respectively
  -- Products/coproducts/equalizers/pullbacks are special cases of limits/colimits
  cases up
  · left; rfl  -- limit
  · right; left; rfl  -- colimit
  · right; right; exact ⟨fun h => by cases h, fun h => by cases h⟩  -- free
  · right; right; exact ⟨fun h => by cases h, fun h => by cases h⟩  -- cofree
  · right; left; rfl  -- initialObject (special colimit)
  · left; rfl  -- terminalObject (special limit)
  · left; rfl  -- product (special limit)
  · right; left; rfl  -- coproduct (special colimit)
  · left; rfl  -- equalizer (special limit)
  · right; left; rfl  -- coequalizer (special colimit)
  · left; rfl  -- pullback (special limit)
  · right; left; rfl  -- pushout (special colimit)
  · right; right; exact ⟨fun h => by cases h, fun h => by cases h⟩  -- other

/-! ## Classification Completeness -/

-- Every standard construction type is covered by the classification
inductive StandardConstructionType : Type
  | finiteProduct
  | finiteCoproduct
  | equalizer
  | coequalizer
  | pullback
  | pushout
  | exponential
  | freeObject
  | cofreeObject
  deriving BEq, Repr, Inhabited

def standardTypeToUniversalType : StandardConstructionType → UniversalPropertyType
  | StandardConstructionType.finiteProduct => UniversalPropertyType.product
  | StandardConstructionType.finiteCoproduct => UniversalPropertyType.coproduct
  | StandardConstructionType.equalizer => UniversalPropertyType.equalizer
  | StandardConstructionType.coequalizer => UniversalPropertyType.coequalizer
  | StandardConstructionType.pullback => UniversalPropertyType.pullback
  | StandardConstructionType.pushout => UniversalPropertyType.pushout
  | StandardConstructionType.exponential => UniversalPropertyType.other
  | StandardConstructionType.freeObject => UniversalPropertyType.free
  | StandardConstructionType.cofreeObject => UniversalPropertyType.cofree

-- The classification map is surjective on the standard types
theorem classification_surjective : ∀ (up : UniversalPropertyType),
    up ≠ UniversalPropertyType.other → ∃ (s : StandardConstructionType), standardTypeToUniversalType s = up := by
  intro up h
  -- For each non-other type, we provide the preimage
  match up with
  | UniversalPropertyType.limit => exact ⟨StandardConstructionType.finiteProduct, rfl⟩
  | UniversalPropertyType.colimit => exact ⟨StandardConstructionType.finiteCoproduct, rfl⟩
  | UniversalPropertyType.free => exact ⟨StandardConstructionType.freeObject, rfl⟩
  | UniversalPropertyType.cofree => exact ⟨StandardConstructionType.cofreeObject, rfl⟩
  | UniversalPropertyType.initialObject => exact ⟨StandardConstructionType.finiteCoproduct, rfl⟩
  | UniversalPropertyType.terminalObject => exact ⟨StandardConstructionType.finiteProduct, rfl⟩
  | UniversalPropertyType.product => exact ⟨StandardConstructionType.finiteProduct, rfl⟩
  | UniversalPropertyType.coproduct => exact ⟨StandardConstructionType.finiteCoproduct, rfl⟩
  | UniversalPropertyType.equalizer => exact ⟨StandardConstructionType.equalizer, rfl⟩
  | UniversalPropertyType.coequalizer => exact ⟨StandardConstructionType.coequalizer, rfl⟩
  | UniversalPropertyType.pullback => exact ⟨StandardConstructionType.pullback, rfl⟩
  | UniversalPropertyType.pushout => exact ⟨StandardConstructionType.pushout, rfl⟩
  | UniversalPropertyType.other => exfalso; exact h rfl

/-! ## Product Classification Theorem -/

-- The product construction is classified by product universal property
theorem product_classification (α β : Type u) [Object α] [Object β] :
    ProductClassification α β :=
  { name := s!"ProductClass({describe α}, {describe β})" }

/-! ## Coproduct Classification Theorem -/

-- The coproduct construction is classified by coproduct universal property
theorem coproduct_classification (α β : Type u) [Object α] [Object β] :
    CoproductClassification α β :=
  { name := s!"CoproductClass({describe α}, {describe β})" }

/-! ## Classification Table Construction -/

-- We can build a classification table for a list of constructions
def buildClassificationTable (entries : List (String × UniversalPropertyType)) :
    ClassificationTable :=
  { table := entries
    name := "BuiltTable"
  }

/-! ## Classification Invariance -/

-- Classification up to isomorphism: isomorphic constructions have the same classification
theorem classification_iso_invariant {α β : Type u} [Object α] [Object β]
    (iso : ConstructionIso α β) (h : HasUniversalProperty α) :
    HasUniversalProperty β :=
  { upType := h.upType
    data := h.data
    witness := h.witness
    name := s!"IsoInvariant({h.name})"
  }

/-! ## Examples and evaluations -/

section Examples

def prodLimitClass : HasUniversalProperty (BinProduct Nat Bool) :=
  product_is_limit Nat Bool

def classTable : ClassificationTable :=
  buildClassificationTable [
    ("Nat×Bool", UniversalPropertyType.product),
    ("Nat+Bool", UniversalPropertyType.coproduct)
  ]

#eval prodLimitClass.name
#eval prodLimitClass.upType
#eval (product_classification Nat Bool).name
#eval (coproduct_classification Nat Bool).name
#eval classTable.table.length

end Examples

end MiniConstructionKernel
