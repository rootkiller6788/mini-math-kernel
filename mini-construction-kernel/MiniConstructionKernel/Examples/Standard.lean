/-
# Constructions Kernel: Standard Examples

Standard examples: free monoid, product, quotient, tensor product,
polynomial ring, and subobject/quotient morphisms.
-/

import MiniConstructionKernel.Core.Basic
import MiniConstructionKernel.Core.Objects
import MiniConstructionKernel.Constructions.Universal
import MiniConstructionKernel.Constructions.Products
import MiniConstructionKernel.Constructions.Subobjects
import MiniConstructionKernel.Constructions.Quotients
import MiniConstructionKernel.Morphisms.Hom
import MiniConstructionKernel.Morphisms.Iso

namespace MiniConstructionKernel

open MiniObjectKernel

/-! ## Object instances for examples -/

instance : Object Nat where
  theory := TheoryName.ofString "Set"
  objName := "Nat"
  repr n := toString n

instance : Object Bool where
  theory := TheoryName.ofString "Set"
  objName := "Bool"
  repr b := toString b

/-! ## Free Monoid (List) -/

instance {α : Type u} [Object α] : Object (List α) where
  theory := TheoryName.ofString "Monoid"
  objName := s!"FreeMonoid({describe α})"
  repr l := repr l

def freeMonoidConstruction (α : Type u) [Object α] : FreeConstruction List where
  unit a := [a]
  extend f := List.map f
  extend_unit f a := rfl
  unique f g h as := by
    induction as with
    | nil => rfl
    | cons a as ih => simp [List.map, h a, ih]
  name := s!"FreeMonoid({describe α})"

/-! ## Product of Sets -/

abbrev SetProduct (α β : Type u) [Object α] [Object β] : Type u := BinProduct α β

instance {α β : Type u} [Object α] [Object β] : Object (SetProduct α β) where
  theory := TheoryName.ofString "Set"
  objName := s!"{describe α}×{describe β}"
  repr p := s!"({Object.repr α p.fst}, {Object.repr β p.snd})"

def setProductConstruction (α β : Type u) [Object α] [Object β] :
    ProductConstruction (Fin 2) fun | 0 => α | 1 => β := buildProduct α β

def setProductUniversal (α β : Type u) [Object α] [Object β] :
    ProductUniversal α β (SetProduct α β) := binProductUniversal α β

/-! ## Coproduct of Sets -/

def setCoproductConstruction (α β : Type u) [Object α] [Object β] :
    CoproductConstruction (Fin 2) fun | 0 => α | 1 => β := buildCoproduct α β

/-! ## Quotient by Equivalence -/

def quotientByRelation {α : Type u} [Object α] (R : α → α → Prop) (h : Equivalence R) :
    QuotientByEquiv α := { R := R, isEquiv := h, name := s!"{describe α}/R" }

def mod3QuotientExample : QuotientByEquiv Nat where
  R a b := a % 3 = b % 3
  isEquiv := { refl := fun _ => rfl, symm := fun h => h.symm, trans := fun h₁ h₂ => h₁.trans h₂ }
  name := "Mod3Eq"

/-! ## Subset as Subobject -/

def subsetSubobject {α : Type u} [Object α] (P : α → Prop) (nm : String := "") :
    Subobject α := subobjectOfPredicate P nm

def evenSubobjectExample : Subobject Nat := subsetSubobject (fun n => n % 2 = 0) "EvenNat"

/-! ## Tensor Product -/

inductive TensorProduct (α β : Type u) : Type u where
  | pure : α → β → TensorProduct α β
  | zero : TensorProduct α β
  | add : TensorProduct α β → TensorProduct α β → TensorProduct α β
  deriving Inhabited

instance {α β : Type u} [Object α] [Object β] : Object (TensorProduct α β) where
  theory := TheoryName.ofString "Module"
  objName := s!"{describe α}⊗{describe β}"
  repr
    | .pure a b => s!"({Object.repr α a}⊗{Object.repr β b})"
    | .zero => "0"
    | .add t1 t2 => s!"({repr t1}+{repr t2})"

def tensorProductConstruction (α β : Type u) [Object α] [Object β] :
    Construction Unit (fun _ => α) (TensorProduct α β) :=
  { build := TensorProduct.zero, name := s!"TensorProduct({describe α},{describe β})" }

/-! ## Polynomial Ring -/

inductive PolynomialExpr (α : Type u) : Type u where
  | const : Nat → PolynomialExpr α
  | var : α → PolynomialExpr α
  | add : PolynomialExpr α → PolynomialExpr α → PolynomialExpr α
  | mul : PolynomialExpr α → PolynomialExpr α → PolynomialExpr α
  deriving Inhabited

instance {α : Type u} [Object α] : Object (PolynomialExpr α) where
  theory := TheoryName.ofString "CommRing"
  objName := s!"Poly({describe α})"
  repr
    | .const n => toString n
    | .var a => s!"X_({Object.repr α a})"
    | .add p q => s!"({repr p}+{repr q})"
    | .mul p q => s!"({repr p})·({repr q})"

def polynomialConstruction (α : Type u) [Object α] :
    Construction Unit (fun _ => α) (PolynomialExpr α) :=
  { build := PolynomialExpr.const 0, name := s!"PolynomialRing({describe α})" }

/-! ## Construction Morphisms -/

def coproductInjection {α β : Type u} [Object α] [Object β] :
    ConstructionMono α (Coproduct α β) :=
  { f := Coproduct.inl
    mono g h hEq x := by
      have hx := hEq x
      injection hx with hx'; exact hx'
    name := s!"ι₁({describe α},{describe β})" }

/-! ## Function Space -/

def functionSpaceExample {α β : Type u} [Object α] [Object β] :
    FunctionSpaceConstruction α β := { name := s!"{describe α}→{describe β}" }

/-! ## Evaluations -/

def prodSetNB : SetProduct Nat Bool := { fst := 1, snd := true }

#eval freeMonoidConstruction Nat |>.name
#eval prodSetNB.fst
#eval tensorProductConstruction Nat Bool |>.name
#eval (polynomialConstruction Nat).name
#eval (setProductUniversal Nat Bool).name
#eval evenSubobjectExample.name
#eval mod3QuotientExample.R 7 10

end MiniConstructionKernel
