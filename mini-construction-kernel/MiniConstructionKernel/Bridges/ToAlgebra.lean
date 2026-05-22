/-
# Constructions Kernel: Bridge to Algebra

Connections between construction theory and algebra.
Free group, polynomial ring, tensor product, and algebraic structures
expressed as Construction instances.
-/

import MiniConstructionKernel.Core.Basic
import MiniConstructionKernel.Core.Objects
import MiniConstructionKernel.Constructions.Products
import MiniConstructionKernel.Constructions.Subobjects
import MiniConstructionKernel.Constructions.Quotients

namespace MiniConstructionKernel

open MiniObjectKernel

/-! ## Object instances -/

instance : Object Nat where
  theory := TheoryName.ofString "Set"
  objName := "Nat"
  repr n := toString n

instance : Object String where
  theory := TheoryName.ofString "Set"
  objName := "String"
  repr s := s

/-! ## Free Monoid (List) as Construction -/

instance (α : Type u) [Object α] : Object (List α) where
  theory := (Object.theory α).extend "List"
  objName := s!"List({describe α})"
  repr l := repr l

def freeMonoidConstruction (α : Type u) [Object α] : Construction Unit (fun _ => α) (List α) :=
  { build := []
    name := s!"FreeMonoid({describe α})"
  }

def listUnit {α : Type u} [Object α] (a : α) : List α := [a]

def listExtend {α β : Type u} [Object α] [Object β] (f : α → β) : List α → List β :=
  List.map f

/-! ## Free Group as Construction -/

inductive FreeGroup (α : Type u) : Type u
  | unit : FreeGroup α
  | gen : α → FreeGroup α
  | inv : FreeGroup α → FreeGroup α
  | mul : FreeGroup α → FreeGroup α → FreeGroup α
  deriving Inhabited

instance (α : Type u) [Object α] : Object (FreeGroup α) where
  theory := TheoryName.ofString "Group"
  objName := s!"FreeGroup({describe α})"
  repr
    | FreeGroup.unit => "e"
    | FreeGroup.gen a => s!"g({repr a})"
    | FreeGroup.inv g => s!"({repr g})⁻¹"
    | FreeGroup.mul g h => s!"({repr g})*({repr h})"

def freeGroupConstruction (α : Type u) [Object α] : Construction Unit (fun _ => α) (FreeGroup α) :=
  { build := FreeGroup.unit
    name := s!"FreeGroup({describe α})"
  }

/-! ## Polynomial Ring over Variables -/

inductive Polynomial (α : Type u) : Type u
  | const : Nat → Polynomial α
  | var : α → Polynomial α
  | add : Polynomial α → Polynomial α → Polynomial α
  | mul : Polynomial α → Polynomial α → Polynomial α
  deriving Inhabited

instance (α : Type u) [Object α] : Object (Polynomial α) where
  theory := TheoryName.ofString "CommRing"
  objName := s!"Z[{describe α}]"
  repr
    | Polynomial.const n => toString n
    | Polynomial.var a => s!"x_({repr a})"
    | Polynomial.add p q => s!"({repr p} + {repr q})"
    | Polynomial.mul p q => s!"({repr p} * {repr q})"

def polynomialConstruction (α : Type u) [Object α] : Construction Unit (fun _ => α) (Polynomial α) :=
  { build := Polynomial.const 0
    name := s!"PolynomialRing({describe α})"
  }

/-! ## Tensor Product as Construction -/

structure TensorProduct (α β : Type u) where
  pure : α → β → TensorProduct α β
  deriving Inhabited

instance (α β : Type u) [Object α] [Object β] : Object (TensorProduct α β) where
  theory := TheoryName.ofString "Module"
  objName := s!"{describe α}⊗{describe β}"
  repr _ := "tensor"

def tensorProductConstruction (α β : Type u) [Object α] [Object β] :
    Construction Unit (fun _ => α) (TensorProduct α β) :=
  { build := Classical.choice (by infer_instance)
    name := s!"TensorProduct({describe α},{describe β})"
  }

/-! ## Algebraic Quotient: Z/nZ -/

def modNRel (n : Nat) (a b : Nat) : Prop := a % n = b % n

def modNEquiv (n : Nat) : Equivalence (modNRel n) where
  refl a := rfl
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂

def znConstruction (n : Nat) : QuotientConstruction Nat :=
  { rel := modNRel n
    isEquiv := modNEquiv n
    name := s!"Z/{n}Z"
  }

/-! ## Algebraic Subobject: Kernel of Homomorphism -/

def kernelSubobject {α β : Type u} [Object α] [Object β] (f : α → β) : SubConstruction α :=
  { pred := fun a => f a = f a
    name := s!"Ker({describe α}→{describe β})"
  }

/-! ## Free Abelian Group (simplified) -/

structure FreeAbelianGroup (α : Type u) where
  coefficients : α → Int
  -- Finitely supported function α → Z

instance (α : Type u) [Object α] : Object (FreeAbelianGroup α) where
  theory := TheoryName.ofString "AbGroup"
  objName := s!"FreeAb({describe α})"
  repr _ := "free-abelian"

def freeAbelianConstruction (α : Type u) [Object α] : Construction Unit (fun _ => α) (FreeAbelianGroup α) :=
  { build := { coefficients := fun _ => 0 }
    name := s!"FreeAbelianGroup({describe α})"
  }

/-! ## Evaluations -/

#eval freeMonoidConstruction Nat |>.name
#eval freeGroupConstruction Nat |>.name
#eval polynomialConstruction String |>.name
#eval znConstruction 5 |>.name

end MiniConstructionKernel
