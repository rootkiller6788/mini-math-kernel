/-
# Constructions Kernel: Bridge to Geometry

Connections between construction theory and geometry.
Fiber product, blow-up, projective space, tangent space, and
geometric constructions in the construction framework.
-/

import MiniConstructionKernel.Core.Basic
import MiniConstructionKernel.Constructions.Products
import MiniConstructionKernel.Constructions.Subobjects
import MiniConstructionKernel.Constructions.Quotients

namespace MiniConstructionKernel

open MiniObjectKernel

/-! ## Geometric Space as Object -/

structure GeometricSpace where
  points : Type
  charts : points → Prop

instance : Object GeometricSpace where
  theory := TheoryName.ofString "Geometry"
  objName := "GeometricSpace"
  repr _ := "<geometric-space>"

/-! ## Fiber Product (Pullback) -/

structure FiberProduct (X Y Z : GeometricSpace) where
  fiberProduct : GeometricSpace
  p₁ : fiberProduct.points → X.points
  p₂ : fiberProduct.points → Y.points

def fiberProductConstruction (X Y Z : GeometricSpace) (f : X.points → Z.points) (g : Y.points → Z.points) :
    SubConstruction (Product X Y) :=
  { pred := fun p => f p.fst = g p.snd
    name := s!"FiberProduct({repr X},{repr Y},{repr Z})"
  }

/-! ## Blow-up Construction -/

structure BlowUp (X : GeometricSpace) where
  blownUp : GeometricSpace
  exceptionalDivisor : GeometricSpace
  blowDown : blownUp.points → X.points

def blowUpConstruction (X : GeometricSpace) (center : GeometricSpace) : Construction Unit (fun _ => X) GeometricSpace :=
  { build := X
    name := s!"BlowUp({repr X})"
  }

/-! ## Projective Space -/

structure ProjectiveSpace (n : Nat) where
  points : Type
  homogeneousCoords : points → List Nat
  -- Points are equivalence classes of (n+1)-tuples under scaling

def projectiveSpaceConstruction (n : Nat) : Construction Unit (fun _ => PUnit) GeometricSpace :=
  { build := { points := Nat, charts := fun _ => True }
    name := s!"P^{n}"
  }

/-! ## Grassmannian -/

structure Grassmannian (k n : Nat) where
  points : Type
  -- k-dimensional subspaces of n-dimensional space

instance : Object (Grassmannian 1 2) where
  theory := TheoryName.ofString "Geometry"
  objName := "Gr(1,2)"
  repr _ := "<grassmannian>"

def grassmannianConstruction (k n : Nat) : Construction Unit (fun _ => PUnit) GeometricSpace :=
  { build := { points := Nat, charts := fun _ => True }
    name := s!"Gr({k},{n})"
  }

/-! ## Tangent Space -/

structure TangentSpace (X : GeometricSpace) (p : X.points) where
  vectors : Type
  dim : Nat

def tangentSpaceConstruction (X : GeometricSpace) (p : X.points) : Construction Unit (fun _ => X) GeometricSpace :=
  { build := X
    name := s!"T_{repr p}({repr X})"
  }

/-! ## Cotangent Space -/

structure CotangentSpace (X : GeometricSpace) (p : X.points) where
  covectors : Type
  dim : Nat

def cotangentSpaceConstruction (X : GeometricSpace) (p : X.points) : Construction Unit (fun _ => X) GeometricSpace :=
  { build := X
    name := s!"T*_{repr p}({repr X})"
  }

/-! ## Vector Bundle -/

structure VectorBundle (base : GeometricSpace) where
  totalSpace : GeometricSpace
  projection : totalSpace.points → base.points
  fiberDim : Nat

def vectorBundleConstruction (base : GeometricSpace) (rank : Nat) : Construction Unit (fun _ => base) GeometricSpace :=
  { build := base
    name := s!"VecBundle_{rank}({repr base})"
  }

/-! ## Evaluations -/

def p2 := projectiveSpaceConstruction 2
def gr12 := grassmannianConstruction 1 2
def tangentEx := tangentSpaceConstruction
    { points := Nat, charts := fun _ => True }
    0

#eval p2.name
#eval gr12.name
#eval tangentEx.name
#eval (fiberProductConstruction
    { points := Nat, charts := fun _ => True }
    { points := Nat, charts := fun _ => True }
    { points := Bool, charts := fun _ => True }
    (fun n => n % 2 = 0)
    (fun n => n > 0)).name

end MiniConstructionKernel
