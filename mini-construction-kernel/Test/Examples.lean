/-
# Step-by-Step Examples — MiniConstructionKernel

Building constructions, products, coproducts, and universal properties.
-/

import MiniConstructionKernel

open MiniConstructionKernel

#eval "══ BUILDING CONSTRUCTIONS: FROM PRODUCTS TO UNIVERSALS ══"

/-! ### Step 1: Register an Object instance -/
instance : Object Nat where
  theory := TheoryName.ofString "Arithmetic"
  objName := "Nat"
  repr n := toString n

#eval describe Nat

/-! ### Step 2: Create a product -/
#eval (Product.mk 1 2).fst
#eval (Product.mk 1 2).snd

/-! ### Step 3: Create a coproduct -/
#eval (Coproduct.inl 42 : Coproduct Nat Nat)
#eval (Coproduct.inr 99 : Coproduct Nat Nat)

/-! ### Step 4: Use the universal property for products -/
def myPair (x : Unit) : Nat := 1
def mySnd (x : Unit) : Nat := 2
#eval (binProductUniversal Nat Nat).pair myPair mySnd ()

/-! ### Step 5: Build a construction -/
def myBuild : buildProduct Nat Nat := buildProduct Nat Nat
#eval myBuild.name

#eval "══ CONSTRUCTION BUILDING COMPLETE ══"
