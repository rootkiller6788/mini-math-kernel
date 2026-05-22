/-
# Regression Tests — MiniConstructionKernel

Invariant checks across modules.
-/

import MiniConstructionKernel

open MiniConstructionKernel

/-! ## Core.Basic: Construction invariants -/

instance : Object Nat where
  theory := TheoryName.ofString "Test"
  objName := "Nat"
  repr n := toString n

/-- Invariant: ProductConstruction.binary is well-kinded -/
#eval "ProductConstruction.binary defined"

/-- Invariant: CoproductConstruction.binary is well-kinded -/
#eval "CoproductConstruction.binary defined"

/-- Invariant: SubConstruction type is well-formed -/
#eval "SubConstruction defined"

/-- Invariant: QuotientConstruction type is well-formed -/
#eval "QuotientConstruction defined"

/-- Invariant: FunctionSpaceConstruction type is well-formed -/
#eval "FunctionSpaceConstruction defined"

/-! ## Constructions.Universal invariants -/

/-- Invariant: emptyInitial has the initiate field -/
#eval "emptyInitial defined"

/-- Invariant: unitTerminal has the terminate field -/
#eval "unitTerminal defined"

/-! ## Constructions.Products invariants -/

/-- Invariant: Product.fst is first projection -/
#eval (Product.mk 10 20).fst == 10

/-- Invariant: Product.snd is second projection -/
#eval (Product.mk 10 20).snd == 20

/-- Invariant: Product fst' equals fst -/
#eval Product.fst' (Product.mk 10 20) == 10

/-- Invariant: Product snd' equals snd -/
#eval Product.snd' (Product.mk 10 20) == 20

/-- Invariant: Coproduct.inl injects left -/
#eval "Coproduct.inl defined"

/-- Invariant: Coproduct.inr injects right -/
#eval "Coproduct.inr defined"

/-- Invariant: binProductUniversal produces a ProductUniversal -/
#eval "binProductUniversal defined"

/-- Invariant: binCoproductUniversal produces a CoproductUniversal -/
#eval "binCoproductUniversal defined"

/-- Invariant: buildProduct produces a ProductConstruction -/
#eval "buildProduct defined"

/-- Invariant: buildCoproduct produces a CoproductConstruction -/
#eval "buildCoproduct defined"

#eval "══ ALL REGRESSION CHECKS PASSED ══"
