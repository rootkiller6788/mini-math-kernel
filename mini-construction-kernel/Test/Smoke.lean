/-
# Smoke Tests — MiniConstructionKernel

Run: `lake env lean --run Test/Smoke.lean`
-/

import MiniConstructionKernel

open MiniConstructionKernel

#eval "══ MINI-CONSTRUCTION-KERNEL SMOKE TESTS ══"

/-! ## Core.Basic: Constructions -/
instance : Object Nat where
  theory := TheoryName.ofString "Test"
  objName := "Nat"
  repr n := toString n

#eval "Construction type defined"

/-! ## Constructions.Universal -/
#eval "UniversalProperty, InitialObject, TerminalObject"
#eval emptyInitial.unique

/-! ## Constructions.Products -/
#eval (Product.mk 1 2).fst
#eval (Coproduct.inl 42 : Coproduct Nat Nat)

#eval "══ ALL MINI-CONSTRUCTION-KERNEL SMOKE TESTS PASSED ══"
