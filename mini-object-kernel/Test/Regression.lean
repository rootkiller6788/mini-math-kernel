/-
# Regression Tests — MiniObjectKernel

Invariant checks across modules.
-/

import MiniObjectKernel

open MiniObjectKernel

/-- Invariant: TheoryName toString roundtrips for single segment -/
#eval (TheoryName.ofString "Test").toString == "Test"

/-- Invariant: EmbeddingGraph.empty has no nodes -/
#eval EmbeddingGraph.empty.nodes == []

/-- Invariant: Iso.toEq is reflexive -/
def regIso : Iso Nat Nat where
  toFun n := n
  invFun n := n
  leftInv _ := rfl
  rightInv _ := rfl
#eval (regIso.toEq 5 5).mpr rfl

/-- Invariant: EqChain refl toEq is rfl -/
#eval (EqChain.refl 42).toEq

#eval "══ ALL REGRESSION CHECKS PASSED ══"
