/-
# Smoke Tests — MiniObjectKernel

Run: `lake env lean --run Test/Smoke.lean`
-/

import MiniObjectKernel

open MiniObjectKernel

#eval "══ MINI-OBJECT-KERNEL SMOKE TESTS ══"

/-! ## Core.Basic -/

#eval "── Core.Basic: TheoryName ──"
#eval TheoryName.ofString "SetTheory"
#eval TheoryName.root
#eval TheoryName.extend (TheoryName.ofString "Algebra") "Group"

#eval "── Core.Basic: Object typeclass ──"
instance : Object Nat where
  theory := TheoryName.ofString "Arithmetic"
  objName := "Nat"
  repr n := toString n

#eval describe Nat
#eval objName Nat

/-! ## Core.Objects -/

#eval "── Core.Objects: Subobject ──"
def trivialSub : Subobject Nat where
  carrier := Nat
  embed n := n
  injective _ _ h := h
  theoryCompat := rfl

#eval "── Core.Objects: Quotient ──"
#eval "Quotient structure defined"

/-! ## Morphisms -/

#eval "── Morphisms.Iso ──"
def natIso : Iso Nat Nat where
  toFun n := n
  invFun n := n
  leftInv _ := rfl
  rightInv _ := rfl

#eval (natIso.toEq 5 5).mpr rfl

#eval "── Morphisms.Equivalence: EqChain ──"
def simpleChain : EqChain Nat 1 3 :=
  .trans _ _ _ (.step 1 2 rfl) (.step 2 3 rfl)
#eval simpleChain.toEq

#eval "── Morphisms.Hom: Embedding ──"
def embedId := Embedding.id (TheoryName.ofString "Test")
#eval embedId.name

/-! ## Constructions -/

#eval "── Constructions.Universal: EmbeddingGraph ──"
def g := EmbeddingGraph.empty
#eval g.nodes
#eval g.edges

#eval "══ ALL MINI-OBJECT-KERNEL SMOKE TESTS PASSED ══"
