/-
# Step-by-Step Examples — MiniObjectKernel

Building objects, isomorphisms, and embedding graphs.
-/

import MiniObjectKernel

open MiniObjectKernel

#eval "══ BUILDING OBJECTS: FROM THEORY TO EMBEDDINGS ══"

/-! ### Step 1: Define a theory name -/
#eval TheoryName.ofString "Algebra.Group"

/-! ### Step 2: Register an Object instance -/
def GroupObj := Nat

instance : Object GroupObj where
  theory := TheoryName.ofString "Algebra.Group"
  objName := "Group"
  repr _ := "G"

#eval describe GroupObj

/-! ### Step 3: Create an isomorphism -/
def groupId : Iso GroupObj GroupObj where
  toFun g := g
  invFun g := g
  leftInv _ := rfl
  rightInv _ := rfl

#eval groupId.leftInv 42

/-! ### Step 4: Build a theory embedding graph -/
def graph := EmbeddingGraph.empty
#eval graph.nodes.length

#eval "══ OBJECT BUILDING COMPLETE ══"
