/-
# Benchmark: MiniObjectKernel Core Coverage

Tracks every definition/theorem with implementation status.
Format: `-- [x] target | file:line`

Status: [x] done  [~] partial  [ ] planned
-/

/-!
## Core — 8 targets

-- [x] TheoryName structure                   | Core/Basic.lean:10
-- [x] Object typeclass                        | Core/Basic.lean:24
-- [x] describe helper                         | Core/Basic.lean:31
-- [x] Subobject structure                     | Core/Objects.lean:12
-- [x] SubobjectPredicate                      | Core/Objects.lean:18
-- [x] Quotient structure                      | Core/Objects.lean:23
-- [x] Core.Laws stub                          | Core/Laws.lean

## Morphisms — 8 targets

-- [x] Embedding structure                     | Morphisms/Hom.lean:9
-- [x] Embedding.id                            | Morphisms/Hom.lean:14
-- [x] Embedding.comp                          | Morphisms/Hom.lean:19
-- [x] ForgetfulEmbedding                      | Morphisms/Hom.lean:25
-- [x] Iso structure                           | Morphisms/Iso.lean:11
-- [x] Iso.toEq theorem                        | Morphisms/Iso.lean:19
-- [x] EqChain inductive                       | Morphisms/Equivalence.lean:9
-- [x] EqChain.toEq                            | Morphisms/Equivalence.lean:14

## Constructions — 4 targets

-- [x] EmbeddingGraph structure                | Constructions/Universal.lean:10
-- [x] EmbeddingGraph.empty                    | Constructions/Universal.lean:14
-- [x] EmbeddingGraph.add                      | Constructions/Universal.lean:16
-- [x] Subobjects/Quotients/Products stubs     | Constructions/

## Properties — 3 stubs

-- [~] Invariants stub                         | Properties/Invariants.lean
-- [~] Preservation stub                       | Properties/Preservation.lean
-- [~] ClassificationData stub                 | Properties/ClassificationData.lean

## Theorems — 4 stubs

-- [~] Basic stub                              | Theorems/Basic.lean
-- [~] UniversalProperties stub                | Theorems/UniversalProperties.lean
-- [~] Classification stub                     | Theorems/Classification.lean
-- [~] Main stub                               | Theorems/Main.lean

## Examples — 2 stubs

-- [~] Standard stub                           | Examples/Standard.lean
-- [~] Counterexamples stub                    | Examples/Counterexamples.lean

## Bridges — 4 stubs

-- [~] ToAlgebra stub                          | Bridges/ToAlgebra.lean
-- [~] ToTopology stub                         | Bridges/ToTopology.lean
-- [~] ToGeometry stub                         | Bridges/ToGeometry.lean
-- [~] ToComputation stub                      | Bridges/ToComputation.lean

## Summary

Total: 33 targets
Done: 16
Stub: 17
Coverage: 48% (core done, expansions stubbed)
-/

#eval "CoreCoverage: 33 targets, 16 done, 17 stubs"
