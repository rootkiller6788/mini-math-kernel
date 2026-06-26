/-
# Benchmark: MiniTheoryDependencyKernel Core Coverage

Tracks every definition/theorem with implementation status.
Format: `-- [x] target | file:line`

Status: [x] done  [~] partial  [ ] planned
-/

/-!
## Core — 10 targets

-- [x] TheoryNode structure                     | Core/Basic.lean:11
-- [x] TheoryNode.simple constructor            | Core/Basic.lean:19
-- [x] DependencyKind inductive                 | Core/Basic.lean:21
-- [x] DependencyEdge structure                 | Core/Basic.lean:28
-- [x] TheoryManifest structure                 | Core/Basic.lean:33
-- [x] TheoryManifest.ofDependencies            | Core/Basic.lean:39
-- [x] TheoryManifest.directDeps               | Core/Basic.lean:42
-- [x] TheoryManifest.importDeps               | Core/Basic.lean:45
-- [x] DependencyGraph structure                | Core/Basic.lean:48
-- [x] DependencyGraph.empty / addNode / addEdge / findNode / edgesFrom / edgesTo / depsOf / nodeCount / edgeCount | Core/Basic.lean:53-70

## Constructions — 10 targets

-- [x] DependencyGraph.topologicalOrder         | Constructions/Universal.lean:12
-- [x] DependencyGraph.findCycle                | Constructions/Universal.lean:28
-- [x] DependencyGraph.transitiveDeps           | Constructions/Universal.lean:41
-- [x] DependencyGraph.transitiveDependents     | Constructions/Universal.lean:50
-- [x] DependencyGraph.buildOrder               | Constructions/Universal.lean:60
-- [x] DependencyGraph.rebuildOrder             | Constructions/Universal.lean:63
-- [x] GraphStats structure                     | Constructions/Universal.lean:72
-- [x] DependencyGraph.stats                    | Constructions/Universal.lean:78
-- [x] kernelNode                               | Constructions/Universal.lean:86
-- [x] dependsOnKernel                          | Constructions/Universal.lean:93

## Morphisms — 3 stubs

-- [~] Hom stub                                 | Morphisms/Hom.lean
-- [~] Iso stub                                 | Morphisms/Iso.lean
-- [~] Equivalence stub                         | Morphisms/Equivalence.lean

## Core Stubs — 2 stubs

-- [~] Objects stub                             | Core/Objects.lean
-- [~] Laws stub                                | Core/Laws.lean

## Constructions Stubs — 3 stubs

-- [~] Subobjects stub                          | Constructions/Subobjects.lean
-- [~] Quotients stub                           | Constructions/Quotients.lean
-- [~] Products stub                            | Constructions/Products.lean

## Properties — 3 stubs

-- [~] Invariants stub                          | Properties/Invariants.lean
-- [~] Preservation stub                        | Properties/Preservation.lean
-- [~] ClassificationData stub                  | Properties/ClassificationData.lean

## Theorems — 4 stubs

-- [~] Basic stub                               | Theorems/Basic.lean
-- [~] UniversalProperties stub                 | Theorems/UniversalProperties.lean
-- [~] Classification stub                      | Theorems/Classification.lean
-- [~] Main stub                                | Theorems/Main.lean

## Examples — 2 stubs

-- [~] Standard stub                            | Examples/Standard.lean
-- [~] Counterexamples stub                     | Examples/Counterexamples.lean

## Bridges — 4 stubs

-- [~] ToAlgebra stub                           | Bridges/ToAlgebra.lean
-- [~] ToTopology stub                          | Bridges/ToTopology.lean
-- [~] ToGeometry stub                          | Bridges/ToGeometry.lean
-- [~] ToComputation stub                       | Bridges/ToComputation.lean

## Summary

Total: 41 targets
Done: 20
Stub: 21
Coverage: 49% (core done, expansions stubbed)
-/

#eval "CoreCoverage: 41 targets, 20 done, 21 stubs"
