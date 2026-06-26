# mini-theory-dependency-kernel

Theory dependency tracking infrastructure for the mini-everything-math ecosystem.

## Module Status: COMPLETE ✅

- **L1-L6: Complete** — Core definitions, concepts, structures, fundamental theorems with proofs, multiple proof techniques, canonical examples with #eval verification
- **L7: Complete** — 4 application domains (Algebra, Topology, Geometry, Computation/build systems)
- **L8: Partial+** — SCC condensation, bisimulation theory, centrality measures, structural analysis
- **L9: Partial** — Research connections documented (condensed mathematics, synthetic spectra referenced)

## Modules

| Layer | Files | Description |
|-------|-------|-------------|
| Core | Basic, Objects, Laws | TheoryNode, DependencyKind, DependencyEdge, TheoryManifest, DependencyGraph, Signature, FormalTheory, Axiom, Extension |
| Morphisms | Hom, Iso, Equivalence | TheoryMorphism, TheoryIsomorphism, MutualInterpretability, TheoryEquivalence, GraphIsomorphism |
| Constructions | Subobjects, Quotients, Products, Universal | Graph algorithms: topologicalOrder, findCycle, transitiveDeps, buildOrder, rebuildOrder, condensation, SCCs, forest/tree detection |
| Properties | Invariants, Preservation, ClassificationData | Dependency invariants (depth, width, rank, connectivity, centrality, impact factor), Preservation rules, Classification taxonomy |
| Theorems | Basic, UniversalProperties, Classification, Main | Dependency graph theorems with complete proofs (no sorry/trivial on non-trivial) |
| Examples | Standard, Counterexamples | ZFC/PA/Algebra/Topology/Geometry dependency graphs, cyclic/self-dependency/mutual-dependency counterexamples |
| Bridges | ToAlgebra, ToTopology, ToGeometry, ToComputation | Cross-domain dependency analysis: algebraic hierarchy, topology chain, geometry dependencies, build system simulation |

## Quick Start

```bash
cd mini-theory-dependency-kernel
lake build
lake env lean --run Test/Smoke.lean
```
