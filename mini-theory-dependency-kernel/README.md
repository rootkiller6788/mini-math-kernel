# mini-theory-dependency-kernel

Theory dependency tracking infrastructure for the mini-everything-math ecosystem.

## Module Status: SUBSTANTIALLY COMPLETE (22/25 modules compile ✅)

- **L1-L6: Complete** — Core definitions, graph algorithms (topological sort, cycle detection, transitive closure, SCC), 37 theorems with proofs, 128 #eval verifications
- **L7: Complete** — 4 application bridges (Algebra 12-theory hierarchy, Topology 8-theory chain, Geometry 6-theory DAG, Computation/build system simulation)
- **L8: Partial+** — SCC condensation, centrality measures, structural analysis (3 modules have remaining import/API fixups)
- **L9: Partial** — Research connections documented
- **Documentation**: knowledge-graph.md, gap-report.md, course-alignment.md, course-tree.md all present ✅

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
