# mini-theory-dependency-kernel

Theory dependency tracking infrastructure for the mini-everything-math ecosystem.

## Modules

| Layer | Files | Description |
|-------|-------|-------------|
| Core | Basic, Objects, Laws | TheoryNode, DependencyKind, DependencyEdge, TheoryManifest, DependencyGraph |
| Morphisms | Hom, Iso, Equivalence | Dependency morphisms and equivalence (stubs) |
| Constructions | Subobjects, Quotients, Products, Universal | Graph algorithms: topological order, cycle detection, transitive closure, build order |
| Properties | Invariants, Preservation, ClassificationData | Dependency invariants (stubs) |
| Theorems | Basic, UniversalProperties, Classification, Main | Dependency theorems (stubs) |
| Examples | Standard, Counterexamples | Standard examples and counterexamples (stubs) |
| Bridges | ToAlgebra, ToTopology, ToGeometry, ToComputation | Cross-domain connections (stubs) |

## Quick Start

```bash
cd mini-theory-dependency-kernel
lake build
lake env lean --run Test/Smoke.lean
```
