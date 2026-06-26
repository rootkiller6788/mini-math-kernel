# mini-theory-dependency-kernel — Architecture

## Overview

The theory dependency kernel tracks which theory depends on which — the "build system"
of the math kernel. It provides graph algorithms for topological ordering, cycle
detection, transitive closure, and build/rebuild order computation.

## Dependency Graph

```
mini-theory-dependency-kernel
    └── mini-object-kernel (for TheoryName)
```

## Module Map

```
MiniTheoryDependencyKernel/
├── Core/
│   ├── Basic.lean              — TheoryNode, DependencyKind, DependencyEdge, TheoryManifest, DependencyGraph
│   ├── Objects.lean            — Object-level dependency structures (stub)
│   └── Laws.lean               — Dependency laws (stub)
├── Morphisms/
│   ├── Hom.lean                — Dependency morphisms (stub)
│   ├── Iso.lean                — Dependency isomorphisms (stub)
│   └── Equivalence.lean        — Dependency equivalence (stub)
├── Constructions/
│   ├── Subobjects.lean         — Subobject dependencies (stub)
│   ├── Quotients.lean          — Quotient dependencies (stub)
│   ├── Products.lean           — Product dependencies (stub)
│   └── Universal.lean          — Graph algorithms: topologicalOrder, findCycle, transitiveDeps, transitiveDependents, buildOrder, rebuildOrder, GraphStats, kernelNode, dependsOnKernel
├── Properties/
│   ├── Invariants.lean         — Dependency invariants (stub)
│   ├── Preservation.lean       — Preservation properties (stub)
│   └── ClassificationData.lean — Classification data (stub)
├── Theorems/
│   ├── Basic.lean              — Basic theorems (stub)
│   ├── UniversalProperties.lean — Universal property theorems (stub)
│   ├── Classification.lean     — Classification theorems (stub)
│   └── Main.lean               — Main theorems (stub)
├── Examples/
│   ├── Standard.lean           — Standard examples (stub)
│   └── Counterexamples.lean    — Counterexamples (stub)
└── Bridges/
    ├── ToAlgebra.lean          — Bridge to algebra (stub)
    ├── ToTopology.lean         — Bridge to topology (stub)
    ├── ToGeometry.lean         — Bridge to geometry (stub)
    └── ToComputation.lean      — Bridge to computation (stub)
```
