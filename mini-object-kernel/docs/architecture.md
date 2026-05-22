# mini-object-kernel — Architecture

## Overview

The object kernel defines the `Object` typeclass — the common interface for
every mathematical structure in the mini-everything-math ecosystem.

## Dependency Graph

```
mini-object-kernel (self-contained, no external deps)
```

## Module Map

```
MiniObjectKernel/
├── Core/
│   ├── Basic.lean              — TheoryName, Object typeclass
│   ├── Objects.lean            — Subobject, SubobjectPredicate, Quotient
│   └── Laws.lean               — Object laws (stub)
├── Morphisms/
│   ├── Hom.lean                — Embedding, ForgetfulEmbedding
│   ├── Iso.lean                — Iso structure, Iso.toEq
│   └── Equivalence.lean        — EqChain, equality infrastructure
├── Constructions/
│   ├── Subobjects.lean         — Subobject constructions (stub)
│   ├── Quotients.lean          — Quotient constructions (stub)
│   ├── Products.lean           — Product constructions (stub)
│   └── Universal.lean          — EmbeddingGraph
├── Properties/
│   ├── Invariants.lean         — Object invariants (stub)
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
