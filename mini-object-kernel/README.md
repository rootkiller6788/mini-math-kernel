# mini-object-kernel

Mathematical object typeclass and equality reasoning infrastructure.

## Modules

| Layer | Files | Description |
|-------|-------|-------------|
| Core | Basic, Objects, Laws | TheoryName, Object typeclass, Subobject, Quotient |
| Morphisms | Hom, Iso, Equivalence | Embeddings, Isomorphisms, EqChain |
| Constructions | Subobjects, Quotients, Products, Universal | Object constructions, EmbeddingGraph |
| Properties | Invariants, Preservation, ClassificationData | Object invariants and classification |
| Theorems | Basic, UniversalProperties, Classification, Main | Theorems of object theory |
| Examples | Standard, Counterexamples | Standard examples and counterexamples |
| Bridges | ToAlgebra, ToTopology, ToGeometry, ToComputation | Cross-domain connections |

## Quick Start

```bash
cd mini-object-kernel
lake build
lake env lean --run Test/Smoke.lean
```
