# mini-construction-kernel

Universal constructions for building new mathematical objects from existing ones.

## Modules

| Layer | Files | Description |
|-------|-------|-------------|
| Core | Basic, Objects, Laws | Construction type, Construction objects, Laws |
| Morphisms | Hom, Iso, Equivalence | Construction morphisms, isomorphisms, equivalence |
| Constructions | Subobjects, Quotients, Products, Universal | Universal property framework, product/coproduct |
| Properties | Invariants, Preservation, ClassificationData | Construction invariants and classification |
| Theorems | Basic, UniversalProperties, Classification, Main | Theorems of construction theory |
| Examples | Standard, Counterexamples | Standard examples and counterexamples |
| Bridges | ToAlgebra, ToTopology, ToGeometry, ToComputation | Cross-domain connections |

## Quick Start

```bash
cd mini-construction-kernel
lake build
lake env lean --run Test/Smoke.lean
```
