# mini-logic-kernel

Propositional and first-order logic infrastructure: formulas,
semantic evaluation, derived inference rules, and model theory.

## Modules

| Layer | Files | Description |
|-------|-------|-------------|
| Core | Basic, Objects, Laws | Formula, PredFormula, Structure, derived rules |
| Morphisms | Hom, Iso, Equivalence | Formula homomorphisms and logical equivalences |
| Constructions | Subobjects, Quotients, Products, Universal | Logical constructions |
| Properties | Invariants, Preservation, ClassificationData | Metalogical properties |
| Theorems | Basic, UniversalProperties, Classification, Main | Theorems of logic |
| Examples | Standard, Counterexamples | Standard examples and counterexamples |
| Bridges | ToAlgebra, ToTopology, ToGeometry, ToComputation | Cross-domain connections |

## Quick Start

```bash
cd mini-logic-kernel
lake build
lake env lean --run Test/Smoke.lean
```
