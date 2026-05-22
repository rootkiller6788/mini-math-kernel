# mini-logic-kernel -- Architecture

## Overview

The logic kernel defines the `Formula` type for propositional logic and
`PredFormula` for first-order predicate logic -- the common reasoning
layer for every theory in the mini-everything-math ecosystem.

## Dependency Graph

```
mini-logic-kernel (self-contained, no external deps)
```

## Module Map

```
MiniLogicKernel/
├── Core/
│   ├── Basic.lean              -- Formula type, eval, semantics, transformations
│   ├── Objects.lean            -- PredFormula, Structure, satisfies
│   └── Laws.lean               -- Derived inference rules (13 rules)
├── Morphisms/
│   ├── Hom.lean                -- Formula homomorphisms (stub)
│   ├── Iso.lean                -- Logical isomorphisms (stub)
│   └── Equivalence.lean        -- Logical equivalence reasoning (stub)
├── Constructions/
│   ├── Subobjects.lean         -- Subformula constructions (stub)
│   ├── Quotients.lean          -- Quotient by logical equivalence (stub)
│   ├── Products.lean           -- Product structures (stub)
│   └── Universal.lean          -- Universal constructions (stub)
├── Properties/
│   ├── Invariants.lean         -- Consistency, completeness (stub)
│   ├── Preservation.lean       -- Preservation theorems (stub)
│   └── ClassificationData.lean -- Classification data (stub)
├── Theorems/
│   ├── Basic.lean              -- Basic theorems (stub)
│   ├── UniversalProperties.lean -- Universal property theorems (stub)
│   ├── Classification.lean     -- Classification theorems (stub)
│   └── Main.lean               -- Main theorems (stub)
├── Examples/
│   ├── Standard.lean           -- Standard examples (stub)
│   └── Counterexamples.lean    -- Counterexamples (stub)
└── Bridges/
    ├── ToAlgebra.lean          -- Bridge to algebra (stub)
    ├── ToTopology.lean         -- Bridge to topology (stub)
    ├── ToGeometry.lean         -- Bridge to geometry (stub)
    └── ToComputation.lean      -- Bridge to computation (stub)
```
