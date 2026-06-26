# Architecture — MiniSyntaxKernel

## Overview

The MiniSyntaxKernel provides the fundamental syntax layer for the mini-everything-math ecosystem. Every mathematical expression is ultimately represented as a `Term`.

## Design

### Term Representation

The kernel uses a named representation with optional de Bruijn indices for safe binding.

- **Variable**: names with optional de Bruijn indices
- **Term**: inductive type with constructors for var, app, lam, pi, sort, lit, letE

### Binding

All binding forms (lam, pi, letE) use the binder's `Variable` as the bound name. De Bruijn indices in variables (when present with `some n`) track original binding positions.

### Substitution

Capture-avoiding substitution is implemented via:
- `lift` / `lift1`: de Bruijn index adjustment
- `subst`: single-variable substitution
- `substParallel`: parallel substitution
- `alphaEquiv`: alpha equivalence checking

## Package Structure

```
Core/         — Variable, Term, freeVars, size, binderDepth, Laws
Morphisms/    — Hom, Iso, Equivalence (substitution)
Constructions/— Subobjects, Quotients, Products, Universal
Properties/   — Invariants, Preservation, ClassificationData
Theorems/     — Basic, UniversalProperties, Classification, Main
Examples/     — Standard, Counterexamples
Bridges/      — ToAlgebra, ToTopology, ToGeometry, ToComputation
```
