# MiniAxiomKernel Overview

The MiniAxiomKernel package provides the axiom layer of the Mini Math Kernel project. It defines formal representations of axioms, axiom sets, and axiom systems, along with tools for reasoning about their meta-properties.

## Key Concepts

- **Axiom** — A named formula asserted without proof, with an optional description.
- **AxiomSet** — A collection of axioms with lookup and traversal operations.
- **AxiomSystem** — A versioned, named collection of axioms forming a coherent theory.
- **AxiomRegistry** — A catalog of registered axiom systems.

## Core Operations

- Build axiom systems from individual axioms.
- Check axiom system consistency via brute-force model search (up to 16 atoms).
- Test axiom independence within a system.
- Register and look up axiom systems.

## Standard Axioms

- Identity: `A -> A`
- Non-contradiction: `not (A and not A)`
- Excluded middle: `A or not A`
