# mini-axiom-kernel

An axiom kernel for the Mini Math Kernel project. Defines axiom declarations, axiom sets, axiom systems, and provides tools for consistency checking and axiom independence.

## Structure

- **Core/** — Axiom, AxiomSet, AxiomSystem, standard axioms, AxiomRegistry
- **Morphisms/** — Homomorphisms, isomorphisms, equivalences between axiom systems
- **Constructions/** — Products, quotients, subobjects, universal constructions
- **Properties/** — Independence, completeness, consistency, decidability
- **Theorems/** — Soundness, deduction, compactness, completeness theorem
- **Examples/** — Peano arithmetic, group theory, set theory as axiom systems
- **Bridges/** — Bridges to logic, proof, and model kernels

## Dependencies

- `mini-logic-kernel`

## Usage

```lean
import MiniAxiomKernel

open MiniAxiomKernel
```
