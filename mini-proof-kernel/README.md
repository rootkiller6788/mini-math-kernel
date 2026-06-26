# mini-proof-kernel

A minimal proof kernel for propositional natural deduction with 23 modules.

## Structure

- **Core/Basic** — ProofTree type, context operations, structural rules
- **Core/Objects** — Proof objects and representation
- **Core/Laws** — Logical laws and inference rules
- **Morphisms/Hom** — Proof homomorphisms
- **Morphisms/Iso** — Proof isomorphisms  
- **Morphisms/Equivalence** — Natural deduction helper combinators
- **Theorems/Basic** — Minimal tactic framework for proof tree construction
- **Theorems/Completeness** — Completeness theorem (stub)
- **Theorems/Soundness** — Soundness theorem (stub)
- **Constructions/** — Product, coproduct, exponential, negation constructions
- **Properties/** — NormalForm, Decidability, Consistency, CutElimination
- **Examples/** — Classical, intuitionistic, and propositional examples
- **Bridges/** — Bridges to logic, type theory, and category theory

## Usage

```bash
lake build
lake env lean --run Test/Smoke.lean
```
