# MiniSyntaxKernel

The syntax kernel for the mini-everything-math ecosystem — terms, variables, binding, and substitution.

## Modules

| Module                              | Description                              |
|-------------------------------------|------------------------------------------|
| `Core/Basic`                        | Variable, Term, ToString instances       |
| `Core/Objects`                      | freeVars, isClosed, maxBoundIndex, size, binderDepth |
| `Core/Laws`                         | Syntactic laws and well-formedness       |
| `Morphisms/Hom`                     | Homomorphism definitions                 |
| `Morphisms/Iso`                     | Isomorphism definitions                  |
| `Morphisms/Equivalence`            | Substitution: lift, subst, substParallel, alphaEquiv |
| `Constructions/Subobjects`          | Subobject constructions                  |
| `Constructions/Quotients`           | Quotient constructions                   |
| `Constructions/Products`            | Product constructions                    |
| `Constructions/Universal`           | Universal constructions                  |
| `Properties/Invariants`             | Invariant properties                     |
| `Properties/Preservation`           | Preservation properties                  |
| `Properties/ClassificationData`     | Classification data structures           |
| `Theorems/Basic`                    | Basic theorems                           |
| `Theorems/UniversalProperties`      | Universal property theorems              |
| `Theorems/Classification`           | Classification theorems                  |
| `Theorems/Main`                     | Main theorems                            |
| `Examples/Standard`                 | Standard examples                        |
| `Examples/Counterexamples`          | Counterexamples                          |
| `Bridges/ToAlgebra`                 | Bridge to algebraic structures           |
| `Bridges/ToTopology`                | Bridge to topological structures         |
| `Bridges/ToGeometry`                | Bridge to geometric structures           |
| `Bridges/ToComputation`             | Bridge to computational structures       |

## Build

```sh
lake build
```

## Test

```sh
lake env lean --run Test/Smoke.lean
```
