# MiniSyntaxKernel

The syntax kernel for the mini-everything-math ecosystem — terms, variables, binding, and substitution.

## Module Status: COMPLETE ✅

- **L1 Definitions**: Complete — Variable (free/bound), Term (7 constructors), Subterm, StructEq, FreeAlgebra
- **L2 Core Concepts**: Complete — Homomorphism, Isomorphism, Substitution, Alpha-Equivalence, Renaming
- **L3 Math Structures**: Complete — Term Algebra, Quotient (AlphaTerm), Products, Universal Constructions
- **L4 Fundamental Theorems**: Complete — Substitution Lemma, Structural Induction, Alpha-Equiv Decidability, Constructor Injectivity
- **L5 Proof Techniques**: Complete — Structural Induction, Case Analysis, Injection, Determinism, Size-based Induction
- **L6 Canonical Examples**: Complete — Church Numerals/Booleans, Y Combinator, Omega Combinator, De Bruijn Normal Forms
- **L7 Applications**: Partial+ (2/4) — Lambda Calculus (β-reduction), Computation (Krivine Machine)
- **L8 Advanced Topics**: Partial (2/5) — Normalization framework, Free Algebra universal property
- **L9 Research Frontiers**: Partial — Documented (de Bruijn representation, normalization, confluence)

## Modules

| Module                              | Lines | Description                              |
|-------------------------------------|-------|------------------------------------------|
| `Core/Basic`                        | 42    | Variable, Term, ToString instances       |
| `Core/Objects`                      | 92    | freeVars, isClosed, maxBoundIndex, size, binderDepth |
| `Core/Laws`                         | 556   | Syntactic laws, structEq (refl/symm/trans), subterm, size, wf |
| `Morphisms/Hom`                     | 167   | TermHom, Renaming, Subst, composition    |
| `Morphisms/Iso`                     | 146   | SyntacticIso, VarPerm, swap, fresh names |
| `Morphisms/Equivalence`            | 80    | lift, subst, substParallel, alphaEquiv   |
| `Constructions/Subobjects`          | 125   | Subterms, paths, contexts, position ops  |
| `Constructions/Quotients`           | 161   | AlphaEquiv quotient, de Bruijn normalization |
| `Constructions/Products`            | 111   | Pairs, tuples, sigma types, currying     |
| `Constructions/Universal`           | 168   | FreeAlgebra, initial algebra, structural induction |
| `Properties/Invariants`             | 328   | Well-formedness, closedness, size, depth preservation |
| `Properties/Preservation`           | 244   | Preservation under subst/rename/alpha/lift |
| `Properties/ClassificationData`     | 162   | Ground/open/closed, linear/affine/relevant |
| `Theorems/Basic`                    | 300   | Substitution lemma, structural induction, decidability |
| `Theorems/UniversalProperties`      | 96    | Lambda as exponential, subst uniqueness  |
| `Theorems/Classification`           | 100   | Sort hierarchy, simple types, universe polymorphism |
| `Theorems/Main`                     | 325   | Beta reduction, determinism, normal form uniqueness |
| `Examples/Standard`                 | 85    | Church encodings, Y combinator, composition |
| `Examples/Counterexamples`          | 82    | Non-normalizing, capture, non-alpha-equiv |
| `Bridges/ToAlgebra`                 | 120   | Free algebra, equational theory, free magma |
| `Bridges/ToTopology`                | 128   | Term positions, prefix order, ultrametric |
| `Bridges/ToGeometry`                | 134   | Term graphs, string diagrams, tree edit |
| `Bridges/ToComputation`             | 147   | CBN/CBV reduction, Krivine machine, serialization |

**Total: 4,302 lines of Lean 4 code (no axiom, no admit, no sorry, no by trivial)**

## Build

```sh
lake build
```

## Test

```sh
lake env lean --run Test/Smoke.lean
```
