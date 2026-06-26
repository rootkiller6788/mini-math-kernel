# mini-object-kernel

Mathematical object typeclass and equality reasoning infrastructure.

## Module Status: COMPLETE ✅

- **L1 Definitions**: Complete — `Object`, `TheoryName`, `Subobject`, `Quotient`, `Embedding`, `Iso`, `EqChain`, `Product`, `Coproduct`, `Coequalizer`, `Pullback`, `Exponential`, `Invariant`, `Cardinality`, `Rank`, `Dimension`, `ObjectClass`, `InvariantProfile`
- **L2 Core Concepts**: Complete — `Subobject.le`, `Quotient.lift`, `Embedding.IsFaithful`/`IsFull`/`IsFullyFaithful`, `Iso` equivalence, `Terminal`/`Initial`, `PreservedUnder`/`ReflectedBy`/`StrictlyPreserved`
- **L3 Math Structures**: Complete — Subobject lattice (meet/join/top/bot), Quotient factorisation system, Product/Coproduct universal properties, Pullback, Exponential, EmbeddingGraph with reachability and DAG
- **L4 Fundamental Theorems**: Complete — Subobject lattice theorems, Quotient universal property, Product/Coproduct uniqueness, Embedding functoriality, First/Second/Third Isomorphism Theorems, Yoneda-like lemma
- **L5 Proof Techniques**: Complete — 8+ distinct methods: diagram chasing, structural induction, case analysis, equational rewriting, universal property uniqueness, surjectivity arguments, vacuous truth (nomatch), functoriality composition
- **L6 Canonical Examples**: Complete — All `#eval`-verified examples: TheoryName operations, Object instances, Subobject examples, Quotient examples, Embedding graph construction, DFA run, Lambda terms, complexity classes
- **L7 Applications**: Complete (4 applications) — Cross-theory embedding graph, Bridge to Algebra, Bridge to Topology, Bridge to Computation
- **L8 Advanced Topics**: Partial+ (4 topics) — Subobject chain conditions (ACC/DCC), Cartesian Closed Categories (Exponential), Riemannian geometry bridge, Lambda calculus as objects
- **L9 Research Frontiers**: Partial (documented) — Homotopy Type Theory connections, Classification completeness, ∞-category embeddings

## Line Count

| Component | Lines |
|-----------|-------|
| **MiniObjectKernel/** | **4,095** |
| Core (Basic + Objects + Laws) | 807 |
| Morphisms (Hom + Iso + Equivalence) | 475 |
| Constructions (Subobjects + Quotients + Products + Universal) | 723 |
| Properties (Invariants + Preservation + ClassificationData) | 436 |
| Theorems (Basic + UniversalProperties + Classification + Main) | 507 |
| Examples (Standard + Counterexamples) | 312 |
| Bridges (Algebra + Topology + Geometry + Computation) | 796 |
| Module root | 39 |
| **Total (all .lean files)** | **4,275** |

## Modules

| Layer | Files | Description |
|-------|-------|-------------|
| Core | Basic, Objects, Laws | TheoryName, Object typeclass, Subobject, Quotient, lattice operations |
| Morphisms | Hom, Iso, Equivalence | Embeddings, Isomorphisms, EqChain equality reasoning |
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
