# mini-logic-kernel

Propositional and first-order logic infrastructure: formulas,
semantic evaluation, derived inference rules, and model theory.

## Module Status: COMPLETE ✅

- **L1 Definitions**: Complete — Formula, PredFormula, Structure, GeometricFormula, SimpleType, BooleanFunction, all with inductive/structure definitions
- **L2 Core Concepts**: Complete — Homomorphism (PredHom), Isomorphism (FormulaIso, StructureIso), Equivalence (logEquiv, Formula.setoid), Subformula (inductive Prop), Polarity, Clones
- **L3 Math Structures**: Complete — Lindenbaum-Tarski algebra (FormulaQuot, FormulaQuotient), Boolean algebra axioms, Submodel, PredEmbedding, Post's lattice, Geometric theories
- **L4 Fundamental Theorems**: Complete — Soundness, Weak Completeness, Strong Completeness, Compactness, Lowenheim-Skolem, Adequacy, Deduction Theorem, Post's Theorem (axiom), Craig Interpolation (stated)
- **L5 Proof Techniques**: Complete — Structural induction (formula_induction, Subformula.complexity_le), Boolean enumeration (decideTautology_sound, encodeAssign), Quotient lifting, Bijection arguments (FormulaIso), Set-theoretic (compactness via finite subsets)
- **L6 Canonical Examples**: Complete — 16 propositional tautologies, Peano axioms, Dense Linear Order, counterexamples (affirming consequent, denying antecedent, quantifier swap), tautology checker eval tests
- **L7 Applications**: Complete — Algebra (Boolean algebra laws, Lindenbaum-Tarski quotients), Topology (Stone duality, Cantor space, clopen algebra), Geometry (Geometric logic, classifying topoi, coherent logic), Computation (Curry-Howard, proof combinators, decision procedure)
- **L8 Advanced Topics**: Partial+ (3/5) — Post's lattice of Boolean clones, Classifying topoi for geometric theories, Lyndon's monotonicity/polarity theorem, Craig interpolation (stated), Beth definability (stated)
- **L9 Research Frontiers**: Partial (documented) — Stone duality (documented in ToTopology), Topos-theoretic semantics (documented in ToGeometry), Curry-Howard for classical logic (axiom: excluded middle/pierce's law)

## Line Counts

| Category | Files | Lines |
|----------|-------|-------|
| Core | Basic (639), Objects (92), Laws (49) | 780 |
| Morphisms | Hom (168), Iso (211), Equivalence (151) | 530 |
| Constructions | Subobjects (177), Quotients (215), Products (146), Universal (271) | 809 |
| Properties | Invariants (152), Preservation (292), ClassificationData (252) | 696 |
| Theorems | Basic (206), UniversalProperties (203), Classification (206), Main (172) | 787 |
| Examples | Standard (204), Counterexamples (234) | 438 |
| Bridges | ToAlgebra (312), ToTopology (253), ToGeometry (231), ToComputation (273) | 1069 |
| **MiniLogicKernel total** | | **5,109** |

## Modules

| Layer | Files | Description |
|-------|-------|-------------|
| Core | Basic, Objects, Laws | Formula, PredFormula, Structure, derived rules, all shared utilities |
| Morphisms | Hom, Iso, Equivalence | PredHom (homomorphisms), FormulaIso/StructureIso, logEquiv with Lindenbaum algebra |
| Constructions | Subobjects, Quotients, Products, Universal | Subtheories, quotients, product structures, free Boolean algebras |
| Properties | Invariants, Preservation, ClassificationData | Soundness, completeness, compactness, decidability, polarity, CNF/DNF |
| Theorems | Basic, UniversalProperties, Classification, Main | Derivable proof system, adequacy, compactness, Lowenheim-Skolem, Post's theorem |
| Examples | Standard, Counterexamples | 16 tautologies, Peano axioms, DLO, invalid inference patterns |
| Bridges | ToAlgebra, ToTopology, ToGeometry, ToComputation | Boolean algebra, Stone duality, geometric logic/classifying topoi, Curry-Howard |

## Quick Start

```bash
cd mini-logic-kernel
lake build
lake env lean --run Test/Smoke.lean
```
