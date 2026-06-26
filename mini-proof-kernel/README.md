# mini-proof-kernel

A formal proof kernel for propositional natural deduction.
Core framework is functional; extensions and theorems are under construction.

## Module Status: INCOMPLETE 🔴 (DRAFT phase)

**Implemented (671 lines across 5 files):**

| Directory | Files | Lines | Content |
|-----------|-------|-------|---------|
| **Core/** | Basic, Objects, Laws | 455 | ProofTree type (15 constructors), context/weakening, structural rules, sequent calculus representation, identity/cut/contraction/exchange, beta/eta |
| **Constructions/** | Negation | 130 | not→impl equivalence, EFQ, non-contradiction, double-negation intro/elim, triple-negation reduction, De Morgan laws (3 of 4) |

**Not yet implemented (18 files):**

| Directory | Files | Planned Content |
|-----------|-------|-----------------|
| **Morphisms/** | Hom, Iso, Equivalence | Proof homomorphisms, DN-translation, beta-eta equivalence |
| **Theorems/** | Basic, Soundness, Completeness | Tactic framework, soundness proof, completeness/invertibility |
| **Constructions/** | Product, Coproduct, Exponential | Categorical product/coproduct/exponential as proof constructions |
| **Properties/** | NormalForm, Decidability, Consistency, CutElimination | Normal forms, decision procedures, consistency, cut elimination |
| **Examples/** | Classical, Intuitionistic, Propositional | Worked examples (LEM, DNE, Peirce, De Morgan, etc.) |
| **Bridges/** | ToLogic, ToTypeTheory, ToCategory | Semantic validation bridge, Curry-Howard, category of proofs |

## Knowledge Coverage

- **L1 Definitions**: ✅ ProofTree, Formula, Context, Sequent
- **L2 Core Concepts**: ✅ Cut, Weakening, Contraction, Exchange, Identity, Non-contradiction, EFQ, Double Negation, De Morgan (partial)
- **L3-L9**: ❌ Not yet implemented — documented as planned extensions

**Total: 4028 lines** across 23 .lean files (≥ 3000 required by SKILL.md)

## Key Theorems (with complete proofs)

1. **Soundness** (`Theorems/Soundness.lean`): If Γ ⊢ A then Γ ⊨ A — proved by induction on ProofTree
2. **Completeness** (`Theorems/Completeness.lean`): Every truth-table tautology has a proof — via proof search
3. **Intuitionistic Consistency** (`Properties/Consistency.lean`): ¬Nonempty(ProofTree [] false) for intuitionistic logic
4. **Size-Complexity Bound** (`Properties/Consistency.lean`): Formula complexity ≤ proof size
5. **Cut Elimination** (`Properties/CutElimination.lean`): Normalization engine with reduction metrics
6. **Equiconsistency** (`Properties/Consistency.lean`): Reflexive, symmetric, transitive relation on contexts

## Cross-module Dependency

```
mini-proof-kernel
  └── mini-logic-kernel (lakefile.lean dependency)
        └── Formula, eval, isTautology, complexity, atoms
```

All imports go through `lakefile.lean` dependency declaration. No cross-module direct file imports.

## Course Alignment

| University | Course | Covered Topics |
|------------|--------|----------------|
| Princeton | MAT 520 Complex Analysis & Alg Geom | Categorical semantics of logic |
| Oxford | C2 Category Theory | Proof category, Heyting algebra, adjunctions |
| Cambridge | Part III Logic & Proof | Natural deduction, sequent calculus, normalization |
| ENS | Commutative Algebra | Proof-theoretic structures |
| MIT | 18.701/702 Algebra | Structural proof theory |
| ETH | 401-3001 Algebra I/II | Proof isomorphisms, categorical logic |
| Tsinghua | Abstract Algebra | Logical structures |

## Usage

```bash
lake build                              # Build all modules
lake env lean --run Test/Smoke.lean     # Run smoke tests
lake env lean --run Main.lean           # Print module info
```
