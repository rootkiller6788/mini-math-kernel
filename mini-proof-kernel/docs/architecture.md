# MiniProofKernel Architecture

## Overview

MiniProofKernel provides a minimal proof kernel for propositional natural deduction.
It builds on MiniLogicKernel for formula representation and adds proof trees, tactics, and structural rules.

## Module Structure

### Core (3 modules)
- **Basic.lean** — ProofTree inductive type, Context operations, structural rules (weakening)
- **Objects.lean** — Proof objects (stub)
- **Laws.lean** — Logical laws (stub)

### Morphisms (3 modules)
- **Hom.lean** — Proof homomorphisms (stub)
- **Iso.lean** — Proof isomorphisms (stub)
- **Equivalence.lean** — Natural deduction helper combinators and classical reasoning

### Theorems (3 modules)
- **Basic.lean** — Tactic framework (ProofState, TacticResult, assumption, intro, apply, split, etc.)
- **Completeness.lean** — Completeness theorem (stub)
- **Soundness.lean** — Soundness theorem (stub)

### Constructions (4 modules)
- **Product.lean** — Conjunction/product construction (stub)
- **Coproduct.lean** — Disjunction/coproduct construction (stub)
- **Exponential.lean** — Implication/exponential construction (stub)
- **Negation.lean** — Negation construction (stub)

### Properties (4 modules)
- **NormalForm.lean** — Normal forms for proofs (stub)
- **Decidability.lean** — Decidability of proof checking (stub)
- **Consistency.lean** — Consistency of the logic (stub)
- **CutElimination.lean** — Cut elimination (stub)

### Examples (3 modules)
- **Classical.lean** — Classical logic examples (stub)
- **Intuitionistic.lean** — Intuitionistic logic examples (stub)
- **Propositional.lean** — General propositional examples (stub)

### Bridges (3 modules)
- **ToLogic.lean** — Bridge to logic kernel (stub)
- **ToTypeTheory.lean** — Bridge to type theory (stub)
- **ToCategory.lean** — Bridge to category theory (stub)

## Core Types

### ProofTree
The central type: `ProofTree : Context → Formula → Type` — a natural deduction proof tree indexed by its context (hypotheses) and conclusion formula.

Constructors cover all propositional connectives plus LEM for classical logic.

### Tactic Framework
`ProofState` with context and goal, `TacticResult` with done/subgoals/failed variants, `Tactic` as a function from state to result.

### Dependencies
- MiniLogicKernel (Formula type and operations)
