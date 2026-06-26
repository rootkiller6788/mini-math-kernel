# Course Tree ¡ª mini-axiom-kernel

## Prerequisites

This module depends on:
- **mini-logic-kernel** (direct dependency via lakefile.lean)
  - Provides: Formula type, semantic evaluation, formula operations
  - Used in: Core/Basic.lean (Axiom definition over Formula)

## Internal Dependency Graph

```
Core/Basic.lean (Axiom, AxiomSet)
  |
  +---> Core/Objects.lean (Standard axioms)
  |
  +---> Core/Laws.lean (AxiomSystem, AxiomRegistry, isModel, isConsistent)
           |
           +---> Constructions/Subobjects.lean (Subtheory, signature, reduct)
           |        |
           |        +---> Constructions/Products.lean (Product theory)
           |        +---> Constructions/Quotients.lean (Quotient system)
           |        +---> Constructions/Universal.lean (Initial/terminal)
           |        +---> Properties/Independence.lean
           |        +---> Properties/Completeness.lean
           |        +---> Properties/Decidability.lean
           |        +---> Properties/Consistency.lean
           |
           +---> Morphisms/Hom.lean (FormulaTranslation, CheckedHom)
           |        |
           |        +---> Morphisms/Iso.lean (CheckedIso, AtomBijection)
           |        +---> Morphisms/Equivalence.lean (SystemEquivalence)
           |
           +---> Theorems/Soundness.lean
           +---> Theorems/Deduction.lean
           +---> Theorems/Compactness.lean
           +---> Theorems/CompletenessTheorem.lean
           +---> Theorems/MetaProperties.lean
           |
           +---> Bridges/ToLogic.lean
           |        |
           |        +---> Bridges/ToProof.lean
           |
           +---> Bridges/ToModel.lean
           |
           +---> Examples/Peano.lean
           +---> Examples/GroupTheory.lean
           +---> Examples/SetTheory.lean
           |
           +---> Applications/KnowledgeRepresentation.lean
           +---> Advanced/FiniteModelTheory.lean
           +---> Advanced/HomotopyLevel.lean
```

## External Dependencies (other mini-xxx-kernel modules)

| Module | Type | Used For |
|--------|------|----------|
| mini-logic-kernel | Required | Formula type, evaluation, atoms, operations |
| mini-proof-kernel | Target (bridge) | Proof tree generation and verification |
| mini-model-kernel | Target (bridge) | Model finding and classification |

## Downstream Dependencies

Modules that may depend on mini-axiom-kernel:
- mini-proof-kernel (axiom justification in proofs)
- mini-model-kernel (axiom-based model constraints)
- mini-set-kernel (ZFC axiom system)
- mini-number-kernel (Peano axiom system)
- mini-algebra-kernel (group/ring/field axiom systems)
