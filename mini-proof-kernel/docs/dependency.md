# MiniProofKernel Dependency Graph

## External Dependencies

- **MiniLogicKernel** — Provides `Formula` type, connectives, evaluation, transformations
  - Path: `../mini-logic-kernel`
  - Import: `MiniLogicKernel.Core.Basic`

## Internal Module Dependencies

```
MiniProofKernel.lean (root aggregator)
├── Core/Basic.lean           ← MiniLogicKernel.Core.Basic
├── Core/Objects.lean         ← Core/Basic
├── Core/Laws.lean            ← Core/Basic
├── Morphisms/Hom.lean        ← Core/Basic
├── Morphisms/Iso.lean        ← Core/Basic
├── Morphisms/Equivalence.lean ← Core/Basic
├── Theorems/Basic.lean       ← Core/Basic
├── Theorems/Completeness.lean ← Core/Basic
├── Theorems/Soundness.lean   ← Core/Basic
├── Constructions/Product.lean     ← Core/Basic
├── Constructions/Coproduct.lean   ← Core/Basic
├── Constructions/Exponential.lean ← Core/Basic
├── Constructions/Negation.lean    ← Core/Basic
├── Properties/NormalForm.lean     ← Core/Basic
├── Properties/Decidability.lean   ← Core/Basic
├── Properties/Consistency.lean    ← Core/Basic
├── Properties/CutElimination.lean ← Core/Basic
├── Examples/Classical.lean         ← Core/Basic
├── Examples/Intuitionistic.lean    ← Core/Basic
├── Examples/Propositional.lean     ← Core/Basic
├── Bridges/ToLogic.lean        ← Core/Basic
├── Bridges/ToTypeTheory.lean   ← Core/Basic
└── Bridges/ToCategory.lean     ← Core/Basic
```

All 22 sub-modules depend on Core/Basic (which depends on MiniLogicKernel).
The root aggregator imports all 23 modules (including itself via the sub-modules).

## Build Order

1. MiniLogicKernel.Core.Basic (external)
2. MiniProofKernel.Core.Basic
3. All other MiniProofKernel modules (any order, in parallel)
4. MiniProofKernel (root aggregator)
