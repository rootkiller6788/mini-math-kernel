# MiniProofKernel Coverage

## Module Coverage

| Module | Status | Lines | Description |
|--------|--------|-------|-------------|
| Core/Basic | Implemented | ~110 | ProofTree, Context, weakening, size |
| Core/Objects | Stub | ~10 | Proof objects |
| Core/Laws | Stub | ~10 | Logical laws |
| Morphisms/Hom | Stub | ~10 | Proof homomorphisms |
| Morphisms/Iso | Stub | ~10 | Proof isomorphisms |
| Morphisms/Equivalence | Implemented | ~55 | Natural deduction helpers |
| Theorems/Basic | Implemented | ~85 | Tactic framework |
| Theorems/Completeness | Stub | ~10 | Completeness |
| Theorems/Soundness | Stub | ~10 | Soundness |
| Constructions/* (4) | Stubs | ~40 | Product, Coproduct, Exponential, Negation |
| Properties/* (4) | Stubs | ~40 | NormalForm, Decidability, Consistency, CutElimination |
| Examples/* (3) | Stubs | ~30 | Classical, Intuitionistic, Propositional |
| Bridges/* (3) | Stubs | ~30 | ToLogic, ToTypeTheory, ToCategory |

## Feature Coverage

- Natural deduction proof trees: Full (all 16 constructors)
- Structural rules: Weakening implemented
- Classical logic: LEM constructor included
- Tactic framework: 9 tactics (assumption, intro, apply, split, left, right, exact, orElse, thenTac)
- Natural deduction combinators: assume, applyModusPonens, andIntro/Left/Right, introImpl/OrLeft/OrRight/Not, byContradiction, doubleNegElim
- Proof size metric: Implemented
- Proof validity check: Stub (always true)
