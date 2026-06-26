# Dependency Graph — MiniSyntaxKernel

```
MiniSyntaxKernel
  ├── Core/Basic           (no imports)
  ├── Core/Objects         → Core/Basic
  ├── Core/Laws            → Core/Basic, Core/Objects
  ├── Morphisms/Hom        → Core/Basic
  ├── Morphisms/Iso        → Core/Basic
  ├── Morphisms/Equivalence → Core/Basic
  ├── Constructions/Subobjects  → Core/Basic
  ├── Constructions/Quotients   → Core/Basic
  ├── Constructions/Products    → Core/Basic
  ├── Constructions/Universal   → Core/Basic
  ├── Properties/Invariants     → Core/Basic
  ├── Properties/Preservation   → Core/Basic
  ├── Properties/ClassificationData → Core/Basic
  ├── Theorems/Basic            → Core/Basic
  ├── Theorems/UniversalProperties → Core/Basic
  ├── Theorems/Classification   → Core/Basic
  ├── Theorems/Main             → Core/Basic
  ├── Examples/Standard         → Core/Basic
  ├── Examples/Counterexamples  → Core/Basic
  ├── Bridges/ToAlgebra         → Core/Basic
  ├── Bridges/ToTopology        → Core/Basic
  ├── Bridges/ToGeometry        → Core/Basic
  └── Bridges/ToComputation     → Core/Basic
```

All modules currently import only `Core.Basic`. The `Core.Laws` module additionally imports `Core.Objects`.
