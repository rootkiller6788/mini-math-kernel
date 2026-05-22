# mini-logic-kernel -- Dependency Graph

## Internal Dependencies

```
Core/Basic.lean              (no deps)
Core/Objects.lean            -> Core/Basic
Core/Laws.lean               -> Core/Basic

Morphisms/Hom.lean           -> Core/Basic
Morphisms/Iso.lean           -> Core/Basic
Morphisms/Equivalence.lean   -> Core/Basic

Constructions/Subobjects.lean -> Core/Basic, Core/Objects
Constructions/Quotients.lean  -> Core/Basic
Constructions/Products.lean   -> Core/Basic
Constructions/Universal.lean  -> Core/Basic, Core/Objects

Properties/Invariants.lean       -> Core/Basic, Core/Objects
Properties/Preservation.lean     -> Core/Basic, Core/Objects, Morphisms/Hom
Properties/ClassificationData.lean -> Core/Basic

Theorems/Basic.lean               -> Core/Basic, Core/Laws
Theorems/UniversalProperties.lean -> Core/Basic, Constructions/Universal
Theorems/Classification.lean      -> Core/Basic, Properties/ClassificationData
Theorems/Main.lean                -> Core/Basic, Theorems/Basic, Theorems/Classification

Examples/Standard.lean        -> Core/Basic, Core/Objects
Examples/Counterexamples.lean -> Core/Basic, Core/Objects

Bridges/*.lean -> Core/Basic
```

## External Dependencies

None -- mini-logic-kernel is self-contained.
