/-
# MiniObjectKernel

The mathematical object typeclass — the common interface for
every structure in the mini-everything-math ecosystem.

## Sub-packages
- `Core`         — TheoryName, Object typeclass, Subobject, Quotient, Laws
- `Morphisms`    — Embedding, Iso, Equality (EqChain)
- `Constructions` — Subobjects, Quotients, Products, Universal (EmbeddingGraph)
- `Properties`   — Invariants, Preservation, ClassificationData
- `Theorems`     — Basic, UniversalProperties, Classification, Main
- `Examples`     — Standard, Counterexamples
- `Bridges`      — ToAlgebra, ToTopology, ToGeometry, ToComputation
-/

import MiniObjectKernel.Core.Basic
import MiniObjectKernel.Core.Objects
import MiniObjectKernel.Core.Laws
import MiniObjectKernel.Morphisms.Hom
import MiniObjectKernel.Morphisms.Iso
import MiniObjectKernel.Morphisms.Equivalence
import MiniObjectKernel.Constructions.Subobjects
import MiniObjectKernel.Constructions.Quotients
import MiniObjectKernel.Constructions.Products
import MiniObjectKernel.Constructions.Universal
import MiniObjectKernel.Properties.Invariants
import MiniObjectKernel.Properties.Preservation
import MiniObjectKernel.Properties.ClassificationData
import MiniObjectKernel.Theorems.Basic
import MiniObjectKernel.Theorems.UniversalProperties
import MiniObjectKernel.Theorems.Classification
import MiniObjectKernel.Theorems.Main
import MiniObjectKernel.Examples.Standard
import MiniObjectKernel.Examples.Counterexamples
import MiniObjectKernel.Bridges.ToAlgebra
import MiniObjectKernel.Bridges.ToTopology
import MiniObjectKernel.Bridges.ToGeometry
import MiniObjectKernel.Bridges.ToComputation
