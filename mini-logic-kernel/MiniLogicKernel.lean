/-
# MiniLogicKernel

The mathematical logic kernel — propositional and predicate logic,
semantic evaluation, derived inference rules, and model theory.

## Sub-packages
- `Core`         — Formula, PredFormula, Structure, Laws
- `Morphisms`    — Hom, Iso, Equivalence
- `Constructions` — Subobjects, Quotients, Products, Universal
- `Properties`   — Invariants, Preservation, ClassificationData
- `Theorems`     — Basic, UniversalProperties, Classification, Main
- `Examples`     — Standard, Counterexamples
- `Bridges`      — ToAlgebra, ToTopology, ToGeometry, ToComputation
-/

import MiniLogicKernel.Core.Basic
import MiniLogicKernel.Core.Objects
import MiniLogicKernel.Core.Laws
import MiniLogicKernel.Morphisms.Hom
import MiniLogicKernel.Morphisms.Iso
import MiniLogicKernel.Morphisms.Equivalence
import MiniLogicKernel.Constructions.Subobjects
import MiniLogicKernel.Constructions.Quotients
import MiniLogicKernel.Constructions.Products
import MiniLogicKernel.Constructions.Universal
import MiniLogicKernel.Properties.Invariants
import MiniLogicKernel.Properties.Preservation
import MiniLogicKernel.Properties.ClassificationData
import MiniLogicKernel.Theorems.Basic
import MiniLogicKernel.Theorems.UniversalProperties
import MiniLogicKernel.Theorems.Classification
import MiniLogicKernel.Theorems.Main
import MiniLogicKernel.Examples.Standard
import MiniLogicKernel.Examples.Counterexamples
import MiniLogicKernel.Bridges.ToAlgebra
import MiniLogicKernel.Bridges.ToTopology
import MiniLogicKernel.Bridges.ToGeometry
import MiniLogicKernel.Bridges.ToComputation
