/-
# MiniSyntaxKernel

The syntax kernel — terms, variables, binding, and substitution.

## Sub-packages
- `Core`         — Variable, Term, freeVars, size, binderDepth, Laws
- `Morphisms`    — Substitution (Hom, Iso, Equivalence)
- `Constructions` — Subobjects, Quotients, Products, Universal
- `Properties`   — Invariants, Preservation, ClassificationData
- `Theorems`     — Basic, UniversalProperties, Classification, Main
- `Examples`     — Standard, Counterexamples
- `Bridges`      — ToAlgebra, ToTopology, ToGeometry, ToComputation
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects
import MiniSyntaxKernel.Core.Laws
import MiniSyntaxKernel.Morphisms.Hom
import MiniSyntaxKernel.Morphisms.Iso
import MiniSyntaxKernel.Morphisms.Equivalence
import MiniSyntaxKernel.Constructions.Subobjects
import MiniSyntaxKernel.Constructions.Quotients
import MiniSyntaxKernel.Constructions.Products
import MiniSyntaxKernel.Constructions.Universal
import MiniSyntaxKernel.Properties.Invariants
import MiniSyntaxKernel.Properties.Preservation
import MiniSyntaxKernel.Properties.ClassificationData
import MiniSyntaxKernel.Theorems.Basic
import MiniSyntaxKernel.Theorems.UniversalProperties
import MiniSyntaxKernel.Theorems.Classification
import MiniSyntaxKernel.Theorems.Main
import MiniSyntaxKernel.Examples.Standard
import MiniSyntaxKernel.Examples.Counterexamples
import MiniSyntaxKernel.Bridges.ToAlgebra
import MiniSyntaxKernel.Bridges.ToTopology
import MiniSyntaxKernel.Bridges.ToGeometry
import MiniSyntaxKernel.Bridges.ToComputation
