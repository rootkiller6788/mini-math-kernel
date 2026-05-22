/-
# Mini Proof Kernel

Root aggregator — imports all 23 modules of the proof kernel sub-package.
-/

import MiniProofKernel.Core.Basic
import MiniProofKernel.Core.Objects
import MiniProofKernel.Core.Laws
import MiniProofKernel.Morphisms.Hom
import MiniProofKernel.Morphisms.Iso
import MiniProofKernel.Morphisms.Equivalence
import MiniProofKernel.Theorems.Basic
import MiniProofKernel.Theorems.Completeness
import MiniProofKernel.Theorems.Soundness
import MiniProofKernel.Constructions.Product
import MiniProofKernel.Constructions.Coproduct
import MiniProofKernel.Constructions.Exponential
import MiniProofKernel.Constructions.Negation
import MiniProofKernel.Properties.NormalForm
import MiniProofKernel.Properties.Decidability
import MiniProofKernel.Properties.Consistency
import MiniProofKernel.Properties.CutElimination
import MiniProofKernel.Examples.Classical
import MiniProofKernel.Examples.Intuitionistic
import MiniProofKernel.Examples.Propositional
import MiniProofKernel.Bridges.ToLogic
import MiniProofKernel.Bridges.ToTypeTheory
import MiniProofKernel.Bridges.ToCategory
