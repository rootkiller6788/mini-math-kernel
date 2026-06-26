/-
# MiniTheoryDependencyKernel

Theory dependency tracking — the "build system" of the math kernel.
Tracks which theory depends on which, with graph algorithms for
topological ordering, cycle detection, transitive closure, and
build/rebuild order computation.

## Sub-packages
- `Core`         — TheoryNode, DependencyKind, DependencyEdge, TheoryManifest, DependencyGraph
- `Morphisms`    — Dependency morphisms (stubs)
- `Constructions` — Graph algorithms: topologicalOrder, findCycle, transitiveDeps, buildOrder, rebuildOrder, stats
- `Properties`   — Dependency invariants (stubs)
- `Theorems`     — Dependency theorems (stubs)
- `Examples`     — Standard examples, counterexamples (stubs)
- `Bridges`      — Cross-domain dependency bridges (stubs)
-/

import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects
import MiniTheoryDependencyKernel.Core.Laws
import MiniTheoryDependencyKernel.Morphisms.Hom
import MiniTheoryDependencyKernel.Morphisms.Iso
import MiniTheoryDependencyKernel.Morphisms.Equivalence
import MiniTheoryDependencyKernel.Constructions.Subobjects
import MiniTheoryDependencyKernel.Constructions.Quotients
import MiniTheoryDependencyKernel.Constructions.Products
import MiniTheoryDependencyKernel.Constructions.Universal
import MiniTheoryDependencyKernel.Properties.Invariants
import MiniTheoryDependencyKernel.Properties.Preservation
import MiniTheoryDependencyKernel.Properties.ClassificationData
import MiniTheoryDependencyKernel.Theorems.Basic
import MiniTheoryDependencyKernel.Theorems.UniversalProperties
import MiniTheoryDependencyKernel.Theorems.Classification
import MiniTheoryDependencyKernel.Theorems.Main
import MiniTheoryDependencyKernel.Examples.Standard
import MiniTheoryDependencyKernel.Examples.Counterexamples
import MiniTheoryDependencyKernel.Bridges.ToAlgebra
import MiniTheoryDependencyKernel.Bridges.ToTopology
import MiniTheoryDependencyKernel.Bridges.ToGeometry
import MiniTheoryDependencyKernel.Bridges.ToComputation
