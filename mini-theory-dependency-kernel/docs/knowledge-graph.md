# Knowledge Graph — mini-theory-dependency-kernel

## Position in the Mini-Everything-Math Ecosystem

```
mini-everything-math/
├── mini-object-kernel/           ← TheoryName type, Object typeclass
│   └── (dependency: none, foundation layer)
│
├── mini-theory-dependency-kernel/  ← THIS KERNEL
│   └── imports: mini-object-kernel (for TheoryName shared type)
│
├── mini-logic-kernel/            ← Uses dependency tracking for proof ordering
├── mini-axiom-kernel/            ← Uses dependency tracking for axiom hierarchies
└── mini-construction-kernel/     ← Uses topological sort for construction pipelines
```

## Internal Module Graph

```
MiniTheoryDependencyKernel.lean (top-level re-export, ~4,500 LoC total)
│
├── Core/
│   ├── Basic.lean          ← TheoryNode, DependencyEdge, DependencyGraph
│   │   └── imports: MiniObjectKernel.Core.Basic
│   ├── Objects.lean        ← Signature, Axiom, FormalTheory, TheoryExtension
│   │   └── imports: Core.Basic
│   └── Laws.lean           ← acyclicity, transitivity, conservativity predicates
│       └── imports: Core.Basic, Core.Objects, Constructions.Universal
│
├── Constructions/
│   ├── Universal.lean      ← topologicalOrder, findCycle, transitiveDeps, SCCs
│   │   └── imports: Core.Basic
│   ├── Subobjects.lean     ← inducedSubgraph, downwardClosure, SubtheoryRelation
│   │   └── imports: Core.Basic, Core.Objects
│   ├── Quotients.lean      ← QuotientTheory, ExtensionChain, AxiomIndependence
│   │   └── imports: Core.Basic, Core.Objects, Constructions.Subobjects
│   └── Products.lean       ← TheoryUnion, TheoryCombination, graph product/merge
│       └── imports: Core.Basic, Core.Objects, Constructions.Subobjects
│
├── Morphisms/
│   ├── Hom.lean            ← SymbolMap, TheoryMorphism, Interpretation
│   │   └── imports: Core.Basic, Core.Objects
│   ├── Iso.lean            ← TheoryIsomorphism, GraphIsomorphism, rename
│   │   └── imports: Core.Basic, Core.Objects, Core.Laws, Morphisms.Hom
│   └── Equivalence.lean    ← MutualInterpretability, TheoryEquivalence
│       └── imports: Core.Basic, Core.Objects, Morphisms.Hom, Morphisms.Iso
│
├── Properties/
│   ├── Invariants.lean     ← depth, rank, impactFactor, centrality, connectivity
│   │   └── imports: Core.Basic, Core.Objects, Core.Laws, Constructions.Universal
│   ├── Preservation.lean   ← acyclicity preservation, morphism compatibility
│   │   └── imports: Core.Basic, Core.Objects, Morphisms.Hom, Properties.Invariants
│   └── ClassificationData.lean ← ConsistencyClass, TheoryClassification
│       └── imports: Core.Basic, Core.Objects, Properties.Invariants
│
├── Theorems/
│   ├── Basic.lean              ← topological order, edge removal, in-degree bounds
│   ├── UniversalProperties.lean ← product node count, free theory, transitive closure
│   ├── Classification.lean      ← interpretability, classification, dependency profile
│   └── Main.lean                ← build chain existence, intersection bounds
│
├── Examples/
│   ├── Standard.lean        ← ZFC, group hierarchy, ring theory, PA, mutual interp
│   └── Counterexamples.lean ← cyclic, self-dep, mutual dep, inconsistent combo
│
└── Bridges/
    ├── ToAlgebra.lean       ← 12-level algebraic hierarchy dependency graph
    ├── ToTopology.lean      ← 8-level topology chain
    ├── ToGeometry.lean      ← 6-theory geometry dependencies
    └── ToComputation.lean   ← Make/Ninja/CI pipeline simulation
```

## Cross-Kernel Dependencies

| Consuming Kernel | What It Uses |
|-----------------|--------------|
| mini-logic-kernel | Build order for proof compilation |
| mini-axiom-kernel | Dependency tracking for axiom hierarchies |
| mini-construction-kernel | Topological sort for construction pipelines |

## Key Design Decisions

1. **TheoryName from mini-object-kernel**: All theory identifiers are hierarchical dotted paths (e.g., `Algebra.GroupTheory.AbelianGroup`), shared across the ecosystem via `MiniObjectKernel.TheoryName`.

2. **Graph-first design**: The `DependencyGraph` is the central data structure. All algorithms operate on it directly via `DependencyGraph.` prefix methods.

3. **Fuel-based recursion**: All recursive graph algorithms use explicit fuel parameters (`Nat` with pattern matching on `fuel + 1`) for guaranteed termination with Lean's structural recursion checker.

4. **Boolean predicates**: Properties like `isAcyclic`, `isValid`, `isForest` are `Bool`-valued (executable) rather than `Prop`-valued (proof-only), enabling `#eval` verification.

5. **Separation of mechanics from semantics**: The dependency graph layer (`DependencyGraph`, `DependencyEdge`) is separate from the theory object layer (`FormalTheory`, `Signature`, `Axiom`), allowing the graph algorithms to work on any named nodes.
