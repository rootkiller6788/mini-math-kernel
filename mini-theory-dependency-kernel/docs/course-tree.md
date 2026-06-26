# Course Tree — mini-theory-dependency-kernel

## Learning Prerequisites

```
mini-theory-dependency-kernel
│
├── [REQUIRED] mini-object-kernel
│   └── Concepts: TheoryName (hierarchical identifiers), Object typeclass
│
├── [REQUIRED] Lean 4 basics
│   └── Topics: inductive types, structures, pattern matching, #eval, termination_by
│
├── [REQUIRED] Graph Theory (basic)
│   └── Topics: directed graphs, DAGs, topological sort, SCCs, DFS/BFS
│
├── [RECOMMENDED] Mathematical Logic
│   └── Topics: formal theories, signatures, axioms, interpretability, consistency strength
│
└── [RECOMMENDED] Build Systems
    └── Topics: Make, Ninja, incremental builds, dependency resolution
```

## Module Learning Path

### Level 1: Core Data Structures (1-2 hours)

**Files**: `Core/Basic.lean`

**Concepts**:
- `TheoryNode` — named theory with metadata (name, title, version, path)
- `DependencyKind` — import, bridge, example, test
- `DependencyEdge` — source → target relation with kind and description
- `TheoryManifest` — self + dependencies + dependents
- `DependencyGraph` — nodes + edges, with basic CRUD operations

**Exercises**:
1. Create a dependency graph with 3 nodes and 2 edges
2. Add a node, check `nodeCount` increases
3. Compute `edgesFrom`, `edgesTo`, `depsOf` for a specific node

### Level 2: Graph Algorithms (2-3 hours)

**Files**: `Constructions/Universal.lean`

**Concepts**:
- Kahn's algorithm for topological ordering
- DFS-based cycle detection
- BFS transitive closure (deps and dependents)
- Build order = topological order
- Rebuild order = affected nodes after a change

**Exercises**:
1. Build a chain A→B→C, verify topological order is [A, B, C]
2. Create a cycle A→B→C→A, verify `findCycle` returns non-none
3. Compute `rebuildOrder` when leaf node changes

### Level 3: Graph Classification (1-2 hours)

**Files**: `Constructions/Universal.lean`, `Properties/Invariants.lean`

**Concepts**:
- SCC detection and condensation (always acyclic)
- Forest detection (indegree ≤ 1)
- Tree detection (forest + connected + one root)
- Weakly/strongly connected components
- Depth, width, rank, centrality measures

**Exercises**:
1. Build a diamond graph, verify it's a DAG but not a forest
2. Compute SCCs for a graph with a mutual dependency pair
3. Compute impact factor ranking

### Level 4: Theory Objects (1-2 hours)

**Files**: `Core/Objects.lean`, `Core/Laws.lean`

**Concepts**:
- Signatures (constants, functions, relations with arities)
- Axioms and axiom schemes
- FormalTheory = signature + axioms
- Conservative extensions
- Transitivity laws, monotonicity

**Exercises**:
1. Define GroupTheory with associativity, identity, inverse axioms
2. Show that AbelianGroup is a proper extension of Group
3. Verify that adding a definition is conservative

### Level 5: Theory Morphisms (1-2 hours)

**Files**: `Morphisms/Hom.lean`, `Morphisms/Iso.lean`, `Morphisms/Equivalence.lean`

**Concepts**:
- Symbol maps between signatures
- Theory morphisms (axiom-preserving translations)
- Interpretability (exists morphism A→B)
- Mutual interpretability (morphisms both ways)
- Theory equivalence (compositions ≈ identity)
- Graph isomorphism and invariants

**Exercises**:
1. Build an interpretation graph of algebraic theories
2. Check if two dependency graphs are isomorphic (via invariants)
3. Classify theories by signature size equivalence classes

### Level 6: Properties & Classification (1-2 hours)

**Files**: `Properties/Invariants.lean`, `Properties/Preservation.lean`, `Properties/ClassificationData.lean`

**Concepts**:
- Dependency closure, depth, width, rank
- Impact factor (dependents/dependencies ratio)
- Betweenness centrality approximation
- Cyclomatic complexity, density, balance ratio
- Acyclicity preservation under edge removal
- Consistency strength classification

**Exercises**:
1. Compute the structural summary of the ZFC dependency graph
2. Verify acyclicity is preserved when removing an edge
3. Classify PA by consistency strength and axiomatizability

### Level 7: Applications (2-3 hours)

**Files**: `Examples/`, `Bridges/`

**Concepts**:
- Real mathematical dependency hierarchies (ZFC, Algebra, Topology, Geometry)
- Build system simulation (Make, Ninja, CI pipelines)
- Parallel build scheduling and critical path analysis
- Cache invalidation and incremental rebuild
- Package manager dependency resolution

**Exercises**:
1. Simulate a Make build of the algebraic theory hierarchy
2. Compute parallel build levels for the topology dependency graph
3. Find bottleneck targets in the geometry dependency graph
4. Simulate a package install with dependency resolution
