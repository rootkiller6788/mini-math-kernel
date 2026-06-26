# Course Alignment — mini-theory-dependency-kernel

## How This Kernel Maps to Academic Curricula

### Computer Science: Data Structures & Algorithms

| Topic | Kernel Implementation |
|-------|----------------------|
| Graph representation (adjacency list) | `DependencyGraph` with `nodes`/`edges` lists |
| Topological sort (Kahn's algorithm) | `DependencyGraph.topologicalOrder` |
| Cycle detection (DFS) | `DependencyGraph.findCycle` |
| Transitive closure | `DependencyGraph.transitiveClosure` |
| Strongly Connected Components | `DependencyGraph.condensation`, `.sccs` |
| BFS/DFS graph traversal | `transitiveDeps`, `isWeaklyConnected`, `ancestors` |
| Shortest paths / diameter | `dependencyDiameter`, `pathsOfLength` |
| Graph classification (tree/forest/DAG) | `isTree`, `isForest`, `isDAG` |

**Courses**: CS 61B (Data Structures), CS 170 (Algorithms), CS 188 (Graph Algorithms)

### Computer Science: Build Systems & DevOps

| Topic | Kernel Implementation |
|-------|----------------------|
| Make/Ninja dependency model | `ToComputation.lean` |
| Parallel build scheduling | `DependencyGraph.parallelism`, `.criticalPath` |
| Incremental rebuild | `rebuildOrder`, `simulateChange` |
| Cache invalidation | `cacheInvalidationSet`, `cacheHitRate` |
| CI pipeline modeling | `CIPipeline` structure and scheduling |
| Package manager resolution | `resolveDependencies`, `hasDiamondConflict` |

**Courses**: CS 162 (Operating Systems), CS 169 (Software Engineering), DevOps bootcamps

### Mathematics: Mathematical Logic

| Topic | Kernel Implementation |
|-------|----------------------|
| Formal theories and signatures | `FormalTheory`, `Signature` |
| Axioms and axiom schemes | `Axiom`, `AxiomScheme` |
| Theory extensions | `TheoryExtension`, `ExtensionChain` |
| Conservative extensions | `isConservative`, `ConservativityReport` |
| Theory interpretability | `Interpretation`, `InterpretationGraph` |
| Mutual interpretability | `MutualInterpretability` |
| Equiconsistency | `EquiconsistencyRelation` |
| Theory classification | `TheoryClassification`, `ConsistencyClass` |

**Courses**: MATH 135 (Mathematical Logic), MATH 230 (Model Theory), MATH 235 (Proof Theory)

### Mathematics: Algebra

| Topic | Kernel Implementation |
|-------|----------------------|
| Group theory hierarchy | `groupTheoryHierarchy` (Magma → Semigroup → Monoid → Group → AbelianGroup) |
| Ring/field hierarchy | `ringTheoryDependency` |
| Algebraic theory lattice | `algebraicDependencyGraph` (12 theories) |
| Subtheory relations | `SubtheoryRelation`, `SubtheoryLattice` |
| Theory products/sums | `TheoryUnion`, `TheoryCombination`, `TheorySum` |

**Courses**: MATH 113 (Abstract Algebra), MATH 114 (Rings and Fields), MATH 210 (Category Theory)

### Mathematics: Topology & Geometry

| Topic | Kernel Implementation |
|-------|----------------------|
| Topological hierarchy | `topologyDependencyGraph` (8 theories) |
| Geometric hierarchy | `geometryDependencyGraph` (6 theories) |
| Cross-domain dependencies | `CrossDomainDependency`, `GeometricCrossReference` |

**Courses**: MATH 132 (Topology), MATH 136 (Differential Geometry), MATH 216 (Algebraic Geometry)

### Mathematics: Foundations & Set Theory

| Topic | Kernel Implementation |
|-------|----------------------|
| ZFC dependency graph | `zfcDependencyGraph` |
| Peano arithmetic hierarchy | `paDependencyGraph` |
| PA ↔ ZF-fin mutual interp | `pa_zffin_mutualInterp` |
| Foundational theory ordering | Consistency strength ranking system |

**Courses**: MATH 135 (Set Theory), MATH 235 (Foundations of Mathematics)

### Formal Methods & Verification

| Topic | Kernel Implementation |
|-------|----------------------|
| Lean 4 formalization | Entire codebase is Lean 4 |
| Structural induction proofs | 37 theorem/lemma blocks |
| Computational verification | 128 #eval blocks |
| Graph invariant preservation | `acyclicityPreservedByRemoval`, morphism compatibility |

**Courses**: CS 195 (Formal Verification), CS 294 (Interactive Theorem Proving)
