# mini-construction-kernel -- Knowledge Graph

## Concept Dependency Map (L1 to L9)

### L1: Definitions (18 types)
Construction, ProductConstruction, CoproductConstruction, SubConstruction,
QuotientConstruction, FreeConstruction, FunctionSpaceConstruction,
LimitConstruction, ColimitConstruction, PullbackConstruction,
PushoutConstruction, EqualizerConstruction, CoequalizerConstruction,
ConstructionMap, ConstructionFunctor, RingLikeConstruction,
GroupLikeConstruction, ModuleLikeConstruction, LatticeLikeConstruction

### L2: Core Concepts (11)
ConstructionHom, ConstructionIso, ConstructionEquivalence, NaturalTransformation,
NaturalIsomorphism, ConstructionAdjunction, ConstructionMono, ConstructionEpi,
ProductUniversal, CoproductUniversal, ExponentialUniversal

### L3: Math Structures (8)
SubobjectLattice, SubobjectClassifier, KernelCokernelSequence, Cone/Cocone,
LimitCone/ColimitCocone, NaturalNumbersObject, ConsistentConstructionLaws,
ProductDistributesOverCoproduct

### L4: Fundamental Theorems (11)
binary_product_unique, binary_coproduct_unique, initial_object_unique,
terminal_object_unique, universal_objects_are_isomorphic,
equivalent_relations_iso_quotients, weak_equivalence_to_iso,
section_is_mono, retraction_is_epi, isomorphism_composition,
isomorphism_inverse

### L5: Proof Techniques (6)
Universal property uniqueness, Quotient induction, Injection-based reasoning,
Bijection-to-isomorphism, Property preservation, NNO induction

### L6: Canonical Examples (15 + 119 #eval)
Free monoid (List), Product/Coproduct of sets, Quotient by mod 3,
Even subobject, Tensor product, Polynomial ring, Free group, Z/nZ,
Discrete/Indiscrete topology, Projective space, Grassmannian,
Option as monad, Tree as initial algebra

### L7: Applications (4 directions)
Algebra, Topology, Geometry, Computation

### L8: Advanced Topics (7)
Pullback/Pushout, Limit/Colimit, Adjoint functor theorem, Birkhoff HSP,
Complete/Cocomplete, Continuous functors, Noether isomorphism

### L9: Research Frontiers (2)
Condensed mathematics interface, Univalent foundations patterns

## Module Dependency Graph



## Knowledge Flow

| From | To | Mechanism |
|------|-----|-----------|
| L1 | L2 | Construction gets morphisms, isos, natural transformations |
| L2 | L3 | Morphisms define universal properties (cones, limits, NNO) |
| L3 | L4 | Universal properties yield uniqueness theorems |
| L4 | L5 | Uniqueness proofs become reusable proof templates |
| L5 | L6 | Templates validated on 15 examples (119 #eval checks) |
| L6 | L7 | Examples bridge to 4 application domains |
| L7 | L8 | Applications reveal advanced patterns |
| L8 | L9 | Patterns connect to research frontiers |
