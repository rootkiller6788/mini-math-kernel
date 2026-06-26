# mini-construction-kernel -- Course/Concept Tree

## L1: Definitions

- Construction
  - ProductConstruction
  - CoproductConstruction
  - SubConstruction
  - QuotientConstruction
  - FreeConstruction
  - FunctionSpaceConstruction
  - LimitConstruction
  - ColimitConstruction
  - PullbackConstruction
  - PushoutConstruction
  - EqualizerConstruction
  - CoequalizerConstruction
  - ConstructionMap
  - ConstructionFunctor
  - RingLikeConstruction
  - GroupLikeConstruction
  - ModuleLikeConstruction
  - LatticeLikeConstruction

## L2: Core Concepts
- ConstructionHom
- ConstructionIso
- ConstructionEquivalence
- NaturalTransformation
- NaturalIsomorphism
- ConstructionAdjunction
- ConstructionMono
- ConstructionEpi
- ProductUniversal
- CoproductUniversal
- ExponentialUniversal

## L3: Mathematical Structures
- SubobjectLattice
- SubobjectClassifier
- KernelCokernelSequence
- Cone / Cocone
- LimitCone / ColimitCocone
- NaturalNumbersObject
- ConsistentConstructionLaws
- ProductDistributesOverCoproduct

## L4: Fundamental Theorems (73 total)

### Uniqueness (6)
- binary_product_unique
- binary_coproduct_unique
- initial_object_unique
- terminal_object_unique
- universal_objects_are_isomorphic
- universal_mapping_property_unique

### Structure (2)
- equivalent_relations_iso_quotients
- weak_equivalence_to_iso

### Morphism (4)
- section_is_mono
- retraction_is_epi
- isomorphism_composition
- isomorphism_inverse

### Existence (9)
- binary_products_exist
- binary_coproducts_exist
- initial_object_exists
- terminal_object_exists
- free_list_exists
- equalizers_exist
- coequalizers_exist
- pullbacks_exist
- pushouts_exist

### Classification (11)
- product_is_limit
- coproduct_is_colimit
- initial_object_is_colimit
- terminal_object_is_limit
- equalizer_is_limit
- coequalizer_is_colimit
- pullback_is_limit
- pushout_is_colimit
- free_is_left_adjoint_classification
- classification_surjective
- classification_iso_invariant

### Main (3)
- construction_category_finitely_complete
- construction_category_finitely_cocomplete
- product_classification

## L5: Proof Techniques
- Universal property uniqueness
- Quotient induction
- Injection-based reasoning
- Bijection-to-isomorphism construction
- Property preservation via structure
- NNO induction

## L6: Canonical Examples (15 + 119 #eval)

- Free monoid (List)
- Product of sets
- Coproduct of sets
- Quotient by mod 3
- Even subobject
- Tensor product
- Polynomial ring
- Free group
- Z/nZ
- Discrete topology
- Indiscrete topology
- Projective space
- Grassmannian
- Option as monad
- Tree as initial algebra

## L7: Application Bridges (4 domains)

### ToAlgebra
- Free group
- Polynomial ring
- Tensor product
- Z/nZ quotient

### ToTopology
- Product topology
- Quotient topology
- Subspace topology
- Compactification
- Covering space

### ToGeometry
- Fiber product
- Blow-up
- Projective space
- Tangent space
- Vector bundle

### ToComputation
- ADT = coproduct
- Functor patterns
- Monad patterns
- Generic programming
- Recursive types

## L8: Advanced Topics (7)
- Pullback/Pushout (proven)
- Limit/Colimit (proven)
- Adjoint functor theorem (statement)
- Birkhoff HSP theorem (statement)
- Complete/Cocomplete category (statement)
- Continuous/Cocontinuous functors (statement)
- Noether isomorphism theorems (statement)

## L9: Research Frontiers (2)
- Condensed mathematics interface
- Univalent foundations patterns

## Statistics

| Metric | Value |
|--------|-------|
| Total .lean lines | 4,466 |
| Theorems/Lemmas | 73 |
| #eval checks | 119 |
| L1 definitions | 18 |
| L2 core concepts | 11 |
| L3 structures | 8 |
| L4 fundamental theorems | 11 |
| L5 proof techniques | 6 |
| L6 examples | 15 |
| L7 application domains | 4 |
| L8 advanced topics | 7 |
| L9 research frontiers | 2 |