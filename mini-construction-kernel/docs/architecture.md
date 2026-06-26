# mini-construction-kernel -- Architecture

## Overview

The construction kernel defines the Construction type -- the common interface for building new mathematical objects from existing ones through universal constructions.

## Dependency Graph

mini-construction-kernel
  depends on mini-object-kernel (Core/Basic)

## Module Map (26 files, 4,466 lines, COMPLETE)

MiniConstructionKernel/
  Core/
    Basic.lean (330 lines) -- Construction, ProductConstruction, CoproductConstruction, SubConstruction, QuotientConstruction, FreeConstruction, FunctionSpaceConstruction, LimitConstruction, ColimitConstruction, PullbackConstruction, PushoutConstruction, EqualizerConstruction, CoequalizerConstruction, ConstructionFunctor, ConstructionMap, RingLikeConstruction, GroupLikeConstruction, ModuleLikeConstruction, LatticeLikeConstruction
    Objects.lean (149 lines) -- Construction objects and instances
    Laws.lean (146 lines) -- Construction laws, ConsistentConstructionLaws
  Morphisms/
    Hom.lean -- ConstructionHom, ConstructionMono, ConstructionEpi, NaturalTransformation
    Iso.lean -- ConstructionIso, NaturalIsomorphism
    Equivalence.lean -- ConstructionEquivalence, ConstructionAdjunction
  Constructions/
    Subobjects.lean (191 lines) -- SubobjectLattice, SubobjectClassifier
    Quotients.lean (185 lines) -- Quotient constructions, KernelCokernelSequence
    Products.lean (256 lines) -- Product, Coproduct, ProductDistributesOverCoproduct
    Universal.lean (190 lines) -- UniversalProperty, InitialObject, TerminalObject, Cone, Cocone, LimitCone, ColimitCocone, NaturalNumbersObject, Equalizers, Coequalizers, Pullbacks, Pushouts
  Properties/
    Invariants.lean -- Construction invariants
    Preservation.lean -- Preservation properties
    ClassificationData.lean -- Classification data
  Theorems/
    Basic.lean -- composition_preserves_construction, self_isomorphism, isomorphism_composition, isomorphism_inverse, product_satisfies_universal, coproduct_satisfies_universal, universal_objects_are_isomorphic, section_is_mono, retraction_is_epi, weak_equivalence_to_iso, equivalent_relations_iso_quotients
    UniversalProperties.lean (210 lines) -- binary_products_exist, binary_coproducts_exist, binary_product_unique (30 lines), binary_coproduct_unique, initial_object_exists, terminal_object_exists, free_list_exists, equalizers_exist, coequalizers_exist, pullbacks_exist, pushouts_exist
    Classification.lean (220 lines) -- product_is_limit, coproduct_is_colimit, equalizer_is_limit, coequalizer_is_colimit, pullback_is_limit, pushout_is_colimit, free_is_left_adjoint_classification, classification_surjective, classification_iso_invariant, product_classification, coproduct_classification
    Main.lean -- construction_category_finitely_complete, construction_category_finitely_cocomplete, universal_mapping_property_unique
  Examples/
    Standard.lean -- 15 canonical examples with #eval verification
    Counterexamples.lean -- Edge cases and failure modes
  Bridges/
    ToAlgebra.lean -- Free group, polynomial ring, tensor product, Z/nZ
    ToTopology.lean -- Product/quotient/subspace topology, compactification
    ToGeometry.lean -- Fiber product, blow-up, projective space, tangent space
    ToComputation.lean -- ADT as coproduct, functor/monad patterns, generic programming