# Coverage — MiniSyntaxKernel

## Implemented

- **Core.Basic**: Variable (free/bound), Term (var/app/lam/pi/sort/lit/letE), ToString
- **Core.Objects**: freeVars, isClosed, maxBoundIndex, size, binderDepth
- **Morphisms.Equivalence**: lift, lift1, subst, substParallel, alphaEquiv

## Stubbed (pending implementation)

- **Core.Laws**: Syntactic laws and well-formedness conditions
- **Morphisms.Hom/Iso**: Homomorphism and isomorphism definitions
- **Constructions**: Subobjects, Quotients, Products, Universal
- **Properties**: Invariants, Preservation, ClassificationData
- **Theorems**: Basic, UniversalProperties, Classification, Main
- **Bridges**: ToAlgebra, ToTopology, ToGeometry, ToComputation
