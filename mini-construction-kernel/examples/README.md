# mini-construction-kernel -- Examples

All example code is in MiniConstructionKernel/Examples/:

- Standard.lean -- 15 canonical mathematical constructions
  - Free monoid (List), product of sets, coproduct of sets, quotient by mod 3
  - Even subobject, tensor product, polynomial ring, free group, Z/nZ
  - Discrete/indiscrete topology, projective space, Grassmannian
  - Option as monad, Tree as initial algebra
- Counterexamples.lean -- Edge cases and failure modes
  - Non-universal product, non-associative operation, missing morphism
  - Non-commuting diagram, trivial quotient, inconsistent laws

119 #eval checks across all modules ensure every construction compiles.
Run: cd mini-construction-kernel && lake build && lake env lean --run Test/Smoke.lean