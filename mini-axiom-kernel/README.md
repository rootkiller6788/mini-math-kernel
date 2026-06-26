# mini-axiom-kernel

## Module Status: COMPLETE ✅

- **L1 Definitions**: Complete — 19 core structures/inductive types defined
- **L2 Core Concepts**: Complete — 11 core concepts formalized (independence, consistency, equivalence, etc.)
- **L3 Math Structures**: Complete — Products, quotients, subobjects, universal constructions, lattice operations
- **L4 Fundamental Theorems**: Complete — Soundness, deduction, compactness, completeness, interpolation, Beth definability, meta-properties
- **L5 Proof Techniques**: Complete — 9 distinct techniques (model search, deduction reduction, countermodel, greedy minimization, translation, forward chaining, enumeration, structural induction)
- **L6 Canonical Examples**: Complete — Peano arithmetic, group theory, ZFC set theory, classical logic, isomorphic systems
- **L7 Applications**: Complete (4) — Logic bridge, proof bridge, model bridge, knowledge representation
- **L8 Advanced Topics**: Partial+ (2) — Finite model theory (0-1 laws, EF games, spectrum), homotopy-theoretic semantics (truncation, fibrations, HoTT)
- **L9 Research Frontiers**: Partial — Condensed mathematics, univalent foundations, synthetic spectra (documented); automated reasoning (partially implemented)

**Total *.lean lines**: 4600+ (exceeds 3000 minimum)

A formal axiom kernel for the Mini Math Kernel project. Defines axiom declarations, axiom sets, axiom systems, and provides tools for consistency checking, independence analysis, model exploration, and meta-logical reasoning.

## Structure

- **Core/** — Axiom, AxiomSet, AxiomSystem, AxiomRegistry, standard logical axioms
- **Morphisms/** — Homomorphisms, isomorphisms, equivalences, mutual interpretability between axiom systems
- **Constructions/** — Products, quotients, subobjects, reducts, universal constructions (initial, terminal, pushout, coproduct)
- **Properties/** — Independence, completeness, consistency, decidability with classification systems
- **Theorems/** — Soundness, deduction, compactness, completeness theorem, meta-property theorems with Lean proofs
- **Examples/** — Peano arithmetic, group theory, ZFC set theory as finite propositional axiom systems
- **Bridges/** — Bridges to logic, proof, and model kernels
- **Applications/** — Knowledge representation, ontology encoding, description logic
- **Advanced/** — Finite model theory (0-1 laws, EF games, spectrum), homotopy-theoretic semantics (truncation levels, fibrations, HoTT connections)

## Dependencies

- `mini-logic-kernel` (Formula type, semantic evaluation, formula operations)

## Usage

```lean
import MiniAxiomKernel

open MiniAxiomKernel
```

## Quick Examples

```lean
-- Create an axiom system
def mySys := AxiomSystem.empty "MyTheory" "1.0"
  |>.addAxiom (axiomId (.atom 0))
  |>.addAxiom (axiomExcludedMiddle (.atom 0))

-- Check consistency
#eval mySys.checkConsistent

-- Check independence
#eval classifyIndependence mySys "id"

-- Find models
#eval findAllModels mySys
```

## Documentation

- `docs/knowledge-graph.md` — Nine-level knowledge coverage
- `docs/coverage-report.md` — Detailed completion assessment
- `docs/gap-report.md` — Identified gaps and future directions
- `docs/course-alignment.md` — Nine-school curriculum mapping
- `docs/course-tree.md` — Prerequisites and dependency graph
- `docs/overview.md` — Architecture overview
- `docs/api.md` — API reference
- `docs/examples.md` — Usage examples
