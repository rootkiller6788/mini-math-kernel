# Knowledge Graph ¡ª mini-axiom-kernel

## L1: Core Definitions

| Entry | Type | Location | Description |
|-------|------|----------|-------------|
| Axiom | structure | Core/Basic.lean | Named formula asserted without proof |
| AxiomSet | structure | Core/Basic.lean | Collection of axioms with lookup/traversal |
| AxiomSystem | structure | Core/Laws.lean | Versioned, named collection forming a theory |
| AxiomRegistry | structure | Core/Laws.lean | Catalog of registered axiom systems |
| FormulaTranslation | structure | Morphisms/Hom.lean | Atom-to-formula mapping extended homomorphically |
| CheckedHom | structure | Morphisms/Hom.lean | Verified homomorphism with translation + flag |
| CheckedIso | structure | Morphisms/Iso.lean | Verified isomorphism with forward/backward maps |
| AtomBijection | structure | Morphisms/Iso.lean | Bijection on atom indices with inverse proofs |
| SystemEquivalence | structure | Morphisms/Equivalence.lean | Equivalence via identical model sets |
| MutualInterpretation | structure | Morphisms/Equivalence.lean | Mutual translation existence |
| ConservativeExtensionOf | structure | Morphisms/Equivalence.lean | Extension preserving all expressible validities |
| Subtheory | structure | Constructions/Subobjects.lean | Axiom subset relation |
| QuotientSystem | structure | Constructions/Quotients.lean | System with extra axioms |
| ProductTheory | structure | Constructions/Products.lean | Categorical product of axiom systems |
| ProofNode | inductive | Bridges/ToProof.lean | Proof tree nodes (axiom/derived/goal) |
| IndependenceStatus | inductive | Properties/Independence.lean | independent/dependent/unknown/notFound |
| CompletenessClass | inductive | Properties/Completeness.lean | complete/incomplete/categorical/unknown |
| ConsistencyClass | inductive | Properties/Consistency.lean | consistent/inconsistent/unknown |
| DecidabilityClass | inductive | Properties/Decidability.lean | decidable/undecidable/trivial |

## L2: Core Concepts

| Entry | Type | Location | Description |
|-------|------|----------|-------------|
| Axiom independence | def/inductive | Properties/Independence.lean | Countermodel existence for axiom |
| Axiom system consistency | Prop/def | Core/Laws.lean | Existence of a model satisfying all axioms |
| Syntactic completeness | def | Properties/Completeness.lean | Every formula or its negation is decided |
| Logical consequence | def | Properties/Decidability.lean | True in all models of the system |
| Homomorphism preservation | def | Morphisms/Hom.lean | Translation preserves axiom validity |
| Isomorphism of axiom systems | structure/def | Morphisms/Iso.lean | Mutual inverse translations mod equivalence |
| Equivalence of systems | structure/def | Morphisms/Equivalence.lean | Same set of models |
| Conservative extension | def | Morphisms/Hom.lean | No new theorems in original language |
| Definitional extension | def | Morphisms/Hom.lean | Adds definition of new predicate |
| Model counting | def | Bridges/ToModel.lean | Enumeration of all satisfying assignments |
| Entailment | def | Properties/Decidability.lean | One system entails another |

## L3: Mathematical Structures

| Entry | Type | Location | Description |
|-------|------|----------|-------------|
| Product of axiom systems | structure/def | Constructions/Products.lean | Categorical product, disjoint union |
| Quotient system | structure | Constructions/Quotients.lean | System strengthened by extra axioms |
| Subtheory lattice | def | Constructions/Subobjects.lean | Intersection, union of axiom sets |
| Language reduct | def | Constructions/Subobjects.lean | Restriction to smaller signature |
| Universal constructions | def | Constructions/Universal.lean | Initial, terminal, pushout, coproduct |
| Independence basis | def | Properties/Independence.lean | Maximal independent subset |
| Consistency strength ordering | structure/def | Properties/Consistency.lean | Relative consistency comparison |
| Equiconsistency | def | Properties/Consistency.lean | Mutual relative consistency |
# Knowledge Graph ¡ª mini-axiom-kernel (continued)

## L4: Fundamental Theorems

| Entry | Type | Location | Description |
|-------|------|----------|-------------|
| Soundness theorem | def | Theorems/Soundness.lean | Axioms are true in all models |
| Deduction theorem | def | Theorems/Deduction.lean | Deduction equivalence verified |
| Compactness (finite) | def | Theorems/Compactness.lean | Finite satisfiability equals satisfiability |
| Completeness theorem | def | Theorems/CompletenessTheorem.lean | Semantic completeness for finite case |
| Modus ponens soundness | def | Theorems/Soundness.lean | Verified for finite systems |
| Explosion principle | def | Theorems/Soundness.lean | Ex contradictione quodlibet |
| Craig interpolation | def | Theorems/CompletenessTheorem.lean | Interpolant search over common atoms |
| Beth definability | def | Theorems/CompletenessTheorem.lean | Implicit to explicit definition |
| Lindenbaum lemma | def | Theorems/Deduction.lean | Consistent extension to maximal |
| Equivalence theorems | def | Morphisms/Equivalence.lean | Reflexivity, symmetry, transitivity |
| Meta-property theorems | theorem | Theorems/MetaProperties.lean | Structural meta-theorems with proofs |

## L5: Proof Techniques

| Technique | Location | Description |
|-----------|----------|-------------|
| Exhaustive model search | Throughout | Brute-force enumeration of 2^n assignments |
| Deduction theorem reduction | Theorems/Deduction.lean, Bridges/ToLogic.lean | Reduce axiom consequence to tautology check |
| Countermodel search | Properties/Independence.lean | Find assignment satisfying others, falsifying target |
| Greedy minimization | Properties/Consistency.lean | Find minimal inconsistent subset |
| Conservative extension verification | Morphisms/Hom.lean, Morphisms/Equivalence.lean | Model search with constraint propagation |
| Translation-based reduction | Morphisms/Hom.lean, Bridges/ToLogic.lean | Map models via formula translations |
| Forward chaining proof search | Bridges/ToProof.lean | Build proof trees by modus ponens chain |
| Formula enumeration | Properties/Decidability.lean | Generate all formulas up to complexity bound |
| Structural induction | Theorems/MetaProperties.lean | Inductive proofs over formula/axiom structure |

## L6: Canonical Examples

| Example | Location | Description |
|---------|----------|-------------|
| Classical propositional axioms | Core/Objects.lean | Identity, EM, non-contradiction, transitivity, equality |
| Peano arithmetic (finite fragment) | Examples/Peano.lean | 7 PA axioms in propositional encoding |
| Group theory | Examples/GroupTheory.lean | Group axioms + abelian/nontrivial variants |
| ZFC set theory (finite fragment) | Examples/SetTheory.lean | Extensionality, empty set, pairing, union |
| Inconsistent system | Constructions/Universal.lean | Axiom and its negation |
| Empty system | Constructions/Universal.lean | Initial object, all assignments are models |
| Atom-swapping isomorphism | Morphisms/Iso.lean | swap01 bijection |
| Renamed isomorphic system | Morphisms/Iso.lean | Renaming-based isomorphism |

## L7: Applications

| Application | Location | Description |
|-------------|----------|-------------|
| Bridge to Logic Kernel | Bridges/ToLogic.lean | Convert axioms to conjunctions, tautology reduction |
| Bridge to Proof Kernel | Bridges/ToProof.lean | Generate proof trees, verify proofs |
| Bridge to Model Kernel | Bridges/ToModel.lean | Model finding, counting, comparison |
| Knowledge representation | Applications/KnowledgeRepresentation.lean | Ontologies as axiom systems |

## L8: Advanced Topics

| Topic | Location | Description |
|-------|----------|-------------|
| Finite Model Theory | Advanced/FiniteModelTheory.lean | 0-1 laws, asymptotic probabilities |
| Homotopy-theoretic semantics | Advanced/HomotopyLevel.lean | Axiom systems as spaces, HoTT |

## L9: Research Frontiers

| Topic | Status | Description |
|-------|--------|-------------|
| Condensed mathematics | Documented | Axiom systems for condensed sets |
| Univalent foundations | Documented | Axiom systems in HoTT/UF framework |
| Synthetic spectra | Documented | Homotopy-theoretic axiom systems |
| Automated reasoning | Partially implemented | SAT-based decision procedures |
