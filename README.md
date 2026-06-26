# Mini Math Kernel

A collection of **from-scratch, zero-dependency Lean 4 implementations** of university-level mathematical foundations and proof theory. Each sub-package maps to MIT (and other top-tier university) courses, building the foundations of formal mathematics from first principles using the Lean 4 proof assistant.

## Sub-Packages

| Sub-Package | Topics | Key Courses |
|-------------|--------|-------------|
| [mini-logic-kernel](mini-logic-kernel/) | Propositional logic, predicates, quantifiers, tautology checker | MIT 6.042J, Stanford CS103 |
| [mini-syntax-kernel](mini-syntax-kernel/) | Term language, de Bruijn indices, binding structure | MIT 6.821, Cambridge Part II |
| [mini-object-kernel](mini-object-kernel/) | Object typeclass, theory names, typed structures | MIT 18.996, Princeton MAT 595 |
| [mini-proof-kernel](mini-proof-kernel/) | Natural deduction, proof trees, sequent calculus | MIT 6.825, CMU 15-317 |
| [mini-axiom-kernel](mini-axiom-kernel/) | Axiom systems, axiom sets, consistency checking | MIT 18.510, Princeton MAT 560 |
| [mini-construction-kernel](mini-construction-kernel/) | Structures, products, coproducts, quotients, function spaces | MIT 18.996, Cambridge Part III |
| [mini-theory-dependency-kernel](mini-theory-dependency-kernel/) | Theory dependency graphs, dependency kinds, theory manifests | MIT 6.821, Oxford CS |

## Design Philosophy

- **Zero external dependencies** -- pure Lean 4, only kernel imports
- **Self-contained sub-packages** -- each has its own `lakefile.lean`, Core/, Morphisms/, Constructions/, Properties/, Theorems/
- **Theory-to-code mapping** -- every module includes inline `#eval` examples and theorem statements
- **Pattern library** -- establishes coding conventions reused by all downstream domain packages

## Building

Each sub-package is standalone. Build with Lake:

```bash
cd mini-logic-kernel
lake build
lake env lean --run Test/Smoke.lean
```

Requires **Lean 4** and **Lake**.

## Project Structure

```
0. mini-math-kernel/
├── mini-logic-kernel/               # Propositional/predicate logic, tautology checking
├── mini-syntax-kernel/              # Term language, de Bruijn indices, binding
├── mini-object-kernel/              # Object typeclass, typed structures
├── mini-proof-kernel/               # Natural deduction, proof trees, sequent calculus
├── mini-axiom-kernel/               # Axiom systems, consistency checking
├── mini-construction-kernel/        # Products, coproducts, quotients, function spaces
├── mini-theory-dependency-kernel/   # Theory dependency graphs and manifests
├── plan.md                          # Phased execution plan
├── lakefile.lean
└── lean-toolchain
```

## License

MIT
