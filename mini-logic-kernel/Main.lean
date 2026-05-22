import MiniLogicKernel

open MiniLogicKernel

def main : IO Unit := do
  IO.println "═══════════════════════════════════════"
  IO.println "  MiniLogicKernel v0.2.0"
  IO.println "  Propositional and Predicate Logic Kernel"
  IO.println "═══════════════════════════════════════"
  IO.println s!"  Formula: propositional logic with 8 connectives"
  IO.println s!"  PredFormula: first-order predicates and quantifiers"
  IO.println s!"  Structure: model-theoretic semantics"
  IO.println s!"  Laws: 13 derived inference rules"
  IO.println s!"  Morphisms: Hom, Iso, Equivalence (Lindenbaum algebra)"
  IO.println s!"  Constructions: Subobjects, Quotients, Products, Universal"
  IO.println s!"  Properties: Invariants, Preservation, Classification"
  IO.println s!"  Theorems: Soundness, Completeness, Compactness, Lowenheim-Skolem"
  IO.println s!"  Examples: 16 tautologies, Peano axioms, DLO structures"
  IO.println s!"  Bridges: Algebra, Topology (Stone duality), Geometry, Computation"
  IO.println ""
  IO.println "  Run `lake env lean --run Test/Smoke.lean` for tests."
  IO.println "  Run `lake env lean --run Test/Examples.lean` for examples."
  IO.println "  Run `lake build` to compile."
