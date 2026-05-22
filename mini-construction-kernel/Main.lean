import MiniConstructionKernel

open MiniConstructionKernel

def main : IO Unit := do
  IO.println "═══════════════════════════════════════"
  IO.println "  MiniConstructionKernel v0.1.0"
  IO.println "  Universal Constructions Kernel"
  IO.println "═══════════════════════════════════════"
  IO.println s!"  Construction: common interface for building new objects"
  IO.println s!"  ProductConstruction: I-indexed family with projection maps"
  IO.println s!"  CoproductConstruction: I-indexed family with injection maps"
  IO.println s!"  SubConstruction: subobject via a predicate (subtype)"
  IO.println s!"  QuotientConstruction: quotient via an equivalence relation"
  IO.println s!"  FunctionSpaceConstruction: function space α → β"
  IO.println s!"  binary product / binary coproduct: 2-indexed specializations"
  IO.println s!"  compose: chain two constructions together"
  IO.println ""
  IO.println "  Depends on: mini-object-kernel"
  IO.println "  Run `lake env lean --run Test/Smoke.lean` for tests."
