import MiniObjectKernel

open MiniObjectKernel

def main : IO Unit := do
  IO.println "═══════════════════════════════════════"
  IO.println "  MiniObjectKernel v0.1.0"
  IO.println "  Mathematical Object Typeclass"
  IO.println "═══════════════════════════════════════"
  IO.println s!"  Object typeclass: common interface for all mathematical structures"
  IO.println s!"  TheoryName: hierarchical theory namespaces (e.g. SetTheory.ZFC)"
  IO.println s!"  EmbeddingGraph: theory dependency tracking"
  IO.println s!"  repr: human-readable representation for each object"
  IO.println s!"  objName: canonical name for each structure type"
  IO.println s!"  theory: the theory this object belongs to"
  IO.println ""
  IO.println "  Depends on: (none -- kernel root)"
  IO.println "  Run `lake env lean --run Test/Smoke.lean` for tests."
