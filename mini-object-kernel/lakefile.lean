import Lake
open Lake DSL

package «mini-object-kernel» where
  version := v!"0.1.0"
  -- The MiniObjectKernel provides the Object typeclass and related
  -- structures (subobjects, quotients, embeddings) that form the
  -- common interface for all mathematical structures in the
  -- mini-everything-math ecosystem.
  license := "MIT"

@[default_target]
lean_lib «MiniObjectKernel» where
  roots := #[`MiniObjectKernel]
  -- Organize source files for editor tooling and build isolation
  defaultFacets := #[ModuleFacet.oleans]

/-- Smoke test executable: verifies basic imports and examples. -/
lean_exe «smoke-test» where
  root := `Test.Smoke
  supportInterpreter := true

/-- Examples regression test. -/
lean_exe «example-test» where
  root := `Test.Examples
  supportInterpreter := true

/-- Regression test suite. -/
lean_exe «regression-test» where
  root := `Test.Regression
  supportInterpreter := true
