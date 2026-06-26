import Lake
open Lake DSL

package «mini-object-kernel» where

@[default_target]
lean_lib «MiniObjectKernel» where
  roots := #[`MiniObjectKernel]

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
