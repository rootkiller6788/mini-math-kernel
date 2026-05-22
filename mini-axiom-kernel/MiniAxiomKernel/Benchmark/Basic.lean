/-
# Axioms Kernel: Basic Benchmarks

Performance benchmarks for core axiom kernel operations.
Tests checkConsistent, checkHomPreservation, and model counting
on axiom systems of sizes 2-8.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Morphisms.Hom
import MiniAxiomKernel.Bridges.ToModel

open MiniLogicKernel

namespace MiniAxiomKernel

/-! ## Benchmark Data Generation -/

/-- Generate an axiom system with `n` simple axioms.
    Each axiom is of the form P_i → P_{i+1}. -/
def generateBMSystem (n : Nat) : AxiomSystem :=
  let axioms := (List.range n).map fun i =>
    Axiom.simple s!"ax{i}" (.impl (.atom i) (.atom (i + 1)))
  AxiomSystem.empty s!"BM{n}" "1.0" |>.addAxioms axioms

/-- Generate an axiom system with `n` random-looking axioms. -/
def generateBMComplexSystem (n : Nat) (seed : Nat) : AxiomSystem :=
  let baseAtoms := List.range n
  let formulas := baseAtoms.map (.atom ·)
  let more := baseAtoms.bind fun i =>
    baseAtoms.filterMap fun j =>
      if i != j then some [.and (.atom i) (.atom j), .impl (.atom i) (.atom j)] else none
  let allForms := formulas ++ more.join
  let selected := allForms.take n
  let axioms := selected.mapIdx (fun i f => Axiom.simple s!"ax{i}" f)
  AxiomSystem.empty s!"ComplexBM{n}" "1.0" |>.addAxioms axioms

/-! ## Benchmark: checkConsistent -/

/-- Benchmark consistency checking for systems of sizes 2 to 8. -/
def benchCheckConsistent : List (Nat × Bool) :=
  (List.range 7).map fun size =>
    let n := size + 2
    let sys := generateBMSystem n
    (n, sys.checkConsistent)

/-- Benchmark consistency checking for complex systems. -/
def benchCheckConsistentComplex : List (Nat × Bool) :=
  (List.range 7).map fun size =>
    let n := size + 2
    let sys := generateBMComplexSystem n (n * 3)
    (n, sys.checkConsistent)

/-! ## Benchmark: checkHomPreservation -/

/-- Benchmark hom preservation checking between systems. -/
def benchCheckHomPreservation : List (Nat × Bool) :=
  (List.range 5).map fun size =>
    let n := size + 2
    let source := generateBMSystem n
    let target := generateBMSystem (n + 1)
    let t := FormulaTranslation.id
    (n, checkHomPreservation source target t)

/-- Benchmark hom preservation with shift translation. -/
def benchCheckHomShift : List (Nat × Bool) :=
  (List.range 5).map fun size =>
    let n := size + 2
    let source := generateBMSystem n
    let target := generateBMSystem n
    let t := FormulaTranslation.shift 3
    (n, checkHomPreservation source target t)

/-! ## Benchmark: Model Counting -/

/-- Benchmark model counting for systems of various sizes. -/
def benchCountModels : List (Nat × Option Nat) :=
  (List.range 5).map fun size =>
    let n := size + 2
    let sys := generateBMSystem n
    (n, countModels sys)

/-- Benchmark findAllModels for small systems. -/
def benchFindAllModels : List (Nat × Nat) :=
  (List.range 5).map fun size =>
    let n := size + 2
    let sys := generateBMSystem n
    let models := findAllModels sys
    (n, models.length)

/-! ## Benchmark: Independence Checking -/

/-- Benchmark independence checking for all axioms. -/
def benchIndependence : List (Nat × Nat) :=
  (List.range 5).map fun size =>
    let n := size + 2
    let sys := generateBMSystem n
    let independentCount := sys.axioms.axioms.filterMap fun ax =>
      match sys.isIndependent ax.name with
      | some true => some ()
      | _ => none
    (n, independentCount.length)

/-! ## Benchmark Summary -/

/-- Run all benchmarks and produce a summary. -/
def runAllBenchmarks : List String :=
  let cResults := benchCheckConsistent
  let hResults := benchCheckHomPreservation
  let mResults := benchCountModels
  let iResults := benchIndependence
  [s!"Consistency check results: {cResults}"
  ,s!"Hom preservation results: {hResults}"
  ,s!"Model count results: {mResults}"
  ,s!"Independence results: {iResults}"]

/-- Count of benchmarks run (number of individual tests). -/
def benchmarkCount : Nat :=
  (benchCheckConsistent.length + benchCheckHomPreservation.length +
   benchCountModels.length + benchIndependence.length)

/-! ## Atomic Performance Test -/

/-- Test a single consistency check against a 6-axiom system to verify
    the benchmark harness works. -/
def smokeBenchTest : Bool :=
  let sys := generateBMSystem 6
  sys.checkConsistent

/-- Verify that benchmark generation produces valid systems. -/
def verifyBenchSystems : Bool :=
  (List.range 5).all fun i =>
    let n := i + 2
    let sys := generateBMSystem n
    sys.axioms.size == n

/-! ## #eval Examples -/

#eval benchCheckConsistent
#eval benchCheckHomPreservation
#eval benchCountModels
#eval benchFindAllModels
#eval benchIndependence
#eval smokeBenchTest
#eval verifyBenchSystems

end MiniAxiomKernel
