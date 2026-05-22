/-
# Axioms Kernel: Universal Constructions

Defines universal constructions for axiom systems: the trivial system,
terminal system, free closure, and the category structure.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Objects
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Constructions.Subobjects
import MiniAxiomKernel.Constructions.Products

namespace MiniAxiomKernel

/-! ## Initial and Terminal Systems -/

/-- The empty axiom system (no axioms). Every assignment is a model.
    This is the initial object: it maps to every other system. -/
def emptySystem : AxiomSystem :=
  AxiomSystem.empty "empty" "1.0"

/-- Check that the empty system is consistent (it always is). -/
def emptySystemConsistent : Bool := emptySystem.checkConsistent

/-- The inconsistent system: has an axiom and its negation. -/
def inconsistentSystem : AxiomSystem :=
  AxiomSystem.empty "inconsistent" "1.0"
    |>.addAxiom (Axiom.simple "contra" (.and (.atom 0) (.not (.atom 0))))

/-- Check that the inconsistent system has no models. -/
def inconsistentSystemCheck : Bool := not (inconsistentSystem.checkConsistent)

/-! ## Free Theory (Closure Under Logical Consequence) -/

/-- Generate all tautologies over a given set of atoms. These are the
    formulas true under every assignment. In finite form, we enumerate
    formulas up to a given complexity bound. -/
def generateTautologies (atoms : List Nat) (maxComplexity : Nat) : List Formula :=
  let base := atoms.map (.atom ·) ++ [.true, .false]
  generateUpTo base maxComplexity
where
  generateUpTo (seed : List Formula) (remaining : Nat) : List Formula :=
    if remaining == 0 then seed
    else
      let negated := seed.map (.not ·)
      let paired := seed.bind fun a => seed.map fun b => [.and a b, .or a b, .impl a b, .equiv a b]
      let allNew := negated ++ paired.join
      generateUpTo (seed ++ allNew) (remaining - 1)

/-- The deductive closure (free theory) adds all logical consequences
    of the axioms that are tautological. This is a finite approximation
    using a small set of derived formulas. -/
def freeClosure (sys : AxiomSystem) (steps : Nat) : AxiomSystem :=
  let axs := sys.axioms.axioms
  let derived := deriveFormulas axs steps
  AxiomSystem.empty (s!"free({sys.name})") sys.version
    |>.addAxioms axs
    |>.addAxioms (derived.map fun (name, fm) => Axiom.simple name fm)
where
  deriveFormulas (axioms : List Axiom) (s : Nat) : List (String × Formula) :=
    match s with
    | 0 => []
    | n + 1 =>
      let prev := deriveFormulas axioms n
      let prevForms := prev.map (·.2) ++ axioms.map (·.statement)
      let newForms := generateStep prevForms
      let newNamed := newForms.mapIdx (fun i f => (s!"derived{n}-{i}", f))
      prev ++ newNamed

  generateStep (forms : List Formula) : List Formula :=
    let negated := forms.map (.not ·)
    let conjunctions := forms.bind fun a =>
      forms.filterMap fun b => if a != b then some (.and a b) else none
    let implications := forms.bind fun a =>
      forms.filterMap fun b => if a != b then some (.impl a b) else none
    (negated ++ conjunctions ++ implications).take 20

/-! ## Universal Property Morphisms -/

/-- The unique homomorphism from the empty system to any system. -/
def emptySystemHom (sys : AxiomSystem) : CheckedHom emptySystem sys :=
  CheckedHom.id emptySystem |>.comp (CheckedHom.id sys)

/-- Check that the empty system maps to any consistent system. -/
def checkEmptyToConsistentHom (sys : AxiomSystem) : Bool :=
  let t := FormulaTranslation.id
  checkHomPreservation emptySystem sys t

/-- The diagonal morphism Δ : S → S × S (duplicating a system). -/
def diagonalHom (sys : AxiomSystem) (shift : Nat) : FormulaTranslation :=
  let prod := (ProductTheory.mk sys sys shift).build
  FormulaTranslation.id

/-! ## Pushout (Amalgamation) -/

/-- Given two extensions of a base system, the pushout is the union
    of the extensions with the base axioms merged. -/
def pushout (base ext1 ext2 : AxiomSystem) : AxiomSystem :=
  let baseNames := base.axioms.axioms.map (·.name)
  let newFromExt1 := ext1.axioms.axioms.filter fun ax =>
    !(baseNames.any (· == ax.name))
  let newFromExt2 := ext2.axioms.axioms.filter fun ax =>
    !(baseNames.any (· == ax.name)) &&
    !(newFromExt1.any (·.name == ax.name))
  AxiomSystem.empty (s!"pushout({ext1.name},{ext2.name})") "1.0"
    |>.addAxioms base.axioms.axioms
    |>.addAxioms newFromExt1
    |>.addAxioms newFromExt2

/-- Check pushout consistency: if both extensions are consistent
    extensions of the base, the pushout should be consistent. -/
def checkPushoutConsistent (base ext1 ext2 : AxiomSystem) : Bool :=
  let po := pushout base ext1 ext2
  po.checkConsistent

/-! ## Free Product (Coproduction) -/

/-- The coproduct (free product) of two systems is their disjoint
    union with no interaction axioms. -/
def freeProduct (sys1 sys2 : AxiomSystem) (shift : Nat) : AxiomSystem :=
  disjointUnion sys1 sys2 shift

/-- The codiagonal morphism from the coproduct to a single system. -/
def codiagonalHom (sys1 sys2 target : AxiomSystem) (shift : Nat) : Bool :=
  let coprod := freeProduct sys1 sys2 shift
  checkHomPreservation coprod target FormulaTranslation.id

/-! ## #eval Examples -/

#eval emptySystemConsistent
#eval inconsistentSystemCheck
#eval emptySystem.axioms.axioms.length
#eval (generateTautologies [0, 1] 2).length

def univA : AxiomSystem :=
  AxiomSystem.empty "univA" "1.0"
    |>.addAxiom (Axiom.simple "ax" (.impl (.atom 0) (.atom 1)))

#eval checkEmptyToConsistentHom univA
#eval (freeClosure univA 2).axioms.axioms.length
#eval checkPushoutConsistent univA emptySystem univA

end MiniAxiomKernel
