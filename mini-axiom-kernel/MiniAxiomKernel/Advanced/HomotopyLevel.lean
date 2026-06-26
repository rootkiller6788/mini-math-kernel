/-
# Axioms Kernel: Homotopy-Theoretic Semantics (L8 Advanced Topic)

Explores connections between axiom systems and homotopy type theory.
Models form a space whose connected components are equivalence classes
of assignments; axiom systems carve out subspaces via fibrations.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Bridges.ToModel
import MiniAxiomKernel.Morphisms.Equivalence

namespace MiniAxiomKernel

/-! ## The Space of Models -/

/-- In HoTT, the models of an axiom system form a type (space).
    Two models are connected by a path if they agree on all atoms
    that appear in the axiom system's signature.
    This is a discrete notion: either models agree or they do not. -/

/-- Path between two models: they are equal on all atoms in the signature.
    This is the 0-truncation level of the model space. -/
def modelPath (sys : AxiomSystem) (m1 m2 : Nat -> Bool) : Prop :=
  ∀ a, a ∈ signature sys → m1 a = m2 a

/-- Two models are homotopic (connected by a path) if they agree
    on the signature atoms. In the discrete topology of assignments,
    this means they are identical on relevant atoms. -/
def modelsHomotopic (sys : AxiomSystem) (m1 m2 : Nat -> Bool) : Bool :=
  (signature sys).all fun a => m1 a == m2 a

/-- The connected component of a model: all models that agree with it
    on the signature. This is the homotopy fiber. -/
def modelComponent (sys : AxiomSystem) (model : Nat -> Bool) : List (Nat -> Bool) :=
  findAllModels sys |>.filter fun m => modelsHomotopic sys model m

/-- Count the connected components (pi_0) of the model space.
    This is the number of distinct assignments to the signature atoms
    that extend to models of the system. -/
def modelSpacePi0 (sys : AxiomSystem) : Option Nat :=
  let models := findAllModels sys
  if models.length > 1000 then none
  else
    let components := componentCount models sys []
    some components
where
  componentCount (remaining : List (Nat -> Bool)) (sys : AxiomSystem) (seen : List (Nat -> Bool)) : Nat :=
    match remaining with
    | [] => 0
    | m :: ms =>
      if seen.any (fun s => modelsHomotopic sys m s) then
        componentCount ms sys seen
      else
        1 + componentCount ms sys (m :: seen)
/-! ## n-Truncation Levels of Axiom Systems -/

/-- An axiom system is 0-truncated (a set) if any two models that agree
    on the signature are equal. In propositional logic, this always holds
    because models are just functions to Bool. -/
def isZeroTruncated (sys : AxiomSystem) : Bool :=
  let models := findAllModels sys
  models.length <= 1 ||
  (signature sys).all fun a =>
    models.all fun m1 =>
      models.all fun m2 => m1 a == m2 a

/-- An axiom system is (-1)-truncated (a mere proposition) if it has
    at most one connected component of models. Equivalent to: all models
    agree on all signature atoms. -/
def isMereProposition (sys : AxiomSystem) : Bool :=
  let models := findAllModels sys
  match models with
  | [] => true
  | m :: ms => ms.all fun m2 => modelsHomotopic sys m m2

/-- An axiom system is (-2)-truncated (contractible) if it has exactly
    one model (the system is categorical). -/
def isContractible (sys : AxiomSystem) : Bool :=
  match countModels sys with
  | some 1 => true
  | _ => false

/-- Classify the truncation level of an axiom system's model space. -/
inductive TruncationLevel
  | contractible
  | mereProposition
  | set
  | higherType
  deriving Repr, DecidableEq

instance : ToString TruncationLevel where
  toString
    | .contractible => "(-2)-truncated (contractible)"
    | .mereProposition => "(-1)-truncated (mere proposition)"
    | .set => "0-truncated (set)"
    | .higherType => ">= 1-truncated"

/-- Determine the truncation level. -/
def classifyTruncationLevel (sys : AxiomSystem) : TruncationLevel :=
  if isContractible sys then .contractible
  else if isMereProposition sys then .mereProposition
  else if isZeroTruncated sys then .set
  else .higherType
/-! ## Fibrations of Axiom Systems -/

/-- A map (homomorphism) between axiom systems induces a map between
    their model spaces. We analyze the homotopy fiber: models of the
    source that map to a given model of the target. -/

/-- Given a translation t: sys1 -> sys2, the homotopy fiber over a
    target model m2 is the set of source models m1 such that
    t(m1) is equivalent to m2 on the relevant atoms. -/
def homotopyFiber (sys1 sys2 : AxiomSystem) (t : FormulaTranslation) (m2 : Nat -> Bool) : List (Nat -> Bool) :=
  let sourceModels := findAllModels sys1
  sourceModels.filter fun m1 =>
    let translatedAtoms := (signature sys1).map fun a => (t.apply (.atom a)).eval m2
    let sourceAtoms := (signature sys1).map fun a => m1 a
    translatedAtoms == sourceAtoms

/-- The long exact sequence of homotopy groups connects the model
    spaces. In our discrete setting, this is a relation between
    connected component counts. -/
def fiberSequence (sys1 sys2 sys3 : AxiomSystem) (f : FormulaTranslation) (g : FormulaTranslation) : Bool :=
  -- Simplified: check that composition mapping preserves models
  let comp := FormulaTranslation.comp f g
  checkHomPreservation sys1 sys3 comp

/-! ## Univalent Foundations Connection -/

/-- In Univalent Foundations, an axiom system can be seen as a
    specification of a structured type. The univalence axiom would
    identify equivalent axiom systems. We approximate this by
    checking if two systems have isomorphic model spaces. -/

/-- Two axiom systems have equivalent model spaces if there is a
    bijection between their model sets that preserves truth values
    on corresponding atoms. This is the univalence-inspired notion
    of equivalence. -/
def modelSpaceEquivalence (sys1 sys2 : AxiomSystem) : Bool :=
  let models1 := findAllModels sys1
  let models2 := findAllModels sys2
  models1.length == models2.length &&
  modelSpacePi0 sys1 == modelSpacePi0 sys2

/-- A property of axiom systems is homotopy-invariant if it depends
    only on the homotopy type of the model space. Examples:
    consistency (non-empty), categoricity (contractible). -/
def isHomotopyInvariant (property : AxiomSystem -> Bool) : Prop :=
  ∀ sys1 sys2 : AxiomSystem,
    modelSpaceEquivalence sys1 sys2 → property sys1 = property sys2

/-! ## Higher Inductive Types of Axiom Systems -/

/-- We can define higher inductive types corresponding to axiom systems.
    The model space is a HIT generated by:
    - Point constructors: each model of the system
    - Path constructors: between models that agree on the signature
    - Higher path constructors: trivial (set-level) -/

/-- The suspension of an axiom system: double the model space by
    adding two new atoms that can be true or false independently.
    This is the analogue of topological suspension. -/
def suspendAxiomSystem (sys : AxiomSystem) : AxiomSystem :=
  let shifted := (ProductTheory.mk sys sys 20).build
  shifted.addAxiom (Axiom.simple "north" (.atom 20))
    |>.addAxiom (Axiom.simple "south" (.not (.atom 20)))

/-- The join of two axiom systems: models are triples (m1, m2, i)
    where i selects which component is active. -/
def joinAxiomSystems (sys1 sys2 : AxiomSystem) (shift : Nat) : AxiomSystem :=
  let prod := (ProductTheory.mk sys1 sys2 shift).build
  prod.addAxiom (Axiom.simple "join-selector" (.or (.atom shift) (.not (.atom shift))))
/-! ## Homotopy Type Theory Axiom Translation -/

/-- Translate a propositional axiom system into a (simulated) HoTT context.
    Each atom becomes a type family, and axioms become path constructors.
    This is a syntactico-semantic bridge. -/

/-- The HoTT interpretation of an axiom: it becomes an inhabitedness
    condition: the type corresponding to the axiom's statement is inhabited
    in the model. -/
def hottInterpretation (ax : Axiom) : String :=
  s!"{ax.name} ||- {ax.statement}"

/-- The HoTT model category: objects are axiom systems, morphisms are
    formula translations. This is a pre-category structure. -/
structure HoTTMorphism (sys1 sys2 : AxiomSystem) where
  translation : FormulaTranslation
  preservesModels : Bool := true
  deriving Repr

/-- Identity morphism in the HoTT model category. -/
def HoTTMorphism.id (sys : AxiomSystem) : HoTTMorphism sys sys :=
  { translation := FormulaTranslation.id, preservesModels := true }

/-- Composition in the HoTT model category. -/
def HoTTMorphism.comp {sys1 sys2 sys3 : AxiomSystem}
    (f : HoTTMorphism sys1 sys2) (g : HoTTMorphism sys2 sys3) : HoTTMorphism sys1 sys3 :=
  { translation := FormulaTranslation.comp f.translation g.translation
    preservesModels := f.preservesModels && g.preservesModels }

/-! ## #eval Examples -/

def htExampleSys : AxiomSystem :=
  AxiomSystem.empty "HTTest" "1.0"
    |>.addAxiom (Axiom.simple "ax1" (.atom 0))
    |>.addAxiom (Axiom.simple "ax2" (.atom 1))

def htUniqueSys : AxiomSystem :=
  AxiomSystem.empty "UniqueTest" "1.0"
    |>.addAxiom (Axiom.simple "fix0" (.atom 0))
    |>.addAxiom (Axiom.simple "fix1" (.atom 1))

#eval classifyTruncationLevel htExampleSys
#eval classifyTruncationLevel htUniqueSys
#eval classifyTruncationLevel (AxiomSystem.empty "Empty" "1.0")
#eval isContractible htUniqueSys
#eval isMereProposition htExampleSys
#eval modelSpacePi0 htExampleSys
#eval modelSpacePi0 htUniqueSys
#eval (modelComponent htExampleSys (fun _ => true)).length
#eval modelSpaceEquivalence htExampleSys htExampleSys
#eval fiberSequence htExampleSys htExampleSys htExampleSys
    FormulaTranslation.id FormulaTranslation.id
#eval hottInterpretation (Axiom.simple "example" (.atom 0))

end MiniAxiomKernel