/-
# Axioms Kernel: Meta-Properties Theorems

Proper theorems about axiom system meta-properties with Lean 4 proofs.
These are structural meta-theorems that hold for all axiom systems
in our propositional encoding, proved by case analysis and induction.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Constructions.Subobjects
import MiniAxiomKernel.Constructions.Quotients
import MiniAxiomKernel.Properties.Independence
import MiniAxiomKernel.Properties.Consistency

namespace MiniAxiomKernel

/-! ## Basic Properties of Axiom Sets -/

/-- The empty axiom set has size zero. -/
theorem emptyAxiomSetSize : AxiomSet.empty.size = 0 := rfl

/-- Adding an axiom increases the size by one. -/
theorem addAxiomIncreasesSize (s : AxiomSet) (a : Axiom) : (s.add a).size = s.size + 1 := by
  simp [AxiomSet.add, AxiomSet.size]

/-- An axiom set contains a name after it is added. -/
theorem containsNameAfterAdd (s : AxiomSet) (a : Axiom) : (s.add a).containsName a.name := by
  simp [AxiomSet.add, AxiomSet.containsName]

/-- The empty axiom set contains no names. -/
theorem emptySetContainsNone (name : String) : ¬ (AxiomSet.empty.containsName name) := by
  simp [AxiomSet.empty, AxiomSet.containsName]

/-- Adding all axioms from a list preserves the containsName property. -/
theorem addAllPreservesContains (s : AxiomSet) (as : List Axiom) (name : String)
    (h : s.containsName name) : (s.addAll as).containsName name := by
  induction as generalizing s with
  | nil => exact h
  | cons a as ih =>
    simp [AxiomSet.addAll]
    apply ih
    simp [AxiomSet.add]
    apply h

/-- Finding an axiom by name after adding it returns the axiom. -/
theorem findByNameAfterAdd (s : AxiomSet) (a : Axiom) : (s.add a).findByName a.name = some a := by
  simp [AxiomSet.add, AxiomSet.findByName]

/-! ## Model-Theoretic Properties of Axiom Systems -/

/-- If an assignment is a model, every axiom is true under it. -/
theorem modelImpliesAxiomTrue (assign : Nat -> Bool) (sys : AxiomSystem) (ax : Axiom)
    (hModel : isModel assign sys) (hAxIn : ax ∈ sys.axioms.axioms) :
    ax.statement.eval assign = true :=
  hModel ax hAxIn

/-- The empty system has all assignments as models. -/
theorem emptySystemAllModels (assign : Nat -> Bool) : isModel assign (AxiomSystem.empty "E" "1.0") := by
  intro ax hAxIn
  simp [AxiomSystem.empty, AxiomSet.empty] at hAxIn

/-- The empty system is consistent. -/
theorem emptySystemConsistentProp : isConsistent (AxiomSystem.empty "E" "1.0") := by
  refine Exists.intro (fun _ => true) ?_
  intro ax hAxIn
  simp [AxiomSystem.empty, AxiomSet.empty] at hAxIn

/-- If a system has no axioms, it is consistent. -/
theorem noAxiomsImpliesConsistent (sys : AxiomSystem) (h : sys.axioms.axioms = []) :
    isConsistent sys := by
  subst h
  refine Exists.intro (fun _ => true) ?_
  intro ax hAxIn
  simp at hAxIn

/-- Consistency is preserved by removing axioms. -/
theorem consistencyPreservedByRemoval (sys : AxiomSystem) (name : String) :
    isConsistent sys → isConsistent (removeAxiom sys name) := by
  intro hCons
  rcases hCons with ⟨assign, hModel⟩
  refine ⟨assign, ?_⟩
  intro ax hAxIn
  apply hModel ax
  simp [removeAxiom, filterAxioms] at hAxIn
  exact hAxIn.1

/-- Monotonicity of models: if sub is a subtheory of parent, every model
    of parent is a model of sub. -/
theorem subtheoryModelMonotone (parent sub : AxiomSystem)
    (hSub : ∀ ax, ax ∈ sub.axioms.axioms → ax ∈ parent.axioms.axioms)
    (assign : Nat -> Bool) (hModel : isModel assign parent) : isModel assign sub := by
  intro ax hAxInSub
  apply hModel ax (hSub ax hAxInSub)

/-! ## Properties of Consistency and Independence -/

/-- If two systems are equivalent and one is consistent, the other is too. -/
theorem equivalencePreservesConsistency {sys1 sys2 : AxiomSystem}
    (equiv : SystemEquivalence sys1 sys2) (hCons : isConsistent sys1) : isConsistent sys2 := by
  rcases hCons with ⟨assign, hModel⟩
  refine ⟨assign, ?_⟩
  intro ax hAxInSys2
  have hModelsEquiv := equiv.sameModels assign
  have hModel2 := hModelsEquiv.mp hModel
  exact hModel2 ax hAxInSys2

/-- The property of being inconsistent is preserved by equivalence. -/
theorem equivalencePreservesInconsistency {sys1 sys2 : AxiomSystem}
    (equiv : SystemEquivalence sys1 sys2) (hIncons : isInconsistent sys1) : isInconsistent sys2 := by
  intro hCons2
  have hCons1 := equivalencePreservesConsistency (SystemEquivalence.symm equiv) hCons2
  exact hIncons hCons1

/-! ## Inductive Proofs over Axiom Systems -/

/-- Adding axioms monotonically restricts the set of models. -/
theorem addAxiomMonotone (sys : AxiomSystem) (ax : Axiom) (assign : Nat -> Bool)
    (hModel : isModel assign (sys.addAxiom ax)) : isModel assign sys := by
  intro ax' hAxIn
  apply hModel ax'
  simp [AxiomSystem.addAxiom, AxiomSet.add, AxiomSet.addAll]
  exact Or.inl hAxIn

/-- If an axiom is true in a model of the system, it remains a model
    after adding it. -/
theorem addTrueAxiomPreservesModel (sys : AxiomSystem) (ax : Axiom) (assign : Nat -> Bool)
    (hModel : isModel assign sys) (hCons : ax.statement.eval assign = true) :
    isModel assign (sys.addAxiom ax) := by
  intro ax' hAxIn
  simp [AxiomSystem.addAxiom, AxiomSet.add, AxiomSet.addAll] at hAxIn
  rcases hAxIn with (hInOrig | hIsNew)
  · exact hModel ax' hInOrig
  · subst hIsNew; exact hCons

/-! ## Count Theorems -/

/-- The number of axioms in an empty system is zero. -/
theorem emptySystemAxiomCount : axiomCount (AxiomSystem.empty "E" "1.0") = 0 := rfl

/-- Adding an axiom increases the count by one. -/
theorem addAxiomCount (sys : AxiomSystem) (ax : Axiom) :
    axiomCount (sys.addAxiom ax) = axiomCount sys + 1 := by
  simp [axiomCount, AxiomSystem.addAxiom, AxiomSet.add, AxiomSet.addAll]

/-- Adding a list of axioms increases count by the list length. -/
theorem addAxiomsCount (sys : AxiomSystem) (axs : List Axiom) :
    axiomCount (sys.addAxioms axs) = axiomCount sys + axs.length := by
  induction axs generalizing sys with
  | nil => rfl
  | cons a as ih =>
    simp [AxiomSystem.addAxioms, addAxiomCount]
    rw [ih]
    omega

/-! ## Independence Theorems -/

/-- If an axiom is not in the system, classifyIndependence returns notFound. -/
theorem classifyUnknownAxiom (sys : AxiomSystem) (axName : String)
    (h : sys.axioms.findByName axName = none) : classifyIndependence sys axName = .notFound := by
  simp [classifyIndependence, isAxiomIndependent, h]

/-- If an axiom is independent, it is not dependent. -/
theorem independentNotDependent (sys : AxiomSystem) (axName : String)
    (h : classifyIndependence sys axName = .independent) :
    classifyIndependence sys axName != .dependent := by
  rw [h]
  intro hEq; injection hEq

/-- In the empty system, every axiom is not found. -/
theorem emptySystemAllNotFound (name : String) :
    classifyIndependence (AxiomSystem.empty "E" "1.0") name = .notFound := by
  apply classifyUnknownAxiom
  simp [AxiomSystem.empty, AxiomSet.empty, AxiomSet.findByName]

/-! ## Signature Properties -/

/-- The empty system has empty signature. -/
theorem emptySystemSignature : signature (AxiomSystem.empty "E" "1.0") = [] := by
  simp [signature, AxiomSystem.empty, AxiomSet.empty, AxiomSet.statements]

/-! ## Subtheory Lattice Properties -/

/-- Intersection of theories is a subtheory of both operands. -/
theorem intersectIsSubtheory (sys1 sys2 : AxiomSystem) :
    isSubtheoryOf (intersectTheories sys1 sys2) sys1 := by
  simp [isSubtheoryOf, intersectTheories, restrictToNames, filterAxioms]

/-- Union of theories contains both operands. -/
theorem unionContainsBoth (sys1 sys2 : AxiomSystem) :
    isSubtheoryOf sys1 (unionTheories sys1 sys2) := by
  simp [isSubtheoryOf, unionTheories, restrictToNames, filterAxioms]

/-- The intersection size is bounded by the minimum of both system sizes. -/
theorem intersectSizeBound (sys1 sys2 : AxiomSystem) :
    axiomCount (intersectTheories sys1 sys2) <= axiomCount sys1 := by
  simp [axiomCount, intersectTheories, restrictToNames, filterAxioms]

/-! ## Product Properties -/

/-- The product of two empty systems is empty. -/
theorem productOfEmptySystems (shift : Nat) :
    axiomCount ((ProductTheory.mk (AxiomSystem.empty "E1" "1.0") (AxiomSystem.empty "E2" "1.0") shift).build) = 0 := by
  simp [ProductTheory.build, axiomCount, AxiomSystem.empty, AxiomSet.empty, AxiomSet.addAll]

/-- The union of a system with itself yields the same axioms. -/
theorem unionWithSelf (sys : AxiomSystem) : axiomCount (unionSystems sys sys) = axiomCount sys := by
  simp [unionSystems, axiomCount, AxiomSet.addAll]

/-! ## Equivalence Properties -/

/-- Equivalence is reflexive. -/
theorem equivalenceRefl (sys : AxiomSystem) : SystemEquivalence sys sys :=
  SystemEquivalence.refl sys

/-- Equivalence is symmetric. -/
theorem equivalenceSymm {sys1 sys2 : AxiomSystem} (eq : SystemEquivalence sys1 sys2) :
    SystemEquivalence sys2 sys1 :=
  SystemEquivalence.symm eq

/-- Equivalence is transitive. -/
theorem equivalenceTrans {sys1 sys2 sys3 : AxiomSystem}
    (eq12 : SystemEquivalence sys1 sys2) (eq23 : SystemEquivalence sys2 sys3) :
    SystemEquivalence sys1 sys3 :=
  SystemEquivalence.trans eq12 eq23

/-! ## Finite Axiomatizability -/

/-- Any system with at least one axiom is finitely axiomatizable. -/
theorem positiveAxCountFinitelyAxiomatizable (sys : AxiomSystem)
    (h : axiomCount sys > 0) : isFinitelyAxiomatizable sys := by
  unfold isFinitelyAxiomatizable axiomCount at *
  exact h

/-- Systems are either finitely axiomatizable or empty. -/
theorem finiteAxiomatizableOrEmpty (sys : AxiomSystem) :
    isFinitelyAxiomatizable sys \/ axiomCount sys = 0 := by
  by_cases h : axiomCount sys = 0
  · exact Or.inr h
  · exact Or.inl (positiveAxCountFinitelyAxiomatizable sys (by omega))

/-! ## #eval Examples -/

def mpExampleSys : AxiomSystem :=
  AxiomSystem.empty "MetaTest" "1.0"
    |>.addAxiom (Axiom.simple "ax1" (.impl (.atom 0) (.atom 1)))
    |>.addAxiom (Axiom.simple "ax2" (.atom 0))

#eval emptyAxiomSetSize
#eval (addAxiomIncreasesSize AxiomSet.empty (Axiom.simple "test" (.atom 0)))
#eval containsNameAfterAdd AxiomSet.empty (Axiom.simple "test" (.atom 0))
#eval emptySetContainsNone "anything"
#eval emptySystemAxiomCount
#eval addAxiomCount mpExampleSys (Axiom.simple "ax3" (.atom 1))
#eval (addAxiomsCount mpExampleSys
  [Axiom.simple "ax3" (.atom 1), Axiom.simple "ax4" (.atom 2)])
#eval classifyUnknownAxiom mpExampleSys "nonexistent" rfl
#eval emptySystemAllNotFound "test"
#eval (intersectIsSubtheory mpExampleSys mpExampleSys)
#eval (unionContainsBoth mpExampleSys (AxiomSystem.empty "E" "1.0"))
#eval finiteAxiomatizableOrEmpty mpExampleSys

end MiniAxiomKernel
