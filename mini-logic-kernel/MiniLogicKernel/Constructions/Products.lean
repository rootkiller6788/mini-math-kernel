/-
# Logic Kernel: Product Constructions

Product structures, conjunction of theories,
and combined logical systems.

Knowledge coverage: L3 (Product constructions), L4 (Universal property of conjunction)
-/

import MiniLogicKernel.Core.Basic
import MiniLogicKernel.Core.Objects

namespace MiniLogicKernel

/-! ## Product of Two Propositional Formulas -/

/-- The product (conjunction pairing) of two formulas.
    Evaluates to true iff both components do. -/
def formulaProduct (A B : Formula) : Formula := .and A B

/-- First projection from a product formula:
    `A` is a logical consequence of `A ∧ B`. -/
theorem formulaProduct_proj_left (A B : Formula) : isTautology (.impl (formulaProduct A B) A) := by
  intro assignment
  unfold formulaProduct isTautology
  simp [Formula.eval]

/-- Second projection from a product formula:
    `B` is a logical consequence of `A ∧ B`. -/
theorem formulaProduct_proj_right (A B : Formula) : isTautology (.impl (formulaProduct A B) B) := by
  intro assignment
  unfold formulaProduct isTautology
  simp [Formula.eval]

/-- Universal property of formulaProduct: if C implies both A and B,
    then C implies the product A ∧ B. -/
theorem formulaProduct_universal (C A B : Formula)
    (hA : isTautology (.impl C A)) (hB : isTautology (.impl C B)) :
    isTautology (.impl C (formulaProduct A B)) := by
  intro assignment
  unfold formulaProduct isTautology at *
  have hAe := hA assignment
  have hBe := hB assignment
  simp [Formula.eval] at hAe hBe ⊢
  simp [hAe, hBe]

/-! ## #eval Tests -/

def pf1 : Formula := formulaProduct (.atom 0) (.atom 1)
def pf2 : Formula := formulaProduct (.atom 0) (.not (.atom 0))

#eval pf1
#eval pf1.eval (fun n => n = 0)
#eval pf1.eval (fun n => n = 0 || n = 1)
#eval pf2.eval (fun _ => false)
#eval pf2.eval (fun n => n = 0)

#eval checkTautologyBool (productMorphism_left (.atom 0) (.atom 1))
#eval checkTautologyBool (productMorphism_right (.atom 0) (.atom 1))
#eval checkTautologyBool (productMorphism_left (.atom 0) (.not (.atom 0)))

def medExample := productMediating (.atom 2) (.atom 0) (.atom 1)
#eval medExample
#eval checkTautologyBool medExample

/-! ## Product of Two Predicate Structures -/

/-- The product of two first-order structures: domain is the Cartesian product
    of domains, predicates hold in both components. -/
def productStructure (S1 S2 : Structure) : Structure where
  domain := S1.domain × S2.domain
  predInterp := fun p args =>
    let args1 := args.map Prod.fst
    let args2 := args.map Prod.snd
    S1.predInterp p args1 ∧ S2.predInterp p args2
  constInterp := fun n => (S1.constInterp n, S2.constInterp n)

/-! ## Projection Maps for Product Structures -/

/-- First projection: maps the product domain onto the first component's domain. -/
def productProj1 (S1 S2 : Structure) : (productStructure S1 S2).domain → S1.domain :=
  Prod.fst

/-- Second projection: maps the product domain onto the second component's domain. -/
def productProj2 (S1 S2 : Structure) : (productStructure S1 S2).domain → S2.domain :=
  Prod.snd

/-- The first projection preserves satisfaction of propositional subformulas. -/
theorem productProj1_preserves_prop (S1 S2 : Structure) (f : Formula)
    (env : List ((productStructure S1 S2).domain)) :
    (productStructure S1 S2).satisfies (.prop f) env := by
  simp [Structure.satisfies]

/-- Satisfaction of conjunction in the product structure decomposes
    into satisfaction of each conjunct. -/
theorem product_satisfies_and (S1 S2 : Structure) (φ ψ : PredFormula)
    (env : List ((productStructure S1 S2).domain)) :
    (productStructure S1 S2).satisfies (.and φ ψ) env ↔
    (productStructure S1 S2).satisfies φ env ∧
    (productStructure S1 S2).satisfies ψ env := by
  simp [Structure.satisfies]

/-- The product structure satisfies a propositional formula for any zipped environment. -/
theorem product_satisfies_prop (S1 S2 : Structure) (f : Formula)
    (env1 : List S1.domain) (env2 : List S2.domain) :
    (productStructure S1 S2).satisfies (.prop f) (List.zip env1 env2) := by
  simp [Structure.satisfies]

/-! ## Binary Conjunction as Categorical Product -/

/-- In the "category" of formulas with implication as morphisms,
    conjunction serves as the categorical product with projection morphisms. -/
def productMorphism_left (A B : Formula) : Formula := .impl (.and A B) A

def productMorphism_right (A B : Formula) : Formula := .impl (.and A B) B

/-- The mediating morphism for the product universal property:
    given morphisms C → A and C → B, produce C → A ∧ B. -/
def productMediating (C A B : Formula) : Formula :=
  .impl C (.and A B)

theorem productMediating_tautology (C A B : Formula)
    (hA : isTautology (.impl C A)) (hB : isTautology (.impl C B)) :
    isTautology (productMediating C A B) :=
  formulaProduct_universal C A B hA hB

/-! ## #eval Tests -/

def pf1 : Formula := formulaProduct (.atom 0) (.atom 1)
def pf2 : Formula := formulaProduct (.atom 0) (.not (.atom 0))

#eval pf1
#eval pf1.eval (fun n => n = 0)
#eval pf1.eval (fun n => n = 0 || n = 1)
#eval pf2.eval (fun _ => false)
#eval pf2.eval (fun n => n = 0)

#eval checkTautologyBool (productMorphism_left (.atom 0) (.atom 1))
#eval checkTautologyBool (productMorphism_right (.atom 0) (.atom 1))
#eval checkTautologyBool (productMorphism_left (.atom 0) (.not (.atom 0)))

def medExample := productMediating (.atom 2) (.atom 0) (.atom 1)
#eval medExample
#eval checkTautologyBool medExample

end MiniLogicKernel
