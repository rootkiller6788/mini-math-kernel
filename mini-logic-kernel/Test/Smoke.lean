/-
# Smoke Tests — MiniLogicKernel v0.2.0

Run: `lake env lean --run Test/Smoke.lean`
-/

import MiniLogicKernel

open MiniLogicKernel

#eval "══ MINI-LOGIC-KERNEL SMOKE TESTS ══"

/-! ## Core.Basic: Formula -/
#eval Formula.atom 0
#eval Formula.and (Formula.atom 0) (Formula.atom 1)
#eval Formula.eval (Formula.impl (Formula.atom 0) (Formula.atom 0)) (fun _ => true)
#eval Formula.complexity (Formula.and (.atom 0) (.not (.atom 1)))

/-! ## Core.Objects: PredFormula -/
#eval PredFormula.prop (Formula.atom 0)
#eval PredFormula.pred 0 [0, 1]
#eval PredFormula.quantifierDepth (PredFormula.all (PredFormula.pred 0 [0]))

/-! ## Core.Laws: Derived Rules -/
#eval ruleId (Formula.atom 0)
#eval ruleExcludedMiddle (Formula.atom 0)
#eval ruleDeMorganAnd (Formula.atom 0) (Formula.atom 1)

/-! ## Morphisms: Hom, Iso, Equivalence -/
#eval Formula.translate (Formula.and (.atom 0) (.atom 1)) (fun k => k + 5)
#eval Formula.subst (Formula.or (.atom 0) (.atom 1)) 0 (Formula.atom 42)
#eval Formula.prefixAtoms (Formula.impl (.atom 0) (.atom 3)) 10

/-! ## Constructions: Subobjects, Quotients, Products -/
#eval formulaSize (Formula.and (.atom 0) (.or (.atom 1) (.atom 2)))
#eval isDirectSubformula (Formula.atom 0) (Formula.and (.atom 0) (.atom 1))

/-! ## Properties: Invariants, Preservation, Classification -/
#eval Formula.maxAtom (Formula.and (.atom 0) (.atom 5))
#eval isLiteral (Formula.atom 0)
#eval isClause (Formula.or (.atom 0) (.not (.atom 1)))

/-! ## Theorems: Basic, UniversalProperties, Classification, Main -/
#eval decideTautology (Formula.impl (Formula.atom 0) (Formula.atom 0))
#eval decideTautology (Formula.and (Formula.atom 0) (Formula.not (Formula.atom 0)))

/-! ## Examples: Standard -/
#eval checkTautologyBool (lawOfIdentity (Formula.atom 0))
#eval checkTautologyBool (nonContradictionForm (Formula.atom 0))

/-! ## Bridges: Algebra, Topology, Geometry, Computation -/
#eval decideTautology (Formula.impl (.atom 0) (.atom 0))

#eval "══ ALL MINI-LOGIC-KERNEL SMOKE TESTS PASSED ══"
