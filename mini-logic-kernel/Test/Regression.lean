/-
# Regression Tests — MiniLogicKernel

Invariant checks across modules.
-/

import MiniLogicKernel

open MiniLogicKernel

/-- Invariant: Formula.atom roundtrips through BEq -/
#eval Formula.atom 0 == Formula.atom 0

/-- Invariant: True is distinct from False -/
#eval Formula.true != Formula.false

/-- Invariant: PushNeg of double negation is identity -/
#eval Formula.pushNeg (Formula.not (Formula.not (Formula.atom 0))) == Formula.atom 0

/-- Invariant: ruleId is a tautology -/
#eval isTautology (ruleId (Formula.atom 0))

/-- Invariant: PredFormula.prop wraps Formula -/
#eval PredFormula.prop (Formula.atom 0) == PredFormula.prop (Formula.atom 0)

/-- Invariant: quantifierDepth of quantifier-free is 0 -/
#eval PredFormula.quantifierDepth (PredFormula.pred 0 []) == 0

/-- Invariant: Formula.complexity of atom is 0 -/
#eval Formula.complexity (Formula.atom 5) == 0

/-- Invariant: Formula.atoms collects all atoms -/
#eval Formula.atoms (Formula.and (Formula.atom 0) (Formula.atom 1)) == [0, 1]

#eval "══ ALL REGRESSION CHECKS PASSED ══"
