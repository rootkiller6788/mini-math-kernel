/-
# Step-by-Step Examples — MiniLogicKernel

Building formulas, evaluating semantics, and applying derived rules.
-/

import MiniLogicKernel

open MiniLogicKernel

#eval "══ BUILDING FORMULAS: FROM ATOMS TO DERIVED RULES ══"

/-! ### Step 1: Create atomic formulas -/
#eval Formula.atom 0
#eval Formula.atom 1

/-! ### Step 2: Build compound formulas -/
def P := Formula.atom 0
def Q := Formula.atom 1
#eval Formula.and P Q
#eval Formula.impl P Q

/-! ### Step 3: Evaluate under an assignment -/
#eval Formula.eval (Formula.and P Q) (fun n => n == 0)
#eval Formula.eval (Formula.or P Q) (fun _ => false)

/-! ### Step 4: Create predicate formulas -/
def predFormula := PredFormula.all (PredFormula.pred 0 [0, 1])
#eval predFormula

/-! ### Step 5: Apply derived rules -/
#eval ruleSyllogism P Q (Formula.not P)
#eval ruleContraposition P Q

/-! ### Step 6: Check tautology property -/
#eval isTautology (Formula.impl P P)

#eval "══ EXAMPLE BUILDING COMPLETE ══"
