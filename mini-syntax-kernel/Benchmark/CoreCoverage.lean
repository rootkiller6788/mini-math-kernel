/-
# Benchmark: Core Coverage

Coverage targets for all core functions.
-/

import MiniSyntaxKernel

open MiniSyntaxKernel

namespace MiniSyntaxKernel

/-! ## Variable ops -/
#eval Variable.free "x"
#eval Variable.bound "x" 0
#eval (Variable.free "a" == Variable.free "a")

/-! ## Term constructors -/
#eval Term.var (Variable.free "x")
#eval Term.app (.var (Variable.free "f")) (.var (Variable.free "x"))
#eval Term.lam (Variable.free "x") (.var (Variable.free "x"))
#eval Term.pi (Variable.free "A") (.sort 0) (.sort 0)
#eval Term.sort 0
#eval Term.lit 42
#eval Term.letE (Variable.free "x") (.lit 1) (.var (Variable.free "x"))

/-! ## Analysis ops -/
def covEx : Term := .lam (Variable.free "x") (.app (.var (Variable.free "x")) (.lit 1))
#eval freeVars covEx
#eval isClosed covEx
#eval maxBoundIndex covEx
#eval size covEx
#eval binderDepth covEx

/-! ## Substitution ops -/
#eval lift covEx 0 2
#eval lift1 covEx
#eval subst covEx (.lit 42) (Variable.free "f")
#eval alphaEquiv covEx covEx

/-! ## Morphism ops -/
def covHom : TermHom := TermHom.id
#eval covHom.apply (.var (Variable.free "x"))
#eval Renaming.apply Renaming.id covEx

/-! ## Classification -/
#eval isVar covEx
#eval isLam covEx
#eval isValue covEx
#eval termKind covEx

/-! ## Reduction -/
#eval isNormalForm covEx
#eval reduceCBN covEx 10 |>.1

#eval "CORE COVERAGE COMPLETE"

end MiniSyntaxKernel
