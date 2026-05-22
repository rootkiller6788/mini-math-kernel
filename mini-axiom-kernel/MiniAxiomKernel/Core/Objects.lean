/-
# Axioms Kernel: Standard Axioms

Standard logical axioms: identity, non-contradiction, excluded middle,
transitivity, substitution, and equality axioms.
-/

import MiniAxiomKernel.Core.Basic

open MiniLogicKernel

namespace MiniAxiomKernel

/-! ## Basic Logical Axioms -/

def axiomId (A : Formula) : Axiom :=
  Axiom.simple "id" (.impl A A)

def axiomNonContradiction (A : Formula) : Axiom :=
  Axiom.simple "non-contradiction" (.not (.and A (.not A)))

def axiomExcludedMiddle (A : Formula) : Axiom :=
  Axiom.simple "lem" (.or A (.not A))

def axiomDoubleNegElim (A : Formula) : Axiom :=
  Axiom.simple "double-neg-elim" (.impl (.not (.not A)) A)

def axiomDoubleNegIntro (A : Formula) : Axiom :=
  Axiom.simple "double-neg-intro" (.impl A (.not (.not A)))

/-! ## Transitivity and Syllogism -/

def axiomTransitivity (A B C : Formula) : Axiom :=
  Axiom.simple "transitivity" (.impl (.and (.impl A B) (.impl B C)) (.impl A C))

def axiomSyllogism (A B C : Formula) : Axiom :=
  Axiom.simple "syllogism" (.impl (.and (.impl A B) (.impl B C)) (.impl A C))

def axiomModusPonens (A B : Formula) : Axiom :=
  Axiom.simple "modus-ponens" (.impl (.and A (.impl A B)) B)

/-! ## Equality Axioms (Reflexivity, Symmetry, Transitivity) -/

def axiomEqRefl (A : Formula) : Axiom :=
  Axiom.simple "eq-refl" (.equiv A A)

def axiomEqSymm (A B : Formula) : Axiom :=
  Axiom.simple "eq-symm" (.impl (.equiv A B) (.equiv B A))

def axiomEqTrans (A B C : Formula) : Axiom :=
  Axiom.simple "eq-trans" (.impl (.and (.equiv A B) (.equiv B C)) (.equiv A C))

/-! ## Substitution and Congruence -/

def axiomSubst (A B : Formula) (P : Formula) : Axiom :=
  Axiom.simple "subst" (.impl (.equiv A B) (.equiv P P))

def axiomCongrNot (A B : Formula) : Axiom :=
  Axiom.simple "congr-not" (.impl (.equiv A B) (.equiv (.not A) (.not B)))

def axiomCongrAnd (A1 A2 B1 B2 : Formula) : Axiom :=
  Axiom.simple "congr-and" (.impl (.and (.equiv A1 A2) (.equiv B1 B2)) (.equiv (.and A1 B1) (.and A2 B2)))

/-! ## De Morgan Laws as Axioms -/

def axiomDeMorganAnd (A B : Formula) : Axiom :=
  Axiom.simple "de-morgan-and" (.equiv (.not (.and A B)) (.or (.not A) (.not B)))

def axiomDeMorganOr (A B : Formula) : Axiom :=
  Axiom.simple "de-morgan-or" (.equiv (.not (.or A B)) (.and (.not A) (.not B)))

/-! ## Classical Axioms Collection -/

/-- The standard set of classical logical axioms. -/
def classicalAxioms : List Axiom :=
  [ axiomId (.atom 0)
  , axiomNonContradiction (.atom 0)
  , axiomExcludedMiddle (.atom 0)
  , axiomDoubleNegElim (.atom 0)
  , axiomTransitivity (.atom 0) (.atom 1) (.atom 2)
  , axiomEqRefl (.atom 0)
  , axiomEqSymm (.atom 0) (.atom 1)
  , axiomEqTrans (.atom 0) (.atom 1) (.atom 2)
  ]

/-- Build an AxiomSystem containing the classical axioms. -/
def classicalAxiomSystem : AxiomSystem :=
  AxiomSystem.empty "ClassicalLogic" "1.0"
    |>.addAxioms classicalAxioms

/-! ## #eval Examples -/

#eval axiomId (.atom 0)
#eval axiomExcludedMiddle (.impl (.atom 0) (.atom 1)).statement
#eval axiomTransitivity (.atom 0) (.atom 1) (.atom 2)
#eval classicalAxioms.length
#eval classicalAxiomSystem.checkConsistent

end MiniAxiomKernel
