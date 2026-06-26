/-
# Logic Kernel: Derived Inference Rules

Common derived rules of propositional logic.
-/

import MiniLogicKernel.Core.Basic

namespace MiniLogicKernel

def ruleId (A : Formula) : Formula := .impl A A

def ruleModusPonens (implAB A B : Formula) : Formula :=
  .impl (.and implAB A) B

def ruleSyllogism (A B C : Formula) : Formula :=
  .impl (.and (.impl A B) (.impl B C)) (.impl A C)

def ruleExportation (A B C : Formula) : Formula :=
  .impl (.impl (.and A B) C) (.impl A (.impl B C))

def ruleImportation (A B C : Formula) : Formula :=
  .impl (.impl A (.impl B C)) (.impl (.and A B) C)

def ruleContraposition (A B : Formula) : Formula :=
  .impl (.impl A B) (.impl (.not B) (.not A))

def ruleExcludedMiddle (A : Formula) : Formula :=
  .or A (.not A)

def ruleNonContradiction (A : Formula) : Formula :=
  .not (.and A (.not A))

def ruleDoubleNegElim (A : Formula) : Formula :=
  .impl (.not (.not A)) A

def ruleDoubleNegIntro (A : Formula) : Formula :=
  .impl A (.not (.not A))

def ruleDeMorganAnd (A B : Formula) : Formula :=
  .impl (.not (.and A B)) (.or (.not A) (.not B))

def ruleDeMorganOr (A B : Formula) : Formula :=
  .impl (.not (.or A B)) (.and (.not A) (.not B))

def ruleProofByCases (A B C : Formula) : Formula :=
  .impl (.and (.impl A C) (.impl B C)) (.impl (.or A B) C)

end MiniLogicKernel
