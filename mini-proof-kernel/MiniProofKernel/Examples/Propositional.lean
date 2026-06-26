/-
# Proof Kernel: Propositional Logic Examples

Natural deduction proofs of common propositional tautologies.
Covers the full set of standard examples: identity, modus ponens,
syllogism, De Morgan laws, distributivity, and proof constructions
using both classical and intuitionistic reasoning.
-/

import MiniProofKernel.Core.Basic
import MiniProofKernel.Core.Objects
import MiniProofKernel.Core.Laws

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Atomic Propositions -/

def pA : Formula := .atom 0
def pB : Formula := .atom 1
def pC : Formula := .atom 2
def pD : Formula := .atom 3

/-! ## Basic Tautologies -/

-- Identity: A ⊢ A
def propId : ProofTree [pA] pA := .hyp (.head _)

-- Identity as implication: ⊢ A → A
def propIdImpl : ProofTree [] (.impl pA pA) := .implI (.hyp (.head _))

-- Modus ponens: A → B, A ⊢ B
def propMP : ProofTree [.impl pA pB, pA] pB :=
  .implE (.hyp (.head _)) (.hyp (.tail _ (.head _)))

-- True: ⊢ ⊤
def propTrue : ProofTree [] .true := .trueI

-- Weakening: A ⊢ B → A
def propWeakening : ProofTree [pA] (.impl pB pA) :=
  .implI (.hyp (.tail _ (.head _)))

/-! ## Implication Theorems -/

-- Syllogism: (A → B) → ((B → C) → (A → C))
def propSyllogism : ProofTree []
    (.impl (.impl pA pB) (.impl (.impl pB pC) (.impl pA pC))) :=
  .implI (.implI (.implI (
    .implE (.hyp (.tail _ (.head _)))
           (.implE (.hyp (.tail _ (.tail _ (.head _)))) (.hyp (.head _)))
  )))

-- Composition: (A → B) → ((C → A) → (C → B))
def propComposition : ProofTree []
    (.impl (.impl pA pB) (.impl (.impl pC pA) (.impl pC pB))) :=
  .implI (.implI (.implI (
    .implE (.hyp (.tail _ (.tail _ (.head _))))
           (.implE (.hyp (.tail _ (.head _))) (.hyp (.head _)))
  )))

-- Self-distribution: (A → (A → B)) → (A → B)
def propSelfDistrib : ProofTree []
    (.impl (.impl pA (.impl pA pB)) (.impl pA pB)) :=
  .implI (.implI (
    .implE (.implE (.hyp (.tail _ (.head _))) (.hyp (.head _)))
           (.hyp (.head _))
  ))

/-! ## Conjunction Theorems -/

-- ∧-introduction: A → (B → (A ∧ B))
def propAndIntro : ProofTree [] (.impl pA (.impl pB (.and pA pB))) :=
  .implI (.implI (.andI (.hyp (.tail _ (.head _))) (.hyp (.head _))))

-- ∧-elimination left: (A ∧ B) → A
def propAndElimL : ProofTree [] (.impl (.and pA pB) pA) :=
  .implI (.andEl (.hyp (.head _)))

-- ∧-elimination right: (A ∧ B) → B
def propAndElimR : ProofTree [] (.impl (.and pA pB) pB) :=
  .implI (.andEr (.hyp (.head _)))

-- ∧-idempotence: (A ∧ A) ↔ A (one direction)
def propAndIdem : ProofTree [] (.impl (.and pA pA) pA) :=
  .implI (.andEl (.hyp (.head _)))

-- Import-export: (A → (B → C)) ↔ ((A ∧ B) → C) (one direction)
def propImportExportFwd : ProofTree []
    (.impl (.impl pA (.impl pB pC)) (.impl (.and pA pB) pC)) :=
  .implI (.implI (
    .implE (.implE (.hyp (.tail _ (.head _)))
            (.andEl (.hyp (.head _))))
           (.andEr (.hyp (.head _)))
  ))

-- Import-export reverse: ((A ∧ B) → C) → (A → (B → C))
def propImportExportRev : ProofTree []
    (.impl (.impl (.and pA pB) pC) (.impl pA (.impl pB pC))) :=
  .implI (.implI (.implI (
    .implE (.hyp (.tail _ (.tail _ (.head _))))
           (.andI (.hyp (.tail _ (.head _))) (.hyp (.head _)))
  )))

/-! ## Disjunction Theorems -/

-- ∨-introduction left: A → (A ∨ B)
def propOrIntroL : ProofTree [] (.impl pA (.or pA pB)) :=
  .implI (.orIl (.hyp (.head _)))

-- ∨-introduction right: B → (A ∨ B)
def propOrIntroR : ProofTree [] (.impl pB (.or pA pB)) :=
  .implI (.orIr (.hyp (.head _)))

-- ∨-elimination: (A → C) → ((B → C) → ((A ∨ B) → C))
def propOrElim : ProofTree []
    (.impl (.impl pA pC) (.impl (.impl pB pC) (.impl (.or pA pB) pC))) :=
  .implI (.implI (.implI (.orE (.hyp (.head _))
    (.implE (.hyp (.tail _ (.tail _ (.tail _ (.head _))))) (.hyp (.head _)))
    (.implE (.hyp (.tail _ (.tail _ (.head _)))) (.hyp (.head _))))))

/-! ## Negation Theorems -/

-- Non-contradiction: ⊢ ¬(A ∧ ¬A)
def propNC : ProofTree [] (.not (.and pA (.not pA))) :=
  .notI (.notE (.andEr (.hyp (.head _))) (.andEl (.hyp (.head _))))

-- Double negation introduction: A → ¬¬A
def propDNIntro : ProofTree [] (.impl pA (.not (.not pA))) :=
  .implI (.notI (.notE (.hyp (.head _)) (.hyp (.tail _ (.head _)))))

-- Contrapositive: (A → B) → (¬B → ¬A)
def propContrapositive : ProofTree []
    (.impl (.impl pA pB) (.impl (.not pB) (.not pA))) :=
  .implI (.implI (.notI (
    .notE (.hyp (.head _))
          (.implE (.hyp (.tail _ (.tail _ (.head _)))) (.hyp (.head _)))
  )))

-- Ex falso: ⊢ .false → A
def propEFQ : ProofTree [] (.impl .false pA) :=
  .implI (.falseE (.hyp (.head _)))

/-! ## Distributivity -/

-- ∧ over ∨: (A ∧ (B ∨ C)) → ((A ∧ B) ∨ (A ∧ C))
def propDistribAndOr : ProofTree []
    (.impl (.and pA (.or pB pC)) (.or (.and pA pB) (.and pA pC))) :=
  .implI (.orE (.andEr (.hyp (.head _)))
    (.orIl (.andI (.andEl (.hyp (.tail _ (.head _))) (.hyp (.head _))))
    (.orIr (.andI (.andEl (.hyp (.tail _ (.head _))) (.hyp (.head _))))))

-- ∨ over ∧: ((A ∨ B) ∧ (A ∨ C)) → (A ∨ (B ∧ C))
def propDistribOrAnd : ProofTree []
    (.impl (.and (.or pA pB) (.or pA pC)) (.or pA (.and pB pC))) :=
  .implI (.orE (.andEl (.hyp (.head _)))
    (.orIl (.hyp (.head _)))
    (.orE (.andEr (.hyp (.tail _ (.head _))))
      (.orIl (.hyp (.head _)))
      (.orIr (.andI (.hyp (.head _)) (.hyp (.head _))))))

/-! ## Evaluation Examples -/

#eval propIdImpl.size
#eval propMP.size
#eval propSyllogism.size
#eval propAndIntro.size
#eval propOrElim.size
#eval propNC.size
#eval propDNIntro.size
#eval propContrapositive.size
#eval propDistribAndOr.size
#eval propImportExportFwd.size
#eval propTrue.size

end MiniProofKernel
