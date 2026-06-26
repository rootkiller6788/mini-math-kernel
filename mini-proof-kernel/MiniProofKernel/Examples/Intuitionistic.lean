/-
# Proof Kernel: Intuitionistic Logic Examples

Natural deduction proofs valid in intuitionistic logic (no LEM).
Includes: identity, weakening, conjunction properties, disjunction
properties, implication properties, negation (as → ⊥), and
the BHK-interpretation constructions.
-/

import MiniProofKernel.Core.Basic
import MiniProofKernel.Core.Objects
import MiniProofKernel.Core.Laws

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Simple Identities -/

def iA : Formula := .atom 0
def iB : Formula := .atom 1
def iC : Formula := .atom 2

-- Identity: A → A
def iId : ProofTree [] (.impl iA iA) := .implI (.hyp (.head _))

-- True introduction
def iTrue : ProofTree [] .true := .trueI

-- False elimination: ⊥ → A
def iEFQ : ProofTree [] (.impl .false iA) := .implI (.falseE (.hyp (.head _)))

/-! ## Conjunction (Product) Properties -/

-- A → (B → (A ∧ B))
def iAndIntro : ProofTree [] (.impl iA (.impl iB (.and iA iB))) :=
  .implI (.implI (.andI (.hyp (.tail _ (.head _))) (.hyp (.head _))))

-- (A ∧ B) → A (left projection)
def iAndElimL : ProofTree [] (.impl (.and iA iB) iA) :=
  .implI (.andEl (.hyp (.head _)))

-- (A ∧ B) → B (right projection)
def iAndElimR : ProofTree [] (.impl (.and iA iB) iB) :=
  .implI (.andEr (.hyp (.head _)))

-- (A ∧ B) → (B ∧ A) (commutativity of ∧)
def iAndComm : ProofTree [] (.impl (.and iA iB) (.and iB iA)) :=
  .implI (.andI (.andEr (.hyp (.head _))) (.andEl (.hyp (.head _))))

-- ((A ∧ B) ∧ C) → (A ∧ (B ∧ C)) (associativity)
def iAndAssoc : ProofTree []
    (.impl (.and (.and iA iB) iC) (.and iA (.and iB iC))) :=
  .implI (.andI
    (.andEl (.andEl (.hyp (.head _))))
    (.andI (.andEr (.andEl (.hyp (.head _)))) (.andEr (.hyp (.head _)))))

-- (A ∧ A) → A (idempotence)
def iAndIdem : ProofTree [] (.impl (.and iA iA) iA) :=
  .implI (.andEl (.hyp (.head _)))

/-! ## Disjunction (Coproduct) Properties -/

-- A → (A ∨ B) (left injection)
def iOrIntroL : ProofTree [] (.impl iA (.or iA iB)) :=
  .implI (.orIl (.hyp (.head _)))

-- B → (A ∨ B) (right injection)
def iOrIntroR : ProofTree [] (.impl iB (.or iA iB)) :=
  .implI (.orIr (.hyp (.head _)))

-- (A ∨ B) → (B ∨ A) (commutativity of ∨)
def iOrComm : ProofTree [] (.impl (.or iA iB) (.or iB iA)) :=
  .implI (.orE (.hyp (.head _))
    (.orIr (.hyp (.head _)))
    (.orIl (.hyp (.head _))))

-- (A ∨ A) → A (idempotence)
def iOrIdem : ProofTree [] (.impl (.or iA iA) iA) :=
  .implI (.orE (.hyp (.head _)) (.hyp (.head _)) (.hyp (.head _)))

-- (A → C) → ((B → C) → ((A ∨ B) → C)) (case analysis)
def iOrElim : ProofTree []
    (.impl (.impl iA iC) (.impl (.impl iB iC) (.impl (.or iA iB) iC))) :=
  .implI (.implI (.implI (.orE (.hyp (.head _))
    (.implE (.hyp (.tail _ (.tail _ (.tail _ (.head _))))) (.hyp (.head _)))
    (.implE (.hyp (.tail _ (.tail _ (.head _)))) (.hyp (.head _))))))

/-! ## Implication Properties -/

-- A → (B → A) (weakening / K combinator)
def iWeakening : ProofTree [] (.impl iA (.impl iB iA)) :=
  .implI (.implI (.hyp (.tail _ (.head _))))

-- (A → (B → C)) → ((A → B) → (A → C)) (distribution / S combinator)
def iDistrib : ProofTree []
    (.impl (.impl iA (.impl iB iC)) (.impl (.impl iA iB) (.impl iA iC))) :=
  .implI (.implI (.implI (
    .implE (.implE (.hyp (.tail _ (.tail _ (.head _)))) (.hyp (.head _)))
           (.implE (.hyp (.tail _ (.head _))) (.hyp (.head _)))
  )))

-- (A → B) → ((B → C) → (A → C)) (transitivity / syllogism)
def iTrans : ProofTree []
    (.impl (.impl iA iB) (.impl (.impl iB iC) (.impl iA iC))) :=
  .implI (.implI (.implI (
    .implE (.hyp (.tail _ (.head _)))
           (.implE (.hyp (.tail _ (.tail _ (.head _)))) (.hyp (.head _)))
  )))

/-! ## Negation Properties (Intuitionistic) -/

-- ¬A: defined as A → ⊥. These are all intuitionistically valid.

-- (A → (B ∧ ¬B)) → ¬A (non-contradiction)
def iNC : ProofTree [] (.impl (.impl iA (.and iB (.not iB))) (.not iA)) :=
  .implI (.notI (.notE (.andEr (.implE (.hyp (.tail _ (.head _)))
    (.hyp (.head _)))) (.andEl (.implE (.hyp (.tail _ (.head _)))
    (.hyp (.head _))))))

-- A → ¬¬A (double negation introduction)
def iDNIntro : ProofTree [] (.impl iA (.not (.not iA))) :=
  .implI (.notI (.notE (.hyp (.head _)) (.hyp (.tail _ (.head _)))))

-- ¬¬¬A → ¬A (triple negation reduction)
def iTripleNeg : ProofTree [] (.impl (.not (.not (.not iA))) (.not iA)) :=
  .implI (.notI (.notE (.hyp (.head _)) (
    .notI (.notE (.hyp (.tail _ (.head _))) (.hyp (.head _))))))

-- (¬A ∨ B) → (A → B) (intuitionistic variant of implication)
def iImplFromOr : ProofTree [] (.impl (.or (.not iA) iB) (.impl iA iB)) :=
  .implI (.implI (.orE (.hyp (.tail _ (.head _)))
    (.falseE (.notE (.hyp (.head _)) (.hyp (.tail _ (.head _)))))
    (.hyp (.head _))))

-- (A → B) → (¬B → ¬A) (contrapositive)
def iContrapositive : ProofTree [] (.impl (.impl iA iB) (.impl (.not iB) (.not iA))) :=
  .implI (.implI (.notI (
    .notE (.hyp (.head _))
          (.implE (.hyp (.tail _ (.tail _ (.head _)))) (.hyp (.head _)))
  )))

/-! ## Distributivity -/

-- (A ∧ (B ∨ C)) → ((A ∧ B) ∨ (A ∧ C)) (intuitionistic)
def iDistribAndOr : ProofTree []
    (.impl (.and iA (.or iB iC)) (.or (.and iA iB) (.and iA iC))) :=
  .implI (.orE (.andEr (.hyp (.head _)))
    (.orIl (.andI (.andEl (.hyp (.tail _ (.head _)))) (.hyp (.head _))))
    (.orIr (.andI (.andEl (.hyp (.tail _ (.head _)))) (.hyp (.head _)))))

-- ((A ∧ B) ∨ (A ∧ C)) → (A ∧ (B ∨ C)) (intuitionistic, reverse direction)
def iDistribAndOrRev : ProofTree []
    (.impl (.or (.and iA iB) (.and iA iC)) (.and iA (.or iB iC))) :=
  .implI (.orE (.hyp (.head _))
    (.andI (.andEl (.hyp (.head _))) (.orIl (.andEr (.hyp (.head _)))))
    (.andI (.andEl (.hyp (.head _))) (.orIr (.andEr (.hyp (.head _))))))

/-! ## Evaluation Examples -/

#eval iId.size
#eval iAndIntro.size
#eval iAndElimL.size
#eval iOrComm.size
#eval iWeakening.size
#eval iTrans.size
#eval iDNIntro.size
#eval iContrapositive.size
#eval iDistribAndOr.size
#eval iDistribAndOrRev.size

end MiniProofKernel
