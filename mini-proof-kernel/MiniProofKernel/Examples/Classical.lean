/-
# Proof Kernel: Classical Logic Examples

Natural deduction proofs using the law of excluded middle (LEM).
Demonstrates classical tautologies that are not provable
intuitionistically: double-negation elimination, Peirce's law,
and classical De Morgan equivalences.
-/

import MiniProofKernel.Core.Basic
import MiniProofKernel.Core.Objects
import MiniProofKernel.Core.Laws
import MiniProofKernel.Morphisms.Equivalence

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Simple Identities -/

def cA : Formula := .atom 0
def cB : Formula := .atom 1
def cC : Formula := .atom 2

-- Identity: A → A
def cId : ProofTree [] (.impl cA cA) :=
  .implI (.hyp (.head _))

/-! ## Excluded Middle -/

-- A ∨ ¬A
def cLEM : ProofTree [] (.or cA (.not cA)) := .lem

-- ¬¬(A ∨ ¬A): double negation of excluded middle (intuitionistically valid)
def cDNLEM : ProofTree [] (.not (.not (.or cA (.not cA)))) :=
  .notI (.notE (.hyp (.head _)) cLEM)

/-! ## Double Negation Elimination -/

-- ¬¬A → A (classical)
def cDNE : ProofTree [] (.impl (.not (.not cA)) cA) :=
  .implI (.orE (.lem (A:=cA))
    (.hyp (.head _))
    (.falseE (.notE (.hyp (.tail _ (.head _))) (.hyp (.head _)))))

/-! ## Peirce's Law -/

-- ((A → B) → A) → A (classical)
def cPierce : ProofTree [] (.impl (.impl (.impl cA cB) cA) cA) :=
  .implI (.orE (.lem (A:=cA))
    (.hyp (.head _))
    (.falseE (.notE
      (.implI (.falseE (.implE (.hyp (.tail _ (.tail _ (.head _))))
        (.implI (.falseE (.hyp (.head _)))))))
      (.hyp (.head _)))))

/-! ## Classical De Morgan -/

-- ¬(A ∧ B) → (¬A ∨ ¬B) (classical direction)
def cDeMorganAnd : ProofTree [] (.impl (.not (.and cA cB)) (.or (.not cA) (.not cB))) :=
  .implI (.orE (.lem (A:=cA))
    (.orE (.lem (A:=cB))
      (.falseE (.notE (.hyp (.tail _ (.head _)))
        (.andI (.hyp (.head _)) (.hyp (.head _)))))
      (.orIr (.notI (.hyp (.head _)))))
    (.orIl (.notI (.hyp (.head _)))))

-- (¬A ∨ ¬B) → ¬(A ∧ B) (intuitionistic but shown in classical context)
def cDeMorganOr : ProofTree [] (.impl (.or (.not cA) (.not cB)) (.not (.and cA cB))) :=
  .implI (.notI (.orE (.hyp (.tail _ (.head _)))
    (.notE (.hyp (.head _)) (.andEl (.hyp (.head _))))
    (.notE (.hyp (.head _)) (.andEr (.hyp (.head _))))))

-- ¬(¬A ∧ ¬B) → (A ∨ B) (classical)
def cDeMorganAndElim : ProofTree [] (.impl (.not (.and (.not cA) (.not cB))) (.or cA cB)) :=
  .implI (.orE (.lem (A:=cA))
    (.orIl (.hyp (.head _)))
    (.orE (.lem (A:=cB))
      (.orIr (.hyp (.head _)))
      (.falseE (.notE (.hyp (.tail _ (.tail _ (.head _))))
        (.andI (.hyp (.tail _ (.head _))) (.hyp (.head _)))))))

/-! ## Proof by Contradiction -/

-- (¬A → ⊥) → A (classical proof by contradiction)
def cByContradiction : ProofTree [] (.impl (.impl (.not cA) .false) cA) :=
  .implI (.orE (.lem (A:=cA))
    (.hyp (.head _))
    (.falseE (.implE (.hyp (.tail _ (.head _))) (.hyp (.head _)))))

-- A → (¬A → B) (from contradiction, anything follows)
def cExplosion : ProofTree [] (.impl cA (.impl (.not cA) cB)) :=
  .implI (.implI (.falseE (.notE (.hyp (.head _)) (.hyp (.tail _ (.head _))))))

/-! ## Classical Equivalences -/

-- (A → B) ↔ (¬A ∨ B) (classical equivalence)
def cImplAsOr : ProofTree [] (.equiv (.impl cA cB) (.or (.not cA) cB)) :=
  .equivI
    (.implI (.orE (.lem (A:=cA))
      (.orIr (.implE (.hyp (.tail _ (.head _))) (.hyp (.head _))))
      (.orIl (.notI (.hyp (.head _))))))
    (.implI (.orE (.hyp (.head _))
      (.notI (.notE (.hyp (.head _)) (.hyp (.tail _ (.head _)))))
      (.implI (.hyp (.tail _ (.head _))))))

-- (A ↔ B) ↔ ((A → B) ∧ (B → A))
def cEquivAsConj : ProofTree []
    (.equiv (.equiv cA cB) (.and (.impl cA cB) (.impl cB cA))) :=
  .equivI
    (.implI (.andI
      (.implI (.implE (.equivEl (.hyp (.head _))) (.hyp (.head _))))
      (.implI (.implE (.equivEr (.hyp (.head _))) (.hyp (.head _))))))
    (.implI (.equivI (.andEl (.hyp (.head _))) (.andEr (.hyp (.head _)))))

/-! ## Double Negation Shift -/

-- ¬¬A (double negation of A)
def cDNIntro : ProofTree [] (.impl cA (.not (.not cA))) :=
  .implI (.notI (.notE (.hyp (.head _)) (.hyp (.tail _ (.head _)))))

-- ¬¬(A → B) → (¬¬A → ¬¬B) (classical)
def cDNShift : ProofTree []
    (.impl (.not (.not (.impl cA cB)))
           (.impl (.not (.not cA)) (.not (.not cB)))) :=
  .implI (.implI (.notI (.notE (.hyp (.head _))
    (.implE (cDNE.weakenCons.weakenCons.weakenCons)
      (.implI (.notE (.cDNE.weakenCons) (.hyp (.head _))))))))

/-! ## Evaluation Examples -/

#eval cId.size
#eval cLEM.size
#eval cDNE.size
#eval cPierce.size
#eval cDeMorganAnd.size
#eval cDeMorganOr.size
#eval cDeMorganAndElim.size
#eval cByContradiction.size
#eval cExplosion.size
#eval cEquivAsConj.size

end MiniProofKernel
