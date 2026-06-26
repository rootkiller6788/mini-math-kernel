/-
# Proof Kernel: Negation Construction

Negation interpreted as implication of false: ¬A is defined as A → ⊥.
Explores properties of negation: non-contradiction, ex falso quodlibet,
and the relationship between classical and intuitionistic negation.
-/

import MiniProofKernel.Core.Basic
import MiniProofKernel.Core.Laws

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Negation as Implication of False -/

/-- The canonical interpretation: ¬A is equivalent to A → ⊥.
We show both directions of the equivalence. -/

/-- From ¬A (as primitive `.not A`) to A → ⊥. -/
def notToImpl {Γ : Context} {A : Formula}
    (p : ProofTree Γ (.not A)) : ProofTree Γ (.impl A .false) :=
  .implI (.notE (p.weakenCons) (.hyp (.head _)))

/-- From A → ⊥ to ¬A. -/
def implToNot {Γ : Context} {A : Formula}
    (p : ProofTree Γ (.impl A .false)) : ProofTree Γ (.not A) :=
  .notI (.implE (p.weakenCons) (.hyp (.head _)))

/-- Equivalence: ¬A ↔ (A → ⊥). -/
def notEquivImpl {Γ : Context} {A : Formula}
    : ProofTree Γ (.equiv (.not A) (.impl A .false)) :=
  .equivI
    (.implI (notToImpl (.hyp (.head _))))
    (.implI (implToNot (.hyp (.head _))))

/-! ## Ex Falso Quodlibet (Principle of Explosion) -/

/-- From false, anything follows. This is `falseE` from natural deduction. -/
def efq {Γ : Context} {A : Formula}
    (p : ProofTree Γ .false) : ProofTree Γ A :=
  .falseE p

/-- From ¬A and A, derive anything (via false). -/
def notElimExplosion {Γ : Context} {A B : Formula}
    (notA : ProofTree Γ (.not A)) (a : ProofTree Γ A) : ProofTree Γ B :=
  .falseE (.notE notA a)

/-! ## Non-Contradiction -/

/-- Law of non-contradiction: ¬(A ∧ ¬A). -/
def nonContradiction {Γ : Context} {A : Formula}
    : ProofTree Γ (.not (.and A (.not A))) :=
  .notI (.notE (.andEr (.hyp (.head _))) (.andEl (.hyp (.head _))))

/-- Alternative: A → (¬A → B). From A and ¬A, derive anything. -/
def fromContradiction {Γ : Context} {A B : Formula}
    : ProofTree Γ (.impl A (.impl (.not A) B)) :=
  .implI (.implI (notElimExplosion (.hyp (.head _)) (.hyp (.tail _ (.head _)))))

/-! ## Double Negation Properties -/

/-- Introduction of double negation: A → ¬¬A (intuitionistically valid). -/
def doubleNegIntroProp {Γ : Context} {A : Formula}
    : ProofTree Γ (.impl A (.not (.not A))) :=
  .implI (.notI (.notE (.hyp (.head _)) (.hyp (.tail _ (.head _)))))

/-- Triple negation reduces to single negation: ¬¬¬A → ¬A (intuitionistically valid). -/
def tripleNegReduction {Γ : Context} {A : Formula}
    : ProofTree Γ (.impl (.not (.not (.not A))) (.not A)) :=
  .implI (.notI (.notE (.hyp (.tail _ (.head _)))
    (doubleNegIntroProp.weakenCons.weakenCons)))

/-- Double-negation elimination: ¬¬A → A (classically valid, uses LEM). -/
def doubleNegElimProp {Γ : Context} {A : Formula}
    : ProofTree Γ (.impl (.not (.not A)) A) :=
  .implI (.orE (.lem (a:=A))
    (.hyp (.head _))
    (.falseE (.notE (.hyp (.tail _ (.head _))) (.hyp (.head _)))))

/-! ## De Morgan Laws for Negation -/

/-- One direction of De Morgan (intuitionistically valid): ¬(A ∨ B) → (¬A ∧ ¬B). -/
def deMorganOrL {Γ : Context} {A B : Formula}
    : ProofTree Γ (.impl (.not (.or A B)) (.and (.not A) (.not B))) :=
  .implI (.andI
    (.notI (.notE (.hyp (.tail _ (.head _))) (.orIl (.hyp (.head _)))))
    (.notI (.notE (.hyp (.tail _ (.head _))) (.orIr (.hyp (.head _))))))

/-- One direction of De Morgan (intuitionistically valid): (¬A ∨ ¬B) → ¬(A ∧ B). -/
def deMorganAndL {Γ : Context} {A B : Formula}
    : ProofTree Γ (.impl (.or (.not A) (.not B)) (.not (.and A B))) :=
  .implI (.notI (.orE (.hyp (.tail _ (.head _)))
    (.notE (.hyp (.head _)) (.andEl (.hyp (.head _))))
    (.notE (.hyp (.head _)) (.andEr (.hyp (.head _))))))

/-- The other De Morgan direction requires classical logic (LEM):
¬(¬A ∧ ¬B) → (A ∨ B). -/
def deMorganAndRClassical {Γ : Context} {A B : Formula}
    : ProofTree Γ (.impl (.not (.and (.not A) (.not B))) (.or A B)) :=
  .implI (.orE (.lem (a:=A))
    (.orIl (.hyp (.head _)))
    (.orE (.lem (a:=B))
      (.orIr (.hyp (.head _)))
      (.falseE (.notE (.hyp (.tail _ (.tail _ (.head _))))
        (.andI (.hyp (.tail _ (.head _))) (.hyp (.head _)))))))

/-! ## Evaluation Examples -/

def negA : Formula := .atom 0
def negB : Formula := .atom 1

-- Non-contradiction: ¬(A ∧ ¬A)
def negNCProof : ProofTree [] (.not (.and negA (.not negA))) := nonContradiction

-- Double negation intro: A → ¬¬A
def negDNIntro : ProofTree [] (.impl negA (.not (.not negA))) := doubleNegIntroProp

-- Ex falso: ⊥ → A
def negEFQ : ProofTree [] (.impl .false negA) := .implI (.falseE (.hyp (.head _)))

#eval negNCProof.size
#eval negNCProof.isValid
#eval negDNIntro.size
#eval negEFQ.size
#eval nonContradiction.size
#eval tripleNegReduction.size

end MiniProofKernel
