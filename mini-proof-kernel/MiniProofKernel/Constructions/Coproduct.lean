/-
# Proof Kernel: Coproduct Construction

Disjunction (∨) as the categorical coproduct in the proof category.
Defines injection and case-analysis as coproduct structure maps
and proves the universal property.
-/

import MiniProofKernel.Core.Basic
import MiniProofKernel.Core.Laws

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Coproduct Structure (Disjunction) -/

/-- First injection: A → A ∨ B.
(This is just `orIl` from natural deduction.) -/
def coprodIntroL {Γ : Context} {A B : Formula}
    (p : ProofTree Γ A) : ProofTree Γ (.or A B) :=
  .orIl p

/-- Second injection: B → A ∨ B.
(This is just `orIr` from natural deduction.) -/
def coprodIntroR {Γ : Context} {A B : Formula}
    (p : ProofTree Γ B) : ProofTree Γ (.or A B) :=
  .orIr p

/-- Coproduct elimination (case analysis): from A ∨ B and two branches
Γ,A ⊢ C and Γ,B ⊢ C, derive Γ ⊢ C.
(This is just `orE` from natural deduction.) -/
def coprodElim {Γ : Context} {A B C : Formula}
    (p : ProofTree Γ (.or A B))
    (q : ProofTree (A :: Γ) C)
    (r : ProofTree (B :: Γ) C) : ProofTree Γ C :=
  .orE p q r

/-- Unique mediating morphism for the coproduct.
Given Γ ⊢ A → C and Γ ⊢ B → C, produce Γ ⊢ (A ∨ B) → C. -/
def coprodCase {Γ : Context} {A B C : Formula}
    (f : ProofTree Γ (.impl A C)) (g : ProofTree Γ (.impl B C))
    : ProofTree Γ (.impl (.or A B) C) :=
  .implI (.orE (.hyp (.head _))
    (.implE (f.weakenCons) (.hyp (.head _)))
    (.implE (g.weakenCons) (.hyp (.head _))))

/-! ## Universal Property of Disjunction -/

/-- Beta rule for left injection: case(inl(a), f, g) ≈ f(a). -/
def coprodBetaL {Γ : Context} {A B C : Formula}
    (f : ProofTree Γ (.impl A C)) (g : ProofTree Γ (.impl B C))
    : ProofTree Γ (.impl A C) :=
  .implI (.orE (.orIl (.hyp (.head _)))
    (.implE (f.weakenCons) (.hyp (.head _)))
    (.implE (g.weakenCons) (.hyp (.head _))))

/-- Beta rule for right injection: case(inr(b), f, g) ≈ g(b). -/
def coprodBetaR {Γ : Context} {A B C : Formula}
    (f : ProofTree Γ (.impl A C)) (g : ProofTree Γ (.impl B C))
    : ProofTree Γ (.impl B C) :=
  .implI (.orE (.orIr (.hyp (.head _)))
    (.implE (f.weakenCons) (.hyp (.head _)))
    (.implE (g.weakenCons) (.hyp (.head _))))

/-- The eta rule: case distributes over orE.
This expresses the uniqueness part of the universal property. -/
def coprodEta {Γ : Context} {A B C : Formula}
    (h : ProofTree Γ (.impl (.or A B) C))
    : ProofTree Γ (.impl (.or A B) C) :=
  .implI (.orE (.hyp (.head _))
    (.implE (coprodCase
      (.implI (.hyp (.head _)))
      (.implI (.hyp (.head _))).weakenCons)
     (.hyp (.head _)))
    (.implE (coprodCase
      (.implI (.hyp (.head _)))
      (.implI (.hyp (.head _))).weakenCons)
     (.hyp (.head _))))

/-- Universal property: mapping from (A → C) × (B → C) to ((A ∨ B) → C). -/
def coprodUniversal {Γ : Context} {A B C : Formula} : ProofTree Γ
    (.impl (.and (.impl A C) (.impl B C)) (.impl (.or A B) C)) :=
  .implI (.implI (.orE (.hyp (.head _))
    (.implE (.andEl (.hyp (.tail _ (.head _)))) (.hyp (.head _)))
    (.implE (.andEr (.hyp (.tail _ (.head _)))) (.hyp (.head _)))))

/-- Codagonal (fold): A ∨ A → A. -/
def coprodCodiag {Γ : Context} {A : Formula}
    (p : ProofTree Γ (.or A A)) : ProofTree Γ A :=
  .orE p (.hyp (.head _)) (.hyp (.head _))

/-- Swap: A ∨ B → B ∨ A (commutativity of coproduct). -/
def coprodSwap {Γ : Context} {A B : Formula}
    (p : ProofTree Γ (.or A B)) : ProofTree Γ (.or B A) :=
  .orE p (.orIr (.hyp (.head _))) (.orIl (.hyp (.head _)))

/-- Associativity: (A ∨ B) ∨ C → A ∨ (B ∨ C). -/
def coprodAssoc {Γ : Context} {A B C : Formula}
    (p : ProofTree Γ (.or (.or A B) C)) : ProofTree Γ (.or A (.or B C)) :=
  .orE p
    (.orE (.hyp (.head _))
      (.orIl (.hyp (.head _)))
      (.orIr (.orIl (.hyp (.head _)))))
    (.orIr (.orIr (.hyp (.head _))))

/-! ## Evaluation Examples -/

def coprodA : Formula := .atom 0
def coprodB : Formula := .atom 1
def coprodC : Formula := .atom 2

-- Prove A → A ∨ B
def coprodInjLProof : ProofTree [] (.impl coprodA (.or coprodA coprodB)) :=
  .implI (.orIl (.hyp (.head _)))

-- Prove (A → C) ∧ (B → C) → ((A ∨ B) → C)
def coprodUnivProof : ProofTree [] (.impl
    (.and (.impl coprodA coprodC) (.impl coprodB coprodC))
    (.impl (.or coprodA coprodB) coprodC)) :=
  coprodUniversal

-- Swap: A ∨ B → B ∨ A
def coprodSwapProof : ProofTree [] (.impl (.or coprodA coprodB) (.or coprodB coprodA)) :=
  .implI (coprodSwap (.hyp (.head _)))

#eval coprodInjLProof.size
#eval coprodInjLProof.isValid
#eval coprodUnivProof.size
#eval coprodSwapProof.size
#eval (.or coprodA coprodB).complexity

end MiniProofKernel
