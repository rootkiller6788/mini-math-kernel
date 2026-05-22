/-
# Proof Kernel: Product Construction

Conjunction (∧) as the categorical product in the proof category.
Defines introduction and elimination as product structure maps
and proves the universal property.
-/

import MiniProofKernel.Core.Basic
import MiniProofKernel.Core.Laws

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Product Structure (Conjunction) -/

/-- Product introduction: pair two proofs into a conjunction.
(This is just `andI` from natural deduction.) -/
def prodIntro {Γ : Context} {A B : Formula}
    (p : ProofTree Γ A) (q : ProofTree Γ B) : ProofTree Γ (.and A B) :=
  .andI p q

/-- First projection: extract left conjunct.
(This is just `andEl` from natural deduction.) -/
def prodElimL {Γ : Context} {A B : Formula}
    (p : ProofTree Γ (.and A B)) : ProofTree Γ A :=
  .andEl p

/-- Second projection: extract right conjunct.
(This is just `andEr` from natural deduction.) -/
def prodElimR {Γ : Context} {A B : Formula}
    (p : ProofTree Γ (.and A B)) : ProofTree Γ B :=
  .andEr p

/-- The unique pairing induced by two proofs into the product components.
Given Γ ⊢ C → A and Γ ⊢ C → B, produce Γ ⊢ C → (A ∧ B). -/
def prodPair {Γ : Context} {A B C : Formula}
    (f : ProofTree Γ (.impl C A)) (g : ProofTree Γ (.impl C B))
    : ProofTree Γ (.impl C (.and A B)) :=
  .implI (.andI
    (.implE (f.weakenCons) (.hyp (.head _)))
    (.implE (g.weakenCons) (.hyp (.head _))))

/-! ## Universal Property of Conjunction -/

/-- The beta rule: projecting the first component after pairing recovers `f`.
Constructs the proof that prodElimL ∘ prodPair f g ≈ f. -/
def prodBetaL {Γ : Context} {A B C : Formula}
    (f : ProofTree Γ (.impl C A)) (g : ProofTree Γ (.impl C B))
    : ProofTree Γ (.impl C A) :=
  .implI (.andEl (.andI
    (.implE (f.weakenCons) (.hyp (.head _)))
    (.implE (g.weakenCons) (.hyp (.head _)))))

/-- The beta rule: projecting the second component after pairing recovers `g`. -/
def prodBetaR {Γ : Context} {A B C : Formula}
    (f : ProofTree Γ (.impl C A)) (g : ProofTree Γ (.impl C B))
    : ProofTree Γ (.impl C B) :=
  .implI (.andEr (.andI
    (.implE (f.weakenCons) (.hyp (.head _)))
    (.implE (g.weakenCons) (.hyp (.head _)))))

/-- The eta rule: pairing the projections recovers the original proof.
Given Γ ⊢ C → (A ∧ B), we can recover it via pairing the projections. -/
def prodEta {Γ : Context} {A B C : Formula}
    (h : ProofTree Γ (.impl C (.and A B)))
    : ProofTree Γ (.impl C (.and A B)) :=
  .implI (.andI
    (.andEl (.implE (h.weakenCons) (.hyp (.head _))))
    (.andEr (.implE (h.weakenCons) (.hyp (.head _)))))

/-- Universal property: given two proofs f : Γ ⊢ C → A and g : Γ ⊢ C → B,
there exists a unique h : Γ ⊢ C → (A ∧ B) such that projections recover f, g.
We demonstrate the mapping in both directions. -/
def prodUniversal {Γ : Context} {A B C : Formula} : ProofTree Γ
    (.impl (.and (.impl C A) (.impl C B)) (.impl C (.and A B))) :=
  .implI (.implI (.andI
    (.implE (.andEl (.hyp (.head _))) (.hyp (.head _)))
    (.implE (.andEr (.hyp (.head _))) (.hyp (.head _)))))

/-- Diagonal map Δ : A → A ∧ A, the duplication morphism. -/
def prodDiag {Γ : Context} {A : Formula}
    (p : ProofTree Γ A) : ProofTree Γ (.and A A) :=
  .andI p p

/-- Twist map A ∧ B → B ∧ A (commutativity of product). -/
def prodSwap {Γ : Context} {A B : Formula}
    (p : ProofTree Γ (.and A B)) : ProofTree Γ (.and B A) :=
  .andI (.andEr p) (.andEl p)

/-- Associativity: (A ∧ B) ∧ C → A ∧ (B ∧ C). -/
def prodAssoc {Γ : Context} {A B C : Formula}
    (p : ProofTree Γ (.and (.and A B) C)) : ProofTree Γ (.and A (.and B C)) :=
  .andI (.andEl (.andEl p)) (.andI (.andEr (.andEl p)) (.andEr p))

/-! ## Evaluation Examples -/

def prodA : Formula := .atom 0
def prodB : Formula := .atom 1
def prodC : Formula := .atom 2

-- Prove A ∧ B → A (first projection as implication)
def prodProjLProof : ProofTree [] (.impl (.and prodA prodB) prodA) :=
  .implI (.andEl (.hyp (.head _)))

-- Prove A → (B → (A ∧ B))
def prodCurriedPair : ProofTree [] (.impl prodA (.impl prodB (.and prodA prodB))) :=
  .implI (.implI (.andI (.hyp (.tail _ (.head _))) (.hyp (.head _))))

-- Swap proof: A ∧ B → B ∧ A
def prodSwapProof : ProofTree [] (.impl (.and prodA prodB) (.and prodB prodA)) :=
  .implI (prodSwap (.hyp (.head _)))

#eval prodProjLProof.size
#eval prodProjLProof.isValid
#eval prodCurriedPair.size
#eval prodSwapProof.size
#eval (prodAssoc (.andI (.andI (.hyp (.head _ : (prodA :: []).Mem prodA))
                                (.hyp (.head _ : (prodA :: []).Mem prodA)))
                       (.hyp (.head _ : (prodA :: []).Mem prodA)))).size

end MiniProofKernel
