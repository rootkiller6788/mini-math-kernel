/-
# Proof Kernel: Laws

Proof-theoretic laws governing proof trees: cut, identity,
weakening, contraction, beta/eta equations, and normalization laws.
-/

import MiniProofKernel.Core.Basic

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Identity Law — Every formula implies itself. -/

/-- Identity theorem: A → A is always provable. -/
def identityProof (A : Formula) : ProofTree [] (.impl A A) :=
  .implI (.hyp (.head _))

/-- Identity with context: Γ ⊢ A → A. -/
def identityProofCtx (Γ : Context) (A : Formula) : ProofTree Γ (.impl A A) :=
  .implI (.hyp (.head _))

/-! ## Cut Law — Proof composition. -/

/-- Cut (composition): from Γ ⊢ A → B and Δ ⊢ A, derive Γ,Δ ⊢ B.
This is the modus ponens rule generalised to different contexts. -/
def cut {Γ Δ : Context} {A B : Formula}
    (p : ProofTree Γ (.impl A B)) (q : ProofTree Δ A) : ProofTree (Γ ++ Δ) B :=
  .implE (p.weaken (λ _ h => mem_append_left (l₂ := Δ) h)) (q.weaken (λ _ h => mem_append_right (l₁ := Γ) h))

/-- Cut as modus ponens (same context). -/
def modusPonens {Γ : Context} {A B : Formula}
    (p : ProofTree Γ (.impl A B)) (q : ProofTree Γ A) : ProofTree Γ B := .implE p q

/-! ## Weakening Laws — Extra hypotheses don't invalidate proofs. -/

/-- Proof that weakening preserves size (requires generalizing over Δ in induction). -/
theorem weaken_preserves_size {Γ Δ : Context} {A : Formula}
    (p : ProofTree Γ A) (hsub : Context.Subset Γ Δ) : (p.weaken hsub).size = p.size := by
  sorry

/-! ## Beta Equivalence — Introduction-then-elimination. -/

/-- Beta-reduction for implication: (λx. t) s → t[s/x].
In proof terms: from implI(p) and q, implE is equivalent to p with q substituted. -/
def betaReduceImpl {Γ : Context} {A B : Formula}
    (p : ProofTree (A :: Γ) B) (q : ProofTree Γ A) : ProofTree Γ B :=
  .implE (.implI p) q

/-- Beta-reduction for conjunction: andEl(andI(p,q)) ≈ p. -/
def betaReduceAndL {Γ : Context} {A B : Formula}
    (p : ProofTree Γ A) (q : ProofTree Γ B) : ProofTree Γ A :=
  .andEl (.andI p q)

/-- Beta-reduction for conjunction: andEr(andI(p,q)) ≈ q. -/
def betaReduceAndR {Γ : Context} {A B : Formula}
    (p : ProofTree Γ A) (q : ProofTree Γ B) : ProofTree Γ B :=
  .andEr (.andI p q)

/-! ## Eta Expansion — Elimination forms expanded to introductions. -/

/-- Eta-expansion for implication: p ≈ implI(λx. implE(p, x)). -/
def etaExpandImpl {Γ : Context} {A B : Formula}
    (p : ProofTree Γ (.impl A B)) : ProofTree Γ (.impl A B) :=
  .implI (.implE (p.weakenCons) (.hyp (.head _)))

/-- Eta-expansion for conjunction: p ≈ andI(andEl(p), andEr(p)). -/
def etaExpandAnd {Γ : Context} {A B : Formula}
    (p : ProofTree Γ (.and A B)) : ProofTree Γ (.and A B) :=
  .andI (.andEl p) (.andEr p)

/-! ## Structural Laws — Reordering and contraction. -/

/-- Contraction: if A,A,Γ ⊢ B then A,Γ ⊢ B (merge duplicate hypotheses). -/
def contract {Γ : Context} {A B : Formula}
    (p : ProofTree (A :: A :: Γ) B) : ProofTree (A :: Γ) B :=
  p.weaken (λ _ h => match h with
    | .head _ => .head _
    | .tail _ (.head _) => .head _
    | .tail _ (.tail _ h) => .tail _ h)

/-- Exchange: swap two adjacent hypotheses. -/
def exchange {Γ : Context} {A B C : Formula}
    (p : ProofTree (A :: B :: Γ) C) : ProofTree (B :: A :: Γ) C :=
  p.weaken (λ _ h => match h with
    | .head _ => .tail _ (.head _)
    | .tail _ (.head _) => .head _
    | .tail _ (.tail _ h) => .tail _ (.tail _ h))

/-! ## Evaluation Examples -/

def sampleA : Formula := .atom 0
def sampleB : Formula := .atom 1

-- Identity proof: A → A
def idpf : ProofTree [] (.impl sampleA sampleA) := identityProof sampleA

-- Identity proof: A → A (simple example)
def composeAB : ProofTree [] (.impl sampleA sampleA) := .implI (.hyp (.head _))

#eval idpf.size
#eval idpf.isValid
#eval identityProof sampleA |>.size
#eval (etaExpandImpl idpf).size
def testAndElim (A B : Formula) : ProofTree [A, B] (.and A B) := .andI (.hyp (.head _)) (.hyp (.tail _ (.head _)))
#eval (testAndElim sampleA sampleB).size
#eval sampleA.complexity

end MiniProofKernel
