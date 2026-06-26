/-
# Proof Kernel: Natural Deduction

Helper combinators for constructing natural deduction proofs.
-/

import MiniProofKernel.Core.Basic

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Hypothesis Helpers -/

def assume (A : Formula) : ProofTree (A :: Γ) A :=
  .hyp (.head _)

/-! ## Forward Reasoning -/

def applyModusPonens {Γ : Context} {A B : Formula}
    (impl : ProofTree Γ (.impl A B)) (prem : ProofTree Γ A) : ProofTree Γ B :=
  .implE impl prem

def andLeft {Γ : Context} {A B : Formula} (p : ProofTree Γ (.and A B)) : ProofTree Γ A := .andEl p
def andRight {Γ : Context} {A B : Formula} (p : ProofTree Γ (.and A B)) : ProofTree Γ B := .andEr p

def andIntro {Γ : Context} {A B : Formula}
    (p : ProofTree Γ A) (q : ProofTree Γ B) : ProofTree Γ (.and A B) := .andI p q

/-! ## Backward Reasoning -/

def introImpl {Γ : Context} {A B : Formula}
    (f : ProofTree (A :: Γ) A → ProofTree (A :: Γ) B) : ProofTree Γ (.impl A B) :=
  .implI (f (.hyp (.head _)))

def introOrLeft {Γ : Context} {A B : Formula} (p : ProofTree Γ A) : ProofTree Γ (.or A B) :=
  .orIl p

def introOrRight {Γ : Context} {A B : Formula} (p : ProofTree Γ B) : ProofTree Γ (.or A B) :=
  .orIr p

def introNot {Γ : Context} {A : Formula}
    (f : ProofTree (A :: Γ) A → ProofTree (A :: Γ) .false) : ProofTree Γ (.not A) :=
  .notI (f (.hyp (.head _)))

/-! ## Classical Reasoning -/

def byContradiction {Γ : Context} {A : Formula}
    (f : ProofTree ((.not A) :: Γ) (.not A) → ProofTree ((.not A) :: Γ) .false) : ProofTree Γ A :=
  .orE (.lem (a:=A)) (.hyp (.head _)) (.falseE (f (.hyp (.head _))))

def doubleNegElim {Γ : Context} {A : Formula}
    (p : ProofTree Γ (.not (.not A))) : ProofTree Γ A :=
  .orE (.lem (a:=A)) (.hyp (.head _)) (.falseE (.notE (p.weakenCons) (.hyp (.head _))))

end MiniProofKernel
