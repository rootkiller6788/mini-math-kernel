/-
# Proof Kernel: Exponential Construction

Implication (→) as the categorical exponential in the proof category.
Defines currying/uncurrying (abstraction/application) and proves
the adjunction ∧ ⊣ → between product and exponential.
-/

import MiniProofKernel.Core.Basic
import MiniProofKernel.Core.Laws

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Exponential Structure (Implication) -/

/-- Currying (abstraction): from a proof of A ∧ B → C, derive A → (B → C).
This corresponds to the implI rule iterated, moving premises into implications. -/
def curry {Γ : Context} {A B C : Formula}
    (p : ProofTree Γ (.impl (.and A B) C)) : ProofTree Γ (.impl A (.impl B C)) :=
  .implI (.implI (.implE (p.weakenCons.weakenCons)
    (.andI (.hyp (.tail _ (.head _))) (.hyp (.head _)))))

/-- Uncurrying (application): from A → (B → C), derive A ∧ B → C.
Corresponds to using implE twice on the pair components. -/
def uncurry {Γ : Context} {A B C : Formula}
    (p : ProofTree Γ (.impl A (.impl B C))) : ProofTree Γ (.impl (.and A B) C) :=
  .implI (.implE (.implE (p.weakenCons)
    (.andEl (.hyp (.head _))))
    (.andEr (.hyp (.head _))))

/-- Application (evaluation map): (A → B) ∧ A → B, the counit of the adjunction. -/
def evalMap {Γ : Context} {A B : Formula}
    : ProofTree Γ (.impl (.and (.impl A B) A) B) :=
  .implI (.implE (.andEl (.hyp (.head _))) (.andEr (.hyp (.head _))))

/-- The unit of the adjunction: A → (B → A ∧ B). -/
def unitMap {Γ : Context} {A B : Formula}
    : ProofTree Γ (.impl A (.impl B (.and A B))) :=
  .implI (.implI (.andI (.hyp (.tail _ (.head _))) (.hyp (.head _))))

/-! ## Adjunction ∧ ⊣ → -/

/-- The adjunction isomorphism in one direction:
From a proof of A ∧ B ⊢ C derive a proof of A ⊢ B → C.
This is exactly currying. -/
def adjunctionFwd {Γ : Context} {A B C : Formula}
    (p : ProofTree ((.and A B) :: Γ) C) : ProofTree (A :: B :: Γ) C :=
  p.weaken (λ h => match h with
    | .head _ => .andI (.hyp (.head _)) (.hyp (.head _))
    | .tail _ h' => .tail _ (.tail _ h'))

/-- The adjunction isomorphism in the other direction:
From a proof of A ⊢ B → C derive a proof of A ∧ B ⊢ C. -/
def adjunctionBwd {Γ : Context} {A B C : Formula}
    (p : ProofTree (A :: B :: Γ) C) : ProofTree ((.and A B) :: Γ) C :=
  p.weaken (λ h => match h with
    | .head _ => .andEl (.hyp (.head _))
    | .tail _ (.head _) => .andEr (.hyp (.head _))
    | .tail _ (.tail _ h') => h')

/-- The full adjunction: A → (B → C) is equivalent to (A ∧ B) → C.
Demonstrated in both directions as concrete proof transforms. -/
def adjunctionCurry {Γ : Context} {A B C : Formula}
    : ProofTree Γ (.impl (.impl A (.impl B C)) (.impl (.and A B) C)) :=
  .implI (uncurry (.hyp (.head _)))

def adjunctionUncurry {Γ : Context} {A B C : Formula}
    : ProofTree Γ (.impl (.impl (.and A B) C) (.impl A (.impl B C))) :=
  .implI (curry (.hyp (.head _)))

/-! ## Composition (Internal Hom) -/

/-- Composition in the exponential: (B → C) → ((A → B) → (A → C)).
This is the internal composition morphism. -/
def compose {Γ : Context} {A B C : Formula}
    : ProofTree Γ (.impl (.impl B C) (.impl (.impl A B) (.impl A C))) :=
  .implI (.implI (.implI (.implE (.hyp (.tail _ (.tail _ (.head _))))
    (.implE (.hyp (.tail _ (.head _))) (.hyp (.head _))))))

/-- Identity morphism as an arrow: A → A. -/
def identArrow {Γ : Context} {A : Formula}
    : ProofTree Γ (.impl A A) :=
  identityProof A

/-! ## Functoriality -/

/-- The implication functor is contravariant in the first argument:
(B → C) → ((A → B) → (A → C)). Component of the internal hom. -/
def precomp {Γ : Context} {A B C : Formula}
    : ProofTree Γ (.impl (.impl B C) (.impl (.impl A B) (.impl A C))) := compose

/-- Post-composition: (A → B) → ((B → C) → (A → C)). -/
def postcomp {Γ : Context} {A B C : Formula}
    : ProofTree Γ (.impl (.impl A B) (.impl (.impl B C) (.impl A C))) :=
  .implI (.implI (.implI (.implE (.hyp (.tail _ (.head _)))
    (.implE (.hyp (.tail _ (.tail _ (.head _)))) (.hyp (.head _))))))

/-! ## Evaluation Examples -/

def expA : Formula := .atom 0
def expB : Formula := .atom 1
def expC : Formula := .atom 2

-- Curry a simple proof
def expCurryExample : ProofTree [] (.impl expA (.impl expB (.and expA expB))) :=
  curry (.implI (.hyp (.head _)))

-- Uncurried version: A ∧ B → A ∧ B
def expUncurryId : ProofTree [] (.impl (.and expA expB) (.and expA expB)) :=
  identArrow (.and expA expB)

-- Compose: (A → B) → (B → C) → (A → C) — hypothetical syllogism
def expSyllogism : ProofTree []
    (.impl (.impl expA expB) (.impl (.impl expB expC) (.impl expA expC))) :=
  postcomp

#eval expCurryExample.size
#eval expCurryExample.isValid
#eval compose.size
#eval postcomp.size
#eval evalMap.size
#eval expSyllogism.size

end MiniProofKernel
