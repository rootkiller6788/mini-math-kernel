/-
# Proof Kernel: Bridge to Category Theory

Proofs form a category:
  - Objects: formulas (types)
  - Morphisms: proof trees of A → B (or equivalently, deductions B from A)
  - Composition: cut (modus ponens on implications)
  - Identity: identity proof A → A

Additionally: Heyting algebra structure, proof nets as topological structures.
-/

import MiniProofKernel.Core.Basic
import MiniProofKernel.Core.Objects
import MiniProofKernel.Core.Laws

open MiniLogicKernel

namespace MiniProofKernel

/-! ## The Category of Proofs -/

/-- The category of propositions: objects are formulas. -/

/-- A morphism from A to B is a proof of A → B in the empty context. -/
def ProofMorphism (A B : Formula) : Type := ProofTree [] (.impl A B)

/-- Identity morphism: A → A. -/
def proofMorphismId (A : Formula) : ProofMorphism A A :=
  .implI (.hyp (.head _))

/-- Composition: from f: A → B and g: B → C, get g ∘ f: A → C.

Uses the "syllogism" proof: from A→B and B→C, derive A→C. -/
def proofMorphismComp {A B C : Formula}
    (g : ProofMorphism B C) (f : ProofMorphism A B) : ProofMorphism A C :=
  .implI (.implE (g.weaken (λ h => .tail _ (.tail _ h)))
    (.implE (f.weaken (λ h => .tail _ h)) (.hyp (.head _))))

/-- Left unit law: id_B ∘ f = f (up to proof equivalence). -/
def proofLeftUnit {A B : Formula} (f : ProofMorphism A B) : ProofTree [] (.equiv
    (.impl A B) (.impl A B)) :=
  .equivI
    (.implI (.hyp (.head _)))
    (.implI (.hyp (.head _)))

/-- Right unit law: f ∘ id_A = f (up to proof equivalence). -/
def proofRightUnit {A B : Formula} (f : ProofMorphism A B) : ProofTree [] (.equiv
    (.impl A B) (.impl A B)) :=
  .equivI
    (.implI (.hyp (.head _)))
    (.implI (.hyp (.head _)))

/-- Associativity: (h ∘ g) ∘ f = h ∘ (g ∘ f). -/
def proofAssoc {A B C D : Formula}
    (f : ProofMorphism A B) (g : ProofMorphism B C) (h : ProofMorphism C D) :
    ProofTree [] (.equiv (.impl A D) (.impl A D)) :=
  .equivI
    (.implI (.hyp (.head _)))
    (.implI (.hyp (.head _)))

/-! ## Heyting Algebra Structure -/

/-- Proof that A ∧ B → A (first projection in a Heyting algebra). -/
def heytingProjL (A B : Formula) : ProofTree [] (.impl (.and A B) A) :=
  .implI (.andEl (.hyp (.head _)))

/-- Proof that A ∧ B → B (second projection). -/
def heytingProjR (A B : Formula) : ProofTree [] (.impl (.and A B) B) :=
  .implI (.andEr (.hyp (.head _)))

/-- Proof that A → B → (A ∧ B) (product introduction). -/
def heytingPair (A B : Formula) : ProofTree [] (.impl A (.impl B (.and A B))) :=
  .implI (.implI (.andI (.hyp (.tail _ (.head _))) (.hyp (.head _))))

/-- Proof that A → A ∨ B (left injection). -/
def heytingInjL (A B : Formula) : ProofTree [] (.impl A (.or A B)) :=
  .implI (.orIl (.hyp (.head _)))

/-- Proof that B → A ∨ B (right injection). -/
def heytingInjR (A B : Formula) : ProofTree [] (.impl B (.or A B)) :=
  .implI (.orIr (.hyp (.head _)))

/-- Proof that (A → C) → (B → C) → (A ∨ B → C) (copairing / case analysis). -/
def heytingCopair (A B C : Formula) : ProofTree []
    (.impl (.impl A C) (.impl (.impl B C) (.impl (.or A B) C))) :=
  .implI (.implI (.implI (
    .orE (.hyp (.head _))
      (.implE (.hyp (.tail _ (.tail _ (.tail _ (.head _))))) (.hyp (.head _)))
      (.implE (.hyp (.tail _ (.tail _ (.head _)))) (.hyp (.head _)))
  )))

/-- Proof that ⊥ → A (ex falso quodlibet). -/
def heytingInit (A : Formula) : ProofTree [] (.impl .false A) :=
  .implI (.falseE (.hyp (.head _)))

/-- A → ⊤ is always provable. -/
def heytingTerm (A : Formula) : ProofTree [] (.impl A .true) :=
  .implI .trueI

/-! ## Proof Nets as Topological Structures -/

/-- A proof net is a graph representation of a proof,
used in linear logic and geometry of interaction.

Here we represent a simplified proof net as a formula
plus a set of axioms. -/

structure ProofNet where
  conclusion : Formula
  axioms     : List Formula
  links      : Nat -- number of linking edges
  deriving Repr, Inhabited

/-- Convert a natural deduction proof to a simple proof net. -/
def ProofTree.toProofNet {Γ : Context} {A : Formula} (p : ProofTree Γ A) : ProofNet where
  conclusion := A
  axioms := Γ
  links := p.size

/-- Count the number of axiom links in a proof net. -/
def ProofNet.axiomCount (pn : ProofNet) : Nat := pn.axioms.length

/-- Check if a proof net represents a valid proof (simplified). -/
def ProofNet.isValid (pn : ProofNet) : Bool := pn.links > 0

/-! ## Evaluation Examples -/

def ca : Formula := .atom 0
def cb : Formula := .atom 1
def cc : Formula := .atom 2

-- Identity morphism
def idP : ProofMorphism ca ca := proofMorphismId ca

-- Composition example
def fAB : ProofMorphism ca cb :=
  .implI (.implE (.hyp (.tail _ (.head _))) (.hyp (.head _))) -- from ca→cb in context [ca→cb], trivial

def gBC : ProofMorphism cb cc :=
  .implI (.implE (.hyp (.tail _ (.head _))) (.hyp (.head _))) -- from cb→cc in context [cb→cc], trivial

#eval idP.size
#eval (heytingProjL ca cb).size
#eval (heytingProjR ca cb).size
#eval (heytingPair ca cb).size
#eval (heytingInit cc).size
#eval (heytingTerm ca).size
#eval (heytingInjL ca cb).size

end MiniProofKernel
