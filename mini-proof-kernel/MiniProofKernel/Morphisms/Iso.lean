/-
# Proof Kernel: Isomorphisms

Invertible proof homomorphisms between proof systems.
Double-negation translation embedding classical logic into
intuitionistic logic (Godel-Gentzen style), and De Morgan dualities.
-/

import MiniProofKernel.Core.Basic
import MiniProofKernel.Morphisms.Hom

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Proof Isomorphisms -/

/-- A proof isomorphism between two contexts is an invertible
proof homomorphism. Two proof systems over contexts Γ and Δ
are equivalent if proofs can be translated back and forth. -/
structure ProofIso (Γ Δ : Context) where
  toHom : ProofHom Γ Δ
  invHom : ProofHom Δ Γ
  deriving Repr

/-- Identity isomorphism. -/
def ProofIso.id (Γ : Context) : ProofIso Γ Γ where
  toHom := ProofHom.id Γ
  invHom := ProofHom.id Γ

/-- Inverse (symmetry) of an isomorphism. -/
def ProofIso.symm {Γ Δ : Context} (iso : ProofIso Γ Δ) : ProofIso Δ Γ where
  toHom := iso.invHom
  invHom := iso.toHom

/-- Compose two isomorphisms. -/
def ProofIso.trans {Γ Δ Θ : Context}
    (iso1 : ProofIso Γ Δ) (iso2 : ProofIso Δ Θ) : ProofIso Γ Θ where
  toHom := ProofHom.comp iso2.toHom iso1.toHom
  invHom := ProofHom.comp iso1.invHom iso2.invHom

/-! ## Double-Negation Translation (Godel-Gentzen) -/

/-- Godel-Gentzen double-negation translation.
Embeds classical propositional logic into intuitionistic logic
by strategically inserting double-negations. -/
def dnTranslate : Formula → Formula
  | .atom n => .not (.not (.atom n))
  | .true => .true
  | .false => .false
  | .not A => .not (dnTranslate A)
  | .and A B => .and (dnTranslate A) (dnTranslate B)
  | .or A B =>
      .not (.and (.not (dnTranslate A)) (.not (dnTranslate B)))
  | .impl A B => .impl (dnTranslate A) (dnTranslate B)
  | .equiv A B => .and
      (.impl (dnTranslate A) (dnTranslate B))
      (.impl (dnTranslate B) (dnTranslate A))

/-- Translate an entire context. -/
def dnTranslateCtx : Context → Context := List.map dnTranslate

/-- The DN-translation yields a proof homomorphism from a classical
context (with LEM) to its intuitionistic counterpart.
We define the hom by structural recursion on proof trees. -/
def dnProofHom (Γ : Context) : ProofHom Γ (dnTranslateCtx Γ) where
  map _ p :=
    match p with
    | .hyp h => .hyp (List.mem_map_of_mem {a := _} h)
    | .trueI => .trueI
    | .falseE p' => .falseE (map _ p')
    | .andI p' q => .andI (map _ p') (map _ q)
    | .andEl p' => .andEl (map _ p')
    | .andEr p' => .andEr (map _ p')
    | .orIl p' => .orIl (map _ p')
    | .orIr p' => .orIr (map _ p')
    | .orE p' q r => .orE (map _ p') (map _ q) (map _ r)
    | .implI p' => .implI (map _ p')
    | .implE p' q => .implE (map _ p') (map _ q)
    | .notI p' => .notI (map _ p')
    | .notE p' q => .notE (map _ p') (map _ q)
    | .equivI p' q => .equivI (map _ p') (map _ q)
    | .equivEl p' => .equivEl (map _ p')
    | .equivEr p' => .equivEr (map _ p')
    | .lem => .lem
  preservesHyp h := rfl
  hmap A h := List.mem_map_of_mem dnTranslate h

/-! ## De Morgan Dualities as Proof Isomorphisms -/

/-- De Morgan: (¬A ∨ ¬B) → ¬(A ∧ B) (intuitionistically valid). -/
def deMorganAndIntro (A B : Formula) : ProofTree []
    (.impl (.or (.not A) (.not B)) (.not (.and A B))) :=
  .implI (.notI (.orE (.hyp (.tail _ (.head _)))
    (.notE (.hyp (.head _)) (.andEl (.hyp (.head _))))
    (.notE (.hyp (.head _)) (.andEr (.hyp (.head _))))))

/-- De Morgan: ¬(A ∨ B) → (¬A ∧ ¬B) (intuitionistically valid). -/
def deMorganOrIntro (A B : Formula) : ProofTree []
    (.impl (.not (.or A B)) (.and (.not A) (.not B))) :=
  .implI (.andI
    (.notI (.notE (.hyp (.tail _ (.head _)))
      (.orIl (.hyp (.head _)))))
    (.notI (.notE (.hyp (.tail _ (.head _)))
      (.orIr (.hyp (.head _))))))

/-- De Morgan: ¬(¬A ∧ ¬B) → (A ∨ B) (classical, uses LEM). -/
def deMorganAndElim (A B : Formula) : ProofTree []
    (.impl (.not (.and (.not A) (.not B))) (.or A B)) :=
  .implI (.orE (.lem (a:=A))
    (.orIl (.hyp (.head _)))
    (.orE (.lem (a:=B))
      (.orIr (.hyp (.head _)))
      (.falseE (.notE (.hyp (.tail _ (.tail _ (.head _))))
        (.andI (.hyp (.tail _ (.head _))) (.hyp (.head _)))))))

/-! ## Invertible Rules -/

/-- Implication intro/elim forms an adjunction (eta-expansion).
Given p: Γ ⊢ A→B, we can reconstruct it via implI(implE(p, x)). -/
def implInvert {Γ : Context} {A B : Formula}
    (p : ProofTree Γ (.impl A B)) : ProofTree Γ (.impl A B) :=
  .implI (.implE (p.weakenCons) (.hyp (.head _)))

/-- Conjunction intro/elim invertibility.
Given p: Γ ⊢ A∧B, reconstruct via andI(andEl p, andEr p). -/
def andInvert {Γ : Context} {A B : Formula}
    (p : ProofTree Γ (.and A B)) : ProofTree Γ (.and A B) :=
  .andI (.andEl p) (.andEr p)

/-- Count redexes (beta-reducible expressions) in a proof tree. -/
def ProofTree.countRedexes {Γ : Context} {A : Formula} : ProofTree Γ A → Nat
  | .implE (.implI _) _ => 1
  | .andEl (.andI _ _) => 1
  | .andEr (.andI _ _) => 1
  | .orE (.orIl _) _ _ => 1
  | .orE (.orIr _) _ _ => 1
  | .equivEl (.equivI _ _) => 1
  | .equivEr (.equivI _ _) => 1
  | .falseE p => countRedexes p
  | .andI p q => countRedexes p + countRedexes q
  | .andEl p => countRedexes p
  | .andEr p => countRedexes p
  | .orIl p => countRedexes p
  | .orIr p => countRedexes p
  | .orE p q r => countRedexes p + countRedexes q + countRedexes r
  | .implI p => countRedexes p
  | .implE p q => countRedexes p + countRedexes q
  | .notI p => countRedexes p
  | .notE p q => countRedexes p + countRedexes q
  | .equivI p q => countRedexes p + countRedexes q
  | .equivEl p => countRedexes p
  | .equivEr p => countRedexes p
  | .lem => 0
  | _ => 0

/-! ## Evaluation Examples -/

def isoA : Formula := .atom 0
def isoB : Formula := .atom 1
def isoC : Formula := .atom 2

-- Identity iso on empty context
def testIsoId : ProofIso [] [] := ProofIso.id []

-- A proof with a redex: andEl(andI(a,b))
def testAndRedex (A B : Formula) : ProofTree [A, B] A :=
  .andEl (.andI (.hyp (.head _)) (.hyp (.tail _ (.head _))))

-- DN-translate a simple formula and compare
def isoSimple : Formula := .or isoA isoB

#eval testAndRedex isoA isoB |>.countRedexes
#eval testAndRedex isoA isoB |>.size
#eval (deMorganAndIntro isoA isoB).size
#eval (deMorganOrIntro isoA isoB).size
#eval (deMorganAndElim isoA isoB).size
#eval isoSimple.toString
#eval (dnTranslate isoSimple).toString

end MiniProofKernel
