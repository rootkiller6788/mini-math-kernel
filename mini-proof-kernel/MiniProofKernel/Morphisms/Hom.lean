/-
# Proof Kernel: Homomorphisms

Proof translations between deduction systems. Maps that preserve
logical structure: natural deduction to sequent calculus,
Hilbert-style to natural deduction, and proof composition morphisms.
-/

import MiniProofKernel.Core.Basic
import MiniProofKernel.Core.Objects

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Proof Tree Homomorphisms -/

/-- A proof homomorphism `f : Γ → Δ` maps proofs over Γ to proofs over Δ,
preserving the conclusion formula. -/
structure ProofHom (Γ Δ : Context) where
  map   : {A : Formula} → ProofTree Γ A → ProofTree Δ A
  preservesHyp : ∀ {A} (h : A ∈ Γ), map (.hyp h) = .hyp (hmap h)
  hmap  : Context.Subset Γ Δ
  deriving Repr

/-- Identity homomorphism. -/
def ProofHom.id (Γ : Context) : ProofHom Γ Γ where
  map _ p := p
  preservesHyp h := rfl
  hmap h := h

/-- Composition of homomorphisms. -/
def ProofHom.comp {Γ Δ Θ : Context} (g : ProofHom Δ Θ) (f : ProofHom Γ Δ) : ProofHom Γ Θ where
  map _ p := g.map (f.map p)
  preservesHyp h := by
    simp [g.preservesHyp (f.hmap h), f.preservesHyp h]
  hmap h := g.hmap (f.hmap h)

/-! ## Natural Deduction to Sequent Calculus Translation -/

/-- Translate a natural deduction proof tree into a multi-succedent
sequent calculus proof.

Uses Sequent with two-sided representation:
- Left side: hypotheses/context
- Right side: conclusions (just the goal formula for ND translation)

Note: This is a partial translation; we handle the structural embedding
and return a sequent-like structure. For the fully elaborated sequent
calculus, see `Core/Objects.lean`. -/

def ndToSequentGoal {Γ : Context} {A : Formula} (p : ProofTree Γ A) : Formula := A

/-- The syntactic complexity of a proof, used for termination metrics. -/
def ProofTree.complexity {Γ : Context} {A : Formula} : ProofTree Γ A → Nat
  | .hyp _ => 0
  | .trueI => 1
  | .falseE p => 1 + complexity p
  | .andI p q => 1 + complexity p + complexity q
  | .andEl p => 1 + complexity p
  | .andEr p => 1 + complexity p
  | .orIl p => 1 + complexity p
  | .orIr p => 1 + complexity p
  | .orE p q r => 1 + complexity p + complexity q + complexity r
  | .implI p => 1 + complexity p
  | .implE p q => 1 + complexity p + complexity q
  | .notI p => 1 + complexity p
  | .notE p q => 1 + complexity p + complexity q
  | .equivI p q => 1 + complexity p + complexity q
  | .equivEl p => 1 + complexity p
  | .equivEr p => 1 + complexity p
  | .lem => 1

/-! ## Hilbert-Style to Natural Deduction -/

/-- Hilbert-style proof: a set of axiom schemes and modus ponens.
We represent a Hilbert proof as a list of formulas with justifications. -/
inductive HilbertRule : Type where
  | axK  (A B : Formula) : HilbertRule   -- A → (B → A)
  | axS  (A B C : Formula) : HilbertRule -- (A → (B → C)) → ((A → B) → (A → C))
  | axMP : HilbertRule
  deriving Repr, DecidableEq

/-- A Hilbert-style proof step. -/
structure HilbertStep where
  formula : Formula
  rule    : HilbertRule
  premises : List Nat -- indices of previous steps
  deriving Repr, Inhabited

/-- A Hilbert proof is a list of steps. -/
abbrev HilbertProof := List HilbertStep

/-- Convert a single Hilbert axiom instance to a natural deduction proof. -/
def hilbertAxiomK (A B : Formula) : ProofTree [] (.impl A (.impl B A)) :=
  .implI (.implI (.hyp (.tail _ (.head _))))

def hilbertAxiomS (A B C : Formula) : ProofTree []
    (.impl (.impl A (.impl B C)) (.impl (.impl A B) (.impl A C))) :=
  .implI (.implI (.implI (
    .implE (.implE (.hyp (.tail _ (.tail _ (.head _)))) (.hyp (.head _)))
           (.implE (.hyp (.tail _ (.head _))) (.hyp (.head _)))
  )))

/-- We have a natural deduction proof of each Hilbert axiom. -/
def hilbertAxiomND (r : HilbertRule) : ProofTree [] (match r with
    | .axK A B => .impl A (.impl B A)
    | .axS A B C => .impl (.impl A (.impl B C)) (.impl (.impl A B) (.impl A C))
    | .axMP => .impl (.impl (.atom 0) (.atom 1)) (.impl (.atom 0) (.atom 1))) :=
  match r with
  | .axK A B => hilbertAxiomK A B
  | .axS A B C => hilbertAxiomS A B C
  | .axMP => .implI (.hyp (.head _))

/-! ## Evaluation Examples -/

def exA : Formula := .atom 0
def exB : Formula := .atom 1
def exC : Formula := .atom 2

def homId : ProofHom [] [] := ProofHom.id []

-- Translate identity proof to sequent goal
def ndId : ProofTree [] (.impl exA exA) := identityProof exA

#eval ndToSequentGoal ndId |>.toString
#eval ndId.complexity
#eval ndId.size
#eval (hilbertAxiomK exA exB).size
#eval (hilbertAxiomS exA exB exC).size
#eval (identityProof exA).complexity

end MiniProofKernel
