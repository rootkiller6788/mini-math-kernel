/-
# Proof Kernel: Proof Trees

Core proof representation — natural deduction proof trees
indexed by context and conclusion formula.
-/

import MiniLogicKernel.Core.Basic

open MiniLogicKernel

namespace MiniProofKernel

/-! ## Context -/

abbrev Context := List Formula

instance : Membership Formula Context where
  mem A Γ := List.Mem A Γ

def Context.headMem {A : Formula} {Γ : Context} : A ∈ (A :: Γ) := .head _
def Context.tailMem {A B : Formula} {Γ : Context} (h : A ∈ Γ) : A ∈ (B :: Γ) := .tail _ h
def Context.Subset (Γ Δ : Context) : Prop := ∀ {A : Formula}, A ∈ Γ → A ∈ Δ

def Context.consSubset {Γ Δ : Context} {A : Formula} (hsub : Γ.Subset Δ) :
    (A :: Γ).Subset (A :: Δ)
  | _, .head _ => .head _
  | _, .tail _ h => .tail _ (hsub h)

def Context.subsetRefl (Γ : Context) : Γ.Subset Γ := fun _ h => h
def Context.subsetCons {Γ : Context} {A : Formula} : Γ.Subset (A :: Γ) :=
  fun _ h => .tail _ h

/-! ## Proof Tree -/

inductive ProofTree : Context → Formula → Type where
  | hyp  (h : A ∈ Γ) : ProofTree Γ A
  | trueI : ProofTree Γ .true
  | falseE (p : ProofTree Γ .false) : ProofTree Γ A
  | andI  (p : ProofTree Γ A) (q : ProofTree Γ B) : ProofTree Γ (.and A B)
  | andEl (p : ProofTree Γ (.and A B)) : ProofTree Γ A
  | andEr (p : ProofTree Γ (.and A B)) : ProofTree Γ B
  | orIl  (p : ProofTree Γ A) : ProofTree Γ (.or A B)
  | orIr  (p : ProofTree Γ B) : ProofTree Γ (.or A B)
  | orE   (p : ProofTree Γ (.or A B))
          (q : ProofTree (A :: Γ) C)
          (r : ProofTree (B :: Γ) C) : ProofTree Γ C
  | implI (p : ProofTree (A :: Γ) B) : ProofTree Γ (.impl A B)
  | implE (p : ProofTree Γ (.impl A B)) (q : ProofTree Γ A) : ProofTree Γ B
  | notI  (p : ProofTree (A :: Γ) .false) : ProofTree Γ (.not A)
  | notE  (p : ProofTree Γ (.not A)) (q : ProofTree Γ A) : ProofTree Γ .false
  | equivI (p : ProofTree Γ (.impl A B)) (q : ProofTree Γ (.impl B A)) : ProofTree Γ (.equiv A B)
  | equivEl (p : ProofTree Γ (.equiv A B)) : ProofTree Γ (.impl A B)
  | equivEr (p : ProofTree Γ (.equiv A B)) : ProofTree Γ (.impl B A)
  | lem : ProofTree Γ (.or A (.not A))
  deriving Repr

/-! ## Structural Rules -/

def ProofTree.weaken {Γ Δ : Context} {A : Formula}
    (p : ProofTree Γ A) (hsub : Context.Subset Γ Δ) : ProofTree Δ A :=
  match p with
  | .hyp h => .hyp (hsub h)
  | .trueI => .trueI
  | .falseE p' => .falseE (weaken p' hsub)
  | .andI p' q => .andI (weaken p' hsub) (weaken q hsub)
  | .andEl p' => .andEl (weaken p' hsub)
  | .andEr p' => .andEr (weaken p' hsub)
  | .orIl p' => .orIl (weaken p' hsub)
  | .orIr p' => .orIr (weaken p' hsub)
  | .orE p' q r =>
      .orE (weaken p' hsub)
        (weaken q (Context.consSubset hsub))
        (weaken r (Context.consSubset hsub))
  | .implI p' => .implI (weaken p' (Context.consSubset hsub))
  | .implE p' q => .implE (weaken p' hsub) (weaken q hsub)
  | .notI p' => .notI (weaken p' (Context.consSubset hsub))
  | .notE p' q => .notE (weaken p' hsub) (weaken q hsub)
  | .equivI p' q => .equivI (weaken p' hsub) (weaken q hsub)
  | .equivEl p' => .equivEl (weaken p' hsub)
  | .equivEr p' => .equivEr (weaken p' hsub)
  | .lem => .lem

def ProofTree.weakenCons {Γ : Context} {A B : Formula}
    (p : ProofTree Γ B) : ProofTree (A :: Γ) B :=
  p.weaken Context.subsetCons

def ProofTree.conclusion {Γ : Context} {A : Formula} (_ : ProofTree Γ A) : Formula := A
def ProofTree.context {Γ : Context} {A : Formula} (_ : ProofTree Γ A) : Context := Γ

def ProofTree.size {Γ : Context} {A : Formula} : ProofTree Γ A → Nat
  | .hyp _ => 1
  | .trueI => 1
  | .falseE p => 1 + size p
  | .andI p q => 1 + size p + size q
  | .andEl p => 1 + size p
  | .andEr p => 1 + size p
  | .orIl p => 1 + size p
  | .orIr p => 1 + size p
  | .orE p q r => 1 + size p + size q + size r
  | .implI p => 1 + size p
  | .implE p q => 1 + size p + size q
  | .notI p => 1 + size p
  | .notE p q => 1 + size p + size q
  | .equivI p q => 1 + size p + size q
  | .equivEl p => 1 + size p
  | .equivEr p => 1 + size p
  | .lem => 1

def ProofTree.isValid {Γ : Context} {A : Formula} (_ : ProofTree Γ A) : Bool := true

end MiniProofKernel
