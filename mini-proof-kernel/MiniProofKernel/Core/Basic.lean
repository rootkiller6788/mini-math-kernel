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

/-- Validity check: a proof tree is valid if all hypothesis references
are within the declared context. Since the type system enforces this,
all well-typed proofs are automatically valid. We verify this property
by structural inspection. -/
def ProofTree.isValid {Γ : Context} {A : Formula} (p : ProofTree Γ A) : Bool :=
  match p with
  | .hyp h => h.rec (λ _ _ => true) (λ _ _ ih => ih)
  | .trueI => true
  | .falseE p' => p'.isValid
  | .andI p' q => p'.isValid && q.isValid
  | .andEl p' => p'.isValid
  | .andEr p' => p'.isValid
  | .orIl p' => p'.isValid
  | .orIr p' => p'.isValid
  | .orE p' q r => p'.isValid && q.isValid && r.isValid
  | .implI p' => p'.isValid
  | .implE p' q => p'.isValid && q.isValid
  | .notI p' => p'.isValid
  | .notE p' q => p'.isValid && q.isValid
  | .equivI p' q => p'.isValid && q.isValid
  | .equivEl p' => p'.isValid
  | .equivEr p' => p'.isValid
  | .lem => true

/-! ## Proof Tree Composition Utilities -/

/-- Check if a proof tree's context is empty (closed proof / theorem). -/
def ProofTree.isClosed {Γ : Context} {A : Formula} (p : ProofTree Γ A) : Bool :=
  Γ.isEmpty

/-- Collect all atom indices used in a proof tree (both contexts and conclusions). -/
def ProofTree.atoms {Γ : Context} {A : Formula} : ProofTree Γ A → List Nat
  | .hyp _ => A.atoms
  | .trueI => []
  | .falseE p => .false.atoms ++ atoms p
  | .andI p q => (.and A B).atoms ++ atoms p ++ atoms q
  | .andEl p => (.and A B).atoms ++ atoms p
  | .andEr p => (.and A B).atoms ++ atoms p
  | .orIl p => (.or A B).atoms ++ atoms p
  | .orIr p => (.or A B).atoms ++ atoms p
  | .orE p q r => (.or A B).atoms ++ atoms p ++ atoms q ++ atoms r
  | .implI p => (.impl A B).atoms ++ atoms p
  | .implE p q => (.impl A B).atoms ++ atoms p ++ atoms q
  | .notI p => (.not A).atoms ++ atoms p
  | .notE p q => (.not A).atoms ++ atoms p ++ atoms q
  | .equivI p q => (.equiv A B).atoms ++ atoms p ++ atoms q
  | .equivEl p => (.equiv A B).atoms ++ atoms p
  | .equivEr p => (.equiv A B).atoms ++ atoms p
  | .lem => (.or A (.not A)).atoms

/-- Check if a proof tree is structurally positive (no false-elimination at top). -/
def ProofTree.isPositive {Γ : Context} {A : Formula} : ProofTree Γ A → Bool
  | .hyp _ => true
  | .trueI => true
  | .falseE _ => false
  | .andI p q => p.isPositive && q.isPositive
  | .andEl p => p.isPositive
  | .andEr p => p.isPositive
  | .orIl p => p.isPositive
  | .orIr p => p.isPositive
  | .orE p q r => p.isPositive && q.isPositive && r.isPositive
  | .implI p => p.isPositive
  | .implE p q => p.isPositive && q.isPositive
  | .notI p => p.isPositive
  | .notE p q => p.isPositive && q.isPositive
  | .equivI p q => p.isPositive && q.isPositive
  | .equivEl p => p.isPositive
  | .equivEr p => p.isPositive
  | .lem => true

/-- The height of a proof tree (max depth of inference rules). -/
def ProofTree.height {Γ : Context} {A : Formula} : ProofTree Γ A → Nat
  | .hyp _ => 0
  | .trueI => 0
  | .falseE p => 1 + height p
  | .andI p q => 1 + max (height p) (height q)
  | .andEl p => 1 + height p
  | .andEr p => 1 + height p
  | .orIl p => 1 + height p
  | .orIr p => 1 + height p
  | .orE p q r => 1 + max (height p) (max (height q) (height r))
  | .implI p => 1 + height p
  | .implE p q => 1 + max (height p) (height q)
  | .notI p => 1 + height p
  | .notE p q => 1 + max (height p) (height q)
  | .equivI p q => 1 + max (height p) (height q)
  | .equivEl p => 1 + height p
  | .equivEr p => 1 + height p
  | .lem => 0

end MiniProofKernel
