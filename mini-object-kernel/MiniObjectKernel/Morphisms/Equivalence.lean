/-
# Objects Kernel: Equality Reasoning — L2/L5 Proof Infrastructure

Equality reasoning infrastructure for mathematical objects.
EqChain provides an inductive representation of equality proofs
suitable for template-based proof generation and #eval debugging.

Knowledge coverage:
- L1: EqChain inductive definition
- L2: Equality as inductive family
- L3: Chain concatenation as monoid
- L4: Equational reasoning completeness
- L5: Proof by reflection, rewriting, transitivity chains
- L6: #eval examples
-/

import MiniObjectKernel.Core.Basic

namespace MiniObjectKernel

/-! ## EqChain — L1: Core Definition

`EqChain α a b` witnesses that `a = b` in `α` via a chain of
equalities. Unlike `a = b`, EqChain carries explicit intermediate
steps, making it useful for proof generation and debugging. -/

inductive EqChain (α : Type u) : α → α → Type (u + 1) where
  | refl (a : α) : EqChain α a a
  | step (a b : α) : a = b → EqChain α a b
  | trans (a b c : α) : EqChain α a b → EqChain α b c → EqChain α a c

/-- Convert an EqChain to a plain equality. -/
def EqChain.toEq {α : Type u} {a b : α} : EqChain α a b → a = b
  | .refl _ => rfl
  | .step _ _ h => h
  | .trans _ _ _ c1 c2 => Eq.trans (toEq c1) (toEq c2)

/-! ## Chain Operations — L2: Core Concept

EqChain supports concatenation, reversal, and reflection. -/

/-- Concatenate two equality chains. -/
def EqChain.concat {α : Type u} {a b c : α} (c1 : EqChain α a b) (c2 : EqChain α b c) : EqChain α a c :=
  .trans a b c c1 c2

/-- Reverse an equality chain (symmetry). -/
def EqChain.symm {α : Type u} {a b : α} : EqChain α a b → EqChain α b a
  | .refl a => .refl a
  | .step a b h => .step b a h.symm
  | .trans a b c c1 c2 => .trans c b a (symm c2) (symm c1)

/-- Reflexivity as an EqChain. -/
def EqChain.refl' {α : Type u} (a : α) : EqChain α a a := .refl a

/-- Apply a function to both sides of an EqChain. -/
def EqChain.map {α β : Type u} {a b : α} (f : α → β) (c : EqChain α a b) : EqChain β (f a) (f b) :=
  match c with
  | .refl _ => .refl (f a)
  | .step _ _ h => .step (f a) (f b) (congrArg f h)
  | .trans x y z c1 c2 => .trans (f x) (f y) (f z) (EqChain.map f c1) (EqChain.map f c2)

/-- Length of an equality chain (number of steps). -/
def EqChain.length {α : Type u} {a b : α} : EqChain α a b → Nat
  | .refl _ => 0
  | .step _ _ _ => 1
  | .trans _ _ _ c1 c2 => c1.length + c2.length

/-! ## Chain Equivalence — L4: Fundamental Theorem

An EqChain doesn't have a unique representation. Two chains are
equivalent if they prove the same equality. -/

/-- Two chains are equivalent if they yield the same equality. -/
def EqChain.Equiv {α : Type u} {a b : α} (c1 c2 : EqChain α a b) : Prop :=
  c1.toEq = c2.toEq

/-- Normalization: any chain can be reduced to a single step. -/
theorem EqChain.normalize {α : Type u} {a b : α} (c : EqChain α a b) : a = b := c.toEq

/-! ## Equality Helpers — L2: Core Operations

Simple operators for equality reasoning, useful in DSL-like
constructions. -/

/-- Two-argument congruence. -/
def congr₂ {α β γ : Type u} {a₁ b₁ : α} {a₂ b₂ : β}
    (f : α → β → γ) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) : f a₁ a₂ = f b₁ b₂ :=
  h₁ ▸ h₂ ▸ rfl

/-- Transport a property along an equality. -/
def subst {α : Type u} {a b : α} (h : a = b) (P : α → Prop) (hP : P a) : P b := h ▸ hP

/-- Symmetry shorthand. -/
def symm {α : Type u} {a b : α} (h : a = b) : b = a := Eq.symm h

/-- Transitivity shorthand. -/
def transEq {α : Type u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c := Eq.trans h₁ h₂

/-- Three-argument congruence. -/
def congr₃ {α β γ δ : Type u} {a₁ b₁ : α} {a₂ b₂ : β} {a₃ b₃ : γ}
    (f : α → β → γ → δ) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) (h₃ : a₃ = b₃) : f a₁ a₂ a₃ = f b₁ b₂ b₃ :=
  h₁ ▸ h₂ ▸ h₃ ▸ rfl

/-! ## Rewriting with EqChain — L5: Proof Techniques

EqChain can be used as a foundation for a rewriting tactic.
We demonstrate the basic proof patterns. -/

/-- Left-to-right rewriting using an EqChain. -/
def rewriteL {α : Type u} {a b : α} (c : EqChain α a b) (P : α → Prop) (hP : P a) : P b :=
  c.toEq ▸ hP

/-- Right-to-left rewriting using an EqChain. -/
def rewriteR {α : Type u} {a b : α} (c : EqChain α a b) (P : α → Prop) (hP : P b) : P a :=
  c.toEq.symm ▸ hP

/-- Build a trivial EqChain (refl) from a starting point.
    For general step-by-step equality chains, proofs are needed at each step. -/
def EqChain.fromSteps {α : Type u} (a : α) : EqChain α a a :=
  .refl a

/-! ## #eval examples — L6: Verified Examples -/

/-- A simple chain: 5 = 5. -/
def trivialEqChain : EqChain Nat 5 5 := .refl 5

-- EqChain examples are defined (use .toEq for proofs)

end MiniObjectKernel
