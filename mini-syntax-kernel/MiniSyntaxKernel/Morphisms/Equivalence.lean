/-
# Syntax Kernel: Substitution

Explicit, capture-avoiding substitution for the kernel term language.
-/

import MiniSyntaxKernel.Core.Basic

namespace MiniSyntaxKernel

open Term

/-! ## Lifting (de Bruijn index adjustment) -/

def lift (t : Term) (cutoff d : Nat) : Term :=
  match t with
  | .var v =>
    match v.index with
    | some n =>
      if n >= cutoff then .var {v with index := some (n + d)}
      else .var v
    | none => .var v
  | .app f a => .app (lift f cutoff d) (lift a cutoff d)
  | .lam v body => .lam v (lift body (cutoff + 1) d)
  | .pi v dom cod => .pi v (lift dom cutoff d) (lift cod (cutoff + 1) d)
  | .sort _ => t
  | .lit _ => t
  | .letE v val body => .letE v (lift val cutoff d) (lift body (cutoff + 1) d)

def lift1 (t : Term) : Term := lift t 0 1

/-! ## Single-variable Substitution -/

def subst (t s : Term) (x : Variable) : Term :=
  match t with
  | .var v =>
    if v == x then s else .var v
  | .app f a => .app (subst f s x) (subst a s x)
  | .lam v body =>
    if v == x then .lam v body
    else .lam v (subst body (lift1 s) x)
  | .pi v dom cod =>
    if v == x then .pi v (subst dom s x) cod
    else .pi v (subst dom s x) (subst cod (lift1 s) x)
  | .sort _ => t
  | .lit _ => t
  | .letE v val body =>
    if v == x then .letE v (subst val s x) body
    else .letE v (subst val s x) (subst body (lift1 s) x)

/-! ## Parallel Substitution -/

def substParallel (t : Term) (σ : List (Variable × Term)) : Term :=
  match t with
  | .var v =>
    match σ.lookup v with
    | some s => s
    | none => .var v
  | .app f a => .app (substParallel f σ) (substParallel a σ)
  | .lam v body =>
    let σ' := σ.map fun (y, s) => (y, lift1 s)
    .lam v (substParallel body (σ'.filter fun (y, _) => y != v))
  | .pi v dom cod =>
    let σLifted := σ.map fun (y, s) => (y, lift1 s)
    .pi v (substParallel dom σ) (substParallel cod (σLifted.filter fun (y, _) => y != v))
  | .sort _ => t
  | .lit _ => t
  | .letE v val body =>
    let σLifted := σ.map fun (y, s) => (y, lift1 s)
    .letE v (substParallel val σ) (substParallel body (σLifted.filter fun (y, _) => y != v))
where
  lookup : List (Variable × Term) → Variable → Option Term
    | [], _ => none
    | (y, s) :: rest, x => if y == x then some s else lookup rest x

/-! ## Alpha Equivalence -/

def alphaEquiv (t₁ t₂ : Term) : Bool :=
  go 0 t₁ t₂
where
  go (depth : Nat) : Term → Term → Bool
    | .var v1, .var v2 =>
      match v1.index, v2.index with
      | some n1, some n2 => n1 == n2
      | none, none => v1.name == v2.name
      | _, _ => false
    | .app f1 a1, .app f2 a2 => go depth f1 f2 && go depth a1 a2
    | .lam _ body1, .lam _ body2 => go (depth + 1) body1 body2
    | .pi _ dom1 cod1, .pi _ dom2 cod2 => go depth dom1 dom2 && go (depth + 1) cod1 cod2
    | .sort n1, .sort n2 => n1 == n2
    | .lit n1, .lit n2 => n1 == n2
    | .letE _ v1 b1, .letE _ v2 b2 => go depth v1 v2 && go (depth + 1) b1 b2
    | _, _ => false

end MiniSyntaxKernel
