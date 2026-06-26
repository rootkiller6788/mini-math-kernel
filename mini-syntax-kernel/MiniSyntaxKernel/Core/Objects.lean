/-
# Syntax Kernel: Term Analysis

Operations for analyzing terms: free variables, size, binding depth.
-/

import MiniSyntaxKernel.Core.Basic

namespace MiniSyntaxKernel

open Term

/-! ## Free Variables -/

def freeVars (t : Term) : List Variable :=
  go t []
where
  go : Term → List Variable → List Variable
    | .var v, acc => v :: acc
    | .app f a, acc => go f (go a acc)
    | .lam v body, acc => go body acc |>.filter (· != v)
    | .pi v dom cod, acc => go dom (go cod acc |>.filter (· != v))
    | .sort _, acc => acc
    | .lit _, acc => acc
    | .letE v t b, acc => go t (go b acc |>.filter (· != v))

def isClosed (t : Term) : Bool :=
  freeVars t |>.isEmpty

/-! ## Bound Variables -/

def maxBoundIndex (t : Term) : Nat :=
  go t 0
where
  go : Term → Nat → Nat
    | .var v, acc =>
      match v.index with
      | some n => max acc n
      | none => acc
    | .app f a, acc => go f (go a acc)
    | .lam _ body, acc => go body acc
    | .pi _ dom cod, acc => go dom (go cod acc)
    | .sort _, acc => acc
    | .lit _, acc => acc
    | .letE _ t b, acc => go t (go b acc)

/-! ## Size and Complexity -/

def size (t : Term) : Nat :=
  match t with
  | .var _ => 1
  | .app f a => 1 + size f + size a
  | .lam _ body => 1 + size body
  | .pi _ dom cod => 1 + size dom + size cod
  | .sort _ => 1
  | .lit _ => 1
  | .letE _ t b => 1 + size t + size b

def binderDepth (t : Term) : Nat :=
  match t with
  | .var _ => 0
  | .app f a => max (binderDepth f) (binderDepth a)
  | .lam _ body => 1 + binderDepth body
  | .pi _ dom cod => 1 + max (binderDepth dom) (binderDepth cod)
  | .sort _ => 0
  | .lit _ => 0
  | .letE _ _ b => 1 + binderDepth b

/-! ## Term Kind Classification -/

/-- The kind (head constructor) of a term. -/
inductive TermKind where
  | varKind | appKind | lamKind | piKind | sortKind | litKind | letKind
deriving BEq, Repr, DecidableEq

/-- The head constructor kind of a term. -/
def termKind (t : Term) : TermKind :=
  match t with
  | .var _ => .varKind
  | .app _ _ => .appKind
  | .lam _ _ => .lamKind
  | .pi _ _ _ => .piKind
  | .sort _ => .sortKind
  | .lit _ => .litKind
  | .letE _ _ _ => .letKind

/-- Predicate: is the term a variable? -/
def isVar (t : Term) : Bool :=
  match t with | .var _ => true | _ => false

/-- Predicate: is the term an application? -/
def isApp (t : Term) : Bool :=
  match t with | .app _ _ => true | _ => false

/-- Predicate: is the term a lambda abstraction? -/
def isLam (t : Term) : Bool :=
  match t with | .lam _ _ => true | _ => false

/-- Predicate: is the term a Pi type? -/
def isPi (t : Term) : Bool :=
  match t with | .pi _ _ _ => true | _ => false

/-- Predicate: is the term a sort? -/
def isSort (t : Term) : Bool :=
  match t with | .sort _ => true | _ => false

/-- Predicate: is the term a literal? -/
def isLit (t : Term) : Bool :=
  match t with | .lit _ => true | _ => false

/-- Predicate: is the term a let-expression? -/
def isLetE (t : Term) : Bool :=
  match t with | .letE _ _ _ => true | _ => false

end MiniSyntaxKernel
