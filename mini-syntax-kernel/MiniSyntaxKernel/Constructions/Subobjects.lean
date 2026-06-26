/-
# Syntax Kernel: Constructions — Subobjects

Subterm relation and subterm-based constructions.
A subobject of a term is another term that appears as a subterm.
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects
import MiniSyntaxKernel.Core.Laws

namespace MiniSyntaxKernel

open Term

/-! ## Subterm Decision Procedure -/

/-- Decide whether `s` is a subterm of `t`. -/
def isSubterm (s t : Term) : Bool :=
  if s == t then true
  else
    match t with
    | .var _    => false
    | .app f a  => isSubterm s f || isSubterm s a
    | .lam _ body => isSubterm s body
    | .pi _ dom cod => isSubterm s dom || isSubterm s cod
    | .sort _   => false
    | .lit _    => false
    | .letE _ val body => isSubterm s val || isSubterm s body

/-- Collect all subterms of a term into a list. -/
def subterms (t : Term) : List Term :=
  t :: match t with
  | .var _    => []
  | .app f a  => subterms f ++ subterms a
  | .lam _ body => subterms body
  | .pi _ dom cod => subterms dom ++ subterms cod
  | .sort _   => []
  | .lit _    => []
  | .letE _ val body => subterms val ++ subterms body

/-- Count the number of distinct subterms. -/
def subtermCount (t : Term) : Nat :=
  (subterms t).eraseDups.length

/-- Compute the maximum depth of any subterm in the tree. -/
def subtermMaxDepth (t : Term) : Nat :=
  (subterms t).map binderDepth |>.foldl max 0

/-! ## Positions in Terms -/

/-- A position in a term tree, represented as a list of directions. -/
inductive Direction where
  | left | right
deriving BEq, Repr, DecidableEq

/-- A path is a list of directions from the root to a subterm. -/
abbrev Path := List Direction

/-- Get the subterm at a path, or none if the path is invalid. -/
def subtermAt (t : Term) (p : Path) : Option Term :=
  match p with
  | [] => some t
  | .left :: rest =>
    match t with
    | .app f _   => subtermAt f rest
    | .pi _ dom _ => subtermAt dom rest
    | .letE _ val _ => subtermAt val rest
    | _ => none
  | .right :: rest =>
    match t with
    | .app _ a   => subtermAt a rest
    | .pi _ _ cod => subtermAt cod rest
    | .letE _ _ body => subtermAt body rest
    | .lam _ body => subtermAt body rest
    | _ => none

/-- Replace the subterm at a path with a new term. -/
def replaceSubterm (t : Term) (p : Path) (new : Term) : Option Term :=
  match p with
  | [] => some new
  | .left :: rest =>
    match t with
    | .app f a   => (λ f' => .app f' a) <$> replaceSubterm f rest new
    | .pi v dom cod => (λ dom' => .pi v dom' cod) <$> replaceSubterm dom rest new
    | .letE v val body => (λ val' => .letE v val' body) <$> replaceSubterm val rest new
    | _ => none
  | .right :: rest =>
    match t with
    | .app f a   => (λ a' => .app f a') <$> replaceSubterm a rest new
    | .pi v dom cod => (λ cod' => .pi v dom' cod') <$> replaceSubterm cod rest new
    | _ => none

/-! ## Term Contexts -/

/-- A term context is a term with a single hole. -/
inductive Context : Type where
  | hole : Context
  | varC  : Variable → Context
  | appC  : Context → Term → Context
  | appC' : Term → Context → Context
  | lamC  : Variable → Context → Context
  | piC   : Variable → Context → Term → Context
  | piC'  : Variable → Term → Context → Context
  | sortC : Nat → Context
  | litC  : Nat → Context
  | letC  : Variable → Context → Term → Context
  | letC' : Variable → Term → Context → Context
deriving Repr, Inhabited

/-- Fill a context hole with a term. -/
def Context.fill (C : Context) (t : Term) : Term :=
  match C with
  | .hole => t
  | .varC v => .var v
  | .appC C' a => .app (fill C' t) a
  | .appC' f C' => .app f (fill C' t)
  | .lamC v C' => .lam v (fill C' t)
  | .piC v C' cod => .pi v (fill C' t) cod
  | .piC' v dom C' => .pi v dom (fill C' t)
  | .sortC n => .sort n
  | .litC n => .lit n
  | .letC v C' body => .letE v (fill C' t) body
  | .letC' v val C' => .letE v val (fill C' t)

/-! ## Subterm Closure Properties -/

/-- The subterm relation is decidable. The instance is provided by `Core.Laws`. -/
-- Decidable instance is in Core.Laws to avoid conflicts

/-- Every term has itself as a subterm. -/
theorem subterm_self (t : Term) : Subterm t t := Subterm.refl

/-- A proper subterm is strictly smaller than the containing term. -/
theorem properSubterm_size (s t : Term) (h : Subterm s t) (hne : s ≠ t) :
    size s < size t :=
  subterm_size_lt s t h hne

/-! ## #eval Examples -/

def exTerm : Term :=
  .app (.lam (Variable.free "x") (.app (.var (Variable.free "x")) (.lit 1))) (.lit 2)

#eval isSubterm (.var (Variable.free "x")) exTerm
#eval isSubterm (.lit 3) exTerm
#eval subterms exTerm |>.length

#eval subtermAt exTerm [Direction.left] |>.map toString

#eval Context.fill (Context.appC Context.hole (.lit 2)) (.lam (Variable.free "x") (.var (Variable.free "x")))

end MiniSyntaxKernel
