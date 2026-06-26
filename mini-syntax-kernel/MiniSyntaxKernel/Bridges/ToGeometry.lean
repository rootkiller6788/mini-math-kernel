/-
# Syntax Kernel: Bridges — ToGeometry

Bridge from the syntax kernel to geometric structures.
Term graphs, string diagrams, term representation as geometric objects.
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects
import MiniSyntaxKernel.Core.Laws
import MiniSyntaxKernel.Constructions.Subobjects

namespace MiniSyntaxKernel

open Term

/-! ## Term Graphs -/

/-- A term graph is a DAG representation where shared subterms
    are identified. -/
structure TermGraph where
  nodes : List Term
  edges : List (Nat × Nat × String)  -- (source, target, label)
  deriving BEq, Repr, Inhabited

/-- Build a term graph from a term, sharing equal subterms.
    Simple version: just flatten the tree. -/
def toGraph (t : Term) : TermGraph where
  nodes := subterms t
  edges := buildEdges t 0
where
  buildEdges (t : Term) (nodeIdx : Nat) : List (Nat × Nat × String) :=
    match t with
    | .var _ => []
    | .app f a =>
      let fIdx := subterms t |>.indexOf f
      let aIdx := subterms t |>.indexOf a
      (nodeIdx, fIdx, "fun") :: (nodeIdx, aIdx, "arg") ::
        buildEdges f fIdx ++ buildEdges a aIdx
    | .lam _ body =>
      let bIdx := subterms t |>.indexOf body
      (nodeIdx, bIdx, "body") :: buildEdges body bIdx
    | .pi _ dom cod =>
      let dIdx := subterms t |>.indexOf dom
      let cIdx := subterms t |>.indexOf cod
      (nodeIdx, dIdx, "dom") :: (nodeIdx, cIdx, "cod") ::
        buildEdges dom dIdx ++ buildEdges cod cIdx
    | .sort _ => []
    | .lit _ => []
    | .letE _ val body =>
      let vIdx := subterms t |>.indexOf val
      let bIdx := subterms t |>.indexOf body
      (nodeIdx, vIdx, "val") :: (nodeIdx, bIdx, "body") ::
        buildEdges val vIdx ++ buildEdges body bIdx

/-- IndexOf in a list. -/
def List.indexOf? (xs : List Term) (x : Term) : Option Nat :=
  let rec go (xs : List Term) (i : Nat) : Option Nat :=
    match xs with
    | [] => none
    | y :: ys => if y == x then some i else go ys (i + 1)
  go xs 0

/-- IndexOf with default. -/
def indexOf (xs : List Term) (x : Term) : Nat :=
  match xs.indexOf? x with
  | some i => i
  | none => 0

/-! ## String Diagrams -/

/-- A string diagram is a planar representation of terms with wires
    for variables and boxes for applications. -/
structure StringDiagram where
  boxes : List (Nat × Nat × Nat)  -- (x, y, label_index)
  wires : List (Nat × Nat × Nat × Nat)  -- (x1, y1, x2, y2)
  deriving BEq, Repr, Inhabited

/-- Generate box positions for a term tree. -/
def layoutBoxes (t : Term) : List (Term × Nat × Nat) :=
  let rec go (t : Term) (x y depth : Nat) : List (Term × Nat × Nat) :=
    (t, x, y) :: match t with
    | .var _ => []
    | .app f a =>
      go f (x - depth) (y + 1) (depth / 2) ++
      go a (x + depth) (y + 1) (depth / 2)
    | .lam _ body =>
      go body x (y + 1) (depth)
    | .pi _ dom cod =>
      go dom (x - depth) (y + 1) (depth / 2) ++
      go cod (x + depth) (y + 1) (depth / 2)
    | .sort _ => []
    | .lit _ => []
    | .letE _ val body =>
      go val (x - depth) (y + 1) (depth / 2) ++
      go body (x + depth) (y + 1) (depth / 2)
  go t (size t * 2) 0 (size t)

/-! ## Tree Embedding Distance -/

/-- Compute an embedding of one term tree into another.
    Returns the minimum number of node modifications needed. -/
def treeEditDistance (t₁ t₂ : Term) : Nat :=
  if t₁ == t₂ then 0
  else
    match t₁, t₂ with
    | .var v1, .var v2 => if v1 == v2 then 0 else 1
    | .app f1 a1, .app f2 a2 =>
      treeEditDistance f1 f2 + treeEditDistance a1 a2
    | .lam _ b1, .lam _ b2 => treeEditDistance b1 b2
    | .pi _ d1 c1, .pi _ d2 c2 =>
      treeEditDistance d1 d2 + treeEditDistance c1 c2
    | .sort n1, .sort n2 => if n1 == n2 then 0 else 1
    | .lit n1, .lit n2 => if n1 == n2 then 0 else 1
    | .letE _ v1 b1, .letE _ v2 b2 =>
      treeEditDistance v1 v2 + treeEditDistance b1 b2
    | _, _ => max (size t₁) (size t₂)

/-! ## Geometric Invariants -/

/-- The geometric dimension of a term: the branching factor. -/
def dimension (t : Term) : Nat :=
  match t with
  | .var _ => 0
  | .app f a => max (dimension f) (dimension a) + 1
  | .lam _ body => dimension body
  | .pi _ dom cod => max (dimension dom) (dimension cod) + 1
  | .sort _ => 0
  | .lit _ => 0
  | .letE _ val body => max (dimension val) (dimension body) + 1

/-- The width of a term: the maximum number of children at any node. -/
def width (t : Term) : Nat :=
  match t with
  | .var _ => 0
  | .app _ _ => 2
  | .lam _ _ => 1
  | .pi _ _ _ => 2
  | .sort _ => 0
  | .lit _ => 0
  | .letE _ _ _ => 2

/-! ## #eval Examples -/

def geoEx1 : Term := .app (.var (Variable.free "f")) (.app (.var (Variable.free "g")) (.lit 1))
def geoEx2 : Term := .lam (Variable.free "x") (.lam (Variable.free "y") (.app (.var (Variable.free "x")) (.var (Variable.free "y"))))

#eval toGraph geoEx1 |>.edges.length
#eval treeEditDistance geoEx1 geoEx2
#eval dimension geoEx1
#eval dimension geoEx2

#eval width geoEx1
#eval size geoEx2

end MiniSyntaxKernel
