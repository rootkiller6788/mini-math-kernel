/-
# Syntax Kernel: Bridges — ToComputation

Bridge from the syntax kernel to computational structures.
Reduction machine, small-step semantics, normal order evaluation, `reduce` function.
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects
import MiniSyntaxKernel.Core.Laws
import MiniSyntaxKernel.Morphisms.Equivalence
import MiniSyntaxKernel.Theorems.Main

namespace MiniSyntaxKernel

open Term

/-! ## Reduction Machine -/

/-- A computation state: a term paired with an environment. -/
structure State where
  term : Term
  env : List (Variable × Term)
  deriving BEq, Repr, Inhabited

/-- The empty state for a given term. -/
def State.empty (t : Term) : State := { term := t, env := [] }

/-- Look up a variable in the environment. -/
def State.lookup (s : State) (v : Variable) : Option Term :=
  s.env.find? (λ (w, _) => w == v) |>.map (λ (_, t) => t)

/-! ## Small-Step Semantics -/

/-- A single small step of call-by-name reduction.
    Returns `none` if the term is in normal form. -/
def stepCBN (t : Term) : Option Term :=
  match t with
  | .app (.lam v body) arg => some (subst body arg v)
  | .app f a =>
    match stepCBN f with
    | some f' => some (.app f' a)
    | none =>
      match stepCBN a with
      | some a' => some (.app f a')
      | none => none
  | .lam v body =>
    stepCBN body |>.map (.lam v)
  | .pi v dom cod =>
    match stepCBN dom with
    | some dom' => some (.pi v dom' cod)
    | none => stepCBN cod |>.map (.pi v dom)
  | .letE v val body =>
    some (subst body val v)
  | _ => none

/-- A single small step of call-by-value reduction. -/
def stepCBV (t : Term) : Option Term :=
  match t with
  | .app (.lam v body) arg =>
    if isValue arg then some (subst body arg v) else
      stepCBV arg |>.map (λ a' => .app (.lam v body) a')
  | .app f a =>
    match stepCBV f with
    | some f' => some (.app f' a)
    | none => stepCBV a |>.map (.app f)
  | .letE v val body =>
    if isValue val then some (subst body val v) else
      stepCBV val |>.map (λ v' => .letE v v' body)
  | _ => none

/-! ## Reduction Strategies -/

/-- Reduce a term to normal form using call-by-name. -/
def reduceCBN (t : Term) (maxSteps : Nat) : Term × Nat :=
  let rec go (t : Term) (steps : Nat) : Term × Nat :=
    if steps ≥ maxSteps then (t, steps)
    else match stepCBN t with
         | some t' => go t' (steps + 1)
         | none => (t, steps)
  go t 0

/-- Reduce a term to normal form using call-by-value. -/
def reduceCBV (t : Term) (maxSteps : Nat) : Term × Nat :=
  let rec go (t : Term) (steps : Nat) : Term × Nat :=
    if steps ≥ maxSteps then (t, steps)
    else match stepCBV t with
         | some t' => go t' (steps + 1)
         | none => (t, steps)
  go t 0

/-- Reduce a term fully (up to 1000 steps) using the best strategy. -/
def reduce (t : Term) : Term :=
  (reduceCBN t 1000).1

/-! ## Abstract Machine (Krivine Machine) -/

/-- A Krivine machine configuration: (term, stack, environment). -/
structure KrivineConfig where
  term : Term
  stack : List Term  -- arguments awaiting the function result
  env : List (Variable × Term)
  deriving BEq, Repr, Inhabited

/-- One step of the Krivine abstract machine (call-by-name). -/
def krivineStep (c : KrivineConfig) : Option KrivineConfig :=
  match c.term with
  | .var v =>
    match c.env.find? (λ (w, _) => w == v) with
    | some (_, t) =>
      match c.stack with
      | [] => some { term := t, stack := [], env := c.env }
      | arg :: rest =>
        some { term := t, stack := rest ++ c.stack, env := c.env }
    | none =>
      match c.stack with
      | [] => none  -- free variable, stuck
      | _ => none
  | .app f a =>
    some { term := f, stack := a :: c.stack, env := c.env }
  | .lam v body =>
    match c.stack with
    | [] => none  -- value, done
    | arg :: rest =>
      some { term := body, stack := rest, env := (v, arg) :: c.env }
  | _ => none  -- sort, lit are values

/-- Krivine machine evaluation: run until normal form or max steps. -/
def krivineEval (c : KrivineConfig) (maxSteps : Nat) : KrivineConfig :=
  let rec go (c : KrivineConfig) (steps : Nat) : KrivineConfig :=
    if steps ≥ maxSteps then c
    else match krivineStep c with
         | some c' => go c' (steps + 1)
         | none => c
  go c 0

/-- Start the Krivine machine on a term. -/
def runKrivine (t : Term) : Term :=
  (krivineEval { term := t, stack := [], env := [] } 1000).term

/-! ## Term Serialization Format -/

/-- Serialize a term as S-expression style string. -/
def serializeSexpr (t : Term) : String :=
  match t with
  | .var v => s!"(var {v.name})"
  | .app f a => s!"(app {serializeSexpr f} {serializeSexpr a})"
  | .lam v body => s!"(lam {v.name} {serializeSexpr body})"
  | .pi v dom cod => s!"(pi {v.name} {serializeSexpr dom} {serializeSexpr cod})"
  | .sort n => s!"(sort {n})"
  | .lit n => s!"(lit {n})"
  | .letE v val body => s!"(let {v.name} {serializeSexpr val} {serializeSexpr body})"

/-! ## Step Counting and Performance -/

/-- Count the number of reduction steps to normal form. -/
def reductionSteps (t : Term) (maxSteps : Nat) : Nat :=
  (reduceCBN t maxSteps).2

/-- Check if a term is reducible (has a redex). -/
def isReducible (t : Term) : Bool :=
  stepCBN t |>.isSome

/-! ## #eval Examples -/

def compEx1 : Term := .app (.lam (Variable.free "x") (.app (.var (Variable.free "x")) (.var (Variable.free "x")))) (.lit 42)
def compEx2 : Term := .app (.lam (Variable.free "x") (.var (Variable.free "x"))) (.lit 1)

#eval stepCBN compEx1 |>.map toString
#eval reduceCBN compEx1 10 |>.1 |> toString
#eval reductionSteps compEx2 100

#eval isReducible compEx1
#eval isReducible (.lit 42)

#eval serializeSexpr compEx2

end MiniSyntaxKernel
