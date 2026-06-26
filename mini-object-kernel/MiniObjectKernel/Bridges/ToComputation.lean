/-
# Objects Kernel: Bridge to Computation

Connections between object theory and computation:
Types, programs, and computational objects
represented in the object-theoretic framework.
-/

import MiniObjectKernel.Core.Basic

namespace MiniObjectKernel

/-! ## Computational Theory names -/

def typeTheoryName : TheoryName := TheoryName.ofString "Computation.TypeTheory"
def programTheoryName : TheoryName := TheoryName.ofString "Computation.ProgramTheory"
def automatonTheoryName : TheoryName := TheoryName.ofString "Computation.AutomatonTheory"
def complexityTheoryName : TheoryName := TheoryName.ofString "Computation.ComplexityTheory"

/-! ## Type as an Object

In the computational interpretation, types are objects
and terms are elements. The Object typeclass itself
is the meta-level representation. -/

/-- A computational type: a type equipped with decidable equality
    and a representation function. This refines the Object typeclass
    for computational use. -/
class ComputationalObject (α : Type u) extends Object α where
  decEq : DecidableEq α
  encode : α → String
  decode : String → Option α

export ComputationalObject (decEq encode decode)

/-! ## Simple Computational Objects -/

instance : ComputationalObject Nat where
  theory := typeTheoryName
  objName := "Nat"
  repr n := toString n
  decEq := inferInstance
  encode n := toString n
  decode s := s.toNat?

instance : ComputationalObject Bool where
  theory := typeTheoryName
  objName := "Bool"
  repr b := toString b
  decEq := inferInstance
  encode b := toString b
  decode s :=
    if s == "true" then some true
    else if s == "false" then some false
    else none

instance : ComputationalObject Char where
  theory := typeTheoryName
  objName := "Char"
  repr c := toString c
  decEq := inferInstance
  encode c := toString c
  decode s :=
    if s.length = 1 then
      s.get? 0 |>.bind (λ c => some c)
    else none

/-! ## Program as an Object

A program is an object that computes a function from input to output.
We model this as a "morphism" in the category of computational objects. -/

/-- A program object: a function from input type α to output type β,
    represented as a finite state machine or expression tree. We use
    a simplified untyped representation for flexibility. -/
inductive ProgramExpr (α β : Type u) [Object α] [Object β] where
  | input (idx : Nat) : ProgramExpr α β
  | const (val : β) : ProgramExpr α β
  | apply (fn : String) (args : List String) : ProgramExpr α β
  | ifThenElse (cond thenBranch elseBranch : ProgramExpr α β) : ProgramExpr α β
  deriving Repr

/-- String representation for ProgramExpr. -/
def ProgramExpr.toString {α β : Type u} [Object α] [Object β] : ProgramExpr α β → String
  | .input idx => s!"input({idx})"
  | .const val => s!"const({repr val})"
  | .apply fn args => s!"{fn}({String.intercalate ", " args})"
  | .ifThenElse c t e => s!"if({toString c})then({toString t})else({toString e})"

instance (α β : Type u) [Object α] [Object β] : ToString (ProgramExpr α β) where
  toString p := ProgramExpr.toString p

instance (α β : Type u) [Object α] [Object β] : Object (ProgramExpr α β) where
  theory := programTheoryName
  objName := s!"Program({objName α} → {objName β})"
  repr p := toString p

/-- The identity program (returns its input). -/
def idProgram (α : Type u) [Object α] : ProgramExpr α α :=
  .input 0

/-- Constant program (returns a fixed value). -/
def constProgram (α β : Type u) [Object α] [Object β] (b : β) : ProgramExpr α β :=
  .const b

/-- Composition of two programs (nominal representation). -/
def composePrograms {α β γ : Type u} [Object α] [Object β] [Object γ]
    (p : ProgramExpr β γ) (q : ProgramExpr α β) : ProgramExpr α γ :=
  .apply "compose" [toString p, toString q]

/-! ## Finite Automaton

A deterministic finite automaton (DFA) is a computational object
that recognizes a regular language. -/

structure DFA (alphabet : Type u) [Object alphabet] where
  states : Type u
  [statesObj : Object states]
  initialState : states
  acceptStates : List states
  transition : states → alphabet → states

instance (alphabet : Type u) [Object alphabet] (d : DFA alphabet) : Object d.states := d.statesObj

/-- A DFA that accepts strings ending with 'a'. -/
inductive TwoState where
  | q0 | q1
  deriving BEq, Repr, DecidableEq

instance : Object TwoState where
  theory := automatonTheoryName
  objName := "TwoStateDFA"
  repr
    | .q0 => "q0"
    | .q1 => "q1"

def endsWithA_DFA : DFA Char where
  states := TwoState
  initialState := .q0
  acceptStates := [.q1]
  transition s c :=
    match s, c with
    | .q0, 'a' => .q1
    | .q0, _ => .q0
    | .q1, 'a' => .q1
    | .q1, _ => .q0

/-- Run a DFA on an input string and return whether it accepts. -/
def DFArun {alphabet : Type u} [Object alphabet] {states : Type u} [BEq states]
    (d : DFA alphabet) (input : List alphabet) : Bool :=
  let finalState := input.foldl d.transition d.initialState
  d.acceptStates.any (· == finalState)

/-! ## Turing Machine (Abstract)

A Turing machine as an object: states, tape alphabet, transition function. -/

structure TuringMachine where
  states : Type u
  [statesObj : Object states]
  alphabet : Type u
  [alphaObj : Object alphabet]
  initialState : states
  acceptState : states
  rejectState : states
  transition : states → alphabet → states × alphabet × (Option alphabet)  -- state, write, move

instance (tm : TuringMachine) : Object tm.states := tm.statesObj
instance (tm : TuringMachine) : Object tm.alphabet := tm.alphaObj

/-! ## Complexity Classes (as invariants)

Complexity classes group computational objects by their resource usage. -/

/-- Time complexity as an invariant of a computational object. -/
inductive TimeComplexity where
  | constant
  | logarithmic
  | linear
  | polynomial (degree : Nat)
  | exponential
  | factorial
  deriving BEq, Repr, Inhabited

instance : ToString TimeComplexity where
  toString
    | constant => "O(1)"
    | logarithmic => "O(log n)"
    | linear => "O(n)"
    | polynomial d => s!"O(n^{d})"
    | exponential => "O(2ⁿ)"
    | factorial => "O(n!)"

/-- Space complexity as an invariant. -/
inductive SpaceComplexity where
  | constant
  | logarithmic
  | linear
  | polynomial (degree : Nat)
  | exponential
  deriving BEq, Repr, Inhabited

instance : ToString SpaceComplexity where
  toString
    | .constant => "O(1)"
    | .logarithmic => "O(log n)"
    | .linear => "O(n)"
    | .polynomial d => s!"O(n^{d})"
    | .exponential => "O(2ⁿ)"

/-- Complexity class: an invariant of a computational object
    that describes its resource requirements. -/
structure ComplexityClass where
  time : TimeComplexity
  space : SpaceComplexity
  deterministic : Bool
  deriving Repr

def constantTime : ComplexityClass := {
  time := TimeComplexity.constant
  space := SpaceComplexity.constant
  deterministic := true
}

def linearTime : ComplexityClass := {
  time := TimeComplexity.linear
  space := SpaceComplexity.linear
  deterministic := true
}

/-! ## Lambda Calculus Terms (as objects)

A lambda term is a fundamental computational object. -/

/-- Untyped lambda calculus terms as a data type. -/
inductive LambdaTerm where
  | var (index : Nat)
  | lam (body : LambdaTerm)
  | app (fn arg : LambdaTerm)
  deriving Repr

instance : ToString LambdaTerm where
  toString
    | .var n => s!"x{n}"
    | .lam b => s!"λ.{toString b}"
    | .app f a => s!"({toString f} {toString a})"

instance : Object LambdaTerm where
  theory := typeTheoryName
  objName := "LambdaTerm"
  repr t := toString t

/-- The identity lambda term: λx. x -/
def lambdaId : LambdaTerm := .lam (.var 0)

/-- Church encoding of the boolean true: λx y. x -/
def lambdaTrue : LambdaTerm := .lam (.lam (.var 1))

/-- Church encoding of the boolean false: λx y. y -/
def lambdaFalse : LambdaTerm := .lam (.lam (.var 0))

/-! ## #eval examples -/

#eval describe (α := Bool)
#eval describe (α := Char)
#eval describe (α := LambdaTerm)
#eval DFArun endsWithA_DFA ['a', 'b', 'a']
#eval DFArun endsWithA_DFA ['a', 'b']
#eval lambdaId
#eval typeTheoryName

end MiniObjectKernel
