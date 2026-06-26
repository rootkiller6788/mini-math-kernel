/-
# Logic Kernel: Propositional Formulas

Defines the core propositional logic layer: formulas, connectives,
semantic evaluation, and basic formula transformations.
-/

namespace MiniLogicKernel

/-! ## Formula Type -/

inductive Formula : Type where
  | atom  : Nat → Formula
  | true  : Formula
  | false : Formula
  | not   : Formula → Formula
  | and   : Formula → Formula → Formula
  | or    : Formula → Formula → Formula
  | impl  : Formula → Formula → Formula
  | equiv : Formula → Formula → Formula
  deriving BEq, DecidableEq, Repr, Inhabited

instance : ToString Formula where
  toString
    | .atom n => s!"P{n}"
    | .true => "⊤"
    | .false => "⊥"
    | .not A => s!"¬({A})"
    | .and A B => s!"({A} ∧ {B})"
    | .or A B => s!"({A} ∨ {B})"
    | .impl A B => s!"({A} → {B})"
    | .equiv A B => s!"({A} ↔ {B})"

instance : Neg Formula where
  neg := Formula.not

instance : AndOp Formula where
  and := Formula.and

instance : OrOp Formula where
  or := Formula.or

/-! ## Semantic Evaluation -/

def Formula.eval (f : Formula) (assignment : Nat → Bool) : Bool :=
  match f with
  | .atom n => assignment n
  | .true => true
  | .false => false
  | .not A => !(eval A assignment)
  | .and A B => eval A assignment && eval B assignment
  | .or A B => eval A assignment || eval B assignment
  | .impl A B => !(eval A assignment) || eval B assignment
  | .equiv A B => eval A assignment == eval B assignment

def isTautology (f : Formula) : Prop :=
  ∀ assignment : Nat → Bool, f.eval assignment = true

def isSatisfiable (f : Formula) : Prop :=
  ∃ assignment : Nat → Bool, f.eval assignment = true

def isUnsatisfiable (f : Formula) : Prop :=
  ∀ assignment : Nat → Bool, f.eval assignment = false

/-! ## Formula Complexity -/

def Formula.complexity : Formula → Nat
  | .atom _ => 0
  | .true => 0
  | .false => 0
  | .not A => 1 + complexity A
  | .and A B => 1 + complexity A + complexity B
  | .or A B => 1 + complexity A + complexity B
  | .impl A B => 1 + complexity A + complexity B
  | .equiv A B => 1 + complexity A + complexity B

def Formula.atoms : Formula → List Nat
  | .atom n => [n]
  | .true => []
  | .false => []
  | .not A => atoms A
  | .and A B => atoms A ++ atoms B
  | .or A B => atoms A ++ atoms B
  | .impl A B => atoms A ++ atoms B
  | .equiv A B => atoms A ++ atoms B

/-! ## Basic Transformations -/

def Formula.pushNeg : Formula → Formula
  | .atom n => .atom n
  | .true => .true
  | .false => .false
  | .not A => pushNegAux A
  | .and A B => .and (pushNeg A) (pushNeg B)
  | .or A B => .or (pushNeg A) (pushNeg B)
  | .impl A B => .or (pushNeg (.not A)) (pushNeg B)
  | .equiv A B => .and (pushNeg (.impl A B)) (pushNeg (.impl B A))
where
  pushNegAux : Formula → Formula
    | .atom n => .not (.atom n)
    | .true => .false
    | .false => .true
    | .not A => pushNeg A
    | .and A B => .or (pushNegAux A) (pushNegAux B)
    | .or A B => .and (pushNegAux A) (pushNegAux B)
    | .impl A B => .and (pushNeg A) (pushNegAux B)
    | .equiv A B => pushNeg (.not (.impl A B))

end MiniLogicKernel
