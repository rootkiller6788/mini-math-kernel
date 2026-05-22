/-
# Syntax Kernel: Properties — ClassificationData

Classification of terms: ground, open, closed, linear, affine, and other classes.
Data structures for categorizing terms by their variable usage patterns.
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects
import MiniSyntaxKernel.Core.Laws

namespace MiniSyntaxKernel

open Term

/-! ## Term Classification -/

/-- A term is ground if it contains no variables at all (not even bound). -/
def isGround (t : Term) : Bool :=
  go t
where
  go : Term → Bool
    | .var _ => false
    | .app f a => go f && go a
    | .lam _ body => go body
    | .pi _ dom cod => go dom && go cod
    | .sort _ => true
    | .lit _ => true
    | .letE _ val body => go val && go body

/-- A term is open if it contains free variables. -/
def isOpen (t : Term) : Bool :=
  !isClosed t

/-- A term is a combinator if it is closed and contains no literals. -/
def isCombinator (t : Term) : Bool :=
  isClosed t && noLiterals t
where
  noLiterals : Term → Bool
    | .lit _ => false
    | .var _ => true
    | .app f a => noLiterals f && noLiterals a
    | .lam _ body => noLiterals body
    | .pi _ dom cod => noLiterals dom && noLiterals cod
    | .sort _ => true
    | .letE _ val body => noLiterals val && noLiterals body

/-! ## Variable Occurrence Analysis -/

/-- Count the number of free occurrences of a variable in a term. -/
def freeOccurrences (v : Variable) (t : Term) : Nat :=
  go t 0
where
  go : Term → Nat → Nat
    | .var w, acc => if w == v then acc + 1 else acc
    | .app f a, acc => go f (go a acc)
    | .lam w body, acc => if w == v then acc else go body acc
    | .pi w dom cod, acc => if w == v then go dom acc else go dom (go cod acc)
    | .sort _, acc => acc
    | .lit _, acc => acc
    | .letE w val body, acc => if w == v then go val acc else go val (go body acc)

/-- A term is linear (with respect to a free variable) if the variable occurs exactly once free. -/
def isLinear (v : Variable) (t : Term) : Bool :=
  freeOccurrences v t = 1

/-- A term is affine if each free variable occurs at most once. -/
def isAffine (t : Term) : Bool :=
  freeVars t |>.all λ v => freeOccurrences v t ≤ 1

/-- A term is relevant if every free variable occurs at least once. -/
def isRelevant (t : Term) : Bool :=
  freeVars t |>.all λ v => freeOccurrences v t ≥ 1

/-! ## Term Shape Classification -/

/-- The head constructor of a term (for classification by shape). -/
inductive HeadShape where
  | varH | appH | lamH | piH | sortH | litH | letH
deriving BEq, Repr, DecidableEq

def headShape (t : Term) : HeadShape :=
  match t with
  | .var _ => .varH
  | .app _ _ => .appH
  | .lam _ _ => .lamH
  | .pi _ _ _ => .piH
  | .sort _ => .sortH
  | .lit _ => .litH
  | .letE _ _ _ => .letH

/-- A term is a value (cannot be reduced further) if it is a lambda, sort, or literal. -/
def isValue (t : Term) : Bool :=
  match t with
  | .lam _ _ => true
  | .sort _ => true
  | .lit _ => true
  | _ => false

/-- A term is neutral (stuck on a variable) if its head is a variable or application with neutral head. -/
def isNeutral (t : Term) : Bool :=
  match t with
  | .var _ => true
  | .app f _ => isNeutral f
  | _ => false

/-- A term is a redex if it is an application with a lambda on the left. -/
def isRedex (t : Term) : Bool :=
  match t with
  | .app (.lam _ _) _ => true
  | _ => false

/-! ## Complexity Classification -/

/-- The syntactic complexity class (based on size thresholds). -/
inductive ComplexityClass where
  | trivial    -- size = 1
  | simple     -- size ≤ 5
  | moderate   -- size ≤ 20
  | complex    -- size ≤ 100
  | huge       -- size > 100
deriving BEq, Repr, DecidableEq

def classifyComplexity (t : Term) : ComplexityClass :=
  let s := size t
  if s = 1 then .trivial
  else if s ≤ 5 then .simple
  else if s ≤ 20 then .moderate
  else if s ≤ 100 then .complex
  else .huge

/-! ## Binding Classification -/

/-- A term is an abstraction (starts with a lambda). -/
def isAbstraction (t : Term) : Bool :=
  match t with
  | .lam _ _ => true
  | _ => false

/-- A term is a type former (starts with Pi or Sort). -/
def isTypeFormer (t : Term) : Bool :=
  match t with
  | .pi _ _ _ => true
  | .sort _ => true
  | _ => false

/-- Count the number of lambda abstractions at the head of a term. -/
def lambdaCount (t : Term) : Nat :=
  match t with
  | .lam _ body => 1 + lambdaCount body
  | _ => 0

/-- Count the number of Pi quantifiers at the head of a term. -/
def piCount (t : Term) : Nat :=
  match t with
  | .pi _ _ cod => 1 + piCount cod
  | _ => 0

/-! ## Free/Bound Variable Classification -/

/-- Separate the free and bound variables in a term. -/
def classifyVars (t : Term) : List Variable × List Variable :=
  go t ([], [])
where
  go : Term → (List Variable × List Variable) → (List Variable × List Variable)
    | .var v, (free, bound) =>
      match v.index with
      | some _ => (free, v :: bound)
      | none => (v :: free, bound)
    | .app f a, (free, bound) =>
      let (free₁, bound₁) := go f (free, bound)
      go a (free₁, bound₁)
    | .lam _ body, acc => go body acc
    | .pi _ dom cod, acc =>
      let acc₁ := go dom acc
      go cod acc₁
    | .sort _, acc => acc
    | .lit _, acc => acc
    | .letE _ val body, acc =>
      let acc₁ := go val acc
      go body acc₁

/-! ## #eval Examples -/

def closedEx : Term :=
  .lam (Variable.bound "f" 0) (.lam (Variable.bound "x" 1) (.app (.var (Variable.bound "f" 0)) (.var (Variable.bound "x" 1))))

#eval isClosed closedEx
#eval isCombinator closedEx
#eval isGround (.lit 42)

#eval freeOccurrences (Variable.free "x") (.app (.var (Variable.free "x")) (.var (Variable.free "x")))
#eval isAffine (.app (.var (Variable.free "x")) (.var (Variable.free "y")))

#eval classifyComplexity closedEx
#eval lambdaCount closedEx

end MiniSyntaxKernel
