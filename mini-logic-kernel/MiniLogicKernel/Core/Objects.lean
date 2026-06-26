/-
# Logic Kernel: Predicates and Quantifiers

First-order predicate structures: predicate symbols, terms,
universal and existential quantifiers.
-/

import MiniLogicKernel.Core.Basic

namespace MiniLogicKernel

/-! ## Predicate Formulas -/

inductive PredFormula : Type where
  | prop  : Formula → PredFormula
  | pred  : Nat → List Nat → PredFormula
  | eq    : Nat → Nat → PredFormula
  | not   : PredFormula → PredFormula
  | and   : PredFormula → PredFormula → PredFormula
  | or    : PredFormula → PredFormula → PredFormula
  | impl  : PredFormula → PredFormula → PredFormula
  | equiv : PredFormula → PredFormula → PredFormula
  | all   : PredFormula → PredFormula
  | ex    : PredFormula → PredFormula
  deriving BEq, Repr, Inhabited

instance : ToString PredFormula where
  toString
    | .prop f => toString f
    | .pred p ts => s!"P{p}({ts})"
    | .eq t1 t2 => s!"({t1} = {t2})"
    | .not A => s!"¬({A})"
    | .and A B => s!"({A} ∧ {B})"
    | .or A B => s!"({A} ∨ {B})"
    | .impl A B => s!"({A} → {B})"
    | .equiv A B => s!"({A} ↔ {B})"
    | .all P => s!"(∀. {P})"
    | .ex P => s!"(∃. {P})"

/-! ## First-Order Structures -/

structure Structure where
  domain : Type
  predInterp : Nat → List domain → Prop
  constInterp : Nat → domain

def Structure.satisfies (S : Structure) (φ : PredFormula) (env : List S.domain) : Prop :=
  match φ with
  | .prop _ => True
  | .pred p ts =>
    let args := ts.map fun n =>
      match env.get? n with
      | some x => x
      | none => S.constInterp n
    S.predInterp p args
  | .eq t1 t2 =>
    let v1 := match env.get? t1 with | some x => x | none => S.constInterp t1
    let v2 := match env.get? t2 with | some x => x | none => S.constInterp t2
    v1 = v2
  | .not A => ¬ S.satisfies A env
  | .and A B => S.satisfies A env ∧ S.satisfies B env
  | .or A B => S.satisfies A env ∨ S.satisfies B env
  | .impl A B => S.satisfies A env → S.satisfies B env
  | .equiv A B => S.satisfies A env ↔ S.satisfies B env
  | .all P => ∀ x : S.domain, S.satisfies P (x :: env)
  | .ex P => ∃ x : S.domain, S.satisfies P (x :: env)

def PredFormula.freeTermVars : PredFormula → Nat
  | .prop _ => 0
  | .pred _ ts => ts.foldl max 0
  | .eq t1 t2 => max t1 t2
  | .not A => freeTermVars A
  | .and A B => max (freeTermVars A) (freeTermVars B)
  | .or A B => max (freeTermVars A) (freeTermVars B)
  | .impl A B => max (freeTermVars A) (freeTermVars B)
  | .equiv A B => max (freeTermVars A) (freeTermVars B)
  | .all P => freeTermVars P
  | .ex P => freeTermVars P

def PredFormula.quantifierDepth : PredFormula → Nat
  | .prop _ => 0
  | .pred _ _ => 0
  | .eq _ _ => 0
  | .not A => quantifierDepth A
  | .and A B => max (quantifierDepth A) (quantifierDepth B)
  | .or A B => max (quantifierDepth A) (quantifierDepth B)
  | .impl A B => max (quantifierDepth A) (quantifierDepth B)
  | .equiv A B => max (quantifierDepth A) (quantifierDepth B)
  | .all P => 1 + quantifierDepth P
  | .ex P => 1 + quantifierDepth P

end MiniLogicKernel
