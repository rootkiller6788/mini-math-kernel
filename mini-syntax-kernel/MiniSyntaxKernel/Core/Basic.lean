/-
# Syntax Kernel: Terms and Variables

The fundamental syntax layer. Every mathematical expression in the
mini-everything-math ecosystem is ultimately represented as a `Term`.

We use a named representation with optional de Bruijn indices for
safe binding.
-/

namespace MiniSyntaxKernel

/-! ## Variables -/

structure Variable where
  name : String
  index : Option Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

instance : ToString Variable where
  toString v :=
    match v.index with
    | none => v.name
    | some n => s!"{v.name}#{n}"

def Variable.free (name : String) : Variable :=
  { name, index := none }

def Variable.bound (name : String) (n : Nat) : Variable :=
  { name, index := some n }

/-! ## Terms -/

inductive Term : Type where
  | var  : Variable → Term
  | app  : Term → Term → Term
  | lam  : Variable → Term → Term
  | pi   : Variable → Term → Term → Term
  | sort : Nat → Term
  | lit  : Nat → Term
  | letE : Variable → Term → Term → Term
  deriving BEq, Repr, Inhabited

instance : ToString Term where
  toString t :=
    let rec go (t' : Term) : String :=
      match t' with
      | .var v => toString v
      | .app f a => s!"({go f} {go a})"
      | .lam v body => s!"(λ {v}. {go body})"
      | .pi v dom cod => s!"(Π {v}:{go dom}. {go cod})"
      | .sort n => s!"Sort({n})"
      | .lit n => s!"{n}"
      | .letE v t b => s!"(let {v} := {go t} in {go b})"
    go t

end MiniSyntaxKernel
