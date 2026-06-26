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
  deriving BEq, Hashable, Repr, Inhabited

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
  toString
    | .var v => toString v
    | .app f a => s!"({f} {a})"
    | .lam v body => s!"(λ {v}. {body})"
    | .pi v dom cod => s!"(Π {v}:{dom}. {cod})"
    | .sort n => s!"Sort({n})"
    | .lit n => s!"{n}"
    | .letE v t b => s!"(let {v} := {t} in {b})"

end MiniSyntaxKernel
