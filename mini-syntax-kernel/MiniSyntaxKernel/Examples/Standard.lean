/-
# Syntax Kernel: Examples — Standard

Standard examples illustrating the term language:
identity function, Church numerals, boolean encodings, pair encoding, composition.
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects
import MiniSyntaxKernel.Core.Laws
import MiniSyntaxKernel.Morphisms.Equivalence

namespace MiniSyntaxKernel

open Term

/-! ## Identity Function -/

/-- The identity function: λ x. x -/
def idFun : Term := .lam (Variable.free "x") (.var (Variable.free "x"))

/-- Application of identity to a literal: (λ x. x) 42 -/
def idApp42 : Term := .app idFun (.lit 42)

/-! ## Church Booleans -/

/-- Church encoding of true: λ t f. t -/
def churchTrue : Term := .lam (Variable.free "t") (.lam (Variable.free "f") (.var (Variable.free "t")))

/-- Church encoding of false: λ t f. f -/
def churchFalse : Term := .lam (Variable.free "t") (.lam (Variable.free "f") (.var (Variable.free "f")))

/-- Church encoding of if-then-else: λ b t f. b t f -/
def churchIf : Term := .lam (Variable.free "b") (.lam (Variable.free "t")
    (.lam (Variable.free "f") (.app (.app (.var (Variable.free "b")) (.var (Variable.free "t"))) (.var (Variable.free "f")))))

/-- Church-encoded AND: λ a b. a b false -/
def churchAnd : Term := .lam (Variable.free "a") (.lam (Variable.free "b")
    (.app (.app (.var (Variable.free "a")) (.var (Variable.free "b"))) churchFalse))

/-- Church-encoded OR: λ a b. a true b -/
def churchOr : Term := .lam (Variable.free "a") (.lam (Variable.free "b")
    (.app (.app (.var (Variable.free "a")) churchTrue) (.var (Variable.free "b"))))

/-- Church-encoded NOT: λ b. b false true -/
def churchNot : Term := .lam (Variable.free "b")
    (.app (.app (.var (Variable.free "b")) churchFalse) churchTrue)

/-! ## Church Numerals -/

/-- Church numeral zero: λ f x. x -/
def churchZero : Term := .lam (Variable.free "f") (.lam (Variable.free "x") (.var (Variable.free "x")))

/-- Church numeral successor: λ n f x. f (n f x) -/
def churchSucc : Term := .lam (Variable.free "n") (.lam (Variable.free "f") (.lam (Variable.free "x")
    (.app (.var (Variable.free "f")) (.app (.app (.var (Variable.free "n")) (.var (Variable.free "f"))) (.var (Variable.free "x"))))))

/-- Generate the nth Church numeral. -/
def churchNumeral (n : Nat) : Term :=
  match n with
  | 0 => churchZero
  | n' + 1 => .app churchSucc (churchNumeral n')

/-- Church addition: λ m n f x. m f (n f x) -/
def churchAdd : Term := .lam (Variable.free "m") (.lam (Variable.free "n") (.lam (Variable.free "f") (.lam (Variable.free "x")
    (.app (.app (.var (Variable.free "m")) (.var (Variable.free "f")))
          (.app (.app (.var (Variable.free "n")) (.var (Variable.free "f"))) (.var (Variable.free "x")))))))

/-- Church multiplication: λ m n f. m (n f) -/
def churchMult : Term := .lam (Variable.free "m") (.lam (Variable.free "n") (.lam (Variable.free "f")
    (.app (.var (Variable.free "m")) (.app (.var (Variable.free "n")) (.var (Variable.free "f"))))))

/-! ## Pair Encoding -/

/-- Church pair constructor: λ x y f. f x y -/
def churchPair : Term := .lam (Variable.free "x") (.lam (Variable.free "y") (.lam (Variable.free "f")
    (.app (.app (.var (Variable.free "f")) (.var (Variable.free "x"))) (.var (Variable.free "y")))))

/-- Church first projection: λ p. p (λ x y. x) -/
def churchFst : Term := .lam (Variable.free "p") (.app (.var (Variable.free "p")) churchTrue)

/-- Church second projection: λ p. p (λ x y. y) -/
def churchSnd : Term := .lam (Variable.free "p") (.app (.var (Variable.free "p")) churchFalse)

/-! ## Composition -/

/-- Function composition: λ f g x. f (g x) -/
def compose : Term := .lam (Variable.free "f") (.lam (Variable.free "g") (.lam (Variable.free "x")
    (.app (.var (Variable.free "f")) (.app (.var (Variable.free "g")) (.var (Variable.free "x"))))))

/-- Flip: λ f x y. f y x -/
def flip : Term := .lam (Variable.free "f") (.lam (Variable.free "x") (.lam (Variable.free "y")
    (.app (.app (.var (Variable.free "f")) (.var (Variable.free "y"))) (.var (Variable.free "x")))))

/-! ## Fixed Point Combinator -/

/-- The Y combinator (call-by-name): λ f. (λ x. f (x x)) (λ x. f (x x)) -/
def yCombinator : Term := .lam (Variable.free "f")
    (.app (.lam (Variable.free "x") (.app (.var (Variable.free "f")) (.app (.var (Variable.free "x")) (.var (Variable.free "x")))))
          (.lam (Variable.free "x") (.app (.var (Variable.free "f")) (.app (.var (Variable.free "x")) (.var (Variable.free "x"))))))

/-! ## #eval Examples -/

#eval toString idFun
#eval size idFun
#eval freeVars idFun

#eval toString churchTrue
#eval toString churchFalse
#eval isClosed churchTrue

#eval size (churchNumeral 3)
#eval binderDepth (churchNumeral 5)

#eval toString compose
#eval isClosed compose

#eval size yCombinator
#eval freeVars yCombinator

end MiniSyntaxKernel
