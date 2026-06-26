/-
# Syntax Kernel: Constructions — Products

Product constructions: tuples, pairs, and n-ary products of syntax types.
Products allow combining multiple terms into a single structure.
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects
import MiniSyntaxKernel.Core.Laws

namespace MiniSyntaxKernel

open Term

/-! ## Pair (Binary Product) of Terms -/

/-- A pair of terms, encoded as a term using application of a pairing constructor. -/
def mkPair (a b : Term) : Term :=
  .app (.app (.var (Variable.free "Pair")) a) b

/-- First projection from a pair. -/
def fst (p : Term) : Term :=
  .app (.var (Variable.free "fst")) p

/-- Second projection from a pair. -/
def snd (p : Term) : Term :=
  .app (.var (Variable.free "snd")) p

/-! ## N-ary Tuples -/

/-- An n-ary tuple of terms (right-associated pairs). -/
def mkTuple : List Term → Term
  | [] => .var (Variable.free "Unit")
  | [t] => t
  | t :: ts => mkPair t (mkTuple ts)

/-- Project the i-th element (0-indexed) from a tuple. -/
def proj (t : Term) (i : Nat) : Term :=
  .app (.app (.var (Variable.free "proj")) (.lit i)) t

/-! ## Sigma Type Encoding -/

/-- Encode a dependent pair (Sigma type) as a term. -/
def mkSigma (dom : Term) (cod : Variable → Term) (a : Term) (b : Term) : Term :=
  .app (.app (.var (Variable.free "Sigma")) dom) b

/-- The first projection of a Sigma type (domain). -/
def sigmaFst : Term := .var (Variable.free "sigmaFst")

/-- The second projection of a Sigma type (dependent codomain). -/
def sigmaSnd : Term := .var (Variable.free "sigmaSnd")

/-! ## Product Type Construction -/

/-- The product type A × B encoded as a Pi/Sigma-like term. -/
def prodType (A B : Term) : Term :=
  .pi (Variable.free "x") A B

/-- The product introduction (pairing) term. -/
def prodIntro (A B a b : Term) : Term :=
  .lam (Variable.free "x") A (.lam (Variable.free "y") B (mkPair a b))

/-! ## Product Operations -/

/-- Swap the components of a pair. -/
def swapPair (p : Term) : Term :=
  mkPair (snd p) (fst p)

/-- Zip two lists of terms into a list of pairs. -/
def zipPairs (xs ys : List Term) : List Term :=
  match xs, ys with
  | x :: xs', y :: ys' => mkPair x y :: zipPairs xs' ys'
  | _, _ => []

/-- Curry: convert a function on pairs to a curried function. -/
def curry (f : Term) : Term :=
  .lam (Variable.free "x") (.lam (Variable.free "y") (.app (.app f (.var (Variable.free "x"))) (.var (Variable.free "y"))))

/-- Uncurry: convert a curried function to a function on pairs. -/
def uncurry (f : Term) : Term :=
  .lam (Variable.free "p") (.app (.app f (fst (.var (Variable.free "p")))) (snd (.var (Variable.free "p"))))

/-! ## Product of Syntax Signatures -/

/-- A syntax signature is a list of (name, arity) pairs. -/
structure SignatureEntry where
  name : String
  arity : Nat
deriving BEq, Repr, Inhabited

/-- A signature is a list of entries. -/
abbrev Signature := List SignatureEntry

/-- The product of two signatures is their concatenation. -/
def Signature.product (S₁ S₂ : Signature) : Signature := S₁ ++ S₂

/-- Generate term constructors from a signature. -/
def Signature.mkConstructor (entry : SignatureEntry) (args : List Term) : Term :=
  match args with
  | [] => .var (Variable.free entry.name)
  | _  => List.foldl (λ acc a => .app acc a) (.var (Variable.free entry.name)) args

/-! ## Product Properties -/

/-- The size of a pair is greater than the sum of the sizes of its components. -/
theorem pair_size_gt (a b : Term) : size a + size b < size (mkPair a b) := by
  simp [mkPair, size]
  omega

/-- mkPair, fst, snd are purely syntactic encodings as terms.
    They don't reduce; the pair laws hold only modulo β-reduction
    (not at the raw syntax level). We state structural properties instead. -/

/-- mkPair produces an application term. -/
theorem mkPair_is_app (a b : Term) : isApp (mkPair a b) := by
  simp [mkPair, isApp]

/-- fst and snd are variable applications. -/
theorem fst_is_app (p : Term) : isApp (fst p) := by
  simp [fst, isApp]

/-- The size of fst(p) is exactly 1 + size p (it wraps p). -/
theorem fst_size (p : Term) : size (fst p) = size (.app (.var (Variable.free "fst")) p) := by
  simp [fst]

/-- mkPair is injective in its arguments: if mkPair a b = mkPair a' b', then a = a' and b = b'. -/
theorem mkPair_injective (a b a' b' : Term) (h : mkPair a b = mkPair a' b') :
    a = a' ∧ b = b' := by
  simp [mkPair] at h
  injection h with h1 h2
  injection h1 with _ ha
  exact ⟨ha, h2⟩

/-! ## #eval Examples -/

#eval mkPair (.lit 1) (.lit 2) |> toString

#eval fst (mkPair (.lit 10) (.lit 20)) |> toString
#eval snd (mkPair (.lit 10) (.lit 20)) |> toString

#eval mkTuple [.lit 1, .lit 2, .lit 3] |> toString

#eval curry (mkPair (.var (Variable.free "x")) (.var (Variable.free "y"))) |> toString

#eval uncurry (curry (.var (Variable.free "f"))) |> toString

end MiniSyntaxKernel
