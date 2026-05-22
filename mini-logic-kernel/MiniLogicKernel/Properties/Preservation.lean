/-
# Logic Kernel: Preservation

Preservation theorems: substructure, homomorphism,
and model-theoretic preservation properties.
-/

import MiniLogicKernel.Core.Basic
import MiniLogicKernel.Core.Objects

namespace MiniLogicKernel

/-! ## Subformula Relation

A formula A is a subformula of B if A appears as a constituent
of B's syntactic construction.
-/

inductive Subformula : Formula → Formula → Prop where
  | refl (f : Formula) : Subformula f f
  | not_body (f A : Formula) : Subformula A f → Subformula A (.not f)
  | and_left (f g A : Formula) : Subformula A f → Subformula A (.and f g)
  | and_right (f g A : Formula) : Subformula A g → Subformula A (.and f g)
  | or_left (f g A : Formula) : Subformula A f → Subformula A (.or f g)
  | or_right (f g A : Formula) : Subformula A g → Subformula A (.or f g)
  | impl_left (f g A : Formula) : Subformula A f → Subformula A (.impl f g)
  | impl_right (f g A : Formula) : Subformula A g → Subformula A (.impl f g)
  | equiv_left (f g A : Formula) : Subformula A f → Subformula A (.equiv f g)
  | equiv_right (f g A : Formula) : Subformula A g → Subformula A (.equiv f g)

/-- Subformulas have complexity at most that of their parent. -/
theorem Subformula.complexity_le {A B : Formula} (h : Subformula A B) :
    A.complexity ≤ B.complexity := by
  induction h with
  | refl f => rfl
  | not_body f A h ih =>
    simp [Formula.complexity]
    exact Nat.le_succ_of_le ih
  | and_left f g A h ih =>
    simp [Formula.complexity]
    exact Nat.le_trans ih (by omega)
  | and_right f g A h ih =>
    simp [Formula.complexity]
    exact Nat.le_trans ih (by omega)
  | or_left f g A h ih =>
    simp [Formula.complexity]
    exact Nat.le_trans ih (by omega)
  | or_right f g A h ih =>
    simp [Formula.complexity]
    exact Nat.le_trans ih (by omega)
  | impl_left f g A h ih =>
    simp [Formula.complexity]
    exact Nat.le_trans ih (by omega)
  | impl_right f g A h ih =>
    simp [Formula.complexity]
    exact Nat.le_trans ih (by omega)
  | equiv_left f g A h ih =>
    simp [Formula.complexity]
    exact Nat.le_trans ih (by omega)
  | equiv_right f g A h ih =>
    simp [Formula.complexity]
    exact Nat.le_trans ih (by omega)

/-- Subformulas contain a subset of the parent's atoms. -/
theorem Subformula.atoms_subset {A B : Formula} (h : Subformula A B) :
    ∀ n, n ∈ A.atoms → n ∈ B.atoms := by
  induction h with
  | refl f => exact λ n hn => hn
  | not_body f A h ih => simp [Formula.atoms]; exact ih
  | and_left f g A h ih =>
    intro n hn
    simp [Formula.atoms]
    apply List.mem_append_left; exact ih n hn
  | and_right f g A h ih =>
    intro n hn
    simp [Formula.atoms]
    apply List.mem_append_right; exact ih n hn
  | or_left f g A h ih =>
    intro n hn; simp [Formula.atoms]; apply List.mem_append_left; exact ih n hn
  | or_right f g A h ih =>
    intro n hn; simp [Formula.atoms]; apply List.mem_append_right; exact ih n hn
  | impl_left f g A h ih =>
    intro n hn; simp [Formula.atoms]; apply List.mem_append_left; exact ih n hn
  | impl_right f g A h ih =>
    intro n hn; simp [Formula.atoms]; apply List.mem_append_right; exact ih n hn
  | equiv_left f g A h ih =>
    intro n hn; simp [Formula.atoms]; apply List.mem_append_left; exact ih n hn
  | equiv_right f g A h ih =>
    intro n hn; simp [Formula.atoms]; apply List.mem_append_right; exact ih n hn

/-! ## Polarity of Subformula Occurrences

An occurrence of a subformula is positive if it appears under an even
number of negations (and not in the left of an implication), and
negative otherwise.
-/

inductive Polarity where | positive | negative
  deriving BEq, Repr

/-- Negate a polarity: positive becomes negative, negative becomes positive. -/
def Polarity.flip : Polarity → Polarity
  | .positive => .negative
  | .negative => .positive

/-- Determine the polarity of an occurrence of A in B, given the
    polarity at the root (default: positive). Returns positive/negative
    or none if A is not a subformula.
    This is a boolean check via structural recursion. -/
def polarityIn (A B : Formula) : Option Polarity :=
  match B with
  | _ => if A == B then some .positive else
    match B with
    | .atom _ => none
    | .true => none
    | .false => none
    | .not B' => Option.map Polarity.flip (polarityIn A B')
    | .and B1 B2 =>
      match polarityIn A B1 with
      | some p => some p
      | none => polarityIn A B2
    | .or B1 B2 =>
      match polarityIn A B1 with
      | some p => some p
      | none => polarityIn A B2
    | .impl B1 B2 =>
      match polarityIn A B1 with
      | some p => some (p.flip)
      | none => polarityIn A B2
    | .equiv B1 B2 =>
      match polarityIn A B1 with
      | some p => some p
      | none => polarityIn A B2

/-- Semantic substitution respects logical equivalence: if two formulas
    g and h are logically equivalent (same truth table), then replacing
    atom n with g vs h in any formula B yields equivalent results. -/
def polarityProperty : Prop :=
  ∀ (B : Formula) (n : Nat) (g h : Formula),
    (∀ a, g.eval a = h.eval a) →
    (∀ a, (B.subst n g).eval a = (B.subst n h).eval a)

/-!
Proof sketch: By induction on B. For the base case (.atom m):
- If m = n, the substitution yields g vs h, which are equivalent by hypothesis.
- If m ≠ n, both yield .atom m, which are identical.
For compound formulas, the induction hypothesis lifts through the connectives.

This is a special case of the more general polarity monotonicity theorem
(Lyndon's theorem): if g → h and atom n occurs only positively in B,
then B[g/n] → B[h/n].
-/


/-! ## Formula Substitution

Replace all occurrences of atom n in f with formula g.
-/

def Formula.subst (f : Formula) (n : Nat) (g : Formula) : Formula :=
  match f with
  | .atom m => if m == n then g else .atom m
  | .true => .true
  | .false => .false
  | .not A => .not (subst A n g)
  | .and A B => .and (subst A n g) (subst B n g)
  | .or A B => .or (subst A n g) (subst B n g)
  | .impl A B => .impl (subst A n g) (subst B n g)
  | .equiv A B => .equiv (subst A n g) (subst B n g)

/-- Substitution never decreases complexity. This is because replacing
    an atom (complexity 0) with an arbitrary formula g (complexity ≥ 0)
    can only increase or maintain the total complexity. -/
theorem Formula.subst_complexity_ge (f : Formula) (n : Nat) (g : Formula) :
    f.complexity ≤ f.subst n g .complexity := by
  induction f with
  | atom m =>
    simp [Formula.subst, Formula.complexity]
    split
    · omega
    · rfl
  | true => simp [Formula.subst, Formula.complexity]
  | false => simp [Formula.subst, Formula.complexity]
  | not A ih =>
    simp [Formula.subst, Formula.complexity]
    omega
  | and A B ihA ihB =>
    simp [Formula.subst, Formula.complexity]
    omega
  | or A B ihA ihB =>
    simp [Formula.subst, Formula.complexity]
    omega
  | impl A B ihA ihB =>
    simp [Formula.subst, Formula.complexity]
    omega
  | equiv A B ihA ihB =>
    simp [Formula.subst, Formula.complexity]
    omega

/-- Substitution preserves tautology status when replacing equivalent formulas. -/
theorem Formula.subst_preserves_tautology (f : Formula) (n : Nat) (g h : Formula)
    (h_eq : ∀ a, g.eval a = h.eval a) (h_taut : isTautology f) :
    isTautology (f.subst n g) := by
  -- This is a semantic version: if g and h are equivalent, the substitution
  -- doesn't affect tautology status. However, replacing any atom with any
  -- formula may break tautology. The correct statement is:
  -- If f is a tautology, then for any assignment a,
  -- (f.subst n g).eval a = f.eval (λ m => if m = n then g.eval a else a m)
  -- So if f.eval a' = true for all a', then (f.subst n g).eval a = true for all a.
  intro a
  -- Evaluate the substituted formula by modifying the assignment at position n
  let a' : Nat → Bool := λ m => if m = n then g.eval a else a m
  have h_eval : (f.subst n g).eval a = f.eval a' := by
    induction f with
    | atom m => simp [Formula.subst, Formula.eval, a']
    | true => rfl
    | false => rfl
    | not A ih => simp [Formula.subst, Formula.eval, ih]
    | and A B ihA ihB => simp [Formula.subst, Formula.eval, ihA, ihB]
    | or A B ihA ihB => simp [Formula.subst, Formula.eval, ihA, ihB]
    | impl A B ihA ihB => simp [Formula.subst, Formula.eval, ihA, ihB]
    | equiv A B ihA ihB => simp [Formula.subst, Formula.eval, ihA, ihB]
  rw [h_eval]
  exact h_taut a'

/-! ## Predicate Homomorphisms and Preservation

A homomorphism between structures preserves positive existential formulas.
We define homomorphisms here (since Hom.lean is a stub).
-/

/-- A homomorphism between structures S and T. -/
structure PredHom (S T : Structure) where
  domMap : S.domain → T.domain
  predCompat : ∀ (p : Nat) (args : List S.domain),
    S.predInterp p args → T.predInterp p (args.map domMap)
  constCompat : ∀ (c : Nat), domMap (S.constInterp c) = T.constInterp c

/-- Identity homomorphism. -/
def PredHom.id (S : Structure) : PredHom S S where
  domMap := id
  predCompat := λ _ _ h => h
  constCompat := λ _ => rfl

/-- Composition of homomorphisms. -/
def PredHom.comp {S T U : Structure} (g : PredHom T U) (f : PredHom S T) : PredHom S U where
  domMap := g.domMap ∘ f.domMap
  predCompat := by
    intro p args h
    apply g.predCompat p (args.map f.domMap)
    apply f.predCompat p args
    exact h
  constCompat := by
    intro c; simp [g.constCompat c, f.constCompat c]

/-- A predicate formula is positive if it contains no negation
    and no universal quantifier. Positive formulas are preserved
    under homomorphisms (Lyndon's theorem, restricted form). -/
def PredFormula.isPositive : PredFormula → Bool
  | .prop _ => true
  | .pred _ _ => true
  | .eq _ _ => true
  | .not _ => false
  | .and A B => isPositive A && isPositive B
  | .or A B => isPositive A && isPositive B
  | .impl A B => isPositive A && isPositive B
  | .equiv A B => isPositive A && isPositive B
  | .all _ => false
  | .ex P => isPositive P

/-!
Preservation theorem (statement): If φ is a positive predicate formula
and h : PredHom S T, then S.satisfies φ env implies T.satisfies φ (env.map h.domMap).

Proof sketch: By induction on φ, using the compatibility conditions.
For atomic formulas (pred, eq, prop), the result follows directly.
For ∧, ∨, ∃, the result lifts inductively.
The restriction to positive formulas ensures we never encounter ¬ or ∀,
which are not preserved under homomorphisms.
-/

def homomorphismPreservation : Prop :=
  ∀ (S T : Structure) (h : PredHom S T) (φ : PredFormula),
    φ.isPositive = true →
    ∀ (env : List S.domain),
      S.satisfies φ env → T.satisfies φ (env.map h.domMap)

/-! ## Decidable Subformula (Bool-valued for #eval) -/

/-- Boolean predicate: is A a subformula of B? Coincides with Subformula A B. -/
def isSubformula (A B : Formula) : Bool :=
  A == B ||
  match B with
  | .not B' => isSubformula A B'
  | .and B1 B2 => isSubformula A B1 || isSubformula A B2
  | .or B1 B2 => isSubformula A B1 || isSubformula A B2
  | .impl B1 B2 => isSubformula A B1 || isSubformula A B2
  | .equiv B1 B2 => isSubformula A B1 || isSubformula A B2
  | _ => false

/-! ## #eval Examples -/

-- Subformula examples
def sf1 : Formula := .and (.atom 0) (.not (.atom 1))
#eval isSubformula (.atom 0) sf1
#eval isSubformula (.atom 1) sf1
#eval isSubformula (.atom 2) sf1

-- Complexity comparison
#eval (.atom 0).complexity
#eval sf1.complexity

-- Substitution examples
#eval Formula.subst (.atom 0) 0 (.atom 5)
#eval Formula.subst (.and (.atom 0) (.atom 1)) 0 (.not (.atom 2))
#eval Formula.subst (.impl (.atom 0) (.atom 0)) 0 (.atom 1)

-- Polarity checks
#eval polarityIn (.atom 0) (.atom 0)
#eval polarityIn (.atom 0) (.not (.atom 0))
#eval polarityIn (.atom 0) (.and (.atom 0) (.atom 1))

end MiniLogicKernel
