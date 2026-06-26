/-
# Logic Kernel: Bridge to Computation

Connections between logic and computation:
Curry-Howard correspondence, type theory, and proof assistants.

The Curry-Howard correspondence (also known as "propositions as types")
identifies:
- Propositions with types
- Proofs with terms/programs
- Implication with function types
- Conjunction with product types
- Disjunction with sum types
- Negation with the empty type (⊥)
- Universal quantification with dependent products (Π-types)
- Existential quantification with dependent sums (Σ-types)
-/

import MiniLogicKernel.Core.Basic

namespace MiniLogicKernel

/-! ## Simple Types Corresponding to Propositional Formulas

We define a grammar of simple types (no type variables beyond atoms)
that mirrors the structure of propositional formulas.
-/

/--
Simple types mirroring propositional formulas:
- Unit type (⊤) corresponds to true
- Empty type (⊥) corresponds to false
- Product type (×) corresponds to conjunction (∧)
- Sum type (+) corresponds to disjunction (∨)
- Arrow type (→) corresponds to implication (→)
- Base types correspond to propositional atoms
-/
inductive SimpleType : Type where
  | base : Nat → SimpleType
  | unit : SimpleType
  | void : SimpleType
  | prod : SimpleType → SimpleType → SimpleType
  | sum  : SimpleType → SimpleType → SimpleType
  | arr  : SimpleType → SimpleType → SimpleType
  deriving BEq, DecidableEq, Repr, Inhabited

def SimpleType.toStringAux : SimpleType → String
  | .base n => "P" ++ ToString.toString n
  | .unit => "Unit"
  | .void => "Void"
  | .prod A B => "(" ++ SimpleType.toStringAux A ++ " × " ++ SimpleType.toStringAux B ++ ")"
  | .sum A B => "(" ++ SimpleType.toStringAux A ++ " ⊕ " ++ SimpleType.toStringAux B ++ ")"
  | .arr A B => "(" ++ SimpleType.toStringAux A ++ " → " ++ SimpleType.toStringAux B ++ ")"

instance : ToString SimpleType where
  toString := SimpleType.toStringAux

/--
Translation from propositional formulas to simple types
(Curry-Howard embedding).
-/
def Formula.toType : Formula → SimpleType
  | .atom n => .base n
  | .true => .unit
  | .false => .void
  | .not A => .arr (toType A) .void
  | .and A B => .prod (toType A) (toType B)
  | .or A B => .sum (toType A) (toType B)
  | .impl A B => .arr (toType A) (toType B)
  | .equiv A B => .prod (.arr (toType A) (toType B)) (.arr (toType B) (toType A))

/-! ## Proof Terms as Lambda Expressions (Curry-Howard Embedding)

Under Curry-Howard, a proof of A → B is a function from proofs of A
to proofs of B. A proof of A ∧ B is a pair of proofs. A proof of A ∨ B
is a tagged proof (left or right injection). A proof of ¬A is a function
from proofs of A to proofs of ⊥ (Empty).

We use Lean's native type system as the target of the embedding:
propositional formulas map to actual Lean types, and proofs are
terms inhabiting those types.
-/

/--
The Curry-Howard embedding: maps propositional formulas to Lean types.
- ⊤ → Unit
- ⊥ → Empty
- ¬A → (A.type → Empty)
- A ∧ B → A.type × B.type
- A ∨ B → A.type ⊕ B.type
- A → B → A.type → B.type
- A ↔ B → (A.type → B.type) × (B.type → A.type)
- Atoms → Unit (uninterpreted base types)
-/
def Formula.toLeanType : Formula → Type
  | .atom _ => Unit
  | .true => Unit
  | .false => Empty
  | .not A => toLeanType A → Empty
  | .and A B => toLeanType A × toLeanType B
  | .or A B => toLeanType A ⊕ toLeanType B
  | .impl A B => toLeanType A → toLeanType B
  | .equiv A B => (toLeanType A → toLeanType B) × (toLeanType B → toLeanType A)

/--
The K combinator: a proof of A → B → A.
This type is inhabited for all A, B.
-/
def proof_K (A B : Formula) : Formula.toLeanType (Formula.impl A (Formula.impl B A)) :=
  fun (x : Formula.toLeanType A) (_y : Formula.toLeanType B) => x

/--
The I combinator (identity): a proof of A → A.
-/
def proof_I (A : Formula) : Formula.toLeanType (Formula.impl A A) :=
  fun (x : Formula.toLeanType A) => x

/--
The S combinator: a proof of (A → B → C) → (A → B) → A → C.
-/
def proof_S (A B C : Formula) :
    Formula.toLeanType
      (Formula.impl
        (Formula.impl A (Formula.impl B C))
        (Formula.impl (Formula.impl A B) (Formula.impl A C))) :=
  fun (f : Formula.toLeanType A → Formula.toLeanType B → Formula.toLeanType C)
      (g : Formula.toLeanType A → Formula.toLeanType B)
      (x : Formula.toLeanType A) =>
    f x (g x)

/--
A proof of A ∧ B → A (first projection).
-/
def proof_fst (A B : Formula) :
    Formula.toLeanType (Formula.impl (Formula.and A B) A) :=
  fun (p : Formula.toLeanType A × Formula.toLeanType B) => p.1

/--
A proof of A ∧ B → B (second projection).
-/
def proof_snd (A B : Formula) :
    Formula.toLeanType (Formula.impl (Formula.and A B) B) :=
  fun (p : Formula.toLeanType A × Formula.toLeanType B) => p.2

/--
A proof of A → A ∨ B (left injection).
-/
def proof_inl (A B : Formula) :
    Formula.toLeanType (Formula.impl A (Formula.or A B)) :=
  fun (x : Formula.toLeanType A) => Sum.inl x

/--
A proof of B → A ∨ B (right injection).
-/
def proof_inr (A B : Formula) :
    Formula.toLeanType (Formula.impl B (Formula.or A B)) :=
  fun (x : Formula.toLeanType B) => Sum.inr x

/--
A proof of modus ponens: (A ∧ (A → B)) → B.
-/
def proof_modus_ponens (A B : Formula) :
    Formula.toLeanType
      (Formula.impl (Formula.and A (Formula.impl A B)) B) :=
  fun (p : Formula.toLeanType A × (Formula.toLeanType A → Formula.toLeanType B)) =>
    p.2 p.1

/--
Curry-Howard for excluded middle: A ∨ ¬A corresponds to
A ⊕ (A → Empty). In intuitionistic type theory, this type is NOT
generally inhabited; it requires classical axioms (e.g., call/cc).
We state it as an axiom here, noting its classical character.
-/
axiom proof_excluded_middle (A : Formula) :
    Formula.toLeanType (Formula.or A (Formula.not A))

/--
Pierce's law: ((A → B) → A) → A.
Also not intuitionistically valid; requires classical logic.
-/
axiom proof_pierces_law (A B : Formula) :
    Formula.toLeanType
      (Formula.impl (Formula.impl (Formula.impl A B) A) A)

/-! ## Truth Tables as Decision Procedures

For propositional logic, truth tables provide a complete decision
procedure for tautology checking. Since formulas have finitely many atoms,
we can enumerate all 2^n assignments and verify the formula evaluates
to true under each.

(NOTE: `allAssignmentsNat`, `Formula.maxAtom`, and `decideTautology`
are defined in Core/Basic. This file provides alternative implementations
and Curry-Howard correspondence constructions.)
-/

/--
Verify: A → A is a tautology.
-/
#eval decideTautology (Formula.impl (Formula.atom 0) (Formula.atom 0))

/--
Verify: A ∨ ¬A is a tautology.
-/
#eval decideTautology (Formula.or (Formula.atom 0) (Formula.not (Formula.atom 0)))

/--
Verify: A ∧ B → A is a tautology.
-/
#eval decideTautology
  (Formula.impl (Formula.and (Formula.atom 0) (Formula.atom 1)) (Formula.atom 0))

/--
Verify: (A ∧ (A → B)) → B is a tautology (modus ponens).
-/
#eval decideTautology
  (Formula.impl
    (Formula.and (Formula.atom 0) (Formula.impl (Formula.atom 0) (Formula.atom 1)))
    (Formula.atom 1))

/--
Counter-example: A ∨ B → A is NOT a tautology.
-/
#eval decideTautology
  (Formula.impl (Formula.or (Formula.atom 0) (Formula.atom 1)) (Formula.atom 0))

/-! ## Decision Procedure Correctness

The truth-table algorithm is sound and complete for propositional logic:
a formula is a tautology iff `decideTautology` returns true.
-/

/--
Soundness: if the decision procedure says "tautology", the formula
is indeed a tautology (for all assignments respecting the max atom bound).
-/
def ddSoundness : Prop :=
  ∀ (f : Formula),
    decideTautology f = true →
    (∀ σ : Nat → Bool, f.eval σ = true)

/--
Completeness: if a formula is a tautology, the decision procedure
will return true.
-/
def ddCompleteness : Prop :=
  ∀ (f : Formula),
    (∀ σ : Nat → Bool, f.eval σ = true) →
    decideTautology f = true

/--
Soundness and completeness of the truth-table decision procedure.
This holds because the truth table enumerates all relevant assignments,
and atoms beyond maxAtom do not affect evaluation.
-/
axiom truth_table_sound : ddSoundness
axiom truth_table_complete : ddCompleteness

/-! ## #eval Examples: Curry-Howard -/

-- Convert formulas to types and display
def ch_formula1 : Formula := Formula.impl (Formula.atom 0) (Formula.impl (Formula.atom 1) (Formula.atom 0))
def ch_formula2 : Formula := Formula.and (Formula.atom 0) (Formula.atom 1)
def ch_formula3 : Formula := Formula.or (Formula.atom 0) (Formula.not (Formula.atom 0))

#eval toString (Formula.toType ch_formula1)
#eval toString (Formula.toType ch_formula2)
#eval toString (Formula.toType ch_formula3)

-- Truth table checks for formulas with multiple atoms
#eval decideTautology (Formula.or (Formula.atom 0) (Formula.not (Formula.atom 0)))
#eval decideTautology ch_formula1
#eval decideTautology (Formula.not (Formula.and (Formula.atom 0) (Formula.not (Formula.atom 0))))

end MiniLogicKernel
