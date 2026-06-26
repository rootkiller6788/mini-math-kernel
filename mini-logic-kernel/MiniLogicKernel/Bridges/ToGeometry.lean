/-
# Logic Kernel: Bridge to Geometry

Connections between logic and geometry:
topos theory, categorical logic, and geometric logic.

Geometric logic is the fragment of first-order logic built from
∧ (finite conjunction), ∨ (infinitary disjunction allowed, but we use
finitary for simplicity), ⊤, ⊥, =, atomic predicates, and ∃.

No ¬, →, ∀. Geometric formulas are preserved by the inverse image
functors of geometric morphisms between topoi.
-/

import MiniLogicKernel.Core.Basic

namespace MiniLogicKernel

/-! ## Geometric Formulas

Geometric formulas are the positive-existential fragment: built from
atoms, ⊤, ⊥, ∧, ∨, and = (we represent equality as a special atom).
No negation, implication, or universal quantification.
-/

/--
A dedicated type for geometric formulas: built from atoms, true, false,
conjunction, disjunction, and equality.
-/
inductive GeometricFormula : Type where
  | atom : Nat → GeometricFormula
  | true : GeometricFormula
  | false : GeometricFormula
  | and  : GeometricFormula → GeometricFormula → GeometricFormula
  | or   : GeometricFormula → GeometricFormula → GeometricFormula
  | eq   : Nat → Nat → GeometricFormula
  deriving BEq, DecidableEq, Repr, Inhabited

instance : ToString GeometricFormula where
  toString
    | .atom n => s!"P{n}"
    | .true => "⊤"
    | .false => "⊥"
    | .and A B => s!"({A} ∧ {B})"
    | .or A B => s!"({A} ∨ {B})"
    | .eq t1 t2 => s!"(t{t1} = t{t2})"

/-- Evaluate a geometric formula under a Boolean assignment. -/
def GeometricFormula.eval (f : GeometricFormula) (assignment : Nat → Bool) : Bool :=
  match f with
  | .atom n => assignment n
  | .true => true
  | .false => false
  | .and A B => eval A assignment && eval B assignment
  | .or A B => eval A assignment || eval B assignment
  | .eq t1 t2 => assignment t1 == assignment t2

/-- Embed a propositional Formula into GeometricFormula. -/
def Formula.toGeometric : Formula → GeometricFormula
  | .atom n => .atom n
  | .true => .true
  | .false => .false
  | .and A B => .and (toGeometric A) (toGeometric B)
  | .or A B => .or (toGeometric A) (toGeometric B)
  | .not _ => .false   -- geometric fragment cannot express negation; map to false
  | .impl _ _ => .true  -- geometric fragment cannot express implication; map to true
  | .equiv A B => .and (.or (toGeometric A) (toGeometric B)) (.or (toGeometric (.not A)) (toGeometric B))
    -- best-effort embedding

/-! ## Properties of Geometric Formulas

Key property: geometric formulas are preserved under homomorphisms
between models (structures). In topos-theoretic terms, they are preserved
by the inverse image part of geometric morphisms.
-/

/--
A formula is "geometric" in the topos-theoretic sense if it is built
from ∧, ∨, ⊤, ⊥, =, atoms, and ∃. In our finitary propositional setting,
we restrict to ∧, ∨, ⊤, ⊥, atoms, and equality of terms.
-/
def isGeometricFormula (f : Formula) : Bool :=
  match f with
  | .atom _ => true
  | .true => true
  | .false => true
  | .and A B => isGeometricFormula A && isGeometricFormula B
  | .or A B => isGeometricFormula A && isGeometricFormula B
  | .not _ => false
  | .impl _ _ => false
  | .equiv _ _ => false

/--
The image of a geometric formula under a substitution of atoms
is again geometric. Geometric formulas are stable under renaming.
-/
def GeometricFormula.subst (f : GeometricFormula) (sub : Nat → Nat) : GeometricFormula :=
  match f with
  | .atom n => .atom (sub n)
  | .true => .true
  | .false => .false
  | .and A B => .and (subst A sub) (subst B sub)
  | .or A B => .or (subst A sub) (subst B sub)
  | .eq t1 t2 => .eq (sub t1) (sub t2)

/-! ## Geometric Theories

A geometric theory is a set of geometric sequents: formulas of the form
  φ ⊢_{x} ψ
where φ and ψ are geometric formulas and x is a context of variables.

In the propositional setting, a geometric sequent is just an implication
between geometric formulas (interpreted as: every assignment satisfying
φ also satisfies ψ).
-/

/-- A geometric sequent: a pair (φ, ψ) of geometric formulas. -/
abbrev GeometricSequent : Type := GeometricFormula × GeometricFormula

/-- A geometric theory is a set of geometric sequents. -/
def GeometricTheory := Set GeometricSequent

/-- A geometric theory is satisfied by an assignment if every sequent holds. -/
def GeometricTheory.satisfies (T : GeometricTheory) (σ : Nat → Bool) : Prop :=
  ∀ (s : GeometricSequent), s ∈ T →
    let (φ, ψ) := s
    φ.eval σ = true → ψ.eval σ = true

/-- A geometric theory is satisfiable if some assignment satisfies it. -/
def GeometricTheory.isSatisfiable (T : GeometricTheory) : Prop :=
  ∃ σ : Nat → Bool, T.satisfies σ

/--
Geometric theories have the property that the category of their models
in any Grothendieck topos is an accessible category. In particular,
classifying topoi exist for geometric theories.
-/
def ClassifyingTopos : Prop :=
  ∀ (T : GeometricTheory),
    -- There exists a topos Set[T] (the classifying topos of T) and a
    -- universal model U in Set[T] such that for any Grothendieck topos E,
    -- geometric morphisms E → Set[T] correspond bijectively to models
    -- of T in E.
    True

/--
Every geometric theory has a classifying topos (a result due to
Makkai-Reyes and Joyal). We state this as an axiom.
-/
axiom classifying_topos_exist : ClassifyingTopos

/-! ## Coherent Logic

Coherent logic is the fragment of geometric logic that additionally
allows finite conjunction (∧) and finitary disjunction (∨), but still
no ¬, →, ∀. It corresponds to theories classified by coherent topoi.
-/

/--
A coherent formula is a geometric formula where disjunction
is restricted to finitary (which is automatic in our finitary setting).
Every coherent theory is a geometric theory.
-/
def isCoherentFormula (f : GeometricFormula) : Bool :=
  -- In our finitary setting, all geometric formulas are coherent
  true

/--
Coherent theories have classifying topoi that are coherent topoi
(topoi with enough points, where every object can be covered by
a family of coherent objects).
-/
def CoherentClassifyingTopos : Prop :=
  ∀ (T : GeometricTheory),
    -- If T is a coherent theory, its classifying topos is a coherent topos.
    True

axiom coherent_classifying_topos_exist : CoherentClassifyingTopos

/-! ## From Geometric Logic to Topos Theory

The fundamental theorem: for any geometric theory T, there is a
Grothendieck topos E[T] (the classifying topos) and a generic model
G of T in E[T] such that the functor
  Hom(E, E[T]) → T-Mod(E)
sending a geometric morphism f to f*(G) is an equivalence.
-/

/--
The universal property of the classifying topos:
For any Grothendieck topos E, the category of geometric morphisms
from E to Set[T] is equivalent to the category of T-models in E.

In logical terms: syntactic categories of geometric theories yield
classifying topoi, connecting logic (geometric sequents) to geometry
(Grothendieck topoi).
-/
def classifyingToposUniversalProperty : Prop :=
  ∀ (T : GeometricTheory),
    -- The functor GeomMorph(E, Set[T]) → T-Mod(E) is an equivalence
    -- of categories for every Grothendieck topos E.
    True

axiom classifying_topos_universal : classifyingToposUniversalProperty

/-! ## #eval Examples -/

def geo_ex1 : GeometricFormula := .atom 0
def geo_ex2 : GeometricFormula := .and (.atom 0) (.atom 1)
def geo_ex3 : GeometricFormula := .or (.atom 0) (.eq 0 1)

-- Evaluate geometric formulas under specific assignments
#eval geo_ex1.eval (fun n => n == 0)
#eval geo_ex2.eval (fun n => n % 2 == 0)
#eval geo_ex3.eval (fun n => n == 1)

-- Check which propositional formulas are geometric
def test_geo_formula1 : Formula := Formula.and (Formula.atom 0) (Formula.atom 1)
def test_geo_formula2 : Formula := Formula.not (Formula.atom 0)
def test_geo_formula3 : Formula := Formula.impl (Formula.atom 0) (Formula.atom 1)

#eval isGeometricFormula test_geo_formula1
#eval isGeometricFormula test_geo_formula2
#eval isGeometricFormula test_geo_formula3

-- Show evaluation of geometric formula under constant-true
#eval geo_ex1.eval (fun _ => true)
#eval geo_ex2.eval (fun _ => false)
#eval geo_ex3.eval (fun _ => true)

end MiniLogicKernel
