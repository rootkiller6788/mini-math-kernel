/-
# Objects Kernel: Bridge to Algebra

Connections between object theory and algebra:
Groups, rings, modules, and their object-theoretic representations.
-/

import MiniObjectKernel.Core.Basic

namespace MiniObjectKernel

/-! ## Bridge pattern

This bridge provides Object instances for standard algebraic
structures, enabling object-theoretic reasoning about groups,
rings, and modules. -/

/-! ## Algebraic Theory names -/

def groupTheory : TheoryName := TheoryName.ofString "Algebra.GroupTheory"
def ringTheory : TheoryName := TheoryName.ofString "Algebra.RingTheory"
def moduleTheory : TheoryName := TheoryName.ofString "Algebra.ModuleTheory"
def fieldTheory : TheoryName := TheoryName.ofString "Algebra.FieldTheory"
def vectorSpaceTheory : TheoryName := TheoryName.ofString "Algebra.VectorSpaceTheory"

/-! ## Monoid Object

A monoid is the simplest algebraic object: a set with an
associative binary operation and an identity element. -/

structure MonoidObject where
  carrier : Type u
  [obj : Object carrier]
  mul : carrier → carrier → carrier
  one : carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  deriving Repr

instance (M : MonoidObject) : Object M.carrier := M.obj

/-- The trivial monoid. -/
def trivialMonoid : MonoidObject where
  carrier := Unit
  mul := λ _ _ => ()
  one := ()
  mul_assoc := λ _ _ _ => rfl
  one_mul := λ _ => rfl
  mul_one := λ _ => rfl

/-! ## Group Object

A group is a monoid where every element has an inverse. -/

structure GroupObj where
  carrier : Type u
  [obj : Object carrier]
  mul : carrier → carrier → carrier
  one : carrier
  inv : carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  mul_left_inv : ∀ a, mul (inv a) a = one
  deriving Repr

instance (G : GroupObj) : Object G.carrier := G.obj

/-- The trivial group. -/
def trivialGroupObj : GroupObj where
  carrier := Unit
  mul := λ _ _ => ()
  one := ()
  inv := λ _ => ()
  mul_assoc := λ _ _ _ => rfl
  one_mul := λ _ => rfl
  mul_one := λ _ => rfl
  mul_left_inv := λ _ => rfl

/-- The cyclic group of order 2 (as a finite type). -/
inductive Z2 where
  | e | a
  deriving Repr

instance : Object Z2 where
  theory := groupTheory
  objName := "Z/2Z"
  repr
    | .e => "0"
    | .a => "1"

def Z2Group : GroupObj where
  carrier := Z2
  mul x y :=
    match x, y with
    | .e, y => y
    | x, .e => x
    | .a, .a => .e
  one := .e
  inv x := x
  mul_assoc := λ a b c => by
    cases a <;> cases b <;> cases c <;> rfl
  one_mul := λ a => by cases a <;> rfl
  mul_one := λ a => by cases a <;> rfl
  mul_left_inv := λ a => by cases a <;> rfl

/-! ## Ring Object

A ring is an abelian group under addition with a monoid structure
under multiplication, satisfying distributivity. -/

structure RingObj where
  carrier : Type u
  [obj : Object carrier]
  zero : carrier
  one : carrier
  add : carrier → carrier → carrier
  mul : carrier → carrier → carrier
  neg : carrier → carrier
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  add_zero : ∀ a, add a zero = a
  add_left_neg : ∀ a, add (neg a) a = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
  deriving Repr

instance (R : RingObj) : Object R.carrier := R.obj

/-- The zero ring. -/
def zeroRingObj : RingObj where
  carrier := Unit
  zero := ()
  one := ()
  add := λ _ _ => ()
  mul := λ _ _ => ()
  neg := λ _ => ()
  add_assoc := λ _ _ _ => rfl
  add_comm := λ _ _ => rfl
  add_zero := λ _ => rfl
  add_left_neg := λ _ => rfl
  mul_assoc := λ _ _ _ => rfl
  one_mul := λ _ => rfl
  mul_one := λ _ => rfl
  left_distrib := λ _ _ _ => rfl
  right_distrib := λ _ _ _ => rfl

/-! ## Module Object over a Ring

A module is an abelian group with a scalar multiplication by a ring
satisfying the module axioms. -/

structure ModuleObj (R : RingObj) where
  carrier : Type u
  [obj : Object carrier]
  zero : carrier
  add : carrier → carrier → carrier
  neg : carrier → carrier
  smul : R.carrier → carrier → carrier
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  add_zero : ∀ a, add a zero = a
  add_left_neg : ∀ a, add (neg a) a = zero
  smul_add : ∀ r x y, smul r (add x y) = add (smul r x) (smul r y)
  add_smul : ∀ r s x, smul (R.add r s) x = add (smul r x) (smul s x)
  mul_smul : ∀ r s x, smul (R.mul r s) x = smul r (smul s x)
  one_smul : ∀ x, smul R.one x = x
  zero_smul : ∀ x, smul R.zero x = zero
  deriving Repr

instance (R : RingObj) (M : ModuleObj R) : Object M.carrier := M.obj

/-! ## Free Group on One Generator (Z) -/

/-- The free group on one generator is isomorphic to Z (the integers). -/
axiom freeGroupOnOneGenerator : GroupObj

/-! ## #eval examples — L6: Verified Examples -/

#eval describe (α := Z2)
#eval trivialMonoid
#eval trivialGroupObj
#eval zeroRingObj
#eval groupTheory

end MiniObjectKernel
