/-
# Constructions Kernel: Universal Properties

The universal property framework.
-/

import MiniConstructionKernel.Core.Basic

namespace MiniConstructionKernel

structure UniversalProperty (U : Type u) [Object U] where
  solutions : Type u → Type u
  universal : solutions U
  mediate  : {X : Type u} → [Object X] → solutions X → (U → X)
  mediate_universal : ∀ {X : Type u} [objX : Object X] (x : solutions X), True
  unique : ∀ {X : Type u} [Object X] (x : solutions X) (f g : U → X), True

structure InitialObject (U : Type u) [Object U] where
  initiate : {X : Type u} → [Object X] → U → X
  unique : ∀ {X : Type u} [Object X] (f g : U → X), ∀ u, f u = g u

def emptyInitial : InitialObject Empty where
  initiate _ _ e := nomatch e
  unique _ _ _ e := nomatch e

structure TerminalObject (U : Type u) [Object U] where
  terminate : {X : Type u} → [Object X] → X → U
  unique : ∀ {X : Type u} [Object X] (f g : X → U), ∀ x, f x = g x

def unitTerminal : TerminalObject Unit where
  terminate _ _ := fun _ => ()
  unique f g x := by
    have : f x = () := rfl
    have : g x = () := rfl
    rfl

structure ProductUniversal (α β P : Type u) [Object α] [Object β] [Object P] where
  fst : P → α
  snd : P → β
  pair : {X : Type u} → [Object X] → (X → α) → (X → β) → (X → P)
  pair_fst : ∀ {X : Type u} [Object X] (p : X → α) (q : X → β) (x : X), fst (pair p q x) = p x
  pair_snd : ∀ {X : Type u} [Object X] (p : X → α) (q : X → β) (x : X), snd (pair p q x) = q x
  unique : ∀ {X : Type u} [Object X] (p : X → α) (q : X → β) (h : X → P),
    (∀ x, fst (h x) = p x) → (∀ x, snd (h x) = q x) → (∀ x, h x = pair p q x)

structure CoproductUniversal (α β C : Type u) [Object α] [Object β] [Object C] where
  inl : α → C
  inr : β → C
  cases : {X : Type u} → [Object X] → (α → X) → (β → X) → (C → X)
  cases_inl : ∀ {X : Type u} [Object X] (f : α → X) (g : β → X) (a : α), cases f g (inl a) = f a
  cases_inr : ∀ {X : Type u} [Object X] (f : α → X) (g : β → X) (b : β), cases f g (inr b) = g b
  unique : ∀ {X : Type u} [Object X] (f : α → X) (g : β → X) (h : C → X),
    (∀ a, h (inl a) = f a) → (∀ b, h (inr b) = g b) → (∀ c, h c = cases f g c)

/-! ## Uniqueness Theorems for Initial and Terminal Objects -/

-- Two initial objects are isomorphic (proved via the universal property)
theorem initial_object_unique {I J : Type u} [Object I] [Object J] (hI : InitialObject I) (hJ : InitialObject J) :
    ∃ (f : I → J) (g : J → I), (∀ x, g (f x) = x) ∧ (∀ x, f (g x) = x) := by
  let f : I → J := hJ.initiate
  let g : J → I := hI.initiate
  have hfg : ∀ x, g (f x) = x := by
    intro x; apply hI.unique (fun x => g (f x)) (fun x => x)
  have hgf : ∀ x, f (g x) = x := by
    intro x; apply hJ.unique (fun x => f (g x)) (fun x => x)
  exact ⟨f, g, hfg, hgf⟩

theorem terminal_object_unique {T U : Type u} [Object T] [Object U] (hT : TerminalObject T) (hU : TerminalObject U) :
    ∃ (f : T → U) (g : U → T), (∀ x, g (f x) = x) ∧ (∀ x, f (g x) = x) := by
  let f : T → U := hU.terminate
  let g : U → T := hT.terminate
  have hfg : ∀ x, g (f x) = x := by
    intro x; apply hT.unique (fun x => g (f x)) (fun x => x)
  have hgf : ∀ x, f (g x) = x := by
    intro x; apply hU.unique (fun x => f (g x)) (fun x => x)
  exact ⟨f, g, hfg, hgf⟩

/-! ## Universal Arrow -/

structure UniversalArrow {X : Type u} (F : Type u → Type v) [∀ α, Object (F α)] [Object X] where
  object : Type v
  [obj : Object object]
  arrow : X → F object
  universal : ∀ {Y : Type v} [Object Y] (f : X → F Y), object → Y
  universal_property : ∀ {Y : Type v} [Object Y] (f : X → F Y) (x : X),
    universal f x = f x
  name : String

/-! ## Cone over a diagram -/

structure Cone (J : Type u) (D : J → Type v) where
  vertex : Type v
  [obj : Object vertex]
  legs : (j : J) → vertex → D j
  name : String

/-! ## Cocone under a diagram -/

structure Cocone (J : Type u) (D : J → Type v) where
  vertex : Type v
  [obj : Object vertex]
  legs : (j : J) → D j → vertex
  name : String

/-! ## Limit as a Universal Cone -/

structure LimitCone (J : Type u) (D : J → Type v) where
  limit : Type v
  [obj : Object limit]
  cone : Cone J D
  universal : ∀ (C : Cone J D), C.vertex → limit
  universal_property : ∀ (C : Cone J D) (c : C.vertex) (j : J),
    cone.legs j (universal C c) = C.legs j c
  unique : ∀ (C : Cone J D) (f : C.vertex → limit),
    (∀ (c : C.vertex) (j : J), cone.legs j (f c) = C.legs j c) →
    (∀ c, f c = universal C c)
  name : String

/-! ## Colimit as a Universal Cocone -/

structure ColimitCocone (J : Type u) (D : J → Type v) where
  colimit : Type v
  [obj : Object colimit]
  cocone : Cocone J D
  universal : ∀ (C : Cocone J D), colimit → C.vertex
  universal_property : ∀ (C : Cocone J D) (j : J) (d : D j),
    universal C (cocone.legs j d) = C.legs j d
  unique : ∀ (C : Cocone J D) (f : colimit → C.vertex),
    (∀ (j : J) (d : D j), f (cocone.legs j d) = C.legs j d) →
    (∀ c, f c = universal C c)
  name : String

/-! ## Representable Functor -/

structure RepresentableFunctor (F : Type u → Type v) [∀ α, Object (F α)] where
  representingObject : Type u
  [obj : Object representingObject]
  naturalBijection : ∀ {α : Type u} [Object α], ((representingObject → α) → F α) × ((F α) → (representingObject → α))
  name : String

/-! ## Exponential Universal Property -/

structure ExponentialUniversal (α β E : Type u) [Object α] [Object β] [Object E] where
  eval : E → α → β
  curry : ∀ {X : Type u} [Object X], (X → α → β) → (X → E)
  curry_eval : ∀ {X : Type u} [Object X] (f : X → α → β) (x : X) (a : α),
    eval (curry f x) a = f x a
  unique : ∀ {X : Type u} [Object X] (f : X → α → β) (g : X → E),
    (∀ (x : X) (a : α), eval (g x) a = f x a) → (∀ x, g x = curry f x)
  name : String

/-! ## Natural Numbers Object (NNO) -/

structure NaturalNumbersObject (N : Type u) [Object N] where
  zero : N
  succ : N → N
  universal : ∀ {X : Type u} [Object X] (z : X) (s : X → X), N → X
  universal_zero : ∀ {X : Type u} [Object X] (z : X) (s : X → X),
    universal z s zero = z
  universal_succ : ∀ {X : Type u} [Object X] (z : X) (s : X → X) (n : N),
    universal z s (succ n) = s (universal z s n)
  unique : ∀ {X : Type u} [Object X] (z : X) (s : X → X) (f : N → X),
    f zero = z → (∀ n, f (succ n) = s (f n)) → (∀ n, f n = universal z s n)
  name : String

/-! ## Nat as Natural Numbers Object -/

def natAsNNO : NaturalNumbersObject Nat where
  zero := 0
  succ := Nat.succ
  universal z s := Nat.rec z (fun _ => s)
  universal_zero z s := rfl
  universal_succ z s n := rfl
  unique z s f hz hs n := by
    induction n with
    | zero => exact hz
    | succ n ih =>
      rw [hs n, ih]
  name := "NatNNO"

/-! ## Subobject Classifier -/

structure SubobjectClassifier (Ω : Type u) [Object Ω] where
  true : Ω
  classify : ∀ {α : Type u} [Object α] (m : α → α → Prop), α → Ω
  characteristic : ∀ {α : Type u} [Object α] (m : α → α → Prop) (a : α),
    classify m a = true ↔ m a a
  name : String

end MiniConstructionKernel
