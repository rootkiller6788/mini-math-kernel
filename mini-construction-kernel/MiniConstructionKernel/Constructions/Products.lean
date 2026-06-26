/-
# Constructions Kernel: Product and Coproduct

Concrete implementations of product and coproduct constructions.
-/

import MiniConstructionKernel.Core.Basic
import MiniConstructionKernel.Constructions.Universal

namespace MiniConstructionKernel

structure Product (α : Type u) (β : α → Type v) where
  fst : α
  snd : β fst

abbrev BinProduct (α β : Type u) := Product α fun _ => β
infixr:70 " ×ₖ " => BinProduct

def Product.mk (a : α) (b : β a) : Product α β := { fst := a, snd := b }
def Product.fst' (p : Product α β) : α := p.fst
def Product.snd' (p : Product α β) : β p.fst := p.snd

def binProductUniversal (α β : Type u) [Object α] [Object β] :
    ProductUniversal α β (BinProduct α β) where
  fst p := p.fst
  snd p := p.snd
  pair p q x := { fst := p x, snd := q x }
  pair_fst p q x := rfl
  pair_snd p q x := rfl
  unique p q h hFst hSnd x := by
    cases h x; constructor <;> assumption

inductive Coproduct (α β : Type u) : Type u where
  | inl : α → Coproduct α β
  | inr : β → Coproduct α β

infixr:60 " +ₖ " => Coproduct

def binCoproductUniversal (α β : Type u) [Object α] [Object β] :
    CoproductUniversal α β (Coproduct α β) where
  inl := Coproduct.inl
  inr := Coproduct.inr
  cases f g
    | Coproduct.inl a => f a
    | Coproduct.inr b => g b
  cases_inl f g a := rfl
  cases_inr f g b := rfl
  unique f g h hInl hInr c :=
    match c with
    | Coproduct.inl a => hInl a
    | Coproduct.inr b => hInr b

def buildProduct (α β : Type u) [Object α] [Object β] :
    ProductConstruction (Fin 2) fun
      | 0 => α
      | 1 => β :=
  { carrier := BinProduct α β
    proj := fun
      | 0 => Product.fst'
      | 1 => Product.snd'
    name := s!"Product({describe α}, {describe β})"
  }

def buildCoproduct (α β : Type u) [Object α] [Object β] :
    CoproductConstruction (Fin 2) fun
      | 0 => α
      | 1 => β :=
  { carrier := Coproduct α β
    inj := fun
      | 0 => Coproduct.inl
      | 1 => Coproduct.inr
    name := s!"Coproduct({describe α}, {describe β})"
  }

/-! ## Properties of Product -/

theorem Product_eta (p : Product α β) : Product.mk p.fst p.snd = p := rfl

theorem Product_fst_mk (a : α) (b : β a) : (Product.mk a b).fst = a := rfl

theorem Product_snd_mk (a : α) (b : β a) : (Product.mk a b).snd = b := rfl

theorem Product_ext (p q : Product α β) (h_fst : p.fst = q.fst) (h_snd : p.snd = q.snd) : p = q := by
  cases p; cases q; simp [h_fst, h_snd]

/-! ## Sigma type as dependent product -/

def SigmaAsProduct {α : Type u} (β : α → Type v) : Product α β → Sigma β :=
  fun p => ⟨p.fst, p.snd⟩

def ProductFromSigma {α : Type u} (β : α → Type v) : Sigma β → Product α β :=
  fun s => Product.mk s.1 s.2

theorem Product_sigma_equiv {α : Type u} (β : α → Type v) :
    Function.LeftInverse (ProductFromSigma β) (SigmaAsProduct β) := by
  intro s; cases s; rfl

/-! ## Properties of Coproduct -/

theorem Coproduct_inl_injective {α β : Type u} (a₁ a₂ : α)
    (h : Coproduct.inl a₁ = Coproduct.inl a₂) : a₁ = a₂ := by
  injection h

theorem Coproduct_inr_injective {α β : Type u} (b₁ b₂ : β)
    (h : Coproduct.inr b₁ = Coproduct.inr b₂) : b₁ = b₂ := by
  injection h

theorem Coproduct_inl_ne_inr {α β : Type u} (a : α) (b : β) : Coproduct.inl a ≠ Coproduct.inr b := by
  intro h; injection h

/-! ## Mapping over products and coproducts -/

def Product.map {α α' : Type u} {β β' : α → Type v} {β'' : α' → Type v}
    (f : α → α') (g : (a : α) → β a → β'' (f a)) (p : Product α β) : Product α' β'' :=
  Product.mk (f p.fst) (g p.fst p.snd)

def Coproduct.map {α β α' β' : Type u} (f : α → α') (g : β → β') : Coproduct α β → Coproduct α' β' :=
  fun
    | Coproduct.inl a => Coproduct.inl (f a)
    | Coproduct.inr b => Coproduct.inr (g b)

theorem Coproduct.map_inl {α β α' β' : Type u} (f : α → α') (g : β → β') (a : α) :
    Coproduct.map f g (Coproduct.inl a) = Coproduct.inl (f a) := rfl

theorem Coproduct.map_inr {α β α' β' : Type u} (f : α → α') (g : β → β') (b : β) :
    Coproduct.map f g (Coproduct.inr b) = Coproduct.inr (g b) := rfl

/-! ## Product functor -/

def Product.bifunctor {α β α' β' : Type u} (f : α → α') (g : β → β') : BinProduct α β → BinProduct α' β' :=
  fun p => Product.mk (f p.fst) (g p.snd)

theorem Product.bifunctor_fst {α β α' β' : Type u} (f : α → α') (g : β → β') (p : BinProduct α β) :
    (Product.bifunctor f g p).fst = f p.fst := rfl

theorem Product.bifunctor_snd {α β α' β' : Type u} (f : α → α') (g : β → β') (p : BinProduct α β) :
    (Product.bifunctor f g p).snd = g p.snd := rfl

/-! ## Symmetry of binary product -/

def Product.swap {α β : Type u} (p : BinProduct α β) : BinProduct β α :=
  Product.mk p.snd p.fst

theorem Product.swap_swap {α β : Type u} (p : BinProduct α β) : Product.swap (Product.swap p) = p := rfl

/-! ## Symmetry of binary coproduct -/

def Coproduct.swap {α β : Type u} : Coproduct α β → Coproduct β α :=
  fun
    | Coproduct.inl a => Coproduct.inr a
    | Coproduct.inr b => Coproduct.inl b

theorem Coproduct.swap_swap {α β : Type u} (c : Coproduct α β) : Coproduct.swap (Coproduct.swap c) = c := by
  cases c <;> rfl

/-! ## Associativity of product -/

def Product.assoc {α β γ : Type u} (p : BinProduct (BinProduct α β) γ) : BinProduct α (BinProduct β γ) :=
  Product.mk p.fst.fst (Product.mk p.fst.snd p.snd)

def Product.unassoc {α β γ : Type u} (p : BinProduct α (BinProduct β γ)) : BinProduct (BinProduct α β) γ :=
  Product.mk (Product.mk p.fst p.snd.fst) p.snd.snd

theorem Product.assoc_unassoc {α β γ : Type u} (p : BinProduct α (BinProduct β γ)) :
    Product.assoc (Product.unassoc p) = p := rfl

theorem Product.unassoc_assoc {α β γ : Type u} (p : BinProduct (BinProduct α β) γ) :
    Product.unassoc (Product.assoc p) = p := rfl

/-! ## Associativity of coproduct -/

def Coproduct.assoc {α β γ : Type u} : Coproduct (Coproduct α β) γ → Coproduct α (Coproduct β γ) :=
  fun
    | Coproduct.inl (Coproduct.inl a) => Coproduct.inl a
    | Coproduct.inl (Coproduct.inr b) => Coproduct.inr (Coproduct.inl b)
    | Coproduct.inr c => Coproduct.inr (Coproduct.inr c)

def Coproduct.unassoc {α β γ : Type u} : Coproduct α (Coproduct β γ) → Coproduct (Coproduct α β) γ :=
  fun
    | Coproduct.inl a => Coproduct.inl (Coproduct.inl a)
    | Coproduct.inr (Coproduct.inl b) => Coproduct.inl (Coproduct.inr b)
    | Coproduct.inr (Coproduct.inr c) => Coproduct.inr c

theorem Coproduct.assoc_unassoc {α β γ : Type u} (c : Coproduct α (Coproduct β γ)) :
    Coproduct.assoc (Coproduct.unassoc c) = c := by
  cases c <;> rfl
  <;> cases _ <;> rfl

theorem Coproduct.unassoc_assoc {α β γ : Type u} (c : Coproduct (Coproduct α β) γ) :
    Coproduct.unassoc (Coproduct.assoc c) = c := by
  cases c <;> rfl
  <;> (rename_i h; cases h <;> rfl)

/-! ## Distributivity of product over coproduct -/

def Product.distrib {α β γ : Type u} : BinProduct α (Coproduct β γ) → Coproduct (BinProduct α β) (BinProduct α γ) :=
  fun p =>
    match p.snd with
    | Coproduct.inl b => Coproduct.inl (Product.mk p.fst b)
    | Coproduct.inr c => Coproduct.inr (Product.mk p.fst c)

def Product.factor {α β γ : Type u} : Coproduct (BinProduct α β) (BinProduct α γ) → BinProduct α (Coproduct β γ) :=
  fun
    | Coproduct.inl p => Product.mk p.fst (Coproduct.inl p.snd)
    | Coproduct.inr p => Product.mk p.fst (Coproduct.inr p.snd)

theorem Product.distrib_factor {α β γ : Type u} (c : Coproduct (BinProduct α β) (BinProduct α γ)) :
    Product.distrib (Product.factor c) = c := by
  cases c <;> rfl

theorem Product.factor_distrib {α β γ : Type u} (p : BinProduct α (Coproduct β γ)) :
    Product.factor (Product.distrib p) = p := by
  cases p; cases snd <;> rfl

/-! ## Fixpoint operator on products -/

def Product.diag {α : Type u} (a : α) : BinProduct α α := Product.mk a a

def Coproduct.fold {α β γ : Type u} (f : α → γ) (g : β → γ) : Coproduct α β → γ :=
  fun
    | Coproduct.inl a => f a
    | Coproduct.inr b => g b

theorem Coproduct.fold_inl {α β γ : Type u} (f : α → γ) (g : β → γ) (a : α) :
    Coproduct.fold f g (Coproduct.inl a) = f a := rfl

theorem Coproduct.fold_inr {α β γ : Type u} (f : α → γ) (g : β → γ) (b : β) :
    Coproduct.fold f g (Coproduct.inr b) = g b := rfl

/-! ## Empty and Unit as neutral elements -/

abbrev VoidProduct : Type u := BinProduct Empty Empty
abbrev UnitProduct : Type u := BinProduct Unit Unit

def VoidProduct.elim {α : Type u} : BinProduct Empty α → Empty := fun p => nomatch p.fst
def UnitProduct.unique {α : Type u} (p q : BinProduct Unit α) : p = q := by
  cases p; cases q; have : fst = fst := rfl; cases fst; cases fst; rfl

/-! ## Projection lemmas -/

theorem BinProduct.proj_fst {α β : Type u} (p : BinProduct α β) : p.fst = p.fst := rfl
theorem BinProduct.proj_snd {α β : Type u} (p : BinProduct α β) : p.snd = p.snd := rfl

/-! ## Product and Coproduct as functor on indexed families -/

def Product.pi {ι : Type u} (α : ι → Type v) : Type _ := ∀ i, α i

def Coproduct.sigma {ι : Type u} (α : ι → Type v) : Type _ := Σ i, α i

def Product.indexedMap {ι : Type u} {α β : ι → Type v} (f : ∀ i, α i → β i) (p : Product.pi α) : Product.pi β :=
  fun i => f i (p i)

def Coproduct.indexedMap {ι : Type u} {α β : ι → Type v} (f : ∀ i, α i → β i) (s : Coproduct.sigma α) : Coproduct.sigma β :=
  ⟨s.1, f s.1 s.2⟩

end MiniConstructionKernel
