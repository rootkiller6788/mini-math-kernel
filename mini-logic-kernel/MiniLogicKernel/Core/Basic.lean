/-
# Logic Kernel: Propositional Formulas

Defines the core propositional logic layer: formulas, connectives,
semantic evaluation, and basic formula transformations.

Knowledge coverage: L1 (Definitions), L2 (Core Concepts)
-/

namespace MiniLogicKernel

/-! ## Formula Type -/

inductive Formula : Type where
  | atom  : Nat → Formula
  | true  : Formula
  | false : Formula
  | not   : Formula → Formula
  | and   : Formula → Formula → Formula
  | or    : Formula → Formula → Formula
  | impl  : Formula → Formula → Formula
  | equiv : Formula → Formula → Formula
  deriving BEq, DecidableEq, Repr, Inhabited

instance : ToString Formula where
  toString
    | .atom n => s!"P{n}"
    | .true => "⊤"
    | .false => "⊥"
    | .not A => s!"¬({A})"
    | .and A B => s!"({A} ∧ {B})"
    | .or A B => s!"({A} ∨ {B})"
    | .impl A B => s!"({A} → {B})"
    | .equiv A B => s!"({A} ↔ {B})"

instance : Neg Formula where
  neg := Formula.not

instance : AndOp Formula where
  and := Formula.and

instance : OrOp Formula where
  or := Formula.or

/-! ## Semantic Evaluation -/

def Formula.eval (f : Formula) (assignment : Nat → Bool) : Bool :=
  match f with
  | .atom n => assignment n
  | .true => true
  | .false => false
  | .not A => !(eval A assignment)
  | .and A B => eval A assignment && eval B assignment
  | .or A B => eval A assignment || eval B assignment
  | .impl A B => !(eval A assignment) || eval B assignment
  | .equiv A B => eval A assignment == eval B assignment

def isTautology (f : Formula) : Prop :=
  ∀ assignment : Nat → Bool, f.eval assignment = true

def isSatisfiable (f : Formula) : Prop :=
  ∃ assignment : Nat → Bool, f.eval assignment = true

def isUnsatisfiable (f : Formula) : Prop :=
  ∀ assignment : Nat → Bool, f.eval assignment = false

/-! ## Formula Complexity -/

def Formula.complexity : Formula → Nat
  | .atom _ => 0
  | .true => 0
  | .false => 0
  | .not A => 1 + complexity A
  | .and A B => 1 + complexity A + complexity B
  | .or A B => 1 + complexity A + complexity B
  | .impl A B => 1 + complexity A + complexity B
  | .equiv A B => 1 + complexity A + complexity B

def Formula.atoms : Formula → List Nat
  | .atom n => [n]
  | .true => []
  | .false => []
  | .not A => atoms A
  | .and A B => atoms A ++ atoms B
  | .or A B => atoms A ++ atoms B
  | .impl A B => atoms A ++ atoms B
  | .equiv A B => atoms A ++ atoms B

/-! ## Formula Size (total node count) -/

/-- Counts the total number of nodes (atoms + connectives) in a formula tree. -/
def formulaSize : Formula → Nat
  | .atom _   => 1
  | .true     => 1
  | .false    => 1
  | .not A    => 1 + formulaSize A
  | .and A B  => 1 + formulaSize A + formulaSize B
  | .or A B   => 1 + formulaSize A + formulaSize B
  | .impl A B => 1 + formulaSize A + formulaSize B
  | .equiv A B => 1 + formulaSize A + formulaSize B

/-! ## Maximum Atom -/

/-- Maximum atom index appearing in a formula. -/
def Formula.maxAtom : Formula → Nat
  | .atom n => n
  | .true => 0
  | .false => 0
  | .not A => maxAtom A
  | .and A B => max (maxAtom A) (maxAtom B)
  | .or A B => max (maxAtom A) (maxAtom B)
  | .impl A B => max (maxAtom A) (maxAtom B)
  | .equiv A B => max (maxAtom A) (maxAtom B)

/-! ## Basic Transformations -/

def Formula.pushNeg : Formula → Formula
  | .atom n => .atom n
  | .true => .true
  | .false => .false
  | .not A => pushNegAux A
  | .and A B => .and (pushNeg A) (pushNeg B)
  | .or A B => .or (pushNeg A) (pushNeg B)
  | .impl A B => .or (pushNeg (.not A)) (pushNeg B)
  | .equiv A B => .and (pushNeg (.impl A B)) (pushNeg (.impl B A))
where
  pushNegAux : Formula → Formula
    | .atom n => .not (.atom n)
    | .true => .false
    | .false => .true
    | .not A => pushNeg A
    | .and A B => .or (pushNegAux A) (pushNegAux B)
    | .or A B => .and (pushNegAux A) (pushNegAux B)
    | .impl A B => .and (pushNeg A) (pushNegAux B)
    | .equiv A B => pushNeg (.not (.impl A B))

/-! ## Formula Translation (Atom Renaming) -/

/-- Translate atom indices via a mapping function. -/
def Formula.translate (f : Formula) (atomMap : Nat → Nat) : Formula :=
  match f with
  | .atom n => .atom (atomMap n)
  | .true => .true
  | .false => .false
  | .not A => .not (translate A atomMap)
  | .and A B => .and (translate A atomMap) (translate B atomMap)
  | .or A B => .or (translate A atomMap) (translate B atomMap)
  | .impl A B => .impl (translate A atomMap) (translate B atomMap)
  | .equiv A B => .equiv (translate A atomMap) (translate B atomMap)

/-- Rename atoms by adding an offset. -/
def Formula.prefixAtoms (f : Formula) (n : Nat) : Formula :=
  f.translate fun k => k + n

/-- Evaluation after translation corresponds to evaluation with transformed assignment. -/
theorem Formula.eval_translate (f : Formula) (atomMap : Nat → Nat) (assignment : Nat → Bool) :
    (f.translate atomMap).eval assignment = f.eval (assignment ∘ atomMap) := by
  induction f with
  | atom n => rfl
  | true => rfl
  | false => rfl
  | not A ih => simp [translate, eval, ih]
  | and A B ihA ihB => simp [translate, eval, ihA, ihB]
  | or A B ihA ihB => simp [translate, eval, ihA, ihB]
  | impl A B ihA ihB => simp [translate, eval, ihA, ihB]
  | equiv A B ihA ihB => simp [translate, eval, ihA, ihB]

/-! ## Formula Substitution -/

/-- Substitute a formula for a specific atom index. -/
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

/-- Simultaneous substitution of multiple atoms. -/
def Formula.substMany (f : Formula) (substs : List (Nat × Formula)) : Formula :=
  match f with
  | .atom m => match substs.lookup m with
    | some g => g
    | none => .atom m
  | .true => .true
  | .false => .false
  | .not A => .not (substMany A substs)
  | .and A B => .and (substMany A substs) (substMany B substs)
  | .or A B => .or (substMany A substs) (substMany B substs)
  | .impl A B => .impl (substMany A substs) (substMany B substs)
  | .equiv A B => .equiv (substMany A substs) (substMany B substs)

/-- Substitution evaluation: eval of substituted formula equals eval of original
    with modified assignment. -/
theorem Formula.eval_subst (f : Formula) (n : Nat) (g : Formula) (a : Nat → Bool) :
    (f.subst n g).eval a = f.eval (λ m => if m = n then g.eval a else a m) := by
  induction f with
  | atom m => simp [subst, eval]; split <;> rfl
  | true => rfl
  | false => rfl
  | not A ih => simp [subst, eval, ih]
  | and A B ihA ihB => simp [subst, eval, ihA, ihB]
  | or A B ihA ihB => simp [subst, eval, ihA, ihB]
  | impl A B ihA ihB => simp [subst, eval, ihA, ihB]
  | equiv A B ihA ihB => simp [subst, eval, ihA, ihB]

/-- Substitution preserves tautology status: tautologies contain no information,
    so replacing any atom with any formula preserves tautology. -/
theorem Formula.subst_preserves_tautology (f : Formula) (n : Nat) (g : Formula)
    (h_taut : isTautology f) : isTautology (f.subst n g) := by
  intro a
  rw [Formula.eval_subst f n g a]
  apply h_taut

/-! ## Subformula Relations -/

/-- `isDirectSubformula sub sup`: `sub` is an immediate child of `sup` in the formula tree. -/
def isDirectSubformula (sub sup : Formula) : Bool :=
  match sup with
  | .atom _   => false
  | .true     => false
  | .false    => false
  | .not A    => sub == A
  | .and A B  => sub == A || sub == B
  | .or A B   => sub == A || sub == B
  | .impl A B => sub == A || sub == B
  | .equiv A B => sub == A || sub == B

/-- `isSubformula sub sup` (reflexive-transitive closure): `sub` appears anywhere in `sup`. -/
def isSubformula (sub sup : Formula) : Bool :=
  if sub == sup then true
  else
    match sup with
    | .atom _   => false
    | .true     => false
    | .false    => false
    | .not A    => isSubformula sub A
    | .and A B  => isSubformula sub A || isSubformula sub B
    | .or A B   => isSubformula sub A || isSubformula sub B
    | .impl A B => isSubformula sub A || isSubformula sub B
    | .equiv A B => isSubformula sub A || isSubformula sub B

/-- `isProperSubformula sub sup`: `sub` is a strict subformula of `sup`. -/
def isProperSubformula (sub sup : Formula) : Bool :=
  sub != sup && isSubformula sub sup

/-! ## Enumerating Assignments -/

/-- Decode an integer as a Boolean assignment: atom j is true
    iff the j-th binary digit of i is 1. -/
def decodeAssign (i : Nat) : Nat → Bool :=
  λ j => ((i / (2 : Nat) ^ j) % 2 = 1)

/-- Generate all 2^k Boolean assignments (via integer encoding). -/
def allAssignmentsNat (k : Nat) : List (Nat → Bool) :=
  (List.range (2 ^ k)).map decodeAssign

/-- Check whether a formula is a tautology by enumerating all assignments
    to the atoms 0..maxAtom. -/
def decideTautology (f : Formula) : Bool :=
  let k := f.maxAtom + 1
  (allAssignmentsNat k).all (λ a => f.eval a == true)

/-! ## Evaluation Depends Only on Atoms -/

theorem Formula.atom_le_maxAtom (f : Formula) : ∀ n ∈ f.atoms, n ≤ f.maxAtom := by
  induction f with
  | atom m => simp [atoms, maxAtom]
  | true => simp [atoms]
  | false => simp [atoms]
  | not A ih => simp [atoms, maxAtom]; exact ih
  | and A B ihA ihB =>
    simp [atoms, maxAtom]
    intro n hn
    rcases List.mem_append.mp hn with (hnA | hnB)
    · exact Nat.le_trans (ihA n hnA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB n hnB) (Nat.le_max_right _ _)
  | or A B ihA ihB =>
    simp [atoms, maxAtom]
    intro n hn
    rcases List.mem_append.mp hn with (hnA | hnB)
    · exact Nat.le_trans (ihA n hnA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB n hnB) (Nat.le_max_right _ _)
  | impl A B ihA ihB =>
    simp [atoms, maxAtom]
    intro n hn
    rcases List.mem_append.mp hn with (hnA | hnB)
    · exact Nat.le_trans (ihA n hnA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB n hnB) (Nat.le_max_right _ _)
  | equiv A B ihA ihB =>
    simp [atoms, maxAtom]
    intro n hn
    rcases List.mem_append.mp hn with (hnA | hnB)
    · exact Nat.le_trans (ihA n hnA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB n hnB) (Nat.le_max_right _ _)

theorem Formula.eval_depends_only_on_atoms (f : Formula) (a b : Nat → Bool)
    (h : ∀ n, n ∈ f.atoms → a n = b n) : f.eval a = f.eval b := by
  induction f with
  | atom n => simp [eval, atoms]; exact h n (by simp)
  | true => rfl
  | false => rfl
  | not A ih => simp [eval, atoms]; apply ih; intro n hn; apply h n; simpa using hn
  | and A B ihA ihB =>
    simp [eval, atoms]
    have hA : ∀ n, n ∈ A.atoms → a n = b n := λ n hn => h n (List.mem_append_left _ hn)
    have hB : ∀ n, n ∈ B.atoms → a n = b n := λ n hn => h n (List.mem_append_right _ hn)
    rw [ihA a b hA, ihB a b hB]
  | or A B ihA ihB =>
    simp [eval, atoms]
    have hA : ∀ n, n ∈ A.atoms → a n = b n := λ n hn => h n (List.mem_append_left _ hn)
    have hB : ∀ n, n ∈ B.atoms → a n = b n := λ n hn => h n (List.mem_append_right _ hn)
    rw [ihA a b hA, ihB a b hB]
  | impl A B ihA ihB =>
    simp [eval, atoms]
    have hA : ∀ n, n ∈ A.atoms → a n = b n := λ n hn => h n (List.mem_append_left _ hn)
    have hB : ∀ n, n ∈ B.atoms → a n = b n := λ n hn => h n (List.mem_append_right _ hn)
    rw [ihA a b hA, ihB a b hB]
  | equiv A B ihA ihB =>
    simp [eval, atoms]
    have hA : ∀ n, n ∈ A.atoms → a n = b n := λ n hn => h n (List.mem_append_left _ hn)
    have hB : ∀ n, n ∈ B.atoms → a n = b n := λ n hn => h n (List.mem_append_right _ hn)
    rw [ihA a b hA, ihB a b hB]

/-! ## Subformula Induction Principle -/

/-- A well-founded induction principle based on the formula structure.
    To prove a property `P` holds for all formulas, it suffices to:
    1. Prove it for atoms, true, and false.
    2. Prove it for compound connectives assuming it holds for subformulas. -/
theorem formula_induction {P : Formula → Prop}
    (hAtom : ∀ n, P (.atom n))
    (hTrue : P .true)
    (hFalse : P .false)
    (hNot : ∀ A, P A → P (.not A))
    (hAnd : ∀ A B, P A → P B → P (.and A B))
    (hOr : ∀ A B, P A → P B → P (.or A B))
    (hImpl : ∀ A B, P A → P B → P (.impl A B))
    (hEquiv : ∀ A B, P A → P B → P (.equiv A B))
    (f : Formula) : P f := by
  induction f with
  | atom n => exact hAtom n
  | true => exact hTrue
  | false => exact hFalse
  | not A ih => exact hNot A ih
  | and A B ihA ihB => exact hAnd A B ihA ihB
  | or A B ihA ihB => exact hOr A B ihA ihB
  | impl A B ihA ihB => exact hImpl A B ihA ihB
  | equiv A B ihA ihB => exact hEquiv A B ihA ihB

/-! ## Subformula Substitution Lemma -/

/-- Replace every occurrence of `atom n` in `f` with the formula `r`.
    (Variant of `subst` that maps via `=` on Nat instead of `==`.) -/
def Formula.substAtom (f : Formula) (n : Nat) (r : Formula) : Formula :=
  match f with
  | .atom m    => if m = n then r else .atom m
  | .true      => .true
  | .false     => .false
  | .not A     => .not (substAtom A n r)
  | .and A B   => .and (substAtom A n r) (substAtom B n r)
  | .or A B    => .or (substAtom A n r) (substAtom B n r)
  | .impl A B  => .impl (substAtom A n r) (substAtom B n r)
  | .equiv A B => .equiv (substAtom A n r) (substAtom B n r)

/-- Substituting equivalent formulas preserves equivalence (Substitution Theorem). -/
theorem substAtom_preserves_equiv (f : Formula) (n : Nat) (A B : Formula)
    (h : ∀ (assignment : Nat → Bool), A.eval assignment = B.eval assignment) :
    ∀ (assignment : Nat → Bool),
      (f.substAtom n A).eval assignment = (f.substAtom n B).eval assignment := by
  intro assignment
  induction f with
  | atom m =>
    unfold Formula.substAtom
    split
    · apply h
    · rfl
  | true => rfl
  | false => rfl
  | not f' ih => unfold Formula.substAtom Formula.eval; rw [ih]
  | and f1 f2 ih1 ih2 => unfold Formula.substAtom Formula.eval; rw [ih1, ih2]
  | or f1 f2 ih1 ih2 => unfold Formula.substAtom Formula.eval; rw [ih1, ih2]
  | impl f1 f2 ih1 ih2 => unfold Formula.substAtom Formula.eval; rw [ih1, ih2]
  | equiv f1 f2 ih1 ih2 => unfold Formula.substAtom Formula.eval; rw [ih1, ih2]

/-! ## Logical Equivalence -/

/-- Two formulas are logically equivalent if they agree under every assignment. -/
def logEquiv (A B : Formula) : Prop :=
  ∀ (a : Nat → Bool), A.eval a = B.eval a

theorem logEquiv_refl (A : Formula) : logEquiv A A := by
  intro a; rfl

theorem logEquiv_symm {A B : Formula} (h : logEquiv A B) : logEquiv B A := by
  intro a; rw [h a]

theorem logEquiv_trans {A B C : Formula} (hAB : logEquiv A B) (hBC : logEquiv B C) : logEquiv A C := by
  intro a; rw [hAB a, hBC a]

theorem logEquiv_iff_equiv_taut (A B : Formula) : logEquiv A B ↔ isTautology (.equiv A B) := by
  constructor
  · intro h a; simp [Formula.eval, h a]
  · intro h a
    have h' := h a
    simp [Formula.eval] at h'
    exact Bool.eq_of_beq_eq_true h'

theorem not_logEquiv_not {A B : Formula} (h : logEquiv A B) : logEquiv (.not A) (.not B) := by
  intro a; simp [Formula.eval, h a]

theorem and_logEquiv_and {A B C D : Formula} (hAB : logEquiv A B) (hCD : logEquiv C D) :
    logEquiv (.and A C) (.and B D) := by
  intro a; simp [Formula.eval, hAB a, hCD a]

theorem or_logEquiv_or {A B C D : Formula} (hAB : logEquiv A B) (hCD : logEquiv C D) :
    logEquiv (.or A C) (.or B D) := by
  intro a; simp [Formula.eval, hAB a, hCD a]

theorem impl_logEquiv_impl {A B C D : Formula} (hAB : logEquiv A B) (hCD : logEquiv C D) :
    logEquiv (.impl A C) (.impl B D) := by
  intro a; simp [Formula.eval, hAB a, hCD a]

/-! ## Setoid Instance -/

instance Formula.setoid : Setoid Formula where
  r := logEquiv
  iseqv := ⟨logEquiv_refl, logEquiv_symm, logEquiv_trans⟩

/-! ## Equivalence Class Operations -/

def EquivClass (A : Formula) : Set Formula :=
  {B | logEquiv A B}

theorem EquivClass.mem_self (A : Formula) : A ∈ EquivClass A :=
  logEquiv_refl A

theorem EquivClass.ext {A B : Formula} (h : logEquiv A B) : EquivClass A = EquivClass B := by
  ext C; constructor
  · intro hAC; exact logEquiv_trans (logEquiv_symm h) hAC
  · intro hBC; exact logEquiv_trans h hBC

/-! ## List Utility Functions -/

/-- Check if all elements of a list satisfy a predicate. -/
def listAll {α : Type} (l : List α) (p : α → Bool) : Bool :=
  match l with
  | [] => true
  | x :: xs => p x && listAll xs p

/-- Check if any element of a list satisfies a predicate. -/
def listAny {α : Type} (l : List α) (p : α → Bool) : Bool :=
  match l with
  | [] => false
  | x :: xs => p x || listAny xs p

/-- Find the first element satisfying a predicate. -/
def listFind? {α : Type} (l : List α) (p : α → Bool) : Option α :=
  match l with
  | [] => none
  | x :: xs => if p x then some x else listFind? xs p

/-! ## Enumerate All Assignments for Variable Sets -/

/-- Enumerate all 2^n assignments for a list of n distinct atom variables. -/
def allAssignmentsVars : List Nat → List (Nat → Bool)
  | []      => [fun _ => false]
  | v :: vs =>
    let rest := allAssignmentsVars vs
    let setTrue := rest.map fun σ n => if n = v then true else σ n
    let setFalse := rest.map fun σ n => if n = v then false else σ n
    setTrue ++ setFalse

/-! ## Tautology Checker via Enumeration -/

/-- Check if a formula is a tautology by enumerating all assignments
    for the atoms that appear in it. -/
def checkTautologyBool (f : Formula) : Bool :=
  let vars := f.atoms
  listAll (allAssignmentsVars vars) fun σ => f.eval σ == true

/-- Check if a formula is satisfiable by searching all assignments. -/
def checkSatisfiableBool (f : Formula) : Bool :=
  let vars := f.atoms
  listAny (allAssignmentsVars vars) fun σ => f.eval σ == true

/-- Find a counterexample assignment as a printable list.
    Returns `none` if the formula is a tautology. -/
def findCounterexample (f : Formula) : Option (List (Nat × Bool)) :=
  let vars := f.atoms
  match listFind? (allAssignmentsVars vars) (fun σ => f.eval σ == false) with
  | none => none
  | some σ => some (vars.map fun v => (v, σ v))

/-! ## Set Satisfiability -/

/-- A set of formulas is satisfiable if there exists an assignment
    making every formula in the set true. -/
def isSatisfiableSet (Γ : Set Formula) : Prop :=
  ∃ (σ : Nat → Bool), ∀ f ∈ Γ, f.eval σ = true

/-- A set of formulas is unsatisfiable if every assignment fails
    to satisfy at least one formula. -/
def isUnsatisfiableSet (Γ : Set Formula) : Prop :=
  ∀ (σ : Nat → Bool), ¬ (∀ f ∈ Γ, f.eval σ = true)

/-- A set of formulas is finitely satisfiable if every finite subset is satisfiable. -/
def isFinitelySatisfiable (Γ : Set Formula) : Prop :=
  ∀ (Δ : Set Formula), Δ ⊆ Γ → Set.Finite Δ → isSatisfiableSet Δ

/-- Semantic implication: Γ semantically implies f if every assignment
    satisfying all formulas in Γ also satisfies f. -/
def semanticallyImplies (Γ : Set Formula) (f : Formula) : Prop :=
  ∀ (σ : Nat → Bool), (∀ g ∈ Γ, g.eval σ = true) → f.eval σ = true

/-! ## Decide Tautology Soundness and Completeness -/

/-- Encode a Boolean assignment (restricted to the first k atoms) as an integer. -/
def encodeAssign (k : Nat) (a : Nat → Bool) : Nat :=
  (List.range k).foldl (λ acc j => if a j then acc + 2 ^ j else acc) 0

theorem encodeAssign_lt (k : Nat) (a : Nat → Bool) : encodeAssign k a < 2 ^ k := by
  induction k with
  | zero => simp [encodeAssign]
  | succ k ih =>
    simp [encodeAssign, List.range_succ, List.foldl_append]
    split
    · have h_sum : encodeAssign k a + 2 ^ k < 2 ^ k + 2 ^ k :=
        Nat.add_lt_add_right ih (2 ^ k)
      omega
    · have h_lt : encodeAssign k a < 2 ^ k := ih
      have h_pow_lt : 2 ^ k < 2 ^ (k + 1) := by
        simp [Nat.pow_succ]; omega
      omega

theorem decode_encode_eq (k j : Nat) (a : Nat → Bool) (hj : j < k) :
    decodeAssign (encodeAssign k a) j = a j := by
  unfold decodeAssign encodeAssign
  induction k generalizing j with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    simp [List.range_succ, List.foldl_append]
    let x := (List.range k).foldl (λ acc n => if a n then acc + 2 ^ n else acc) 0
    have hx_lt : x < 2 ^ k := encodeAssign_lt k a
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with (hj_lt | rfl)
    · by_cases hak : a k
      · simp [hak]
        have hdvd : 2 ^ j ∣ 2 ^ k := Nat.pow_dvd_pow (2 : Nat) (Nat.le_of_lt hj_lt)
        have h_div : (x + 2 ^ k) / 2 ^ j = x / 2 ^ j + 2 ^ k / 2 ^ j := by
          calc
            (x + 2 ^ k) / 2 ^ j = (2 ^ k + x) / 2 ^ j := by rw [Nat.add_comm]
            _ = 2 ^ k / 2 ^ j + x / 2 ^ j := Nat.add_div_of_dvd hdvd
            _ = x / 2 ^ j + 2 ^ k / 2 ^ j := by rw [Nat.add_comm]
        have h_pow_div : 2 ^ k / 2 ^ j = 2 ^ (k - j) := by
          have h_eq : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by
            rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hj_lt)]
          rw [h_eq]; exact Nat.mul_div_cancel_left _ (Nat.pow_pos (by norm_num) j)
        have h_mod : (2 ^ k / 2 ^ j) % 2 = 0 := by
          rw [h_pow_div]
          induction (k - j) with
          | zero => simp
          | succ n ih' => simp [Nat.pow_succ, mul_two]
        rw [h_div, h_mod, add_zero]
        exact ih j hj_lt
      · simp [hak]; exact ih j hj_lt
    · have h_div : x / 2 ^ k = 0 := Nat.div_eq_of_lt hx_lt
      by_cases hak : a k
      · simp [hak, h_div]
      · simp [hak, h_div]

theorem decideTautology_sound (f : Formula) : decideTautology f = true → isTautology f := by
  intro h a
  unfold decideTautology at h
  have hall_true : ∀ x ∈ allAssignmentsNat (f.maxAtom + 1), f.eval x = true := by
    have hlist := List.all_eq_true.mp h
    intro x hx
    have hx' := hlist x hx
    cases f.eval x with
    | true => rfl
    | false => simp at hx'
  let a_restricted : Nat → Bool := λ n => if n < f.maxAtom + 1 then a n else false
  have h_agree : ∀ n, n ∈ f.atoms → a n = a_restricted n := by
    intro n hn
    have hnle : n ≤ f.maxAtom := Formula.atom_le_maxAtom f n hn
    simp [a_restricted, Nat.lt_succ_of_le hnle]
  let i := encodeAssign (f.maxAtom + 1) a_restricted
  have h_decode : a_restricted = decodeAssign i := by
    funext n
    by_cases hnlt : n < f.maxAtom + 1
    · rw [decode_encode_eq (f.maxAtom + 1) n a_restricted hnlt]
      simp [a_restricted, hnlt]
    · simp [a_restricted, decodeAssign, encodeAssign, hnlt]
  have hi_mem : decodeAssign i ∈ allAssignmentsNat (f.maxAtom + 1) := by
    unfold allAssignmentsNat
    apply List.mem_map.mpr
    refine ⟨i, ?_, rfl⟩
    have hi_lt : i < 2 ^ (f.maxAtom + 1) := encodeAssign_lt _ _
    have mem_range_lemma (a n : Nat) (h : a < n) : a ∈ List.range n := by
      induction' n with k ih
      · exact absurd h (Nat.not_lt_zero _)
      · rw [List.range_succ]
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with (hl | heq)
        · apply List.mem_append_of_mem_left; exact ih hl
        · apply List.mem_append_of_mem_right
          subst heq; exact List.mem_singleton_self _
    exact mem_range_lemma i (2 ^ (f.maxAtom + 1)) hi_lt
  calc
    f.eval a = f.eval a_restricted :=
      Formula.eval_depends_only_on_atoms f a a_restricted h_agree
    _ = f.eval (decodeAssign i) := by rw [h_decode]
    _ = true := hall_true (decodeAssign i) hi_mem

theorem decideTautology_complete (f : Formula) : isTautology f → decideTautology f = true := by
  intro htaut
  unfold decideTautology
  apply List.all_eq_true.mpr
  intro a ha
  have htrue := htaut a
  simp [htrue]

/-! ## #eval Examples -/

def testBasicFormula1 : Formula := .impl (.and (.atom 0) (.atom 1)) (.or (.atom 0) (.atom 2))

#eval formulaSize testBasicFormula1
#eval isDirectSubformula (.atom 0) testBasicFormula1
#eval isSubformula (.atom 2) testBasicFormula1
#eval isProperSubformula (.atom 2) testBasicFormula1
#eval isProperSubformula testBasicFormula1 testBasicFormula1
#eval Formula.atoms (Formula.and (Formula.atom 0) (Formula.atom 1))
#eval Formula.maxAtom (Formula.and (Formula.atom 0) (Formula.atom 5))

#eval Formula.translate (Formula.and (.atom 0) (.atom 1)) (fun k => k + 5)
#eval Formula.subst (Formula.or (.atom 0) (.atom 1)) 0 (Formula.atom 42)
#eval Formula.prefixAtoms (Formula.impl (.atom 0) (.atom 3)) 10
#eval Formula.substMany (Formula.and (.atom 0) (.atom 1)) [(0, Formula.true), (1, Formula.false)]

-- #eval decideTautology (.or (.atom 0) (.not (.atom 0)))
-- #eval decideTautology (.and (.atom 0) (.atom 1))
-- #eval decideTautology (.impl (.atom 0) (.atom 0))
-- #eval checkTautologyBool (.impl (.atom 0) (.atom 0))
-- #eval checkSatisfiableBool (.and (.atom 0) (.not (.atom 0)))

end MiniLogicKernel
