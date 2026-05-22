/-
# Logic Kernel: Invariants

Logical invariants: consistency, completeness, decidability,
and other metalogical properties.
-/

import MiniLogicKernel.Core.Basic
import MiniLogicKernel.Core.Objects
import MiniLogicKernel.Theorems.Basic

namespace MiniLogicKernel

/-! ## Soundness of the Proof System

Theorems/Basic.lean defines `Derivable` and proves `soundness`.
We restate for self-contained reference.
-/

theorem derivable_implies_tautology (f : Formula) (h : Derivable f) : isTautology f :=
  soundness f h

/-! ## Consistency

A logical theory is consistent if it does not prove both a formula
and its negation. For our system, consistency follows from soundness
because no formula and its negation can both be tautologies.
-/

def isConsistent : Prop :=
  ¬ ∃ (f : Formula), Derivable f ∧ Derivable (.not f)

theorem consistency_holds : isConsistent := by
  intro h
  rcases h with ⟨f, hf, hnf⟩
  have htaut_f := soundness f hf
  have htaut_nf := soundness (.not f) hnf
  -- If both f and ¬f are tautologies, then f ∧ ¬f is also a tautology
  have h_contra : isTautology (.and f (.not f)) := by
    intro a
    have h1 := htaut_f a
    have h2 := htaut_nf a
    simp [Formula.eval, h1, h2]
  -- But f ∧ ¬f is never true (evaluate under any assignment)
  have h_false : ¬ isTautology (.and f (.not f)) := by
    intro ht
    have htest := ht (λ _ => false)
    simp [Formula.eval] at htest
  exact h_false h_contra

/-! ## Completeness

Weak completeness: every tautology is derivable.
Defined as an axiom in Theorems/Basic.lean (Post, 1921).
-/

def weakCompletenessStatement : Prop :=
  ∀ (f : Formula), isTautology f → Derivable f

theorem weakCompleteness_self : weakCompletenessStatement :=
  weak_completeness

/-! ## Strong Completeness

If a set Γ semantically implies f, then some finite subset
of Γ semantically implies f. Proved from compactness + weak completeness.
-/

def isSatisfiableSet (Γ : Set Formula) : Prop :=
  ∃ (σ : Nat → Bool), ∀ f ∈ Γ, f.eval σ = true

def semanticallyImplies (Γ : Set Formula) (f : Formula) : Prop :=
  ∀ (σ : Nat → Bool), (∀ g ∈ Γ, g.eval σ = true) → f.eval σ = true

/-- Strong completeness: semantic consequence from an arbitrary set
    can be reduced to a finite subset. -/
def strongCompletenessStatement : Prop :=
  ∀ (Γ : Set Formula) (f : Formula),
    semanticallyImplies Γ f →
    ∃ (Δ : Finset Formula),
      ((Δ : Set Formula) ⊆ Γ) ∧
      semanticallyImplies ((Δ : Set Formula)) f

theorem strongCompleteness_holds : strongCompletenessStatement :=
  strong_completeness

/-! ## Decidability of Propositional Tautology

Propositional logic is decidable: the truth-table method enumerates
all 2^n Boolean assignments to the atoms occurring in a formula.
-/

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

/-- Every atom in a formula is at most its maxAtom. -/
theorem Formula.atom_le_maxAtom (f : Formula) : ∀ n ∈ f.atoms, n ≤ f.maxAtom := by
  induction f with
  | atom m => simp [Formula.atoms, Formula.maxAtom]
  | true => simp [Formula.atoms]
  | false => simp [Formula.atoms]
  | not A ih => simp [Formula.atoms, Formula.maxAtom]; exact ih
  | and A B ihA ihB =>
    simp [Formula.atoms, Formula.maxAtom]
    intro n hn
    rcases List.mem_append.mp hn with (hnA | hnB)
    · exact Nat.le_trans (ihA n hnA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB n hnB) (Nat.le_max_right _ _)
  | or A B ihA ihB =>
    simp [Formula.atoms, Formula.maxAtom]
    intro n hn
    rcases List.mem_append.mp hn with (hnA | hnB)
    · exact Nat.le_trans (ihA n hnA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB n hnB) (Nat.le_max_right _ _)
  | impl A B ihA ihB =>
    simp [Formula.atoms, Formula.maxAtom]
    intro n hn
    rcases List.mem_append.mp hn with (hnA | hnB)
    · exact Nat.le_trans (ihA n hnA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB n hnB) (Nat.le_max_right _ _)
  | equiv A B ihA ihB =>
    simp [Formula.atoms, Formula.maxAtom]
    intro n hn
    rcases List.mem_append.mp hn with (hnA | hnB)
    · exact Nat.le_trans (ihA n hnA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB n hnB) (Nat.le_max_right _ _)

/-- Evaluation depends only on the atoms that appear in the formula.
    If two assignments agree on all atoms of f, eval agrees. -/
theorem Formula.eval_depends_only_on_atoms (f : Formula) (a b : Nat → Bool)
    (h : ∀ n, n ∈ f.atoms → a n = b n) : f.eval a = f.eval b := by
  induction f with
  | atom n => simp [Formula.eval, Formula.atoms]; exact h n (by simp)
  | true => rfl
  | false => rfl
  | not A ih => simp [Formula.eval, Formula.atoms]; exact ih a b (λ n hn => h n (by simpa using hn))
  | and A B ihA ihB =>
    simp [Formula.eval, Formula.atoms]
    have hA : ∀ n, n ∈ A.atoms → a n = b n := λ n hn => h n (List.mem_append_left _ hn)
    have hB : ∀ n, n ∈ B.atoms → a n = b n := λ n hn => h n (List.mem_append_right _ hn)
    rw [ihA a b hA, ihB a b hB]
  | or A B ihA ihB =>
    simp [Formula.eval, Formula.atoms]
    have hA : ∀ n, n ∈ A.atoms → a n = b n := λ n hn => h n (List.mem_append_left _ hn)
    have hB : ∀ n, n ∈ B.atoms → a n = b n := λ n hn => h n (List.mem_append_right _ hn)
    rw [ihA a b hA, ihB a b hB]
  | impl A B ihA ihB =>
    simp [Formula.eval, Formula.atoms]
    have hA : ∀ n, n ∈ A.atoms → a n = b n := λ n hn => h n (List.mem_append_left _ hn)
    have hB : ∀ n, n ∈ B.atoms → a n = b n := λ n hn => h n (List.mem_append_right _ hn)
    rw [ihA a b hA, ihB a b hB]
  | equiv A B ihA ihB =>
    simp [Formula.eval, Formula.atoms]
    have hA : ∀ n, n ∈ A.atoms → a n = b n := λ n hn => h n (List.mem_append_left _ hn)
    have hB : ∀ n, n ∈ B.atoms → a n = b n := λ n hn => h n (List.mem_append_right _ hn)
    rw [ihA a b hA, ihB a b hB]

/-- Decode an integer as a Boolean assignment: atom j is true
    iff the j-th binary digit of i is 1. -/
def decodeAssign (i : Nat) : Nat → Bool :=
  λ j => ((i / (2 : Nat) ^ j) % 2 = 1)

/-- Encode a Boolean assignment (restricted to the first k atoms)
    as an integer: sum_{j=0}^{k-1} (if a j then 2^j else 0). -/
def encodeAssign (k : Nat) (a : Nat → Bool) : Nat :=
  (List.range k).foldl (λ acc j => if a j then acc + 2 ^ j else acc) 0

/-- The encoding of a restricted assignment fits in k bits. -/
theorem encodeAssign_lt (k : Nat) (a : Nat → Bool) : encodeAssign k a < 2 ^ k := by
  induction k with
  | zero => simp [encodeAssign]
  | succ k ih =>
    simp [encodeAssign, List.range_succ, List.foldl_append]
    split
    · -- a k = true: we add 2^k
      have h_sum : encodeAssign k a + 2 ^ k < 2 ^ k + 2 ^ k :=
        Nat.add_lt_add_right ih (2 ^ k)
      have h_pow : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
        simp [Nat.pow_succ, mul_two]
      omega
    · -- a k = false: no addition, just the inductive bound
      have h_lt : encodeAssign k a < 2 ^ k := ih
      have h_pow_lt : 2 ^ k < 2 ^ (k + 1) := by
        simp [Nat.pow_succ]
        omega
      omega

/-- Decoding the encoding recovers the original assignment on the first k atoms.
    (Proof sketch: the j-th binary digit of the sum equals a j because all
    higher bits are multiples of 2^(j+1) and all lower bits sum to < 2^j.
    Follows by strong induction on k - j using elementary properties of Nat division.) -/
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
    · -- j < k: the k-th bit doesn't affect position j
      by_cases hak : a k
      · -- a k = true, we added 2^k; show (x + 2^k)/2^j % 2 = x/2^j % 2
        simp [hak]
        have hdvd : 2 ^ j ∣ 2 ^ k := Nat.pow_dvd_pow (2 : Nat) (Nat.le_of_lt hj_lt)
        -- Use add_comm to make 2^k the first argument, since add_div_of_dvd expects d ∣ first arg
        have h_div : (x + 2 ^ k) / 2 ^ j = x / 2 ^ j + 2 ^ k / 2 ^ j := by
          calc
            (x + 2 ^ k) / 2 ^ j = (2 ^ k + x) / 2 ^ j := by rw [Nat.add_comm]
            _ = 2 ^ k / 2 ^ j + x / 2 ^ j := Nat.add_div_of_dvd hdvd
            _ = x / 2 ^ j + 2 ^ k / 2 ^ j := by rw [Nat.add_comm]
        have h_pow_div : 2 ^ k / 2 ^ j = 2 ^ (k - j) := by
          have h_eq : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by
            rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hj_lt)]
          rw [h_eq]
          exact Nat.mul_div_cancel_left _ (Nat.pow_pos (by norm_num) j)
        have h_mod : (2 ^ k / 2 ^ j) % 2 = 0 := by
          rw [h_pow_div]
          induction (k - j) with
          | zero => simp
          | succ n ih' => simp [Nat.pow_succ, mul_two]
        rw [h_div, h_mod, add_zero]
        exact ih j hj_lt
      · -- a k = false, no addition
        simp [hak]
        exact ih j hj_lt
    · -- j = k: (x + (if a k then 2^k else 0)) / 2^k % 2 = a k
      have h_div : x / 2 ^ k = 0 := Nat.div_eq_of_lt hx_lt
      by_cases hak : a k
      · simp [hak, h_div]
      · simp [hak, h_div]

/-- Generate a list of all 2^k Boolean assignments (via integer encoding). -/
def allAssignments (k : Nat) : List (Nat → Bool) :=
  (List.range (2 ^ k)).map decodeAssign

/-- Check whether a formula is a tautology by enumerating all assignments
    to the atoms 0..maxAtom. Atoms beyond maxAtom are fixed to false. -/
def decideTautology (f : Formula) : Bool :=
  let k := f.maxAtom + 1
  (allAssignments k).all (λ a => f.eval a == true)

/--
Soundness of `decideTautology`. Since `allAssignments k` covers every
possible combination of truth values for atoms 0..k-1, and all atoms
of f are ≤ maxAtom < k, `eval_depends_only_on_atoms` guarantees that
if all enumerated assignments give true, then every assignment does.

The proof uses `encodeAssign` to map any assignment to an index i < 2^k
whose decoding agrees with the original on atoms ≤ maxAtom, then applies
the `decode_encode_eq` lemma.
-/
theorem decideTautology_sound (f : Formula) : decideTautology f = true → isTautology f := by
  intro h a
  unfold decideTautology at h
  have hall_true : ∀ x ∈ allAssignments (f.maxAtom + 1), f.eval x = true := by
    have hlist := List.all_eq_true.mp h
    intro x hx
    have hx' := hlist x hx
    cases f.eval x with
    | true => rfl
    | false => simp at hx'
  let a_restricted : Nat → Bool := λ n => if n < f.maxAtom + 1 then a n else false
  -- a_restricted matches a on all atoms of f (since atoms are ≤ maxAtom)
  have h_agree : ∀ n, n ∈ f.atoms → a n = a_restricted n := by
    intro n hn
    have hnle : n ≤ f.maxAtom := Formula.atom_le_maxAtom f n hn
    simp [a_restricted, Nat.lt_succ_of_le hnle]
  -- a_restricted is exactly decodeAssign of its encoding
  let i := encodeAssign (f.maxAtom + 1) a_restricted
  have h_decode : a_restricted = decodeAssign i := by
    funext n
    by_cases hnlt : n < f.maxAtom + 1
    · rw [decode_encode_eq (f.maxAtom + 1) n a_restricted hnlt]
      simp [a_restricted, hnlt]
    · simp [a_restricted, decodeAssign, encodeAssign, hnlt]
  have hi_mem : decodeAssign i ∈ allAssignments (f.maxAtom + 1) := by
    unfold allAssignments
    apply List.mem_map.mpr
    refine ⟨i, ?_, rfl⟩
    have hi_lt : i < 2 ^ (f.maxAtom + 1) := encodeAssign_lt _ _
    exact List.mem_range.mpr hi_lt
  -- Now chain everything together
  calc
    f.eval a = f.eval a_restricted :=
      Formula.eval_depends_only_on_atoms f a a_restricted h_agree
    _ = f.eval (decodeAssign i) := by rw [h_decode]
    _ = true := hall_true (decodeAssign i) hi_mem

/-- Completeness: if f is a tautology, decideTautology reports true. -/
theorem decideTautology_complete (f : Formula) : isTautology f → decideTautology f = true := by
  intro htaut
  unfold decideTautology
  apply List.all_eq_true.mpr
  intro a ha
  have htrue := htaut a
  simp [htrue]

/-- The set of propositional tautologies is decidable. -/
theorem decidability_holds : ∃ (algo : Formula → Bool), ∀ (f : Formula), algo f = true ↔ isTautology f := by
  refine ⟨decideTautology, λ f => ?_⟩
  constructor
  · exact decideTautology_sound f
  · exact decideTautology_complete f

/-! ## Compactness

Compactness theorem for propositional logic: if every finite subset
of a set of formulas is satisfiable, then the whole set is satisfiable.

Equivalent to Tychonoff's theorem for {0,1}^Nat (products of compact spaces).
-/

def compactnessStatement : Prop :=
  ∀ (Γ : Set Formula),
    (∀ (Δ : Set Formula), Δ ⊆ Γ → Set.Finite Δ → isSatisfiableSet Δ) →
    isSatisfiableSet Γ

/-!
Proof sketch for compactness:
1. Each formula f defines a basic clopen set V(f) = {σ | f.eval σ = true}
   in the product topology on {0,1}^Nat.
2. The hypothesis says every finite intersection of V(f) for f∈Γ is nonempty
   (by satisfiability of finite subsets).
3. {0,1}^Nat is compact by Tychonoff's theorem: {0,1} is finite (hence compact),
   and arbitrary products of compact spaces are compact.
4. In a compact space, any family of closed sets satisfying the finite
   intersection property has nonempty total intersection.
5. Thus ∩_{f∈Γ} V(f) ≠ ∅, yielding an assignment satisfying Γ.
-/

/-! ## #eval Examples -/

def tautExample : Formula := .or (.atom 0) (.not (.atom 0))
def nonTautExample : Formula := .and (.atom 0) (.atom 1)
def implRefl : Formula := .impl (.atom 0) (.atom 0)

#eval decideTautology tautExample
#eval decideTautology nonTautExample
#eval decideTautology implRefl
#eval decideTautology (.equiv (.atom 0) (.atom 0))
#eval decideTautology (.impl (.and (.atom 0) (.atom 1)) (.atom 0))

-- Verify consistency: the contradictory formula is never a tautology
#eval decideTautology (.or (.atom 0) (.not (.atom 0)))
#eval decideTautology (.and (.atom 0) (.not (.atom 0)))
#eval decideTautology (.impl (.and (.atom 0) (.atom 1)) (.or (.atom 0) (.atom 1)))

end MiniLogicKernel
