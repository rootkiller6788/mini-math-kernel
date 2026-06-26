filepath = r"F:\nano-everything\mini-everything-math\0. mini-math-kernel\mini-logic-kernel\MiniLogicKernel\Core\Basic.lean"

with open(filepath, 'r', encoding='utf-8') as f:
    content = f.read()

print(f"Initial sorries: {content.count('sorry')}")

# ALL replacements done at once before any write

# 1. atom_le_maxAtom
old1 = '  sorry\n\n/-- Evaluation of a formula'
new1 = '''  induction f with
  | atom m => simp [Formula.atoms, Formula.maxAtom]
  | true => simp [Formula.atoms]
  | false => simp [Formula.atoms]
  | not A ih => simp [Formula.atoms, Formula.maxAtom]; exact ih
  | and A B ihA ihB =>
    simp [Formula.atoms, Formula.maxAtom]
    intro n hn
    rcases (mem_append (l₁ := Formula.atoms A) (l₂ := Formula.atoms B)).mp hn with (hnA | hnB)
    · exact Nat.le_trans (ihA n hnA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB n hnB) (Nat.le_max_right _ _)
  | or A B ihA ihB =>
    simp [Formula.atoms, Formula.maxAtom]
    intro n hn
    rcases (mem_append (l₁ := Formula.atoms A) (l₂ := Formula.atoms B)).mp hn with (hnA | hnB)
    · exact Nat.le_trans (ihA n hnA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB n hnB) (Nat.le_max_right _ _)
  | impl A B ihA ihB =>
    simp [Formula.atoms, Formula.maxAtom]
    intro n hn
    rcases (mem_append (l₁ := Formula.atoms A) (l₂ := Formula.atoms B)).mp hn with (hnA | hnB)
    · exact Nat.le_trans (ihA n hnA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB n hnB) (Nat.le_max_right _ _)
  | equiv A B ihA ihB =>
    simp [Formula.atoms, Formula.maxAtom]
    intro n hn
    rcases (mem_append (l₁ := Formula.atoms A) (l₂ := Formula.atoms B)).mp hn with (hnA | hnB)
    · exact Nat.le_trans (ihA n hnA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB n hnB) (Nat.le_max_right _ _)

/-- Evaluation of a formula'''
content = content.replace(old1, new1)
print(f"  After #1: {content.count('sorry')} sorries")

# 2. eval_depends_only_on_atoms
old2 = '    (h : ∀ n, n ∈ f.atoms → a n = b n) : f.eval a = f.eval b := by\n  sorry'
new2 = '''    (h : ∀ n, n ∈ f.atoms → a n = b n) : f.eval a = f.eval b := by
  induction f with
  | atom n =>
    simp [Formula.eval]
    exact h n (by simp [Formula.atoms])
  | true => rfl
  | false => rfl
  | not A ih =>
    simp [Formula.eval]
    rw [ih]
    intro n hn
    apply h n
    simp [Formula.atoms, hn]
  | and A B ihA ihB =>
    simp [Formula.eval]
    have hA : ∀ n, n ∈ A.atoms → a n = b n := λ n hn =>
      h n (mem_append_left (l₁ := Formula.atoms A) (l₂ := Formula.atoms B) hn)
    have hB : ∀ n, n ∈ B.atoms → a n = b n := λ n hn =>
      h n (mem_append_right (l₁ := Formula.atoms A) (l₂ := Formula.atoms B) hn)
    rw [ihA hA, ihB hB]
  | or A B ihA ihB =>
    simp [Formula.eval]
    have hA : ∀ n, n ∈ A.atoms → a n = b n := λ n hn =>
      h n (mem_append_left (l₁ := Formula.atoms A) (l₂ := Formula.atoms B) hn)
    have hB : ∀ n, n ∈ B.atoms → a n = b n := λ n hn =>
      h n (mem_append_right (l₁ := Formula.atoms A) (l₂ := Formula.atoms B) hn)
    rw [ihA hA, ihB hB]
  | impl A B ihA ihB =>
    simp [Formula.eval]
    have hA : ∀ n, n ∈ A.atoms → a n = b n := λ n hn =>
      h n (mem_append_left (l₁ := Formula.atoms A) (l₂ := Formula.atoms B) hn)
    have hB : ∀ n, n ∈ B.atoms → a n = b n := λ n hn =>
      h n (mem_append_right (l₁ := Formula.atoms A) (l₂ := Formula.atoms B) hn)
    rw [ihA hA, ihB hB]
  | equiv A B ihA ihB =>
    simp [Formula.eval]
    have hA : ∀ n, n ∈ A.atoms → a n = b n := λ n hn =>
      h n (mem_append_left (l₁ := Formula.atoms A) (l₂ := Formula.atoms B) hn)
    have hB : ∀ n, n ∈ B.atoms → a n = b n := λ n hn =>
      h n (mem_append_right (l₁ := Formula.atoms A) (l₂ := Formula.atoms B) hn)
    rw [ihA hA, ihB hB]'''
content = content.replace(old2, new2)
print(f"  After #2: {content.count('sorry')} sorries")

# 3. encodeAssign helper lemmas + encodeAssign_lt
old3 = '/-- Recursive unfolding of encodeAssign. -/\ntheorem encodeAssign_lt (k : Nat) (a : Nat → Bool) : encodeAssign k a < 2 ^ k := by\n  sorry'
new3 = '''/-- Recursive unfolding of encodeAssign. -/
private lemma encodeAssign_succ (k : Nat) (a : Nat → Bool) :
    encodeAssign (k+1) a = encodeAssign k a + (if a k then 2 ^ k else 0) := by
  simp [encodeAssign, List.range_succ, List.foldl_append]

/-- (x + d*q) / d = x/d + q when d > 0 (no carry from remainder). -/
private lemma div_add_mul_of_pos {x d q : Nat} (hd : 0 < d) : (x + d * q) / d = x / d + q := by
  have hx := Nat.div_add_mod x d
  have hsum : x + d * q = (x / d + q) * d + x % d := by
    rw [hx]
    ring
  have hmod_lt : x % d < d := Nat.mod_lt x hd
  have h_lower : (x / d + q) * d ≤ x + d * q := by
    rw [hsum]
    exact Nat.le_add_right _ _
  have h_upper : x + d * q < (x / d + q + 1) * d := by
    rw [hsum]
    have hlt : (x / d + q) * d + x % d < (x / d + q) * d + d :=
      Nat.add_lt_add_left hmod_lt _
    calc
      (x / d + q) * d + x % d < (x / d + q) * d + d := hlt
      _ = (x / d + q + 1) * d := by ring
  have h_lower' : d * (x / d + q) ≤ x + d * q := by
    rw [Nat.mul_comm]; exact h_lower
  have h_upper' : x + d * q < d * (x / d + q + 1) := by
    rw [Nat.mul_comm]; exact h_upper
  exact Nat.div_eq_of_lt_le h_lower' h_upper'

theorem encodeAssign_lt (k : Nat) (a : Nat → Bool) : encodeAssign k a < 2 ^ k := by
  induction k with
  | zero =>
    simp [encodeAssign, List.range]
  | succ k ih =>
    rw [encodeAssign_succ k a]
    by_cases hk : a k
    · simp [hk]
      have h_sum : encodeAssign k a + 2 ^ k < 2 ^ k + 2 ^ k :=
        Nat.add_lt_add_right ih (2 ^ k)
      have h_eq : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
        simp [Nat.pow_succ, Nat.two_mul]
      exact Nat.lt_of_lt_of_eq h_sum h_eq
    · simp [hk]
      have h_le : 2 ^ k ≤ 2 ^ (k + 1) := by
        rw [Nat.pow_succ]
        calc
          2 ^ k = 2 ^ k * 1 := by simp
          _ ≤ 2 ^ k * 2 := Nat.mul_le_mul_left (2 ^ k) (by decide : 1 ≤ 2)
      exact Nat.lt_of_lt_of_le ih h_le'''
content = content.replace(old3, new3)
print(f"  After #3: {content.count('sorry')} sorries")

# 4. decode_encode_eq
old4 = 'theorem decode_encode_eq (k j : Nat) (a : Nat → Bool) (hj : j < k) :\n    decodeAssign (encodeAssign k a) j = a j := by\n  sorry'
new4 = '''theorem decode_encode_eq (k j : Nat) (a : Nat → Bool) (hj : j < k) :
    decodeAssign (encodeAssign k a) j = a j := by
  induction k with
  | zero => exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    rw [encodeAssign_succ k a]
    unfold decodeAssign
    by_cases hak : a k
    · simp [hak]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with (h_lt | h_eq)
      · have h_enc_lt : encodeAssign k a < 2 ^ k := encodeAssign_lt k a
        have h_dvd : (2 ^ j) ∣ (2 ^ k) := Nat.pow_dvd_pow 2 (Nat.le_of_lt h_lt)
        rcases h_dvd with ⟨m, hm⟩
        have hpos : 0 < 2 ^ j := Nat.pos_pow_of_pos _ (by decide : 0 < 2)
        have h_div_sum : (encodeAssign k a + (2 ^ j) * m) / (2 ^ j) =
            encodeAssign k a / (2 ^ j) + m :=
          div_add_mul_of_pos hpos
        rw [hm, h_div_sum]
        have hm_even : m % 2 = 0 := by
          have h_dvd2 : (2 ^ (j + 1)) ∣ (2 ^ k) :=
            Nat.pow_dvd_pow 2 (Nat.succ_le_of_lt h_lt)
          rw [hm] at h_dvd2
          rw [Nat.pow_succ] at h_dvd2
          have h_dvd_m : 2 ∣ m :=
            Nat.dvd_of_mul_dvd_mul_left hpos h_dvd2
          exact Nat.mod_eq_zero_of_dvd h_dvd_m
        rw [Nat.add_mod, hm_even, add_zero]
        exact ih j h_lt
      · subst h_eq
        have h_enc_lt : encodeAssign k a < 2 ^ k := encodeAssign_lt k a
        have hpos : 0 < 2 ^ k := Nat.pos_pow_of_pos _ (by decide : 0 < 2)
        have h_div_sum : (encodeAssign k a + (2 ^ k) * 1) / (2 ^ k) =
            encodeAssign k a / (2 ^ k) + 1 :=
          div_add_mul_of_pos hpos
        have h_div_enc : encodeAssign k a / (2 ^ k) = 0 := Nat.div_eq_of_lt h_enc_lt
        have h_result : (encodeAssign k a + 2 ^ k) / (2 ^ k) = 1 := by
          simpa [h_div_enc] using h_div_sum
        simp [h_result]
    · simp [hak]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with (h_lt | h_eq)
      · exact ih j h_lt
      · subst h_eq
        have h_enc_lt : encodeAssign k a < 2 ^ k := encodeAssign_lt k a
        have h_div : encodeAssign k a / (2 ^ k) = 0 := Nat.div_eq_of_lt h_enc_lt
        simp [h_div]'''
content = content.replace(old4, new4)
print(f"  After #4: {content.count('sorry')} sorries")

# 5. decideTautology_sound
old5 = 'theorem decideTautology_sound (f : Formula) : decideTautology f = true → isTautology f := by\n  sorry'
new5 = '''theorem decideTautology_sound (f : Formula) : decideTautology f = true → isTautology f := by
  intro h_chk σ
  unfold decideTautology at h_chk
  let k := f.maxAtom + 1
  have h_all_mem : ∀ (l : List (Nat → Bool)) (p : (Nat → Bool) → Bool) (a : Nat → Bool),
      l.all p = true → a ∈ l → p a = true := by
    intro l p a hall hmem
    induction l with
    | nil => simp at hmem
    | cons x xs ih =>
      simp at hmem ⊢
      rcases hmem with (rfl | hmem')
      · simp at hall
        cases hp : p x
        · simp [hp] at hall
        · rfl
      · simp at hall
        cases hp : p x
        · simp [hp] at hall
        · exact ih hall hmem'
  let i := encodeAssign k σ
  have hi_lt : i < 2 ^ k := encodeAssign_lt k σ
  have hi_mem : decodeAssign i ∈ allAssignmentsNat k := by
    unfold allAssignmentsNat
    apply List.mem_map.mpr
    exact ⟨i, by simp [hi_lt], rfl⟩
  have h_eval_true : (f.eval (decodeAssign i) == true) = true :=
    h_all_mem (allAssignmentsNat k) (λ a => f.eval a == true) (decodeAssign i) h_chk hi_mem
  have h_val : f.eval (decodeAssign i) = true := by
    simpa using h_eval_true
  have h_eval_eq : f.eval σ = f.eval (decodeAssign i) := by
    apply Formula.eval_depends_only_on_atoms f σ (decodeAssign i)
    intro n hn
    have hn_le : n ≤ f.maxAtom := Formula.atom_le_maxAtom f n hn
    have hn_lt_k : n < k := Nat.lt_succ_of_le hn_le
    rw [decode_encode_eq k n σ hn_lt_k]
    rfl
  rw [h_eval_eq, h_val]'''
content = content.replace(old5, new5)
print(f"  After #5: {content.count('sorry')} sorries")

# 6. decideTautology_complete
old6 = 'theorem decideTautology_complete (f : Formula) : isTautology f → decideTautology f = true := by\n  sorry'
new6 = '''theorem decideTautology_complete (f : Formula) : isTautology f → decideTautology f = true := by
  intro h_taut
  unfold decideTautology
  have h_val : ∀ (a : Nat → Bool), f.eval a == true := by
    intro a
    have h := h_taut a
    simp [h]
  induction (allAssignmentsNat (f.maxAtom + 1)) with
  | nil => rfl
  | cons x xs ih =>
    simp [h_val x, ih]'''
content = content.replace(old6, new6)
print(f"  After #6: {content.count('sorry')} sorries")

# Write back (only once at the end!)
with open(filepath, 'w', encoding='utf-8', newline='') as f:
    f.write(content)

print("ALL DONE!")
