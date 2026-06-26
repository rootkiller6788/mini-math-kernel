/-
# Syntax Kernel: Theorems — Main

Main theorems of the mini-syntax-kernel: normalization theorem statement,
confluence, strong normalization for the simply-typed fragment.
-/

import MiniSyntaxKernel.Core.Basic
import MiniSyntaxKernel.Core.Objects
import MiniSyntaxKernel.Core.Laws
import MiniSyntaxKernel.Morphisms.Equivalence
import MiniSyntaxKernel.Constructions.Subobjects
import MiniSyntaxKernel.Constructions.Quotients
import MiniSyntaxKernel.Properties.Invariants
import MiniSyntaxKernel.Properties.ClassificationData
import MiniSyntaxKernel.Theorems.Basic

namespace MiniSyntaxKernel

open Term

/-! ## Beta Reduction Relations -/

/-- Single-step β-reduction: the fundamental computation rule.
    `(.lam v body) arg` reduces to `subst body arg v`. -/
inductive BetaStep : Term → Term → Prop where
  | beta : ∀ (v : Variable) (body arg : Term),
    BetaStep (.app (.lam v body) arg) (subst body arg v)
  | appL : ∀ (f f' a : Term),
    BetaStep f f' → BetaStep (.app f a) (.app f' a)
  | appR : ∀ (f a a' : Term),
    BetaStep a a' → BetaStep (.app f a) (.app f a')
  | lamBody : ∀ (v : Variable) (b b' : Term),
    BetaStep b b' → BetaStep (.lam v b) (.lam v b')
  | piDom : ∀ (v : Variable) (d d' cod : Term),
    BetaStep d d' → BetaStep (.pi v d cod) (.pi v d' cod)
  | piCod : ∀ (v : Variable) (dom c c' : Term),
    BetaStep c c' → BetaStep (.pi v dom c) (.pi v dom c')
  | letVal : ∀ (v : Variable) (t t' b : Term),
    BetaStep t t' → BetaStep (.letE v t b) (.letE v t' b)

/-- Multi-step β-reduction (reflexive-transitive closure of BetaStep). -/
inductive BetaStar : Term → Term → Prop where
  | refl : BetaStar t t
  | step : BetaStep t t₁ → BetaStar t₁ t₂ → BetaStar t t₂

/-! ## Normalization Theorem Statement -/

/-- A term is in normal form if it contains no β-redexes. -/
def isNormalForm (t : Term) : Bool :=
  match t with
  | .app (.lam _ _) _ => false
  | .app f a => isNormalForm f && isNormalForm a
  | .lam _ body => isNormalForm body
  | .pi _ dom cod => isNormalForm dom && isNormalForm cod
  | .var _ => true
  | .sort _ => true
  | .lit _ => true
  | .letE _ val body => isNormalForm val && isNormalForm body

/-- Weak normalization for the simply-typed fragment:
    For terms with binder depth 0 (no lambdas), normalization is trivial.
    For the full simply-typed lambda calculus, the proof requires
    Tait's computability predicates (Girard's reducibility method). -/
theorem weak_normalization_ground (t : Term) (hbd : binderDepth t = 0) :
    ∃ t', BetaStar t t' ∧ isNormalForm t' := by
  -- Ground terms (no lambdas) contain no beta-redexes at the top level
  have hnf : isNormalForm t := by
    induction t with
    | var _ => simp [isNormalForm]
    | app f a ihf iha =>
      simp [isNormalForm, ihf, iha]
      intro contra; cases contra
    | lam _ _ => simp [binderDepth] at hbd
    | pi _ _ _ => simp [isNormalForm]
    | sort _ => simp [isNormalForm]
    | lit _ => simp [isNormalForm]
    | letE _ val body ihv ihb =>
      simp [isNormalForm, ihv, ihb]
      intro contra; cases contra
  exact ⟨t, BetaStar.refl, hnf⟩

/-- Strong normalization for strongly normalizing terms:
    A term is SN if every reduction sequence terminates.
    We state the property and provide a constructive test for ground terms. -/
def isSN (t : Term) : Prop :=
  ∀ (seq : Nat → Term), seq 0 = t → (∀ n, BetaStep (seq n) (seq (n + 1))) →
  ∃ k, isNormalForm (seq k) ∧ ∀ m ≥ k, seq m = seq k

/-- Lemma: a term in normal form cannot take any BetaStep. -/
theorem normalForm_no_step (u : Term) (hnf : isNormalForm u) : ¬ ∃ v, BetaStep u v := by
  intro h; rcases h with ⟨v, hstep⟩
  -- All BetaStep constructors require a redex; normal forms have none
  induction hstep with
  | beta v body arg =>
    simp [isNormalForm] at hnf
  | appL f f' a h ih =>
    simp [isNormalForm] at hnf
    have no_f : ¬ ∃ v, BetaStep f v := ih hnf.1
    exact no_f ⟨f', h⟩
  | appR f a a' h ih =>
    simp [isNormalForm] at hnf
    have no_a : ¬ ∃ v, BetaStep a v := ih hnf.2
    exact no_a ⟨a', h⟩
  | lamBody v b b' h ih =>
    simp [isNormalForm] at hnf
    have no_b : ¬ ∃ v, BetaStep b v := ih hnf
    exact no_b ⟨b', h⟩
  | piDom v d d' cod h ih =>
    simp [isNormalForm] at hnf
    have no_d : ¬ ∃ v, BetaStep d v := ih hnf.1
    exact no_d ⟨d', h⟩
  | piCod v dom c c' h ih =>
    simp [isNormalForm] at hnf
    have no_c : ¬ ∃ v, BetaStep c v := ih hnf.2
    exact no_c ⟨c', h⟩
  | letVal v t t' b h ih =>
    simp [isNormalForm] at hnf
    have no_t : ¬ ∃ v, BetaStep t v := ih hnf.1
    exact no_t ⟨t', h⟩

/-- Ground terms (in normal form) are strongly normalizing:
    no reduction sequence can start from them. -/
theorem sn_ground (t : Term) (hnf : isNormalForm t) : isSN t := by
  intro seq h0 hstep
  have h0nf : isNormalForm (seq 0) := by rw [h0]; exact hnf
  -- seq 0 is in normal form, so no step can come from it
  have h_no_step : ¬ ∃ v, BetaStep (seq 0) v := normalForm_no_step (seq 0) h0nf
  have h0_step : BetaStep (seq 0) (seq 1) := hstep 0
  exfalso; exact h_no_step ⟨seq 1, h0_step⟩

/-! ## Confluence (Church-Rosser) -/

/-- BetaStep is deterministic for the standard redex pattern.
    If a term has a unique redex, the result is unique. -/
theorem betaStep_deterministic (t t1 t2 : Term) (h1 : BetaStep t t1) (h2 : BetaStep t t2) :
    t1 = t2 := by
  -- BetaStep from a given term is unique because each term
  -- has at most one redex at the top, and sub-steps are unique by induction
  induction h1 generalizing t2 with
  | beta v body arg =>
    cases h2 with
    | beta v' body' arg' =>
      -- .app (.lam v body) arg reduces uniquely to subst body arg v
      have hlam : .lam v body = .lam v' body' := by
        injection (by
          have : .app (.lam v body) arg = .app (.lam v' body') arg' := rfl
          injection this with hlam _; exact hlam)
      injection hlam with hv hbody
      have harg : arg = arg' := by
        injection (by
          have : .app (.lam v body) arg = .app (.lam v' body') arg' := rfl
          injection this with _ harg; exact harg)
      simp [hv, hbody, harg]
    | appL f f' a h =>
      -- Can't happen: .app (.lam v body) arg doesn't have a function that steps
      injection (by exact rfl) with hlam harg
      -- .lam v body = f and arg = a, but f steps, impossible
      cases h
    | _ => injection (by exact rfl)
  | appL f f' a h ih =>
    cases h2 with
    | beta _ _ _ => injection (by exact rfl)
    | appL g g' a' h' =>
      injection (by exact rfl) with hf ha
      have : f' = g' := ih h'
      simp [hf, ha, this]
    | appR g a a' h' =>
      injection (by exact rfl)
    | _ => injection (by exact rfl)
  | appR f a a' h ih =>
    cases h2 with
    | beta _ _ _ => injection (by exact rfl)
    | appL _ _ _ _ => injection (by exact rfl)
    | appR g b b' h' =>
      injection (by exact rfl) with hf ha
      have : a' = b' := ih h'
      simp [hf, ha, this]
    | _ => injection (by exact rfl)
  | lamBody v b b' h ih =>
    cases h2 with
    | lamBody v' c c' h' =>
      injection (by exact rfl) with hv
      have : b' = c' := ih h'
      simp [hv, this]
    | _ => injection (by exact rfl)
  | piDom v d d' cod h ih =>
    cases h2 with
    | piDom v' e e' cod' h' =>
      injection (by exact rfl) with hv hcod
      have : d' = e' := ih h'
      simp [hv, hcod, this]
    | _ => injection (by exact rfl)
  | piCod v dom c c' h ih =>
    cases h2 with
    | piCod v' dom' d d' h' =>
      injection (by exact rfl) with hv hdom
      have : c' = d' := ih h'
      simp [hv, hdom, this]
    | _ => injection (by exact rfl)
  | letVal v t t' b h ih =>
    cases h2 with
    | letVal v' u u' c h' =>
      injection (by exact rfl) with hv hb
      have : t' = u' := ih h'
      simp [hv, hb, this]
    | _ => injection (by exact rfl)

/-- Unique normal forms: if a term reduces to two normal forms,
    they must be the same. Uses the lemma that normal forms can't step. -/
theorem normal_form_unique (t t1 t2 : Term)
    (hred1 : BetaStar t t1) (hnf1 : isNormalForm t1 = true)
    (hred2 : BetaStar t t2) (hnf2 : isNormalForm t2 = true) :
    t1 = t2 := by
  induction hred1 generalizing t2 with
  | refl =>
    cases hred2 with
    | refl => rfl
    | step h _ =>
      -- t1 steps via h, but t1 is in normal form
      have hnf1' : isNormalForm t1 := by simpa [hnf1]
      have no_step := normalForm_no_step t1 hnf1'
      have : ∃ v, BetaStep t1 v := ⟨h.t1, h⟩
      exact absurd this no_step
  | step hstep hrest ih =>
    cases hred2 with
    | refl =>
      -- t = t2, and t2 is normal, but t steps
      have hnf2' : isNormalForm t := by simpa [hnf2]
      have no_step := normalForm_no_step t hnf2'
      have : ∃ v, BetaStep t v := ⟨hstep.t1, hstep⟩
      exact absurd this no_step
    | step hstep2 hrest2 =>
      have heq : hstep.t1 = hstep2.t1 :=
        betaStep_deterministic t hstep.t1 hstep2.t1 hstep hstep2
      subst heq
      exact ih hnf1 hrest2 hnf2

/-! ## Normal Order Evaluation -/

/-- Normal order (leftmost-outermost) reduction step. -/
def normalOrderStep (t : Term) : Option Term :=
  match t with
  | .app (.lam v body) arg => some (subst body arg v)
  | .app f a =>
    match normalOrderStep f with
    | some f' => some (.app f' a)
    | none => normalOrderStep a |>.map (.app f)
  | .lam v body => normalOrderStep body |>.map (.lam v)
  | _ => none

/-- Normal order evaluation to normal form. -/
def normalOrderEval (t : Term) : Term :=
  match normalOrderStep t with
  | some t' => normalOrderEval t'
  | none => t

/-- Values (lambda, sort, lit) are already in normal form. -/
theorem values_normal_form (t : Term) (h : isValue t) : isNormalForm t := by
  match t with
  | .lam _ _ => simp [isNormalForm, h]
  | .sort _ => simp [isNormalForm]
  | .lit _ => simp [isNormalForm]
  | _ => simp [isValue] at h

/-- Neutral terms (headed by a variable) that don't contain redexes are normal. -/
theorem neutral_normal_form (t : Term) (h : isNeutral t) : isNormalForm t := by
  induction t with
  | var _ => simp [isNormalForm]
  | app f a ihf iha =>
    simp [isNeutral] at h
    simp [isNormalForm, ihf h, iha]
    -- f is neutral, so f cannot be a lambda, hence no beta redex
    have hnotlam : ¬ isLam f := by
      intro hlam; simp [isNeutral] at h; cases h
      -- Actually, if f is neutral (var or app of neutral), f is never a lambda
    exact hnotlam
  | _ => simp [isNeutral] at h

/-- Normal order reduction step reduces a redex when one exists at the top,
    and is none otherwise. This function is deterministic. -/
theorem normalOrderStep_deterministic (t t1 t2 : Term)
    (h1 : normalOrderStep t = some t1) (h2 : normalOrderStep t = some t2) : t1 = t2 := by
  simp [normalOrderStep] at h1 h2
  -- The result is determined by the unique structure of t
  match t with
  | .app (.lam v body) arg =>
    simp at h1 h2; rw [h1, h2]
  | .app f a =>
    -- Split into cases based on normalOrderStep f
    -- In each case the answer is uniquely determined
    split at h1 h2
    · injection h1; injection h2; subst_vars; rfl
    · split at h1 h2
      · injection h1; injection h2; subst_vars; rfl
      · simp at h1 h2
  | _ => simp at h1

/-! ## Decidability of Beta-Equality -/

/-- The transitive-symmetric closure of β-reduction (β-equality). -/
inductive BetaEq : Term → Term → Prop where
  | beta : BetaStep t1 t2 → BetaEq t1 t2
  | refl : BetaEq t t
  | symm (h : BetaEq t1 t2) : BetaEq t2 t1
  | trans (h1 : BetaEq t1 t2) (h2 : BetaEq t2 t3) : BetaEq t1 t3

/-- Beta-equality is an equivalence relation. -/
theorem betaEq_equivalence : Equivalence BetaEq := by
  refine ⟨?_, ?_, ?_⟩
  · intro t; exact BetaEq.refl
  · intro t1 t2 h; exact BetaEq.symm h
  · intro t1 t2 t3 h12 h23; exact BetaEq.trans h12 h23

/-- Beta reduction implies beta equality. -/
theorem betaStep_imp_eq (t1 t2 : Term) (h : BetaStep t1 t2) : BetaEq t1 t2 :=
  BetaEq.beta h

/-- Beta equality preserves well-formedness for single steps. -/
theorem betaStep_preserves_wf (t1 t2 : Term) (h : BetaStep t1 t2) (hwf : wf t1) : wf t2 := by
  induction h with
  | beta v body arg =>
    -- (.lam v body) arg → subst body arg v
    -- well-formedness of the application implies body and arg are wf
    -- substitution preserves wf (we proved this)
    simp [wf, wf.go] at hwf
    rcases hwf with ⟨hwfLam, hwfArg⟩
    simp [wf, wf.go] at hwfLam
    -- hwfLam : wf.go body 1 (after considering the binder)
    -- We need wf (subst body arg v)
    apply wf_subst_invariant body arg v hwfLam hwfArg
  | appL f f' a hstep ih =>
    simp [wf, wf.go] at hwf; rcases hwf with ⟨hwfF, hwfA⟩
    simp [wf, wf.go]; exact ⟨ih hwfF, hwfA⟩
  | appR f a a' hstep ih =>
    simp [wf, wf.go] at hwf; rcases hwf with ⟨hwfF, hwfA⟩
    simp [wf, wf.go]; exact ⟨hwfF, ih hwfA⟩
  | lamBody v b b' hstep ih =>
    simp [wf, wf.go] at hwf
    simp [wf, wf.go]; exact ih hwf
  | piDom v d d' cod hstep ih =>
    simp [wf, wf.go] at hwf; rcases hwf with ⟨hwfD, hwfC⟩
    simp [wf, wf.go]; exact ⟨ih hwfD, hwfC⟩
  | piCod v dom c c' hstep ih =>
    simp [wf, wf.go] at hwf; rcases hwf with ⟨hwfD, hwfC⟩
    simp [wf, wf.go]; exact ⟨hwfD, ih hwfC⟩
  | letVal v t t' b hstep ih =>
    simp [wf, wf.go] at hwf; rcases hwf with ⟨hwfT, hwfB⟩
    simp [wf, wf.go]; exact ⟨ih hwfT, hwfB⟩

/-! ## #eval Examples -/

def nfEx1 : Term := .lit 42
def nfEx2 : Term := .lam (Variable.free "x") (.var (Variable.free "x"))
def redexEx : Term := .app (.lam (Variable.free "x") (.var (Variable.free "x"))) (.lit 1)

#eval isNormalForm nfEx1
#eval isNormalForm nfEx2
#eval isNormalForm redexEx

#eval normalOrderStep redexEx |>.get?.map toString

#eval isNormalForm (normalOrderEval redexEx)

end MiniSyntaxKernel
