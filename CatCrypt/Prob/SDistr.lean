/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform

/-!
# Sub-distributions

This file defines sub-distributions as probability mass functions over `Option α`.
A sub-distribution can have total mass less than 1, representing computations
that may fail (return `none`).

## Main definitions

* `SDistr α` - Sub-distribution over type `α`, defined as `PMF (Option α)`
* `SDistr.pure` - Point mass distribution
* `SDistr.fail` - Failed computation (mass 0 on all `some` values)
* `SDistr.bind` - Monadic bind for sub-distributions
* `SDistr.uniform` - Uniform distribution over a finite type

## References

* CatCrypt: https://github.com/CatCrypt/ssprove
* EasyCrypt sub-distributions
-/

namespace CatCrypt.Prob

open scoped ENNReal
open PMF

/-- Sub-distribution: a distribution that may have total mass < 1.
    Represented as a PMF over `Option α`, where `none` represents failure. -/
abbrev SDistr (α : Type*) := PMF (Option α)

namespace SDistr

variable {α β γ : Type*}

/-! ## Basic constructors -/

/-- Point mass distribution at `a` -/
noncomputable def pure (a : α) : SDistr α := PMF.pure (some a)

/-- Failed computation: all mass on `none` -/
noncomputable def fail : SDistr α := PMF.pure none

/-- Monadic bind for sub-distributions.
    If the first computation fails, the result fails.
    Otherwise, apply `f` to the result. -/
noncomputable def bind (d : SDistr α) (f : α → SDistr β) : SDistr β :=
  PMF.bind d (fun oa =>
    match oa with
    | some a => f a
    | none => fail)

noncomputable instance : Monad SDistr where
  pure := SDistr.pure
  bind := SDistr.bind

/-! ## Uniform distribution -/

/-- Uniform distribution over a finite nonempty type -/
noncomputable def uniform (α : Type*) [Fintype α] [Nonempty α] : SDistr α :=
  (PMF.uniformOfFintype α).map some

/-! ## Measures and mass -/

/-- Total mass: probability of not failing -/
noncomputable def mass (d : SDistr α) : ℝ≥0∞ := 1 - d none

/-- Support of the distribution: values with nonzero probability -/
def support (d : SDistr α) : Set α :=
  {a | d (some a) ≠ 0}

/-! ## Basic lemmas -/

@[simp]
theorem pure_apply_some (a b : α) [DecidableEq α] :
    (pure a : SDistr α) (some b) = if a = b then 1 else 0 := by
  unfold pure
  rw [PMF.pure_apply]
  simp only [Option.some.injEq]
  by_cases h : a = b <;> simp [h, eq_comm]

@[simp]
theorem pure_apply_none (a : α) : (pure a : SDistr α) none = 0 := by
  unfold pure
  rw [PMF.pure_apply]
  simp

@[simp]
theorem fail_apply_some (a : α) : (fail : SDistr α) (some a) = 0 := by
  unfold fail
  rw [PMF.pure_apply]
  simp

@[simp]
theorem fail_apply_none : (fail : SDistr α) none = 1 := by
  unfold fail
  rw [PMF.pure_apply]
  simp

@[simp] theorem mass_pure (a : α) : mass (pure a) = 1 := by
  unfold mass
  rw [pure_apply_none]
  simp

@[simp] theorem mass_fail : mass (fail : SDistr α) = 0 := by
  unfold mass
  rw [fail_apply_none]
  simp

/-! ## Support lemmas -/

theorem mem_support_iff (d : SDistr α) (a : α) : a ∈ d.support ↔ d (some a) ≠ 0 := Iff.rfl

/-- Membership in support of pure implies equality (without DecidableEq) -/
theorem mem_support_pure_iff (a b : α) : b ∈ (pure a : SDistr α).support ↔ a = b := by
  unfold support pure
  simp only [Set.mem_setOf_eq, PMF.pure_apply, Option.some.injEq, ne_eq]
  constructor
  · intro h
    by_contra hne
    rw [if_neg (fun heq => hne (Option.some.inj heq).symm)] at h
    exact h rfl
  · intro h
    simp only [h, ite_true, one_ne_zero, not_false_eq_true]

theorem support_pure [DecidableEq α] (a : α) : (pure a).support = {a} := by
  ext b
  unfold support
  simp only [Set.mem_setOf_eq, pure_apply_some, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hne
    simp only [Ne.symm hne, ite_false, ne_eq, not_true_eq_false] at h
  · intro h
    simp only [h, ite_true, ne_eq, one_ne_zero, not_false_eq_true]

theorem support_fail : (fail : SDistr α).support = ∅ := by
  ext a
  unfold support
  simp

/-- Binding fail with any function gives fail -/
theorem bind_fail (f : α → SDistr β) : (fail : SDistr α).bind f = fail := by
  unfold bind fail
  -- PMF.bind (PMF.pure none) (match · with some a => f a | none => PMF.pure none)
  -- Since PMF.pure none puts all mass on none, the match gives PMF.pure none
  rw [PMF.pure_bind]

/-- Binding pure with a function gives the function applied to the value -/
theorem pure_bind (a : α) (f : α → SDistr β) : (pure a).bind f = f a := by
  unfold bind pure
  rw [PMF.pure_bind]

/-- Binding with pure is identity -/
theorem bind_pure (d : SDistr α) : d.bind pure = d := by
  unfold bind pure fail
  -- Show: PMF.bind d (match · with some a => PMF.pure (some a) | none => PMF.pure none) = d
  -- The match function is equivalent to PMF.pure, so this is PMF.bind_pure
  have h : (fun oa : Option α => match oa with | some a => PMF.pure (some a) | none => PMF.pure (none : Option α)) = PMF.pure := by
    funext oa; cases oa <;> rfl
  rw [h, PMF.bind_pure]

/-- Bind is associative -/
theorem bind_assoc (d : SDistr α) (f : α → SDistr β) (g : β → SDistr γ) :
    (d.bind f).bind g = d.bind (fun a => (f a).bind g) := by
  unfold bind
  -- Use PMF.bind_bind to restructure
  rw [PMF.bind_bind]
  -- Need to show the inner functions are equal
  congr 1
  funext oa
  cases oa with
  | none =>
    -- fail.bind anything = fail, and match none = fail
    simp only [fail]
    rw [PMF.pure_bind]
  | some a => rfl

/-! ## Lawful Monad Instance -/

/-- SDistr is a lawful monad. The laws follow from `pure_bind`, `bind_pure`, `bind_assoc`. -/
noncomputable instance : LawfulMonad SDistr := LawfulMonad.mk'
  (id_map := fun x => bind_pure x)
  (pure_bind := fun x f => pure_bind x f)
  (bind_assoc := fun x f g => bind_assoc x f g)

/-! ## Support-based congruence (eq_in_dlet in Rocq) -/

/-- If functions agree on the support of a distribution, their binds are equal.
    This is the Lean equivalent of `eq_in_dlet` from mathcomp-experimental-reals:
    If f and g agree on {a | d (some a) ≠ 0}, then d.bind f = d.bind g.

    This is a key lemma for coupling composition proofs. -/
theorem bind_congr_support {d : SDistr α} {f g : α → SDistr β}
    (h : ∀ a, d (some a) ≠ 0 → f a = g a) :
    d.bind f = d.bind g := by
  unfold bind
  apply PMF.ext
  intro ob
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro oa
  cases oa with
  | none =>
    -- Both use fail which is the same
    rfl
  | some a =>
    -- Simplify the match: match some a with | some a => f a | none => fail = f a
    simp only []
    -- Now: d (some a) * (f a) ob = d (some a) * (g a) ob
    -- If d (some a) = 0, both terms are 0
    -- If d (some a) ≠ 0, f a = g a by hypothesis
    by_cases hda : d (some a) = 0
    · simp [hda]
    · rw [h a hda]

/-- Variant: congruence with explicit equality of distributions -/
theorem bind_congr_support' {d₁ d₂ : SDistr α} {f g : α → SDistr β}
    (hd : d₁ = d₂)
    (h : ∀ a, d₁ (some a) ≠ 0 → f a = g a) :
    d₁.bind f = d₂.bind g := by
  subst hd
  exact bind_congr_support h

/-! ## Uniform distribution lemmas -/

theorem uniform_apply_some [Fintype α] [Nonempty α] (a : α) :
    (uniform α) (some a) = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  classical
  unfold uniform
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply]
  rw [tsum_eq_single a]
  · simp
  · intro a' ha'
    simp only [Option.some.injEq]
    split_ifs with h
    · exact absurd h.symm ha'
    · rfl

theorem uniform_apply_none [Fintype α] [Nonempty α] :
    (uniform α) none = 0 := by
  unfold uniform
  simp only [PMF.map_apply]
  simp only [reduceCtorEq, ite_false, tsum_zero]

@[simp] theorem mass_uniform [Fintype α] [Nonempty α] : mass (uniform α) = 1 := by
  unfold mass
  rw [uniform_apply_none]
  simp

/-- Applying a bijection to a uniform distribution gives a uniform distribution -/
theorem uniform_bind_bij [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α ≃ β) :
    (uniform α).bind (fun a => pure (f a)) = uniform β := by
  classical
  -- Strategy: Show both PMFs assign the same probability to each value.
  -- For uniform distributions, each element has probability 1/|type|.
  -- Since f is a bijection, |α| = |β|, so probabilities match.
  have hcard : Fintype.card α = Fintype.card β := Fintype.card_congr f
  unfold uniform bind pure fail
  apply PMF.ext
  intro ob
  simp only [PMF.bind_apply, PMF.map_apply]
  cases ob with
  | none =>
    -- Both sides have probability 0 on none
    -- LHS: ∑' oa, (uniform α map some)(oa) * (continuation)(none)
    -- RHS: ∑' a : β, if none = some a then ... else 0 = 0
    simp only [reduceCtorEq, ite_false, tsum_zero]
    rw [ENNReal.tsum_eq_zero]
    intro oa
    cases oa with
    | none =>
      simp only [reduceCtorEq, ite_false, ite_true, tsum_zero, PMF.pure_apply, zero_mul]
    | some a =>
      simp only [PMF.pure_apply, reduceCtorEq, ite_false, mul_zero]
  | some b =>
    -- Both sides have probability 1/|β| on (some b)
    -- RHS simplifies to 1/|β|
    conv_rhs => rw [tsum_eq_single b (by intro a hne; simp [hne.symm])]
    simp only [↓reduceIte, PMF.uniformOfFintype_apply]
    -- LHS: ∑' oa, (inner)(oa) * continuation(oa)(some b)
    -- We'll show this equals 1/|α| = 1/|β|
    -- Key insight: the only contributing term is when oa = some (f⁻¹ b)
    -- because: (1) none contributes 0 (inner sum is 0)
    --          (2) some a contributes (1/|α|) * (if f a = b then 1 else 0)
    --          (3) only a = f⁻¹ b has f a = b
    rw [tsum_eq_single (some (f.symm b))]
    · -- Main term: (inner)(some (f⁻¹ b)) * (pure (some (f (f⁻¹ b))))(some b)
      --          = (1/|α|) * 1 = 1/|α|
      -- Inner sum for some (f⁻¹ b) equals 1/|α|
      have inner_val : (∑' (a' : α), if some (f.symm b) = some a' then (Fintype.card α : ℝ≥0∞)⁻¹ else 0)
                     = (Fintype.card α : ℝ≥0∞)⁻¹ := by
        rw [tsum_eq_single (f.symm b) (by intro a' hne; simp [hne.symm])]
        simp only [↓reduceIte]
      rw [inner_val]
      simp only [Equiv.apply_symm_apply, PMF.pure_apply, ↓reduceIte, mul_one]
      congr 1
      exact_mod_cast hcard
    · -- Other terms are 0
      intro oa hne
      cases oa with
      | none =>
        -- inner sum for none is 0
        simp only [reduceCtorEq, ite_false, tsum_zero, zero_mul]
      | some a =>
        -- For some a with a ≠ f⁻¹ b, we have f a ≠ b
        have hfa : f a ≠ b := by
          intro heq
          apply hne
          congr 1
          exact f.injective.eq_iff.mp (heq.trans (f.apply_symm_apply b).symm)
        -- (PMF.pure (some (f a)))(some b) = if some b = some (f a) then 1 else 0 = 0
        have hbfa : b ≠ f a := fun h => hfa h.symm
        have hpure : (PMF.pure (some (f a)) : SDistr β) (some b) = 0 := by
          simp only [PMF.pure_apply, Option.some.injEq, hbfa, ite_false]
        rw [hpure, mul_zero]

/-- Compositional version of `uniform_bind_bij`: applying a bijection inside
    a uniform bind doesn't change the distribution.
    `(uniform α).bind (fun a => g (σ a)) = (uniform β).bind g` for any bijection `σ : α ≃ β`. -/
theorem uniform_bind_equiv_comp [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (σ : α ≃ β) (g : β → SDistr γ) :
    (uniform α).bind (fun a => g (σ a)) = (uniform β).bind g := by
  have h1 : (fun a => g (σ a)) = (fun a => (pure (σ a)).bind g) := by
    funext a; exact (pure_bind _ _).symm
  rw [h1, ← bind_assoc, uniform_bind_bij]

/-- Binding uniform distribution with a constant function gives the constant.
    This is because averaging a constant gives the constant.

    **Mathematical Proof:**
    - LHS = ∑_a (1/|α|) * d = |α| * (1/|α|) * d = d
    - The uniform distribution has |α| elements each with probability 1/|α|
    - Summing |α| copies of d weighted by 1/|α| gives d

    This is a fundamental property needed for the averaging coupling argument
    in pRHL sampling rules. -/
theorem uniform_bind_const [Fintype α] [Nonempty α] (d : SDistr β) :
    (uniform α).bind (fun _ => d) = d := by
  -- Use the PMF monad laws directly:
  -- uniform α = (PMF.uniformOfFintype α).map some
  --           = (PMF.uniformOfFintype α).bind (fun a => PMF.pure (some a))
  -- Then by bind_bind and pure_bind, the whole expression reduces to
  -- (PMF.uniformOfFintype α).bind (fun _ => d) = d  [by bind_const]
  unfold uniform bind fail

  -- Step 1: Rewrite (PMF.uniformOfFintype α).map some as a bind
  -- Using bind_pure_comp : bind p (pure ∘ f) = map f p
  -- So map f p = bind p (pure ∘ f)
  rw [← PMF.bind_pure_comp]

  -- Step 2: Use bind_bind associativity
  rw [PMF.bind_bind]

  -- Step 3: Simplify the inner continuation: ((pure ∘ some) a).bind cont = cont (some a) = d
  have hinner : ∀ a : α, ((PMF.pure ∘ some) a).bind
      (fun oa => match oa with | some _ => d | none => PMF.pure none) = d := by
    intro a
    simp only [Function.comp_apply]
    -- PMF.pure_bind says (pure x).bind f = f x
    -- So (pure (some a)).bind cont = cont (some a) = match (some a) with | some _ => d | ... = d
    rw [PMF.pure_bind]

  -- Step 4: Use congrArg to apply hinner inside the bind
  conv_lhs =>
    arg 2; ext a
    rw [hinner a]

  -- Step 5: Now we have (PMF.uniformOfFintype α).bind (fun _ => d), which equals d by bind_const
  exact PMF.bind_const _ _

/-- Helper for `bind_comm`: distributes a constant factor `c₁ * c₂` over a
    PMF sum `∑' x, d x`, rewriting `c₁ * c₂ = ∑' x, c₁ * d x * c₂`.
    Used for the `none` branch of both LHS and RHS transformations. -/
private theorem bind_comm_none_expand {ε : Type*} (c₁ c₂ : ℝ≥0∞)
    (d : PMF (Option ε)) : c₁ * c₂ = ∑' x, c₁ * d x * c₂ := by
  calc c₁ * c₂
      = c₁ * c₂ * 1 := by ring
    _ = c₁ * c₂ * (∑' x, d x) := by rw [d.tsum_coe]
    _ = ∑' x, c₁ * c₂ * d x := by rw [← ENNReal.tsum_mul_left]
    _ = ∑' x, c₁ * d x * c₂ := by congr 1; funext x; ring

/-- Helper for `bind_comm`: expands `w * (∑' x, d x * g x)` into
    `∑' x, w * d x * g x`. Used for the `some` branch of both
    LHS and RHS transformations. -/
private theorem bind_comm_some_expand {ε : Type*} (w : ℝ≥0∞) (d : PMF (Option ε))
    (g : Option ε → ℝ≥0∞) :
    w * (∑' x, d x * g x) = ∑' x, w * d x * g x := by
  calc w * (∑' x, d x * g x)
      = ∑' x, w * (d x * g x) := by rw [ENNReal.tsum_mul_left]
    _ = ∑' x, w * d x * g x := by congr 1; funext x; ring

/-- Commutativity of bind for sub-distributions.
    Two independent bind operations can be swapped. -/
theorem bind_comm (d₁ : SDistr α) (d₂ : SDistr β) (f : α → β → SDistr γ) :
    d₁.bind (fun a => d₂.bind (f a)) = d₂.bind (fun b => d₁.bind (fun a => f a b)) := by
  unfold bind fail
  apply PMF.ext
  intro oc
  simp only [PMF.bind_apply]

  -- LHS none helper
  have hlhs_none :
    d₁ none * (PMF.pure none : SDistr γ) oc =
    ∑' ob, d₁ none * d₂ ob * (PMF.pure none : SDistr γ) oc :=
    bind_comm_none_expand (d₁ none) ((PMF.pure none : SDistr γ) oc) d₂

  -- LHS some helper
  have hlhs_some (a : α) :
    d₁ (some a) * (PMF.bind d₂ (fun ob => match ob with | some b => f a b | none => PMF.pure none)) oc =
    ∑' ob, d₁ (some a) * d₂ ob * (match ob with | some b => f a b oc | none => (PMF.pure none) oc) := by
    simp only [PMF.bind_apply]
    have := bind_comm_some_expand (d₁ (some a)) d₂
              (fun ob => (match ob with | some b => f a b | none => PMF.pure none) oc)
    convert this using 2
    funext ob; cases ob <;> rfl

  -- RHS none helper
  have hrhs_none :
    d₂ none * (PMF.pure none : SDistr γ) oc =
    ∑' oa, d₁ oa * d₂ none * (PMF.pure none : SDistr γ) oc := by
    rw [bind_comm_none_expand (d₂ none) ((PMF.pure none : SDistr γ) oc) d₁]
    congr 1; funext oa; ring

  -- RHS some helper
  have hrhs_some (b : β) :
    d₂ (some b) * (PMF.bind d₁ (fun oa => match oa with | some a => f a b | none => PMF.pure none)) oc =
    ∑' oa, d₁ oa * d₂ (some b) * (match oa with | some a => f a b oc | none => (PMF.pure none) oc) := by
    simp only [PMF.bind_apply]
    have := bind_comm_some_expand (d₂ (some b)) d₁
              (fun oa => (match oa with | some a => f a b | none => PMF.pure none) oc)
    rw [this]
    congr 1; funext oa; cases oa <;> ring

  -- Step 1: Transform LHS to double sum
  have eq1 : (∑' oa, d₁ oa * (match oa with
      | some a => (PMF.bind d₂ (fun ob => match ob with | some b => f a b | none => PMF.pure none))
      | none => PMF.pure none) oc) =
    ∑' (oa : Option α) (ob : Option β), d₁ oa * d₂ ob * (match oa, ob with
      | some a, some b => f a b oc | _, _ => (PMF.pure none) oc) := by
    congr 1
    funext oa
    cases oa with
    | none =>
      simp only []
      rw [← hlhs_none]
    | some a =>
      rw [hlhs_some a]
      congr 1
      funext ob
      cases ob <;> rfl

  -- Step 2: Transform RHS to double sum (with swapped order)
  have eq2 : (∑' ob, d₂ ob * (match ob with
      | some b => (PMF.bind d₁ (fun oa => match oa with | some a => f a b | none => PMF.pure none))
      | none => PMF.pure none) oc) =
    ∑' (ob : Option β) (oa : Option α), d₁ oa * d₂ ob * (match oa, ob with
      | some a, some b => f a b oc | _, _ => (PMF.pure none) oc) := by
    congr 1
    funext ob
    cases ob with
    | none =>
      simp only []
      rw [← hrhs_none]
    | some b =>
      rw [hrhs_some b]
      congr 1
      funext oa
      cases oa <;> rfl

  -- Step 3: Use ENNReal.tsum_comm to connect them
  rw [eq1, ENNReal.tsum_comm, ← eq2]

/-! ## Nested uniform sampling equals product uniform sampling -/

/-- **Nested uniform sampling equals product uniform sampling.**

    For finite types A and B, sampling a : A and b : B independently
    and uniformly, then pairing them, gives the uniform distribution
    over A × B.

    **Mathematical Proof:**
    - LHS: Pr[(a₀, b₀)] = Pr[a = a₀] × Pr[b = b₀] = (1/|A|) × (1/|B|) = 1/(|A| × |B|)
    - RHS: Pr[(a₀, b₀)] = 1/|A × B| = 1/(|A| × |B|)

    These are equal, so the distributions are equal.

    This is a key lemma for cryptographic proofs involving uniform sampling
    over product types. -/
theorem uniform_nested_eq_prod (A B : Type) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    (SDistr.uniform A).bind (fun a => (SDistr.uniform B).bind (fun b => SDistr.pure (a, b))) =
    SDistr.uniform (A × B) := by
  classical
  apply PMF.ext
  intro oab

  unfold bind fail pure
  simp only [PMF.bind_apply]

  cases oab with
  | none =>
    trans 0
    · apply ENNReal.tsum_eq_zero.mpr
      intro oa
      cases oa with
      | none => rw [uniform_apply_none, zero_mul]
      | some a =>
        simp only [PMF.bind_apply, mul_eq_zero]
        right
        apply ENNReal.tsum_eq_zero.mpr
        intro ob
        cases ob with
        | none => rw [uniform_apply_none, zero_mul]
        | some b => simp only [PMF.pure_apply, reduceCtorEq, ite_false, mul_zero]
    · exact uniform_apply_none.symm

  | some ab =>
    obtain ⟨a₀, b₀⟩ := ab

    trans ((Fintype.card A : ℝ≥0∞)⁻¹ * (Fintype.card B : ℝ≥0∞)⁻¹)

    · -- LHS = 1/|A| * 1/|B|
      rw [tsum_eq_single (some a₀)]
      · -- Main term
        rw [uniform_apply_some]
        simp only [PMF.bind_apply]
        congr 1
        rw [tsum_eq_single (some b₀)]
        · rw [uniform_apply_some, PMF.pure_apply]
          simp only [mul_one, ite_true]
        · intro ob hob
          cases ob with
          | none => rw [uniform_apply_none, zero_mul]
          | some b =>
            have hb : b ≠ b₀ := fun h => hob (congrArg some h)
            change (uniform B) (some b) * (PMF.pure (some (a₀, b))) (some (a₀, b₀)) = 0
            rw [PMF.pure_apply]
            have h : ¬(some (a₀, b₀) = some (a₀, b)) := by
              simp only [Option.some.injEq, Prod.mk.injEq, true_and]
              exact hb.symm
            rw [if_neg h, mul_zero]
      · intro oa hoa
        cases oa with
        | none => rw [uniform_apply_none, zero_mul]
        | some a =>
          have hoa' : a ≠ a₀ := fun h => hoa (congrArg some h)
          simp only [PMF.bind_apply, mul_eq_zero]
          right
          apply ENNReal.tsum_eq_zero.mpr
          intro ob
          cases ob with
          | none => rw [uniform_apply_none, zero_mul]
          | some b =>
            change (uniform B) (some b) * (PMF.pure (some (a, b))) (some (a₀, b₀)) = 0
            rw [PMF.pure_apply]
            have h : ¬(some (a₀, b₀) = some (a, b)) := by
              simp only [Option.some.injEq, Prod.mk.injEq]
              intro ⟨ha, _⟩
              exact hoa' ha.symm
            rw [if_neg h, mul_zero]

    · -- RHS = 1/|A×B| = 1/(|A|*|B|)
      rw [uniform_apply_some, Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv (by simp) (by simp)]

/-! ## Option tsum helpers -/

/-- Helper lemma: For a function on Option where the none value is 0,
    the sum over Option equals the sum over some. -/
theorem tsum_option_none_zero {γ : Type*} (f : Option γ → ENNReal) (hf : f none = 0) :
    ∑' x : Option γ, f x = ∑' a : γ, f (some a) := by
  have h1 : Function.support f ⊆ Set.range (some : γ → Option γ) := by
    intro x hx
    cases x with
    | none => exact absurd hf (Function.mem_support.mp hx)
    | some a => exact ⟨a, rfl⟩
  rw [← tsum_subtype_eq_of_support_subset h1]
  let e : γ ≃ Set.range (some : γ → Option γ) := Equiv.ofInjective some (Option.some_injective γ)
  rw [← e.tsum_eq]
  apply tsum_congr
  intro a
  simp only [e, Equiv.ofInjective_apply]

/-- Helper: sum over Option α can be split into the none term plus sum over some terms -/
theorem tsum_option_eq_add {γ : Type*} (f : Option γ → ENNReal) :
    ∑' x : Option γ, f x = f none + ∑' a : γ, f (some a) := by
  let e := Equiv.optionEquivSumPUnit γ
  have heq := e.symm.tsum_eq (f := f)
  rw [← heq]
  have h := Summable.tsum_sum (f := fun y => f (e.symm y))
             (ENNReal.summable) (ENNReal.summable)
  rw [h]
  have h_punit : ∑' u : PUnit, f (e.symm (Sum.inr u)) = f none := by
    rw [tsum_eq_single ()]
    · simp only [Equiv.optionEquivSumPUnit_symm_inr, e]
    · intro u hu; exact absurd (PUnit.eq_punit u) hu
  have h_gamma : ∑' a : γ, f (e.symm (Sum.inl a)) = ∑' a : γ, f (some a) := by
    apply tsum_congr
    intro a
    simp only [Equiv.optionEquivSumPUnit_symm_inl, e]
  rw [h_punit, h_gamma, add_comm]

/-- If two SDistrs agree on all some values, they are equal.
    This follows from PMF having total mass 1. -/
theorem eq_of_some_eq {d₁ d₂ : SDistr α}
    (h : ∀ a, d₁ (some a) = d₂ (some a)) : d₁ = d₂ := by
  have hsums_eq : ∑' a, d₁ (some a) = ∑' a, d₂ (some a) := tsum_congr h
  apply PMF.ext
  intro oa
  cases oa with
  | some a => exact h a
  | none =>
    have htsum1 := PMF.tsum_coe d₁
    have htsum2 := PMF.tsum_coe d₂
    have hsplit1 : ∑' x : Option α, d₁ x = d₁ none + ∑' a, d₁ (some a) := tsum_option_eq_add d₁
    have hsplit2 : ∑' x : Option α, d₂ x = d₂ none + ∑' a, d₂ (some a) := tsum_option_eq_add d₂
    rw [hsplit1] at htsum1
    rw [hsplit2] at htsum2
    rw [hsums_eq] at htsum1
    have heq : d₁ none + ∑' a, d₂ (some a) = d₂ none + ∑' a, d₂ (some a) := by
      rw [htsum1, htsum2]
    have hne_top : ∑' a, d₂ (some a) ≠ ⊤ := by
      have hle : ∑' a, d₂ (some a) ≤ 1 := by
        calc ∑' a, d₂ (some a)
            ≤ d₂ none + ∑' a, d₂ (some a) := le_add_left (le_refl _)
          _ = 1 := htsum2
      exact ne_top_of_le_ne_top (by norm_num : (1 : ENNReal) ≠ ⊤) hle
    rwa [ENNReal.add_left_inj hne_top] at heq

end SDistr

end CatCrypt.Prob
