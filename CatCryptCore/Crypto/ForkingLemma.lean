/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Core.Code
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Prob.Support

/-!
# Forking Lemma

This file provides a general forking lemma for adversaries in the Random Oracle Model (ROM)
with a single oracle query (q = 1).

## Overview

The forking lemma (Bellare-Neven 2006, Pointcheval-Stern 2000) is a key tool for
security reductions of signature schemes in the ROM. It shows that if an adversary
succeeds with probability `acc`, then running the adversary twice with the same
randomness but different oracle responses produces two accepting transcripts with
probability at least `acc² - acc/|R|`.

## Model

We decompose the adversary into two phases:
1. **Commit phase** (`coins`): Probabilistic; produces a commitment `c` using internal
   randomness. This models everything the adversary does *before* the oracle query.
2. **Response phase** (`respond`): Deterministic; given the commitment `c` and oracle
   response `e`, produces the final output `y`. This models the adversary's computation
   *after* receiving the oracle response.

The forking algorithm:
1. Run `coins` once to get commitment `c`
2. Sample two independent oracle responses `e₁, e₂ ← uniform R`
3. Compute `y₁ = respond(x, c, e₁)` and `y₂ = respond(x, c, e₂)`
4. Succeed if both `accept(y₁)` and `accept(y₂)` and `e₁ ≠ e₂`

Since the commit phase is shared, both runs produce the same commitment,
enabling special soundness extraction from the two accepting transcripts.

## Main results

* `ForkableAdversary` - Two-phase adversary structure
* `forkAlg` - The forking algorithm
* `jensen_sub_pmf_sq` - Jensen's inequality: `E[f²] ≥ (E[f])²` for sub-PMF weights
* `fork_success_ge` - Forking lemma: fork success probability ≥ `acc² - acc/|R|`

## References

* [Bellare, Neven, *Multi-signatures in the plain public-key model*]
* [Pointcheval, Stern, *Security arguments for digital signatures and blind signatures*]
* [Firsov, Unruh, *Reflection, rewinding, and coin-toss in EasyCrypt*]
-/

namespace CatCrypt.Crypto.ForkingLemma

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto

open scoped ENNReal

/-! ## Forkable Adversary Model -/

/-- Two-phase adversary for the ROM forking lemma (q = 1 oracle query).

The adversary is decomposed into:
- `coins`: Probabilistic commitment phase (uses internal randomness)
- `respond`: Deterministic response phase (given commitment and oracle response)

This decomposition enables forking: replay the adversary with the same commitment
but a different oracle response. -/
structure ForkableAdversary (X : Type) (C : Type) (R : Type) (Y : Type) where
  /-- Phase 1: Probabilistic commitment. Given input `x`, produce commitment `c`. -/
  coins : X → SPComp C
  /-- Phase 2: Deterministic response. Given input `x`, commitment `c`, and
      oracle response `r`, produce output `y`. -/
  respond : X → C → R → Y

variable {X C R Y : Type}

/-- Run the adversary: commit then respond with a uniform oracle sample. -/
noncomputable def ForkableAdversary.run [Fintype R] [Nonempty R]
    (A : ForkableAdversary X C R Y) (x : X) : SPComp Y := do
  let c ← A.coins x
  let e ← SPComp.sample R
  SPComp.pure (A.respond x c e)

/-- Acceptance probability of the adversary. -/
noncomputable def acceptProb [Fintype R] [Nonempty R]
    (A : ForkableAdversary X C R Y) (x : X) (accept : Y → Bool) : ℝ≥0∞ :=
  prTrue (do
    let c ← A.coins x
    let e ← SPComp.sample R
    SPComp.pure (accept (A.respond x c e))) Heap.empty

/-- The forking algorithm: run the adversary twice with shared commitment
    but independent oracle responses. -/
noncomputable def forkAlg [Fintype R] [Nonempty R]
    (A : ForkableAdversary X C R Y) (x : X) : SPComp (C × R × Y × R × Y) := do
  let c ← A.coins x
  let e₁ ← SPComp.sample R
  let y₁ := A.respond x c e₁
  let e₂ ← SPComp.sample R
  let y₂ := A.respond x c e₂
  SPComp.pure (c, e₁, y₁, e₂, y₂)

/-- Fork success probability: both runs accept and oracle responses differ. -/
noncomputable def forkSuccProb [Fintype R] [Nonempty R] [DecidableEq R]
    (A : ForkableAdversary X C R Y) (x : X) (accept : Y → Bool) : ℝ≥0∞ :=
  prTrue (do
    let c ← A.coins x
    let e₁ ← SPComp.sample R
    let y₁ := A.respond x c e₁
    let e₂ ← SPComp.sample R
    let y₂ := A.respond x c e₂
    SPComp.pure (accept y₁ && accept y₂ && decide (e₁ ≠ e₂))) Heap.empty

/-! ## Jensen's Inequality for ENNReal

The key mathematical ingredient for the forking lemma is Jensen's inequality
for the convex function x² under sub-probability weights:
  `(∑ w(i) * f(i))² ≤ ∑ w(i) * f(i)²`
when `∑ w(i) ≤ 1` and `f(i) ≤ 1`.

The proof uses the AM-GM inequality pointwise. -/

/-- AM-GM inequality for ENNReal: `2 * a * b ≤ a² + b²`. -/
theorem ennreal_two_mul_le_add_sq (a b : ℝ≥0∞) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  by_cases ha : a = ⊤
  · subst ha; simp [sq]
  by_cases hb : b = ⊤
  · subst hb; simp [sq]
  rw [← ENNReal.coe_toNNReal ha, ← ENNReal.coe_toNNReal hb]
  simp only [← ENNReal.coe_ofNat, ← ENNReal.coe_mul, ← ENNReal.coe_pow, ← ENNReal.coe_add,
             ENNReal.coe_le_coe]
  exact two_mul_le_add_sq _ _

/-- Jensen's inequality for squaring under sub-PMF weights.

For weights `w` with `∑ w ≤ 1` and bounded function `f ≤ 1`:
  `(∑ w(i) * f(i))² ≤ ∑ w(i) * f(i)²`

Proof: By AM-GM, `2 * f(i) * μ ≤ f(i)² + μ²`. Multiply by `w(i)` and sum:
  `2μ² ≤ E[f²] + (∑ w) * μ² ≤ E[f²] + μ²`
Cancel `μ²` (finite since μ ≤ 1) to get `μ² ≤ E[f²]`. -/
theorem jensen_sub_pmf_sq {ι : Type} (w : ι → ℝ≥0∞) (f : ι → ℝ≥0∞)
    (hw_sum : ∑' i, w i ≤ 1) (hf : ∀ i, f i ≤ 1) :
    (∑' i, w i * f i) ^ 2 ≤ ∑' i, w i * f i ^ 2 := by
  set μ := ∑' i, w i * f i with hμ_def
  have hμ_le : μ ≤ 1 := by
    calc μ ≤ ∑' i, w i * 1 := ENNReal.tsum_le_tsum fun i => by gcongr; exact hf i
      _ = ∑' i, w i := by simp
      _ ≤ 1 := hw_sum
  have hμ_ne : μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hμ_le
  have hμsq_ne : μ * μ ≠ ⊤ := ENNReal.mul_ne_top hμ_ne hμ_ne
  rw [sq μ]
  suffices h : μ * μ + μ * μ ≤ (∑' i, w i * f i ^ 2) + μ * μ from
    (ENNReal.add_le_add_iff_right hμsq_ne).mp h
  calc μ * μ + μ * μ
      = ∑' i, w i * f i * μ + ∑' i, w i * f i * μ := by
        rw [show μ * μ = (∑' i, w i * f i) * μ from rfl, ENNReal.tsum_mul_right]
    _ = ∑' i, (w i * f i * μ + w i * f i * μ) := ENNReal.tsum_add.symm
    _ = ∑' i, w i * (2 * f i * μ) := by congr 1; funext i; ring
    _ ≤ ∑' i, w i * (f i ^ 2 + μ ^ 2) := by
        apply ENNReal.tsum_le_tsum; intro i; gcongr
        exact ennreal_two_mul_le_add_sq (f i) μ
    _ = ∑' i, (w i * f i ^ 2 + w i * μ ^ 2) := by congr 1; funext i; rw [mul_add]
    _ = (∑' i, w i * f i ^ 2) + ∑' i, w i * μ ^ 2 := ENNReal.tsum_add
    _ = (∑' i, w i * f i ^ 2) + (∑' i, w i) * μ ^ 2 := by
        congr 1; rw [ENNReal.tsum_mul_right]
    _ ≤ (∑' i, w i * f i ^ 2) + 1 * μ ^ 2 := by gcongr
    _ = (∑' i, w i * f i ^ 2) + μ * μ := by rw [one_mul, sq]

/-! ## Representation Lemmas -/

/-- `prTrue` of a bind decomposes as a weighted sum over the PMF of the first computation. -/
theorem prTrue_bind_eq_weighted {α : Type}
    (c : SPComp α) (k : α → SPComp Bool) (h₀ : Heap) :
    prTrue (SPComp.bind c k) h₀ =
      ∑' (p : Option (α × Heap)), (c h₀ : PMF _) p *
        (match p with | some ⟨a, h'⟩ => prTrue (k a) h' | none => 0) := by
  unfold prTrue SPComp.bind SDistr.bind
  simp only [PMF.bind_apply]
  rw [ENNReal.tsum_comm]
  congr 1; funext p; rw [ENNReal.tsum_mul_left]; congr 1
  cases p with
  | none => simp [SDistr.fail, PMF.pure_apply]
  | some pp => rfl

/-- prTrue of a pure Boolean. -/
theorem prTrue_pure_bool (b : Bool) (h₀ : Heap) :
    prTrue (SPComp.pure b) h₀ = if b then 1 else 0 := by
  unfold prTrue SPComp.pure
  simp only [SDistr.pure, PMF.pure_apply, Option.some.injEq, Prod.mk.injEq]
  cases b with
  | true =>
    simp only [true_and, ite_true]
    exact tsum_ite_eq h₀ (fun _ => 1)
  | false =>
    simp only [reduceCtorEq, ite_false, false_and, ite_false, tsum_zero]

/-- prTrue of sampling from R then applying a pure Boolean function. -/
theorem prTrue_sample_pure_bool [Fintype R] [Nonempty R]
    (g : R → Bool) (h₀ : Heap) :
    prTrue (SPComp.bind (SPComp.sample R) (fun e => SPComp.pure (g e))) h₀ =
    (Finset.univ.filter (fun e => g e)).card / (Fintype.card R : ℝ≥0∞) := by
  unfold prTrue
  rw [SPComp.sample_bind_pure]
  -- Now goal: ∑' h, ((uniform R).bind fun a => pure (g a, h₀)) (some (true, h)) = ...
  -- Expand SDistr.bind
  simp only [SDistr.bind, PMF.bind_apply]
  -- Simplify uniform × pure pointwise
  -- Split the Option R sum
  simp_rw [tsum_option_split]
  -- none case: uniform none = 0
  simp only [SDistr.uniform_apply_none, zero_mul, zero_add]
  -- some case: uniform (some r) = 1/|R|, match simplifies
  simp only [SDistr.uniform_apply_some, SDistr.pure, PMF.pure_apply, Option.some.injEq,
    Prod.mk.injEq, mul_ite, mul_one, mul_zero]
  -- Goal: ∑' h a, if true = g a ∧ h = h₀ then (card R)⁻¹ else 0 = card(filter)/card(R)
  -- Extract h = h₀ from outer sum
  have h1 : ∀ h' : Heap, h' ≠ h₀ → ∑' (a : R),
      (if true = g a ∧ h' = h₀ then (Fintype.card R : ℝ≥0∞)⁻¹ else 0) = 0 := by
    intro h' hne; simp [hne]
  rw [tsum_eq_single h₀ h1]; simp only [and_true]
  rw [tsum_eq_sum (s := Finset.univ) (by simp)]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, eq_comm,
    ENNReal.div_eq_inv_mul, mul_comm]
  congr 1
  norm_cast; congr 1; exact Finset.filter_congr (fun a _ => ⟨fun h => h.symm, fun h => h.symm⟩)

/-! ## Monotonicity Lemmas for prTrue -/

/-- If `Q → R`, then `prTrue(pure(decide Q)) ≤ prTrue(pure(decide R))`. -/
theorem prTrue_pure_decide_mono {Q R : Prop} [Decidable Q] [Decidable R]
    (h : Q → R) (h₀ : Heap) :
    prTrue (SPComp.pure (decide Q)) h₀ ≤ prTrue (SPComp.pure (decide R)) h₀ := by
  rw [prTrue_pure_bool, prTrue_pure_bool]
  by_cases hQ : Q
  · simp [decide_eq_true hQ, decide_eq_true (h hQ)]
  · simp [decide_eq_false hQ]

/-- Monotonicity of `prTrue` under `bind`:
    if `k₁` is pointwise ≤ `k₂`, then `bind c k₁` ≤ `bind c k₂`. -/
theorem prTrue_bind_mono {α : Type}
    (c : SPComp α) (k₁ k₂ : α → SPComp Bool) (h₀ : Heap)
    (hk : ∀ a h', prTrue (k₁ a) h' ≤ prTrue (k₂ a) h') :
    prTrue (SPComp.bind c k₁) h₀ ≤ prTrue (SPComp.bind c k₂) h₀ := by
  rw [prTrue_bind_eq_weighted c k₁ h₀, prTrue_bind_eq_weighted c k₂ h₀]
  apply ENNReal.tsum_le_tsum
  intro p
  cases p with
  | none => simp
  | some p => exact mul_le_mul_left' (hk p.1 p.2) _

/-- Scaled monotonicity: if `prTrue(k₁ a) ≤ c * prTrue(k₂ a)` pointwise,
    then `prTrue(bind comp k₁) ≤ c * prTrue(bind comp k₂)`. -/
theorem prTrue_bind_mono_const {α : Type} (c : ℝ≥0∞)
    (comp : SPComp α) (k₁ k₂ : α → SPComp Bool) (h₀ : Heap)
    (hk : ∀ a h', prTrue (k₁ a) h' ≤ c * prTrue (k₂ a) h') :
    prTrue (SPComp.bind comp k₁) h₀ ≤ c * prTrue (SPComp.bind comp k₂) h₀ := by
  -- Reduce to: ∀ a h', prTrue (k₁ a) h' ≤ prTrue ((fun a => SPComp.bind (SPComp.pure a) (fun a => ???)) a) h'
  -- Actually use the weighted sum decomposition directly
  set f₁ := fun p : Option (α × Heap) =>
    match p with | some ⟨a, h'⟩ => prTrue (k₁ a) h' | none => 0
  set f₂ := fun p : Option (α × Heap) =>
    match p with | some ⟨a, h'⟩ => prTrue (k₂ a) h' | none => 0
  rw [prTrue_bind_eq_weighted comp k₁ h₀, prTrue_bind_eq_weighted comp k₂ h₀]
  -- Goal: ∑' p, w(p) * f₁(p) ≤ c * ∑' p, w(p) * f₂(p)
  -- By hypothesis: f₁(p) ≤ c * f₂(p) for all p
  have hpw : ∀ p, f₁ p ≤ c * f₂ p := by
    intro p; cases p with
    | none => simp [f₁, f₂]
    | some p => exact hk p.1 p.2
  calc ∑' p, (comp h₀ : PMF _) p * f₁ p
      ≤ ∑' p, (comp h₀ : PMF _) p * (c * f₂ p) :=
        ENNReal.tsum_le_tsum fun p => mul_le_mul_left' (hpw p) _
    _ = ∑' p, c * ((comp h₀ : PMF _) p * f₂ p) := by
        congr 1; funext p; rw [mul_left_comm]
    _ = c * ∑' p, (comp h₀ : PMF _) p * f₂ p := ENNReal.tsum_mul_left

/-- Lower bound: sampling then testing has probability ≥ 1/|R| times any witness's probability. -/
theorem prTrue_sample_bind_ge [Fintype R] [Nonempty R]
    (k : R → SPComp Bool) (a₀ : R) (h₀ : Heap) :
    (Fintype.card R : ℝ≥0∞)⁻¹ * prTrue (k a₀) h₀ ≤
    prTrue (SPComp.bind (SPComp.sample R) k) h₀ := by
  rw [prTrue_bind_eq_weighted]
  -- Lower bound the tsum by the single term at p = some (a₀, h₀)
  calc (Fintype.card R : ℝ≥0∞)⁻¹ * prTrue (k a₀) h₀
      = (SPComp.sample R h₀ : PMF _) (some (a₀, h₀)) *
        (match (some (a₀, h₀)) with | some ⟨a, h'⟩ => prTrue (k a) h' | none => 0) := by
        simp only [SPComp.sample, SDistr.bind, PMF.bind_apply]
        rw [tsum_eq_single (some a₀)]
        · simp [SDistr.uniform_apply_some, SDistr.pure, PMF.pure_apply]
        · intro b hb; cases b with
          | none => simp [SDistr.uniform_apply_none]
          | some a =>
            have : a ≠ a₀ := fun h => hb (congrArg some h)
            simp [SDistr.uniform_apply_some, SDistr.pure, PMF.pure_apply,
              show ¬(some (a₀, h₀) = some (a, h₀)) from by simp [this.symm]]
    _ ≤ ∑' p, (SPComp.sample R h₀ : PMF _) p *
        (match p with | some ⟨a, h'⟩ => prTrue (k a) h' | none => 0) :=
        ENNReal.le_tsum (some (a₀, h₀))

/-! ## Forking Lemma -/

/-- Conditional acceptance probability for a fixed commitment `c`. -/
noncomputable def condAccProb [Fintype R] [Nonempty R]
    (A : ForkableAdversary X C R Y) (x : X) (accept : Y → Bool)
    (c : C) (h₀ : Heap) : ℝ≥0∞ :=
  prTrue (SPComp.bind (SPComp.sample R) fun e => SPComp.pure (accept (A.respond x c e))) h₀

/-- Conditional fork success probability for a fixed commitment `c`. -/
noncomputable def condForkProb [Fintype R] [Nonempty R] [DecidableEq R]
    (A : ForkableAdversary X C R Y) (x : X) (accept : Y → Bool)
    (c : C) (h₀ : Heap) : ℝ≥0∞ :=
  prTrue (SPComp.bind (SPComp.sample R) fun e₁ =>
    SPComp.bind (SPComp.sample R) fun e₂ =>
      SPComp.pure (accept (A.respond x c e₁) && accept (A.respond x c e₂) &&
        decide (e₁ ≠ e₂))) h₀

/-- Helper: double SPComp.sample reduces to nested SDistr.uniform.bind at the SDistr level. -/
private theorem double_sample_sdisrt [Fintype R] [Nonempty R] {β : Type}
    (f : R → R → β) (h₀ : Heap) :
    (SPComp.bind (SPComp.sample R) fun e₁ =>
      SPComp.bind (SPComp.sample R) fun e₂ =>
        SPComp.pure (f e₁ e₂)) h₀ =
    (SDistr.uniform R).bind (fun e₁ =>
      (SDistr.uniform R).bind (fun e₂ =>
        SDistr.pure (f e₁ e₂, h₀))) := by
  simp only [SPComp.bind_def, SPComp.sample, SPComp.pure]
  rw [SDistr.bind_assoc]; congr 1; funext e₁; rw [SDistr.pure_bind]
  rw [SDistr.bind_assoc]; congr 1; funext e₂; rw [SDistr.pure_bind]

/-- prTrue of two independent samples from R then applying a pure Boolean function.
    The result counts accepting pairs divided by N². -/
theorem prTrue_double_sample_pure_bool [Fintype R] [Nonempty R]
    (f : R → R → Bool) (h₀ : Heap) :
    prTrue (SPComp.bind (SPComp.sample R) fun e₁ =>
      SPComp.bind (SPComp.sample R) fun e₂ =>
        SPComp.pure (f e₁ e₂)) h₀ =
    ((Finset.univ ×ˢ Finset.univ).filter (fun p : R × R => f p.1 p.2)).card /
      (Fintype.card R : ℝ≥0∞) ^ 2 := by
  unfold prTrue
  rw [double_sample_sdisrt]
  -- Now: ∑' h, ((uniform R).bind(fun e₁ => (uniform R).bind(fun e₂ =>
  --   SDistr.pure(f e₁ e₂, h₀))))(some(true,h)) = count / N²
  -- Expand outer SDistr.bind and PMF.bind_apply
  simp only [SDistr.bind, PMF.bind_apply]
  -- Now expand the inner tsum_option_split on the outermost Option sum
  simp_rw [tsum_option_split]
  simp only [SDistr.uniform_apply_none, zero_mul, zero_add, SDistr.uniform_apply_some,
    SDistr.fail_apply_some]
  -- Expand inner PMF.bind_apply
  simp only [PMF.bind_apply]
  simp_rw [tsum_option_split]
  simp only [SDistr.uniform_apply_none, zero_mul, zero_add, SDistr.fail_apply_some]
  simp only [SDistr.uniform_apply_some, SDistr.pure, PMF.pure_apply, Option.some.injEq,
    Prod.mk.injEq, mul_ite, mul_one, mul_zero]
  -- Extract h = h₀ from outer sum
  have h1 : ∀ h' : Heap, h' ≠ h₀ → ∑' (e₁ : R), (Fintype.card R : ℝ≥0∞)⁻¹ *
      ∑' (e₂ : R), (if true = f e₁ e₂ ∧ h' = h₀
        then (Fintype.card R : ℝ≥0∞)⁻¹ else 0) = 0 := by
    intro h' hne; simp only [hne, and_false, ite_false, tsum_zero, mul_zero, tsum_zero]
  rw [tsum_eq_single h₀ h1]; simp only [and_true]
  -- Goal: ∑' h e₁, N⁻¹ * ∑' e₂, (if true = f e₁ e₂ ∧ h = h₀ then N⁻¹ else 0) = count / N²
  -- Convert tsums to finite sums, simplify eq_comm
  simp_rw [show ∀ e₁ e₂, (true = f e₁ e₂) = (f e₁ e₂ = true) from fun _ _ => propext eq_comm]
  simp_rw [tsum_eq_sum (s := Finset.univ) (by simp)]
  simp_rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- Goal: ∑ x, N⁻¹ * (↑|{a : f x a}| * N⁻¹) = count / N²
  rw [sq, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp)]
  -- RHS: N⁻¹ * N⁻¹ * count
  -- Factor: ∑ e₁, N⁻¹ * (|filter e₂| * N⁻¹) = N⁻¹ * N⁻¹ * ∑ e₁, ↑|filter e₂|
  conv_lhs => arg 2; ext e₁; rw [mul_comm _ (Fintype.card R : ℝ≥0∞)⁻¹, ← mul_assoc]
  rw [← Finset.mul_sum]; ring_nf
  congr 1
  -- ∑ e₁ ∈ univ, ↑|{e₂ : f e₁ e₂}| = ↑|{(e₁,e₂) ∈ univ ×ˢ univ : f e₁ e₂}|
  norm_cast
  simp only [Finset.card_filter, Finset.sum_product]

/-- The conditional fork probability equals acc_c² - acc_c/|R| (exact counting). -/
theorem condForkProb_eq [Fintype R] [Nonempty R] [DecidableEq R]
    (A : ForkableAdversary X C R Y) (x : X) (accept : Y → Bool)
    (c : C) (h₀ : Heap) :
    condForkProb A x accept c h₀ =
      condAccProb A x accept c h₀ ^ 2 -
      condAccProb A x accept c h₀ / Fintype.card R := by
  set g : R → Bool := fun e => accept (A.respond x c e) with hg
  set N := (Fintype.card R : ℝ≥0∞) with hN_def
  set S := Finset.univ.filter (fun e => g e = true) with hS_def
  set s := S.card with hs_def
  -- Step 1: Express condAccProb = s / N
  have h_acc : condAccProb A x accept c h₀ = ↑s / N := by
    unfold condAccProb; rw [prTrue_sample_pure_bool]
  rw [h_acc]
  -- Step 2: Express condForkProb using prTrue_double_sample_pure_bool
  have h_fork : condForkProb A x accept c h₀ =
      ↑((S ×ˢ S).filter (fun p : R × R => decide (p.1 ≠ p.2))).card / N ^ 2 := by
    unfold condForkProb
    rw [prTrue_double_sample_pure_bool (fun e₁ e₂ => g e₁ && g e₂ && decide (e₁ ≠ e₂))]
    congr 1; norm_cast; congr 1
    -- Show: filter(g(p.1) && g(p.2) && p.1≠p.2, univ×univ) = filter(p.1≠p.2, S×S)
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨ha, hb⟩, hne⟩
      exact ⟨⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩,
             Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩, hne⟩
    · rintro ⟨⟨ha, hb⟩, hne⟩
      exact ⟨⟨(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2⟩, hne⟩
  -- Step 3: The filtered set is S.offDiag
  have h_count : ((S ×ˢ S).filter (fun p : R × R => decide (p.1 ≠ p.2))).card =
      S.offDiag.card := by
    congr 1; ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, decide_eq_true_eq, Finset.mem_offDiag]
    tauto
  -- Step 4: offDiag.card = s * s - s
  have h_offdiag : S.offDiag.card = s * s - s := by
    rw [Finset.offDiag_card]
  rw [h_fork, h_count, h_offdiag]
  -- Step 5: Arithmetic: ↑(s*s-s)/N² = (↑s/N)² - (↑s/N)/N
  -- Rewrite RHS to common denominator N²
  -- (↑s / N) / N = ↑s / (N * N) = ↑s / N²
  conv_rhs => rw [show (↑s : ℝ≥0∞) / N / N = ↑s / N ^ 2 from by
    simp only [div_eq_mul_inv, mul_assoc, sq]; congr 1
    rw [← ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]]
  -- (↑s / N) ^ 2 = ↑s² / N²
  conv_rhs => rw [show ((↑s : ℝ≥0∞) / N) ^ 2 = ↑s ^ 2 / N ^ 2 from by
    simp only [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow]]
  -- Goal: ↑(s*s-s) / N^2 = ↑s^2 / N^2 - ↑s / N^2
  have hN_ne : (N : ℝ≥0∞) ≠ 0 := by
    simp [hN_def, Fintype.card_ne_zero]
  rw [← ENNReal.sub_div (fun _ _ => pow_ne_zero _ hN_ne)]
  -- Goal: ↑(s*s-s) / N^2 = (↑s^2 - ↑s) / N^2
  congr 1
  rw [ENNReal.natCast_sub, Nat.cast_mul, ← sq]

/-- Acceptance probability decomposes over commitments. -/
theorem acceptProb_decompose [Fintype R] [Nonempty R]
    (A : ForkableAdversary X C R Y) (x : X) (accept : Y → Bool) :
    acceptProb A x accept =
      ∑' (p : Option (C × Heap)), (A.coins x Heap.empty : PMF _) p *
        (match p with
         | some ⟨c, h'⟩ => condAccProb A x accept c h'
         | none => 0) := by
  unfold acceptProb condAccProb
  simp only [SPComp.monad_bind_eq]
  rw [prTrue_bind_eq_weighted]

/-- Fork success probability decomposes over commitments. -/
theorem forkSuccProb_decompose [Fintype R] [Nonempty R] [DecidableEq R]
    (A : ForkableAdversary X C R Y) (x : X) (accept : Y → Bool) :
    forkSuccProb A x accept =
      ∑' (p : Option (C × Heap)), (A.coins x Heap.empty : PMF _) p *
        (match p with
         | some ⟨c, h'⟩ => condForkProb A x accept c h'
         | none => 0) := by
  unfold forkSuccProb condForkProb
  simp only [SPComp.monad_bind_eq]
  rw [prTrue_bind_eq_weighted]

/-- Main forking lemma (q = 1): the fork success probability is at least `acc² - acc/|R|`.

This is the Bellare-Neven bound specialized to a single oracle query:
  `Pr[fork succeeds] ≥ acc · (acc - 1/|R|) = acc² - acc/|R|`

where `acc` is the adversary's acceptance probability and `|R|` is the size
of the oracle response space. -/
theorem fork_success_ge [Fintype R] [Nonempty R] [DecidableEq R]
    (A : ForkableAdversary X C R Y) (x : X) (accept : Y → Bool) :
    forkSuccProb A x accept ≥
      acceptProb A x accept ^ 2 - acceptProb A x accept / Fintype.card R := by
  set acc := acceptProb A x accept with hacc_def
  set N := (Fintype.card R : ℝ≥0∞) with hN_def
  set w := fun p : Option (C × Heap) => (A.coins x Heap.empty : PMF _) p
  set f := fun p : Option (C × Heap) =>
    match p with
    | some ⟨c, h'⟩ => condAccProb A x accept c h'
    | none => (0 : ℝ≥0∞)
  -- Key decompositions
  have hacc : acc = ∑' p, w p * f p := by rw [hacc_def, acceptProb_decompose]
  have hfork : forkSuccProb A x accept =
      ∑' p, w p * (f p ^ 2 - f p / N) := by
    rw [forkSuccProb_decompose]
    congr 1; funext p; congr 1; cases p with
    | none => simp [f]
    | some pp => simp only [f]; rw [condForkProb_eq]
  -- Weight and function bounds (for Jensen)
  have hw_sum : ∑' p, w p ≤ 1 :=
    le_of_eq (A.coins x Heap.empty).tsum_coe
  have hf_le : ∀ p, f p ≤ 1 := by
    intro p; cases p with
    | none => simp [f]
    | some pp => simp only [f]; exact prTrue_le_one _ _
  -- Goal: forkSuccProb ≥ acc² - acc/N
  rw [ge_iff_le, tsub_le_iff_right]
  -- Need: acc² ≤ forkSuccProb + acc/N
  rw [hfork, hacc, sq (∑' p, w p * f p)]
  -- (∑ w·f)² ≤ ∑ w·f²  (Jensen)
  --          ≤ ∑ w·(f²-f/N) + ∑ w·(f/N)  (tsub + right ≥ left)
  --          = ∑ w·(f²-f/N) + (∑ w·f)/N   (factor out 1/N)
  calc (∑' p, w p * f p) * (∑' p, w p * f p)
      = (∑' p, w p * f p) ^ 2 := (sq _).symm
    _ ≤ ∑' p, w p * f p ^ 2 := jensen_sub_pmf_sq w f hw_sum hf_le
    _ ≤ ∑' p, w p * (f p ^ 2 - f p / N) + ∑' p, w p * (f p / N) := by
        calc ∑' p, w p * f p ^ 2
            ≤ ∑' p, (w p * (f p ^ 2 - f p / N) + w p * (f p / N)) :=
              ENNReal.tsum_le_tsum fun p => by
                rw [← mul_add]; gcongr; exact tsub_le_iff_right.mp le_rfl
          _ = _ := ENNReal.tsum_add
    _ = (∑' p, w p * (f p ^ 2 - f p / N)) + (∑' p, w p * f p) / N := by
        congr 1; rw [ENNReal.div_eq_inv_mul, ← ENNReal.tsum_mul_left]
        congr 1; funext p; rw [div_eq_mul_inv]; ring

end CatCrypt.Crypto.ForkingLemma
