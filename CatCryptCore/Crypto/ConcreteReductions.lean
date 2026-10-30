/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCLevels
public import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay

/-!
# Negligible functions and parametric UC emulation

This file defines negligible functions `ℕ → ℝ≥0∞`, UC emulation indexed by a security
parameter, and UC emulation with a negligible bound. It proves that negligible functions are
closed under addition, multiplication by a constant and multiplication by a polynomial, and
that negligible emulation is transitive, follows from perfect emulation, and follows from
emulation with bound `q λ * ε λ` for a polynomially bounded `q` and a negligible `ε`.

Negligibility is Mathlib's `Asymptotics.SuperpolynomialDecay` along `atTop` with parameter
`λ ↦ (λ : ℝ≥0∞)`. `isNegligible_iff_mul_pow_le` states it multiplicatively,
`f λ * λ ^ c ≤ 1` for every `c` and all large `λ`.

## Main definitions

* `IsNegligible` — `f` vanishes faster than every inverse polynomial
* `UCEmulatesParam` — UC emulation indexed by the security parameter `λ`
* `UCEmulatesNegl` — UC emulation with a negligible bound: `∃ ε` negligible, `∀ λ`,
  `UCEmulates (ε λ)`

## Main results

* `isNegligible_iff_mul_pow_le` — the multiplicative form of negligibility
* `isNegligible_zero`, `isNegligible_add`, `isNegligible_mul_const`, `isNegligible_poly_mul`,
  `isNegligible_of_le_eventually` — closure of negligible functions
* `UCEmulatesNegl_trans` — transitivity of negligible emulation
* `UCEmulatesNegl_of_perfect` — perfect emulation is negligible emulation
* `UCEmulatesNegl_hybrid_bound` — a hybrid argument over polynomially many steps

Relation to the literature: `CatCryptCore/Crypto/Complexity.md`.
-/

@[expose] public section

open scoped ENNReal

namespace CatCrypt.Crypto

/-! ## Negligible Functions -/

/-- A function `f : ℕ → ℝ≥0∞` is negligible if it has superpolynomial decay at infinity:
    for every degree `c`, `λ ^ c * f λ` tends to `0` as `λ → ∞`. This is Mathlib's
    `Asymptotics.SuperpolynomialDecay` along `atTop` with parameter `λ ↦ (λ : ℝ≥0∞)`.
    `isNegligible_iff_mul_pow_le` gives the multiplicative form
    `∀ c, ∃ N, ∀ λ ≥ N, f λ * λ ^ c ≤ 1`. -/
def IsNegligible (f : ℕ → ℝ≥0∞) : Prop :=
  Asymptotics.SuperpolynomialDecay Filter.atTop (fun n : ℕ => (n : ℝ≥0∞)) f

/-- Negligibility in multiplicative form: for every degree `c`, `f λ * λ ^ c ≤ 1` for all
    large `λ`. -/
theorem isNegligible_iff_mul_pow_le {f : ℕ → ℝ≥0∞} :
    IsNegligible f ↔ ∀ c : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → f n * (n : ℝ≥0∞) ^ c ≤ 1 := by
  constructor
  · intro hf c
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 <|
      (ENNReal.tendsto_nhds_zero.1 (hf c)) 1 one_pos
    exact ⟨N, fun n hn => by rw [mul_comm]; exact hN n hn⟩
  · intro hf z
    refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := hf (z + 1)
    have hinv := (ENNReal.tendsto_nhds_zero.1 ENNReal.tendsto_inv_nat_nhds_zero) ε hε
    filter_upwards [hinv, Filter.eventually_ge_atTop N] with n hn hNn
    refine le_trans ?_ hn
    rw [ENNReal.le_inv_iff_mul_le]
    calc (n : ℝ≥0∞) ^ z * f n * n = f n * (n : ℝ≥0∞) ^ (z + 1) := by ring
      _ ≤ 1 := hN n hNn

/-- The zero function is negligible. -/
theorem isNegligible_zero : IsNegligible (fun _ => 0) :=
  Asymptotics.superpolynomialDecay_zero _ _

/-- A function that is eventually zero is negligible. -/
theorem isNegligible_of_eventually_zero {f : ℕ → ℝ≥0∞}
    (h : ∃ N, ∀ n, N ≤ n → f n = 0) : IsNegligible f := by
  obtain ⟨N, hN⟩ := h
  refine (Asymptotics.superpolynomialDecay_zero _ _).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  simp [hN n hn]

/-- The sum of two negligible functions is negligible. -/
theorem isNegligible_add {f g : ℕ → ℝ≥0∞}
    (hf : IsNegligible f) (hg : IsNegligible g) :
    IsNegligible (fun n => f n + g n) :=
  Asymptotics.SuperpolynomialDecay.add hf hg

/-- Multiplication by a natural-number constant `k` preserves negligibility. -/
theorem isNegligible_mul_const {f : ℕ → ℝ≥0∞}
    (hf : IsNegligible f) (k : ℕ) :
    IsNegligible (fun n => k * f n) := fun z => by
  have h := ENNReal.Tendsto.const_mul (hf z) (Or.inr (ENNReal.natCast_ne_top k))
  rw [mul_zero] at h
  exact h.congr fun n => by ring

/-- Polynomial × negligible is negligible: if `f` is negligible and `g λ ≤ λ ^ d`,
    then `g * f` is negligible. -/
theorem isNegligible_poly_mul {f : ℕ → ℝ≥0∞} (d : ℕ)
    (g : ℕ → ℝ≥0∞) (hg : ∀ n, g n ≤ (n : ℝ≥0∞) ^ d)
    (hf : IsNegligible f) :
    IsNegligible (fun n => g n * f n) :=
  (Asymptotics.superpolynomialDecay_zero _ _).trans_eventuallyLE
    (Filter.Eventually.of_forall fun _ => zero_le) (hf.param_pow_mul d)
    (Filter.Eventually.of_forall fun _ => zero_le)
    (Filter.Eventually.of_forall fun n => by
      simp only [Pi.mul_apply, Pi.pow_apply]
      gcongr
      exact hg n)

/-- A function eventually below a negligible function is negligible. -/
theorem isNegligible_of_le_eventually {f g : ℕ → ℝ≥0∞} (hf : IsNegligible f)
    (h : ∃ N, ∀ n, N ≤ n → g n ≤ f n) : IsNegligible g :=
  (Asymptotics.superpolynomialDecay_zero _ _).trans_eventuallyLE
    (Filter.Eventually.of_forall fun _ => zero_le) hf
    (Filter.Eventually.of_forall fun _ => zero_le) (Filter.eventually_atTop.2 h)

/-! ## Parametric UC Emulation -/

open UCMonad

variable {T : Type → Type} [UCMonadMetric T]

/-- UC emulation indexed by security parameter. -/
def UCEmulatesParam (ε : ℕ → ℝ≥0∞)
    {hon out leak view : Type}
    (π F : ℕ → hon → T (out ⊕ leak)) : Prop :=
  ∀ n, UCEmulates (T := T) (view := view) (ε n) (π n) (F n)

/-- Negligible UC security: there exists a negligible bound. -/
def UCEmulatesNegl
    {hon out leak view : Type}
    (π F : ℕ → hon → T (out ⊕ leak)) : Prop :=
  ∃ ε, IsNegligible ε ∧ UCEmulatesParam (T := T) (view := view) ε π F

/-- Perfect emulation at all security parameters gives negligible security. -/
theorem UCEmulatesNegl_of_perfect
    {hon out leak view : Type}
    {π F : ℕ → hon → T (out ⊕ leak)}
    (h : ∀ n, UCEmulates (T := T) (view := view) 0 (π n) (F n)) :
    UCEmulatesNegl (T := T) (view := view) π F :=
  ⟨fun _ => 0, isNegligible_zero, fun n => UCEmulates_mono (h n) (le_refl _)⟩

/-- Transitivity of negligible UC emulation (same-interface).

    If `π₁ ≈_negl π₂` and `π₂ ≈_negl π₃`, then `π₁ ≈_negl π₃`.
    The bound is `ε₁ + ε₂`, which is negligible by `isNegligible_add`. -/
theorem UCEmulatesNegl_trans
    {hon out leak view : Type}
    {π₁ π₂ π₃ : ℕ → hon → T (out ⊕ leak)}
    (h₁ : UCEmulatesNegl (T := T) (view := view) π₁ π₂)
    (h₂ : UCEmulatesNegl (T := T) (view := view) π₂ π₃) :
    UCEmulatesNegl (T := T) (view := view) π₁ π₃ := by
  obtain ⟨ε₁, hε₁, hUC₁⟩ := h₁
  obtain ⟨ε₂, hε₂, hUC₂⟩ := h₂
  exact ⟨fun n => ε₁ n + ε₂ n, isNegligible_add hε₁ hε₂,
    fun n => UCEmulates_trans (hUC₁ n) (hUC₂ n)⟩

/-- Monotonicity: if `ε` is negligible and UCEmulates holds pointwise. -/
theorem UCEmulatesNegl_of_le
    {hon out leak view : Type}
    {π F : ℕ → hon → T (out ⊕ leak)}
    {ε : ℕ → ℝ≥0∞}
    (hε : IsNegligible ε)
    (h : ∀ n, UCEmulates (T := T) (view := view) (ε n) (π n) (F n)) :
    UCEmulatesNegl (T := T) (view := view) π F :=
  ⟨ε, hε, h⟩

/-- Hybrid bound: if each step has bound `ε` and there are `q n` steps
    (polynomial in n), then `q * ε` is negligible when `ε` is.

    This is the key theorem for hybrid argument reductions. -/
theorem UCEmulatesNegl_hybrid_bound
    {hon out leak view : Type}
    {π F : ℕ → hon → T (out ⊕ leak)}
    (q : ℕ → ℕ) (ε : ℕ → ℝ≥0∞) (hε : IsNegligible ε)
    (hq : ∃ d, ∀ n, (q n : ℝ≥0∞) ≤ (n : ℝ≥0∞) ^ d)
    (h : ∀ n, UCEmulates (T := T) (view := view) (q n * ε n) (π n) (F n)) :
    UCEmulatesNegl (T := T) (view := view) π F := by
  obtain ⟨d, hd⟩ := hq
  exact ⟨fun n => q n * ε n,
    isNegligible_poly_mul d (fun n => (q n : ℝ≥0∞)) hd hε, h⟩

/-! ## Concrete Reduction Composition -/

/-- Two-step concrete reduction: if step 1 reduces to bound `ε₁` and
    step 2 to bound `ε₂`, the composition has bound `ε₁ + ε₂`. -/
theorem concrete_reduction_compose
    {hon out leak view : Type}
    {ε₁ ε₂ : ℕ → ℝ≥0∞}
    {π₁ π₂ π₃ : ℕ → hon → T (out ⊕ leak)}
    (h₁ : UCEmulatesParam (T := T) (view := view) ε₁ π₁ π₂)
    (h₂ : UCEmulatesParam (T := T) (view := view) ε₂ π₂ π₃) :
    UCEmulatesParam (T := T) (view := view) (fun n => ε₁ n + ε₂ n) π₁ π₃ :=
  fun n => UCEmulates_trans (h₁ n) (h₂ n)

/-- From concrete parameterized bound to negligible, given the bound is negligible. -/
theorem UCEmulatesParam_to_negl
    {hon out leak view : Type}
    {ε : ℕ → ℝ≥0∞}
    {π F : ℕ → hon → T (out ⊕ leak)}
    (hε : IsNegligible ε)
    (h : UCEmulatesParam (T := T) (view := view) ε π F) :
    UCEmulatesNegl (T := T) (view := view) π F :=
  ⟨ε, hε, h⟩

end CatCrypt.Crypto
