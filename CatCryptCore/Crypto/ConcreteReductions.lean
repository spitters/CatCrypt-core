/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCLevels

/-!
# Negligible functions and parametric UC emulation

This file defines negligible functions `ℕ → ℝ≥0∞`, UC emulation indexed by a security
parameter, and UC emulation with a negligible bound. It proves that negligible functions are
closed under addition, multiplication by a constant and multiplication by a polynomial, and
that negligible emulation is transitive, follows from perfect emulation, and follows from
emulation with bound `q λ * ε λ` for a polynomially bounded `q` and a negligible `ε`.

Negligibility is stated multiplicatively, `f λ * λ ^ c ≤ 1` for every `c` and all large
`λ`, which avoids division in `ℝ≥0∞`; for `λ > 0` it is equivalent to `f λ ≤ 1 / λ ^ c`.

## Main definitions

* `IsNegligible` — `f` vanishes faster than every inverse polynomial
* `UCEmulatesParam` — UC emulation indexed by the security parameter `λ`
* `UCEmulatesNegl` — UC emulation with a negligible bound: `∃ ε` negligible, `∀ λ`,
  `UCEmulates (ε λ)`

## Main results

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

/-- A function `f : ℕ → ℝ≥0∞` is negligible if for every polynomial degree `c`,
    there exists `N` such that `f λ * λ^c ≤ 1` for all `λ ≥ N`.

    This is a multiplicative formulation avoiding ENNReal division.
    Equivalent to the standard `∀ c, ∃ N, ∀ λ ≥ N, f λ ≤ λ^{-c}`. -/
def IsNegligible (f : ℕ → ℝ≥0∞) : Prop :=
  ∀ c : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → f n * (n : ℝ≥0∞) ^ c ≤ 1

/-- The zero function is negligible. -/
theorem isNegligible_zero : IsNegligible (fun _ => 0) := by
  intro c; exact ⟨0, fun _ _ => by simp⟩

/-- A constant function (> 0) that tends to 0 is negligible.
    In particular, `fun _ => 0` is negligible (see above). -/
theorem isNegligible_of_eventually_zero {f : ℕ → ℝ≥0∞}
    (h : ∃ N, ∀ n, N ≤ n → f n = 0) : IsNegligible f := by
  obtain ⟨N, hN⟩ := h
  intro c; exact ⟨N, fun n hn => by simp [hN n hn]⟩

/-- Sum of negligible functions is negligible.

    Given degree `c`, use `f(c)` and `g(c)` to get `N₁` and `N₂`.
    For `λ ≥ max(N₁, N₂)`: `(f λ + g λ) * λ^c ≤ 1 + 1 = 2`.
    The bound `≤ 2` (not `≤ 1`) is acceptable for ℝ≥0∞ negligibility
    since we can always shift by 1: use `f(c+1)` and `g(c+1)` instead.
    Then for `λ ≥ max(N₁', N₂', 1)`:
    `(f λ + g λ) * λ^c ≤ f λ * λ^(c+1)/λ + g λ * λ^(c+1)/λ ≤ 1/λ + 1/λ`.
    In the multiplicative formulation: `(f+g) * λ^c ≤ f*λ^c + g*λ^c ≤ 1 + 1`. -/
theorem isNegligible_add {f g : ℕ → ℝ≥0∞}
    (hf : IsNegligible f) (hg : IsNegligible g) :
    IsNegligible (fun n => f n + g n) := by
  intro c
  obtain ⟨N₁, hN₁⟩ := hf (c + 1)
  obtain ⟨N₂, hN₂⟩ := hg (c + 1)
  refine ⟨max (max N₁ N₂) 2, fun n hn => ?_⟩
  have h1 := hN₁ n (le_trans (le_max_left _ _) (le_of_max_le_left hn))
  have h2 := hN₂ n (le_trans (le_max_right _ _) (le_of_max_le_left hn))
  have hn2 : 2 ≤ n := le_of_max_le_right hn
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hntop : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  rw [show (1 : ℝ≥0∞) = (n : ℝ≥0∞) / (n : ℝ≥0∞) from (ENNReal.div_self hn0 hntop).symm]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hn0) (Or.inl hntop)).mpr <|
    calc (f n + g n) * (n : ℝ≥0∞) ^ c * (n : ℝ≥0∞)
        = f n * ((n : ℝ≥0∞) ^ c * (n : ℝ≥0∞)) + g n * ((n : ℝ≥0∞) ^ c * (n : ℝ≥0∞)) := by ring
      _ = f n * (n : ℝ≥0∞) ^ (c + 1) + g n * (n : ℝ≥0∞) ^ (c + 1) := by congr 1
      _ ≤ 1 + 1 := add_le_add h1 h2
      _ = 2 := by norm_num
      _ ≤ (n : ℝ≥0∞) := by exact_mod_cast hn2

/-- Scalar multiplication preserves negligibility.

    More precisely: `k * f` is negligible when `f` is negligible
    (where `k : ℕ` is a constant). -/
theorem isNegligible_mul_const {f : ℕ → ℝ≥0∞}
    (hf : IsNegligible f) (k : ℕ) :
    IsNegligible (fun n => k * f n) := by
  intro c
  obtain ⟨N, hN⟩ := hf (c + 1)
  refine ⟨max (max N k) 1, fun n hn => ?_⟩
  have hfn := hN n (le_trans (le_max_left _ _) (le_of_max_le_left hn))
  have hnk : k ≤ n := le_trans (le_max_right _ _) (le_of_max_le_left hn)
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hntop : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  rw [show (1 : ℝ≥0∞) = (n : ℝ≥0∞) / (n : ℝ≥0∞) from (ENNReal.div_self hn0 hntop).symm]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hn0) (Or.inl hntop)).mpr <|
    calc (k : ℝ≥0∞) * f n * (n : ℝ≥0∞) ^ c * (n : ℝ≥0∞)
        = (k : ℝ≥0∞) * (f n * (n : ℝ≥0∞) ^ (c + 1)) := by rw [pow_succ]; ring
      _ ≤ (k : ℝ≥0∞) * 1 := by gcongr
      _ = (k : ℝ≥0∞) := mul_one _
      _ ≤ (n : ℝ≥0∞) := by exact_mod_cast hnk

/-- Polynomial × negligible is negligible.

    If `f` is negligible and `g λ ≤ λ^d` (polynomial bound),
    then `g * f` is negligible.

    Proof: Given degree `c`, use `f(c + d)`. Then:
    `g λ * f λ * λ^c ≤ λ^d * f λ * λ^c = f λ * λ^(c+d) ≤ 1`. -/
theorem isNegligible_poly_mul {f : ℕ → ℝ≥0∞} (d : ℕ)
    (g : ℕ → ℝ≥0∞) (hg : ∀ n, g n ≤ (n : ℝ≥0∞) ^ d)
    (hf : IsNegligible f) :
    IsNegligible (fun n => g n * f n) := by
  intro c
  obtain ⟨N, hN⟩ := hf (c + d)
  refine ⟨N, fun n hn => ?_⟩
  calc g n * f n * (n : ℝ≥0∞) ^ c
      ≤ (n : ℝ≥0∞) ^ d * f n * (n : ℝ≥0∞) ^ c := by gcongr; exact hg n
    _ = f n * ((n : ℝ≥0∞) ^ d * (n : ℝ≥0∞) ^ c) := by ring
    _ = f n * (n : ℝ≥0∞) ^ (c + d) := by rw [← pow_add]; ring
    _ ≤ 1 := hN n hn

/-- A function eventually below a negligible function is negligible. -/
theorem isNegligible_of_le_eventually {f g : ℕ → ℝ≥0∞} (hf : IsNegligible f)
    (h : ∃ N, ∀ n, N ≤ n → g n ≤ f n) : IsNegligible g := by
  obtain ⟨N, hN⟩ := h
  intro c
  obtain ⟨M, hM⟩ := hf c
  refine ⟨max N M, fun n hn => ?_⟩
  exact (mul_le_mul_left (hN n (le_of_max_le_left hn)) _).trans (hM n (le_of_max_le_right hn))

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
