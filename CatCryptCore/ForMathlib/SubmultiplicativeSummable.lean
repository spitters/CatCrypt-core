/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Submultiplicative sequences tending to zero are summable

Mathlib candidate. Both results belong in `Mathlib/Analysis/SpecificLimits/Basic.lean`,
beside `summable_geometric_of_lt_one`.

## Main results

* `le_pow_mul_of_le_mul` — a nonnegative submultiplicative real sequence satisfies
  `a (m * N + r) ≤ a N ^ m * a r`;
* `summable_of_le_mul_of_tendsto_zero` — a nonnegative submultiplicative real
  sequence tending to `0` is summable.
-/

@[expose] public section

set_option autoImplicit false

open Filter Topology

/-- A nonnegative submultiplicative sequence is bounded along residue classes:
    `a(m N + r) ≤ a(N)^m · a(r)`. -/
theorem le_pow_mul_of_le_mul {a : ℕ → ℝ} (h0 : ∀ n, 0 ≤ a n)
    (hmul : ∀ m n, a (m + n) ≤ a m * a n) (N m r : ℕ) :
    a (m * N + r) ≤ a N ^ m * a r := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc a ((m + 1) * N + r) = a (N + (m * N + r)) := by congr 1; ring
      _ ≤ a N * a (m * N + r) := hmul _ _
      _ ≤ a N * (a N ^ m * a r) := mul_le_mul_of_nonneg_left ih (h0 _)
      _ = a N ^ (m + 1) * a r := by ring

/-- A nonnegative submultiplicative real sequence tending to `0` is summable. -/
theorem summable_of_le_mul_of_tendsto_zero {a : ℕ → ℝ} (h0 : ∀ n, 0 ≤ a n)
    (hmul : ∀ m n, a (m + n) ≤ a m * a n) (ht : Tendsto a atTop (𝓝 0)) :
    Summable a := by
  obtain ⟨N0, hN0⟩ :=
    (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists_forall_of_atTop
  have hN : a (N0 + 1) < 1 / 2 := hN0 (N0 + 1) (by omega)
  have hgeom : Summable fun p : ℕ × Fin (N0 + 1) => (1 / 2 : ℝ) ^ p.1 * a p.2 :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).mul_of_nonneg
      (Summable.of_finite (f := fun r : Fin (N0 + 1) => a r)) (fun _ => by positivity)
      (fun r => h0 _)
  rw [← (Nat.divModEquiv (N0 + 1)).symm.summable_iff]
  refine Summable.of_nonneg_of_le (fun p => h0 _) (fun p => ?_) hgeom
  obtain ⟨m, r⟩ := p
  have h1 := le_pow_mul_of_le_mul h0 hmul (N0 + 1) m r
  have h2 : a (N0 + 1) ^ m ≤ (1 / 2) ^ m := pow_le_pow_left₀ (h0 _) hN.le m
  have h3 := mul_le_mul_of_nonneg_right h2 (h0 r)
  simp only [Function.comp_apply, Nat.divModEquiv]
  exact h1.trans h3
