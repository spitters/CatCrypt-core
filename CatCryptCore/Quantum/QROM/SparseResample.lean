/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.RoundOracle

/-!
# Resampling an oracle and the classical rounds on a sparse random set

A multi-round adversary `A : QAdvMRGen m n w q k c a` is run against two random
oracles `H ω` and `H' ω` that agree with a fixed `H₀` outside a random set
`D ω` of oracle points, whose law `μ` satisfies `∑_ω μ ω · [x ∈ D ω] ≤ λ` at
every point `x`. The averaged acceptance probabilities differ by at most
`8 Q λ^(1/2)`, with `Q = flatQ q k q` the total query count of `A`.

At each `ω` the semi-classical one-way-to-hiding bound is applied to both
oracles with the punctured set `D ω`; `Pr[out = 1 ∧ ¬Find]` and `Pr[Find]`
are the same for both oracles and for `H₀`, so the difference is at most
`4 (Q · Pr[Find : H₀, D ω])^(1/2)`. Jensen's inequality for the square root
and the averaged Find bound `∑_ω μ ω · Pr[Find] ≤ 4 Q λ` give the constant.

If the round function `f` is in addition replaced by `f' ω₂`, which agrees with
`f` outside a random set `E ω₂` of round inputs drawn independently of the
oracle with `∑_{ω₂} ν ω₂ · [y ∈ E ω₂] ≤ λ'`, the classical rounds add
`k λ'` (`rounds_upto_bad`).

## Main results

* `absDiff_prOutMRGen_le_four_rpow_prFind` — two oracles agreeing outside `S`
  change `Pr[out = 1]` by at most `4 (Q · Pr[Find])^(1/2)`
* `prOutMRGen_resample_oracle_le` — the oracle-only resampling bound
  `8 Q λ^(1/2)`
* `prOutMRGen_resample_le` — the bound `8 Q λ^(1/2) + k λ'` for resampling the
  oracle and the round function

## References

* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019, ePrint 2018/904], Theorems 1 and 2
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

noncomputable section

namespace CatCrypt.Quantum.QROM

section Resample

variable {m n w q k c a : ℕ} [NeZero n] [NeZero c]

/-- One-way to hiding with two oracles for a general adversary: if `H` and
`H'` agree outside `S`, then
`|Pr[out = 1 : H] − Pr[out = 1 : H']| ≤ 4 (Q · Pr[Find : H, S])^(1/2)`. -/
theorem absDiff_prOutMRGen_le_four_rpow_prFind (A : QAdvMRGen m n w q k c a)
    (H H' : Fin m → Fin n) (f : Fin c → Fin a) (S : Finset (Fin m))
    (hHH' : ∀ x, x ∉ S → H x = H' x) :
    absDiff (prOutMRGen A H f) (prOutMRGen A H' f) ≤
      4 * ((flatQ q k q : ℝ≥0∞) * prFindMRGen A H f S) ^ (1 / 2 : ℝ) := by
  have h₁ := o2h_semiclassical_gen A H f S
  have h₂ := o2h_semiclassical_gen A H' f S
  rw [← prOutNoFindMRGen_congr A H H' f S hHH', ← prFindMRGen_congr A H H' f S hHH'] at h₂
  calc absDiff (prOutMRGen A H f) (prOutMRGen A H' f)
      ≤ absDiff (prOutMRGen A H f) (prOutNoFindMRGen A H f S) +
          absDiff (prOutNoFindMRGen A H f S) (prOutMRGen A H' f) :=
        absDiff_triangle _ _ _
    _ ≤ 2 * ((flatQ q k q : ℝ≥0∞) * prFindMRGen A H f S) ^ (1 / 2 : ℝ) +
          2 * ((flatQ q k q : ℝ≥0∞) * prFindMRGen A H f S) ^ (1 / 2 : ℝ) := by
        rw [absDiff_comm (prOutNoFindMRGen A H f S)]
        exact add_le_add h₁ h₂
    _ = 4 * ((flatQ q k q : ℝ≥0∞) * prFindMRGen A H f S) ^ (1 / 2 : ℝ) := by
        ring

/-- Resampling the oracle on a sparse random set: if `H ω` and `H' ω` agree
with `H₀` outside `D ω`, and the law `μ` of `ω` satisfies
`∑_ω μ ω · [x ∈ D ω] ≤ λ` at every point `x`, then the averaged acceptance
probabilities of `A` differ by at most `8 Q λ^(1/2)` with `Q = flatQ q k q`.
The values outside `D ω` are those of `H₀`, independent of `D`. -/
theorem prOutMRGen_resample_oracle_le {Ω : Type} [Fintype Ω] (A : QAdvMRGen m n w q k c a)
    (f : Fin c → Fin a) (H H' : Ω → Fin m → Fin n) (D : Ω → Finset (Fin m))
    (H₀ : Fin m → Fin n) (μ : Ω → ℝ≥0∞) (lam : ℝ≥0∞) (hμ : ∑ ω, μ ω = 1)
    (hH : ∀ ω x, x ∉ D ω → H ω x = H₀ x) (hH' : ∀ ω x, x ∉ D ω → H' ω x = H₀ x)
    (hlam : ∀ x, ∑ ω, μ ω * (if x ∈ D ω then 1 else 0) ≤ lam) :
    absDiff (∑ ω, μ ω * prOutMRGen A (H ω) f) (∑ ω, μ ω * prOutMRGen A (H' ω) f) ≤
      8 * (flatQ q k q : ℝ≥0∞) * lam ^ (1 / 2 : ℝ) := by
  set Q : ℝ≥0∞ := (flatQ q k q : ℝ≥0∞)
  have hstep : ∀ ω, absDiff (prOutMRGen A (H ω) f) (prOutMRGen A (H' ω) f) ≤
      4 * (Q * prFindMRGen A H₀ f (D ω)) ^ (1 / 2 : ℝ) := by
    intro ω
    have h := absDiff_prOutMRGen_le_four_rpow_prFind A (H ω) (H' ω) f (D ω)
      fun x hx => (hH ω x hx).trans (hH' ω x hx).symm
    rwa [prFindMRGen_congr A (H ω) H₀ f (D ω) (hH ω)] at h
  have hfind : ∑ ω, μ ω * prFindMRGen A H₀ f (D ω) ≤ 4 * Q * lam :=
    prFindMRGen_avg_le A f (fun _ => H₀) D H₀ μ lam (fun _ _ _ _ => rfl) hlam
  have hjensen : ∑ ω, μ ω * (Q * prFindMRGen A H₀ f (D ω)) ^ (1 / 2 : ℝ) ≤
      (Q * (4 * Q * lam)) ^ (1 / 2 : ℝ) := by
    refine (sum_mul_rpow_half_le μ _ hμ).trans ?_
    have hsum : ∑ ω, μ ω * (Q * prFindMRGen A H₀ f (D ω)) =
        Q * ∑ ω, μ ω * prFindMRGen A H₀ f (D ω) := by
      simp only [Finset.mul_sum, mul_left_comm]
    rw [hsum]
    gcongr
  have harith : 4 * (Q * (4 * Q * lam)) ^ (1 / 2 : ℝ) = 8 * Q * lam ^ (1 / 2 : ℝ) := by
    have hsq : Q * (4 * Q * lam) = (2 * Q) ^ (2 : ℝ) * lam := by
      rw [ENNReal.rpow_two]
      ring
    have h2q : ((2 * Q) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = 2 * Q := by
      rw [← ENNReal.rpow_mul]
      norm_num
    rw [hsq, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), h2q]
    ring
  calc absDiff (∑ ω, μ ω * prOutMRGen A (H ω) f) (∑ ω, μ ω * prOutMRGen A (H' ω) f)
      ≤ ∑ ω, absDiff (μ ω * prOutMRGen A (H ω) f) (μ ω * prOutMRGen A (H' ω) f) :=
        absDiff_sum_le _ _
    _ ≤ ∑ ω, μ ω * (4 * (Q * prFindMRGen A H₀ f (D ω)) ^ (1 / 2 : ℝ)) := by
        gcongr with ω
        exact (absDiff_mul_left_le _ _ _).trans (by gcongr; exact hstep ω)
    _ = 4 * ∑ ω, μ ω * (Q * prFindMRGen A H₀ f (D ω)) ^ (1 / 2 : ℝ) := by
        simp only [Finset.mul_sum, mul_left_comm]
    _ ≤ 4 * (Q * (4 * Q * lam)) ^ (1 / 2 : ℝ) := by gcongr
    _ = 8 * Q * lam ^ (1 / 2 : ℝ) := harith

/-- Resampling the oracle and the classical rounds on sparse random sets: if
`H ω` and `H' ω` agree with `H₀` outside `D ω`, with
`∑_ω μ ω · [x ∈ D ω] ≤ λ` at every point `x`, and the round function `f' ω₂`
agrees with `f` outside `E ω₂`, drawn independently with
`∑_{ω₂} ν ω₂ · [y ∈ E ω₂] ≤ λ'` at every round input `y`, then
`|E Pr[out = 1 : H, f] − E Pr[out = 1 : H', f']| ≤ 8 Q λ^(1/2) + k λ'` with
`Q = flatQ q k q`. -/
theorem prOutMRGen_resample_le {Ω Ω₂ : Type} [Fintype Ω] [Fintype Ω₂]
    (A : QAdvMRGen m n w q k c a) (H H' : Ω → Fin m → Fin n) (D : Ω → Finset (Fin m))
    (H₀ : Fin m → Fin n) (μ : Ω → ℝ≥0∞) (lam : ℝ≥0∞) (hμ : ∑ ω, μ ω = 1)
    (hH : ∀ ω x, x ∉ D ω → H ω x = H₀ x) (hH' : ∀ ω x, x ∉ D ω → H' ω x = H₀ x)
    (hlam : ∀ x, ∑ ω, μ ω * (if x ∈ D ω then 1 else 0) ≤ lam)
    (f : Fin c → Fin a) (f' : Ω₂ → Fin c → Fin a) (E : Ω₂ → Finset (Fin c))
    (ν : Ω₂ → ℝ≥0∞) (lam' : ℝ≥0∞) (hν : ∑ ω₂, ν ω₂ = 1)
    (hf : ∀ ω₂ y, y ∉ E ω₂ → f' ω₂ y = f y)
    (hlam' : ∀ y, ∑ ω₂, ν ω₂ * (if y ∈ E ω₂ then 1 else 0) ≤ lam') :
    absDiff (∑ ω, μ ω * prOutMRGen A (H ω) f)
        (∑ ω, μ ω * ∑ ω₂, ν ω₂ * prOutMRGen A (H' ω) (f' ω₂)) ≤
      8 * (flatQ q k q : ℝ≥0∞) * lam ^ (1 / 2 : ℝ) + k * lam' := by
  have hrounds : absDiff (∑ ω, μ ω * prOutMRGen A (H' ω) f)
      (∑ ω, μ ω * ∑ ω₂, ν ω₂ * prOutMRGen A (H' ω) (f' ω₂)) ≤ k * lam' := by
    calc absDiff (∑ ω, μ ω * prOutMRGen A (H' ω) f)
          (∑ ω, μ ω * ∑ ω₂, ν ω₂ * prOutMRGen A (H' ω) (f' ω₂))
        ≤ ∑ ω, absDiff (μ ω * prOutMRGen A (H' ω) f)
            (μ ω * ∑ ω₂, ν ω₂ * prOutMRGen A (H' ω) (f' ω₂)) := absDiff_sum_le _ _
      _ ≤ ∑ ω, μ ω * (k * lam') := by
        gcongr with ω
        exact (absDiff_mul_left_le _ _ _).trans
          (by gcongr; exact rounds_upto_bad A (H' ω) f f' E ν lam' hν hf hlam')
      _ = k * lam' := by rw [← Finset.sum_mul, hμ, one_mul]
  exact (absDiff_triangle _ _ _).trans
    (add_le_add (prOutMRGen_resample_oracle_le A f H H' D H₀ μ lam hμ hH hH' hlam) hrounds)

end Resample

end CatCrypt.Quantum.QROM
