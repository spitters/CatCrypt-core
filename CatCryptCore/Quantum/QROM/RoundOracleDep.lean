/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.RoundOracleLocal

/-!
# Classical rounds up to bad, for an adversary chosen by the random index

The local up-to-bad bound for the classical rounds of a multi-round adversary,
`rounds_upto_bad_local`, for an adversary `B (κ ω)` chosen by a key `κ ω` of the
random index `ω`. The conditioning of the hypothesis extends to the key: at every
key `j`, oracle `h₀`, outcome `y` and values `g` outside `y`, the event `y ∈ E ω`,
conditioned on `κ ω = j`, on `H ω = h₀` and on the values of `f ω` outside `y`,
has probability at most `λ` under `μ`. The average acceptance probabilities with
`f` and with `f'` then differ by at most `k · λ`.

## Main results

* `rounds_upto_bad_local_dep` — the averaged round bound `k · λ` for the adversary
  `B (κ ω)`
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct CatCrypt.Quantum.UnitaryChannel

noncomputable section

namespace CatCrypt.Quantum.QROM

variable {m n w q k c a : ℕ} [NeZero n]

/-- Up to bad in the classical rounds for an adversary `B (κ ω)` chosen by the
random index: let `f' ω` agree with `f ω` outside `E ω`, and let the event
`y ∈ E ω`, conditioned on the key `κ ω`, on `H ω` and on the values of `f ω`
outside `y`, have probability at most `λ` under `μ`, at every outcome `y`. Then
the average acceptance probabilities of `B (κ ω)` with `f` and with `f'` differ
by at most `k · λ`. -/
theorem rounds_upto_bad_local_dep {Ω K : Type} [Fintype Ω] [DecidableEq K]
    (B : K → QAdvMRGen m n w q k c a) (κ : Ω → K)
    (H : Ω → Fin m → Fin n) (f f' : Ω → Fin c → Fin a) (E : Ω → Finset (Fin c))
    (μ : Ω → ℝ≥0∞) (lam : ℝ≥0∞) (hμ : ∑ ω, μ ω ≤ 1)
    (hf : ∀ ω y, y ∉ E ω → f' ω y = f ω y)
    (hlam : ∀ (j : K) (y : Fin c) (h₀ : Fin m → Fin n) (g : Fin c → Fin a),
      ∑ ω, μ ω * (if κ ω = j ∧ H ω = h₀ ∧ ∀ y', y' ≠ y → f ω y' = g y' then 1 else 0) *
          (if y ∈ E ω then 1 else 0) ≤
        lam * ∑ ω, μ ω *
          (if κ ω = j ∧ H ω = h₀ ∧ ∀ y', y' ≠ y → f ω y' = g y' then 1 else 0)) :
    absDiff (∑ ω, μ ω * prOutMRGen (B (κ ω)) (H ω) (f ω))
        (∑ ω, μ ω * prOutMRGen (B (κ ω)) (H ω) (f' ω)) ≤
      k * lam := by
  set W : K → (Fin m → Fin n) → (Fin c → Fin a) → Fin c → ℝ := fun j h g y =>
    badW1 (oracleQ m n w h) g {y} k q (fun i => ((B j).seg 0 i).toQComp)
      (fun j' i => (Fin.tail (B j).seg j' i).toQComp) (B j).rounds (B j).init.val with hWdef
  have hW : ∀ j h g y, 0 ≤ W j h g y := fun j _ _ _ =>
    badW1_nonneg _ _ _ _ _ _ _ _ _ (B j).init.psd
  have hWsum : ∀ j h g, ∑ y, W j h g y ≤ k := by
    intro j h g
    simpa [(B j).init.tr_one] using sum_badW1_singleton_le (oracleQ m n w h) g k q _ _
      (B j).rounds (B j).init.val (B j).init.psd
  have hstep : ∀ ω, absDiff (prOutMRGen (B (κ ω)) (H ω) (f ω))
      (prOutMRGen (B (κ ω)) (H ω) (f' ω)) ≤
      ∑ y, (if y ∈ E ω then 1 else 0) * ENNReal.ofReal (W (κ ω) (H ω) (f ω) y) := by
    intro ω
    refine (absDiff_prOutMRGen_le_badW1 (B (κ ω)) (H ω) (hf ω)).trans ?_
    refine (ENNReal.ofReal_le_ofReal
      (badW1_le_sum_singleton _ _ _ _ _ _ _ _ _ (B (κ ω)).init.psd)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_sum_of_nonneg fun y _ => hW _ _ _ y, sum_mem_eq_sum_boole_mul]
  have hfib : ∀ y, ∑ ω, μ ω * (if y ∈ E ω then 1 else 0) *
      ENNReal.ofReal (W (κ ω) (H ω) (f ω) y) ≤
      lam * ∑ ω, μ ω * ENNReal.ofReal (W (κ ω) (H ω) (f ω) y) := by
    intro y
    have hκ : ∀ ω ω₀,
        ((κ ω, H ω, fun y' => if y' = y then none else some (f ω y')) =
          (κ ω₀, H ω₀, fun y' => if y' = y then none else some (f ω₀ y'))) ↔
        (κ ω = κ ω₀ ∧ H ω = H ω₀ ∧ ∀ y', y' ≠ y → f ω y' = f ω₀ y') := by
      simp only [Prod.mk.injEq, funext_iff]; grind
    refine sum_mul_boole_mul_le_of_fiber
      (fun ω => (κ ω, H ω, fun y' => if y' = y then none else some (f ω y'))) μ _
      (fun ω => y ∈ E ω) lam ?_ ?_
    · intro ω ω' he
      obtain ⟨h₀, h₁, h₂⟩ := (hκ ω ω').mp he
      simp only [hWdef, h₀, h₁]
      rw [badW1_congr _ (f := f ω') (f' := f ω) (fun y' hy' => h₂ y' (by simpa using hy'))]
    · simpa only [hκ] using fun ω₀ => hlam (κ ω₀) y (H ω₀) (f ω₀)
  calc absDiff (∑ ω, μ ω * prOutMRGen (B (κ ω)) (H ω) (f ω))
        (∑ ω, μ ω * prOutMRGen (B (κ ω)) (H ω) (f' ω))
      ≤ ∑ ω, absDiff (μ ω * prOutMRGen (B (κ ω)) (H ω) (f ω))
          (μ ω * prOutMRGen (B (κ ω)) (H ω) (f' ω)) :=
        absDiff_sum_le _ _
    _ ≤ ∑ ω, μ ω * absDiff (prOutMRGen (B (κ ω)) (H ω) (f ω))
          (prOutMRGen (B (κ ω)) (H ω) (f' ω)) :=
        Finset.sum_le_sum fun ω _ => absDiff_mul_left_le _ _ _
    _ ≤ ∑ ω, μ ω * ∑ y, (if y ∈ E ω then 1 else 0) *
          ENNReal.ofReal (W (κ ω) (H ω) (f ω) y) :=
        Finset.sum_le_sum fun ω _ => mul_le_mul_right (hstep ω) _
    _ = ∑ y, ∑ ω, μ ω * (if y ∈ E ω then 1 else 0) *
          ENNReal.ofReal (W (κ ω) (H ω) (f ω) y) := by
        simp only [Finset.mul_sum, mul_assoc]; rw [Finset.sum_comm]
    _ ≤ ∑ y, lam * ∑ ω, μ ω * ENNReal.ofReal (W (κ ω) (H ω) (f ω) y) :=
        Finset.sum_le_sum fun y _ => hfib y
    _ = lam * ∑ ω, μ ω * ENNReal.ofReal (∑ y, W (κ ω) (H ω) (f ω) y) := by
        simp only [ENNReal.ofReal_sum_of_nonneg fun y _ => hW _ _ _ y, Finset.mul_sum]
        rw [Finset.sum_comm]
    _ ≤ lam * ∑ ω, μ ω * k := by
        gcongr with ω
        exact (ENNReal.ofReal_le_ofReal (hWsum _ _ _)).trans (by simp)
    _ ≤ k * lam := by grw [← Finset.sum_mul, hμ, one_mul, mul_comm]

end CatCrypt.Quantum.QROM
