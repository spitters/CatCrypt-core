/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.MeasureReprogram

/-!
# The Fiat–Shamir reduction in the quantum random-oracle model

The reduction of Don, Fehr, Majenz and Schaffner (CRYPTO 2019) from the
Fiat–Shamir transform of an interactive commit–challenge–respond protocol to
the protocol itself, derived from `measure_reprogram_acc`.

A `q`-query prover is a `QAdv m n w q` whose final projector is replaced by
the verifier's projector `V(x, θ)`, a family `QVerifier m n w` indexed by the
commitment `x : Fin m` and the challenge `θ : Fin n`. The prover's commitment
is its measured query register `x'`. In the non-interactive game the oracle's
value at the commitment `x` is the challenge; in the interactive game the
simulator `simRun` of `MeasureReprogram` runs the prover against `H` up to a
uniform slot, measures the commitment `x`, receives a uniform challenge `θ`
and continues against `H[x ↦ θ]`, and the verifier checks `V(x, θ)`.

## Main definitions

* `QVerifier m n w` — a family of projectors `V(x, θ)`
* `QAdv.withVerifier A V x θ` — the prover `A` with final projector `V(x, θ)`
* `prFSAt A V H x` — the probability that `A` outputs the commitment `x` and is
  accepted when the oracle's value at `x` is a fresh uniform challenge
* `prIntAt A V H x t`, `prInt A V H x` — the probability that the simulator on
  the slot `t` commits to `x` and is accepted against a uniform challenge, and
  its average over the `2q + 1` slots
* `fsChain A H c t` — the simulator's commitment phase when the challenge to
  the commitment `x` is `c x`

## Main results

* `fiatShamir_measure_reprogram` — `prFSAt A V H x ≤ (2q + 1)² · prInt A V H x`
  (DFMS19, Theorem 2 with the challenge averaged)
* `fiatShamir_measure_reprogram_sum` — the same bound summed over the
  commitments: the Fiat–Shamir success probability is at most `(2q + 1)²` times
  the success probability of the interactive simulator
* `fiatShamir_random_oracle` — the bound for a uniformly random oracle `H`,
  with the verifier reading the challenge `H x`
* `sum_prInt_le_inv_of_unique_challenge` — if every commitment has at most one
  challenge with a nonzero verifier projector (special soundness on a statement
  outside the language), the interactive success probability is at most `1/n`
* `fiatShamir_unique_challenge` — then the Fiat–Shamir success probability is
  at most `(2q + 1)² / n` (DFMS19, Theorem 8 shape)

## References

* [Don, Fehr, Majenz, Schaffner — Security of the Fiat-Shamir Transformation in
  the Quantum Random-Oracle Model, CRYPTO 2019], Theorems 2, 7 and 8
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix Classical CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
  CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.Measurement

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Verifiers and provers -/

section Defs

variable {m n w q : ℕ}

/-- A verifier for commitments `Fin m` and challenges `Fin n`: the projector
    `V(x, θ)` accepts the prover's final state for the commitment `x` and the
    challenge `θ`. -/
structure QVerifier (m n w : ℕ) where
  /-- The projector `V(x, θ)`. -/
  proj : Fin m → Fin n → Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ
  proj_conjTranspose : ∀ x θ, (proj x θ)ᴴ = proj x θ
  proj_mul_self : ∀ x θ, proj x θ * proj x θ = proj x θ

/-- The prover `A` with its final projector replaced by `V(x, θ)`. -/
def QAdv.withVerifier (A : QAdv m n w q) (V : QVerifier m n w) (x : Fin m) (θ : Fin n) :
    QAdv m n w q where
  U := A.U
  init := A.init
  final := V.proj x θ
  final_conjTranspose := V.proj_conjTranspose x θ
  final_mul_self := V.proj_mul_self x θ

end Defs

section Game

variable {m n w q : ℕ} [NeZero n]

/-- The Fiat–Shamir success probability at the commitment `x`: `A` run against
    `H[x ↦ θ]` outputs `x` and `V(x, θ)` accepts, averaged over a uniform
    challenge `θ`. -/
def prFSAt (A : QAdv m n w q) (V : QVerifier m n w) (H : Fin m → Fin n) (x : Fin m) : ℝ≥0∞ :=
  (n : ℝ≥0∞)⁻¹ * ∑ θ, prOutAt (A.withVerifier V x θ) (Function.update H x θ) x

/-- The interactive success probability of the simulator on the slot `t` at
    the commitment `x`: the simulator measures the commitment `x`, the challenge
    `θ` is drawn uniformly, and `V(x, θ)` accepts. -/
def prIntAt (A : QAdv m n w q) (V : QVerifier m n w) (H : Fin m → Fin n) (x : Fin m)
    (t : Option (Fin q × Bool)) : ℝ≥0∞ :=
  (n : ℝ≥0∞)⁻¹ * ∑ θ, prSimAcc (A.withVerifier V x θ) H θ x t

/-- The interactive success probability of the simulator with a uniform slot
    among the `2q + 1` slots, at the commitment `x`. -/
def prInt (A : QAdv m n w q) (V : QVerifier m n w) (H : Fin m → Fin n) (x : Fin m) : ℝ≥0∞ :=
  ((2 * q + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∑ t, prIntAt A V H x t

/-- The Fiat–Shamir reduction at one commitment (DFMS19, Theorem 2, averaged
    over the challenge): the probability that `A` outputs `x` and is accepted
    when the oracle's value at `x` is a fresh uniform challenge is at most
    `(2q + 1)²` times the probability that the interactive simulator commits to
    `x` and is accepted. -/
theorem fiatShamir_measure_reprogram (A : QAdv m n w q) (V : QVerifier m n w)
    (H : Fin m → Fin n) (x : Fin m) :
    prFSAt A V H x ≤ ((2 * q + 1 : ℕ) : ℝ≥0∞) ^ 2 * prInt A V H x := by
  set N : ℝ≥0∞ := ((2 * q + 1 : ℕ) : ℝ≥0∞) with hN
  have hN0 : N ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr (2 * q).succ_ne_zero)
  have hNt : N ^ 2 ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  have hθ : ∀ θ, prOutAt (A.withVerifier V x θ) (Function.update H x θ) x ≤
      N ^ 2 * (N⁻¹ * ∑ t, prSimAcc (A.withVerifier V x θ) H θ x t) := fun θ => by
    rw [mul_comm]
    exact (ENNReal.div_le_iff hN0 hNt).mp (measure_reprogram_acc _ H x θ)
  calc prFSAt A V H x
      ≤ (n : ℝ≥0∞)⁻¹ * ∑ θ, N ^ 2 * (N⁻¹ * ∑ t, prSimAcc (A.withVerifier V x θ) H θ x t) := by
        unfold prFSAt
        gcongr with θ
        exact hθ θ
    _ = N ^ 2 * prInt A V H x := by
        simp only [prInt, prIntAt, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
        ring

/-- The Fiat–Shamir reduction summed over the commitments: the probability that
    `A` outputs some commitment `x` and is accepted against a fresh uniform
    challenge at `x` is at most `(2q + 1)²` times the success probability of the
    interactive simulator. -/
theorem fiatShamir_measure_reprogram_sum (A : QAdv m n w q) (V : QVerifier m n w)
    (H : Fin m → Fin n) :
    ∑ x, prFSAt A V H x ≤ ((2 * q + 1 : ℕ) : ℝ≥0∞) ^ 2 * ∑ x, prInt A V H x := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun x _ => fiatShamir_measure_reprogram A V H x

/-- Resampling one value of a function averages over that value: for every
    `f` and point `x`, `∑_H ∑_θ f (H[x ↦ θ]) = n · ∑_H f H`. -/
theorem sum_sum_update_eq (f : (Fin m → Fin n) → ℝ≥0∞) (x : Fin m) :
    ∑ H : Fin m → Fin n, ∑ θ : Fin n, f (Function.update H x θ) =
      (n : ℝ≥0∞) * ∑ H, f H := by
  have hshift : ∀ H : Fin m → Fin n, ∑ θ : Fin n, f (Function.update H x θ) =
      ∑ θ : Fin n, f (Function.update H x (θ + H x)) := fun H =>
    (Fintype.sum_equiv (Equiv.addRight (H x)) _ _ fun _ => rfl).symm
  have hbij : ∀ θ : Fin n, ∑ H : Fin m → Fin n, f (Function.update H x (θ + H x)) =
      ∑ H, f H := fun θ =>
    Fintype.sum_equiv
      { toFun := fun H => Function.update H x (θ + H x)
        invFun := fun G => Function.update G x (G x - θ)
        left_inv := fun H => by simp
        right_inv := fun G => by simp } _ _ fun _ => rfl
  simp only [hshift]
  rw [Finset.sum_comm]
  simp only [hbij, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The Fiat–Shamir reduction for a uniformly random oracle: over a uniform
    `H`, the probability that `A^H` outputs a commitment `x` accepted by
    `V(x, H x)` is at most `(2q + 1)²` times the success probability of the
    interactive simulator run with a uniform `H`. -/
theorem fiatShamir_random_oracle (A : QAdv m n w q) (V : QVerifier m n w) :
    (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
        ∑ H : Fin m → Fin n, ∑ x, prOutAt (A.withVerifier V x (H x)) H x ≤
      ((2 * q + 1 : ℕ) : ℝ≥0∞) ^ 2 *
        ((Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ * ∑ H : Fin m → Fin n, ∑ x, prInt A V H x) := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hnt : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hx : ∀ x : Fin m, ∑ H : Fin m → Fin n, prOutAt (A.withVerifier V x (H x)) H x =
      ∑ H : Fin m → Fin n, prFSAt A V H x := by
    intro x
    have h := sum_sum_update_eq (fun G => prOutAt (A.withVerifier V x (G x)) G x) x
    simp only [Function.update_self] at h
    simp only [prFSAt, ← Finset.mul_sum, h, ← mul_assoc, ENNReal.inv_mul_cancel hn0 hnt, one_mul]
  rw [mul_left_comm]
  gcongr
  rw [Finset.sum_comm, Finset.sum_congr rfl fun x _ => hx x, Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum fun H _ => fiatShamir_measure_reprogram_sum A V H

end Game

/-! ## Protocols with a unique accepting challenge -/

section Unique

variable {m n w q : ℕ} [NeZero n]

/-- The simulator's commitment phase when the challenge answered to the
    commitment `x` is `c x`: the run of `A` against `H` up to the slot `t`, the
    measurement of the commitment `x`, then `H[x ↦ c x]`. -/
def fsChain (A : QAdv m n w q) (H : Fin m → Fin n) (c : Fin m → Fin n)
    (t : Option (Fin q × Bool)) : QComp (m * n * w) (Fin m) :=
  measChain (oracleQ m n w H) (measX m n w) (fun x => oracleQ m n w (Function.update H x (c x)))
    (fun x => oracleQ m n w (mrOracleAt H (c x) t x)) (mrSlot t) q A.U

/-- On the commitment `x` the simulator with challenge `c x` and `fsChain` have
    the same branch. -/
theorem simChain_branch_eq_fsChain (A : QAdv m n w q) (H : Fin m → Fin n)
    (c : Fin m → Fin n) (t : Option (Fin q × Bool)) (x : Fin m) :
    (simChain A H (c x) t).branch x = (fsChain A H c t).branch x := by
  apply LinearMap.ext; intro ρ
  exact (measChain_branch (oracleU m n w H) (measX m n w) (fun x => projS m n w {x})
      (measX_branch m n w) (fun x' => oracleU m n w (Function.update H x' (c x)))
      (fun x' => oracleU m n w (mrOracleAt H (c x) t x')) (mrSlot t) q A.U x ρ).trans
    (measChain_branch (oracleU m n w H) (measX m n w) (fun x => projS m n w {x})
      (measX_branch m n w) (fun x' => oracleU m n w (Function.update H x' (c x')))
      (fun x' => oracleU m n w (mrOracleAt H (c x') t x')) (mrSlot t) q A.U x ρ).symm

/-- The accepting branch of `prSimAcc` is the accepting branch of the output
    measurements applied to the simulator's branch on the commitment `x₀`. -/
theorem prSimAcc_branch (A : QAdv m n w q) (H : Fin m → Fin n) (θ : Fin n) (x₀ : Fin m)
    (t : Option (Fin q × Bool)) (ρ : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (QComp.qbind (simRun A H θ t) fun o => QComp.qpure (decide (o.1 = x₀) && o.2.2)).branch
        true ρ =
      (QComp.qbind (measX m n w) fun _ => A.measure).branch true
        ((simChain A H θ t).branch x₀ ρ) := by
  unfold simRun
  rw [QComp.qbind_assoc, qbind_branch_of_single _ _ true x₀]
  · simp only [QComp.qbind_assoc, QComp.qpure_qbind, decide_true, Bool.true_and,
      QComp.qbind_qpure]
  · intro a ha
    apply LinearMap.ext; intro σ
    simp [QComp.qbind_assoc, QComp.qpure_qbind, qbind_branch_apply, qpure_branch_apply, ha]

/-- The trace of the accepting branch of a `Bool`-valued instrument is at most
    the trace of its positive semidefinite input. -/
theorem branch_true_trace_re_le {d : ℕ} (I : QComp d Bool) (σ : Matrix (Fin d) (Fin d) ℂ)
    (hσ : σ.PosSemidef) : (I.branch true σ).trace.re ≤ σ.trace.re := by
  have h := I.branch_stp σ hσ
  rw [tsum_fintype, Fintype.sum_bool, Complex.add_re] at h
  have h0 := trace_re_nonneg_of_psd (I.branch_psd false σ hσ)
  linarith

/-- The simulator's interactive success probability is at most the probability
    of measuring the commitment `x₀`. -/
theorem prSimAcc_le (A : QAdv m n w q) (H : Fin m → Fin n) (θ : Fin n) (x₀ : Fin m)
    (t : Option (Fin q × Bool)) :
    prSimAcc A H θ x₀ t ≤
      ENNReal.ofReal ((simChain A H θ t).branch x₀ A.init.val).trace.re := by
  unfold prSimAcc prTrue_Q
  rw [prSimAcc_branch]
  exact ENNReal.ofReal_le_ofReal (branch_true_trace_re_le _ _
    ((simChain A H θ t).branch_psd x₀ _ A.init.psd))

/-- A zero verifier projector accepts with probability zero. -/
theorem prSimAcc_eq_zero (A : QAdv m n w q) (H : Fin m → Fin n) (θ : Fin n) (x₀ : Fin m)
    (t : Option (Fin q × Bool)) (h : A.final = 0) : prSimAcc A H θ x₀ t = 0 := by
  unfold prSimAcc prTrue_Q
  rw [prSimAcc_branch]
  simp [qbind_branch_apply, QAdv.measure, measProj_branch_true, h]

/-- The probabilities of the commitments measured by `fsChain` sum to at most
    one. -/
theorem sum_fsChain_trace_le_one (A : QAdv m n w q) (H : Fin m → Fin n) (c : Fin m → Fin n)
    (t : Option (Fin q × Bool)) :
    ∑ x, ENNReal.ofReal ((fsChain A H c t).branch x A.init.val).trace.re ≤ 1 := by
  have h := (fsChain A H c t).branch_stp A.init.val A.init.psd
  rw [tsum_fintype, Complex.re_sum, A.init.tr_one, Complex.one_re] at h
  rw [← ENNReal.ofReal_sum_of_nonneg fun x _ =>
    trace_re_nonneg_of_psd ((fsChain A H c t).branch_psd x _ A.init.psd)]
  exact ENNReal.ofReal_le_one.mpr h

/-- If every commitment `x` has at most one challenge `c x` with a nonzero
    verifier projector (special soundness on a statement outside the
    language), the interactive simulator succeeds with probability at most
    `1/n`. -/
theorem sum_prInt_le_inv_of_unique_challenge (A : QAdv m n w q) (V : QVerifier m n w)
    (H : Fin m → Fin n) (c : Fin m → Fin n) (hV : ∀ x θ, θ ≠ c x → V.proj x θ = 0) :
    ∑ x, prInt A V H x ≤ (n : ℝ≥0∞)⁻¹ := by
  set N : ℝ≥0∞ := ((2 * q + 1 : ℕ) : ℝ≥0∞) with hN
  have hN0 : N ≠ 0 := Nat.cast_ne_zero.mpr (2 * q).succ_ne_zero
  have hNt : N ≠ ⊤ := ENNReal.natCast_ne_top _
  have hat : ∀ x t, prIntAt A V H x t =
      (n : ℝ≥0∞)⁻¹ * prSimAcc (A.withVerifier V x (c x)) H (c x) x t := by
    intro x t
    unfold prIntAt
    rw [Finset.sum_eq_single (c x)]
    · exact fun θ _ hθ => prSimAcc_eq_zero _ H θ x t (hV x θ hθ)
    · exact fun h => absurd (Finset.mem_univ _) h
  have ht : ∀ t, ∑ x, prSimAcc (A.withVerifier V x (c x)) H (c x) x t ≤ 1 := fun t =>
    (Finset.sum_le_sum fun x _ => (prSimAcc_le _ H (c x) x t).trans_eq
      (by rw [simChain_branch_eq_fsChain]; rfl)).trans (sum_fsChain_trace_le_one A H c t)
  calc ∑ x, prInt A V H x
      = N⁻¹ * ∑ t, (n : ℝ≥0∞)⁻¹ *
          ∑ x, prSimAcc (A.withVerifier V x (c x)) H (c x) x t := by
        simp only [prInt, hat, Finset.mul_sum]
        rw [Finset.sum_comm]
    _ ≤ N⁻¹ * ∑ _t : Option (Fin q × Bool), (n : ℝ≥0∞)⁻¹ * 1 := by
        gcongr with t
        exact ht t
    _ = (n : ℝ≥0∞)⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, card_mrIndex, nsmul_eq_mul, mul_one,
          ← mul_assoc, ENNReal.inv_mul_cancel hN0 hNt, one_mul]

/-- The Fiat–Shamir soundness bound for a protocol in which every commitment
    has at most one challenge with a nonzero verifier projector (DFMS19,
    Theorem 8 shape): the probability that `A` outputs a commitment accepted
    against a fresh uniform challenge is at most `(2q + 1)² / n`. -/
theorem fiatShamir_unique_challenge (A : QAdv m n w q) (V : QVerifier m n w)
    (H : Fin m → Fin n) (c : Fin m → Fin n) (hV : ∀ x θ, θ ≠ c x → V.proj x θ = 0) :
    ∑ x, prFSAt A V H x ≤ ((2 * q + 1 : ℕ) : ℝ≥0∞) ^ 2 * (n : ℝ≥0∞)⁻¹ :=
  (fiatShamir_measure_reprogram_sum A V H).trans
    (mul_le_mul_right (sum_prInt_le_inv_of_unique_challenge A V H c hV) _)

end Unique

end CatCrypt.Quantum.QROM
