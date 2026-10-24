/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.MeasureReprogram
public import CatCryptCore.Quantum.ClassicalEmbed

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
* `uniformQ α` — the uniform mixture over a finite type as an instrument
* `preChain`, `sufU` — the prefix of `measChain` before its instrument and the
  unitary of its suffix after it
* `fsInteractive A V H` — the interactive game as one program: a uniform slot,
  the run of `A` against `H` up to it, the measurement of the commitment `x`, a
  uniform challenge `θ`, the rest of the run against `H[x ↦ θ]` (response
  unitary `fsSufU A H t x θ`), and the verifier projector `V(x, θ)`

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
* `measChain_eq_split` — `measChain` with unitary oracles is its prefix, its
  instrument and its suffix unitary
* `prTrue_fsInteractive` — the acceptance probability of `fsInteractive A V H`
  is `∑ x, prInt A V H x`
* `fiatShamir_interactive`, `fiatShamir_random_oracle_interactive` — the
  Fiat–Shamir success probability is at most `(2q + 1)²` times the acceptance
  probability of the interactive game, for a fixed and for a uniform oracle
* `prTrue_fsInteractive_le_inv_of_unique_challenge` — with a unique accepting
  challenge per commitment the interactive game accepts with probability at
  most `1/n`

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

/-! ## The uniform mixture -/

section Uniform

variable {d : ℕ}

/-- The uniform mixture over a finite nonempty type `α` as an instrument: the
    classical embedding of the uniform sub-distribution, whose branch at every
    outcome scales the state by `1 / |α|`. -/
def uniformQ (α : Type) [Fintype α] [Nonempty α] : QComp d α :=
  classicalEmbed (CatCrypt.Prob.SDistr.uniform α)

theorem uniformQ_branch_apply (α : Type) [Fintype α] [Nonempty α] (a : α)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (uniformQ α : QComp d α).branch a ρ = (((Fintype.card α : ℝ)⁻¹ : ℝ) : ℂ) • ρ := by
  show ((((CatCrypt.Prob.SDistr.uniform α) (some a)).toReal : ℝ) : ℂ) • ρ = _
  simp only [CatCrypt.Prob.SDistr.uniform, PMF.map_apply, Option.some.injEq,
    PMF.uniformFintype_apply, tsum_fintype, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.ofReal_inv, Complex.ofReal_natCast]

/-- The real trace of a branch of a bind over a finite type is the sum over the
    intermediate outcomes. -/
theorem trace_re_qbind_branch {α β : Type} [Fintype α] (I : QComp d α) (f : α → QComp d β)
    (b : β) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    ((QComp.qbind I f).branch b ρ).trace.re = ∑ a, ((f a).branch b (I.branch a ρ)).trace.re := by
  rw [qbind_branch_apply, tsum_fintype, Matrix.trace_sum, Complex.re_sum]

/-- A uniform draw commutes with an instrument with finitely many outcomes. -/
theorem qbind_uniformQ_comm {α β γ : Type} [Fintype α] [Fintype β] [Nonempty β]
    (I : QComp d α) (f : α → β → QComp d γ) :
    QComp.qbind I (fun a => QComp.qbind (uniformQ β) fun b => f a b) =
      QComp.qbind (uniformQ β) fun b => QComp.qbind I fun a => f a b := by
  apply QComp.ext_fun; intro c ρ
  simp only [qbind_branch_apply, tsum_fintype, uniformQ_branch_apply, map_smul, Finset.smul_sum]
  exact Finset.sum_comm

/-- The acceptance probability after a uniform draw is the average of the
    acceptance probabilities. -/
theorem prTrue_Q_uniformQ_bind {α : Type} [Fintype α] [Nonempty α] (f : α → QComp d Bool)
    (ρ : DensityMatrix d) :
    prTrue_Q (QComp.qbind (uniformQ α) f) ρ =
      (Fintype.card α : ℝ≥0∞)⁻¹ * ∑ a, prTrue_Q (f a) ρ := by
  unfold prTrue_Q
  rw [trace_re_qbind_branch]
  simp only [uniformQ_branch_apply, map_smul, Matrix.trace_smul, smul_eq_mul,
    Complex.re_ofReal_mul, ← Finset.mul_sum]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg fun a _ =>
      trace_re_nonneg_of_psd ((f a).branch_psd _ _ ρ.psd),
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast Fintype.card_pos), ENNReal.ofReal_natCast]

/-- The acceptance probability of a bind over a finite type is the sum of the
    acceptance probabilities of the continuations on the branches. -/
theorem prTrue_Q_qbind_eq_sum {α : Type} [Fintype α] (I : QComp d α) (f : α → QComp d Bool)
    (ρ : DensityMatrix d) :
    prTrue_Q (QComp.qbind I f) ρ =
      ∑ a, ENNReal.ofReal ((f a).branch true (I.branch a ρ.val)).trace.re := by
  unfold prTrue_Q
  rw [trace_re_qbind_branch, ENNReal.ofReal_sum_of_nonneg fun a _ =>
    trace_re_nonneg_of_psd ((f a).branch_psd _ _ ((I.branch_psd a _ ρ.psd)))]

/-- An event implied by another has at least its probability. -/
theorem prTrue_Q_qbind_decide_mono {α : Type} [Fintype α] (I : QComp d α) (e e' : α → Bool)
    (h : ∀ a, e a = true → e' a = true) (ρ : DensityMatrix d) :
    prTrue_Q (QComp.qbind I fun a => QComp.qpure (e a)) ρ ≤
      prTrue_Q (QComp.qbind I fun a => QComp.qpure (e' a)) ρ := by
  rw [prTrue_Q_qbind_eq_sum, prTrue_Q_qbind_eq_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  simp only [qpure_branch_apply]
  by_cases ha : e a = true
  · simp [ha, h a ha]
  · simp [Bool.eq_false_iff.mpr ha]

end Uniform

/-! ## The commitment phase split at the measurement -/

section Split

variable {d : ℕ} {α : Type}

/-- The identity unitary channel is the pure return. -/
theorem unitaryChannel_one_eq_qpure_unit :
    unitaryChannel (1 : Matrix.unitaryGroup (Fin d) ℂ) = QComp.qpure () := by
  apply QComp.ext_fun; intro u ρ
  cases u
  rw [unitaryChannel_branch_apply, qpure_branch_apply]
  simp

/-- The unitary `U_q g ⋯ g U_0` of `oracleChain` for a unitary oracle `g`. -/
def chainU (g : Matrix.unitaryGroup (Fin d) ℂ) :
    (q : ℕ) → (Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) → Matrix.unitaryGroup (Fin d) ℂ
  | 0, U => U 0
  | q + 1, U => chainU g q (Fin.tail U) * g * U 0

theorem oracleChain_unitaryChannel_eq (g : Matrix.unitaryGroup (Fin d) ℂ) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    oracleChain (unitaryChannel g) q U = unitaryChannel (chainU g q U) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [oracleChain, chainU, ih, unitaryChannel_compose]

/-- The prefix of `measChain` before its instrument: `U₀ ; O ; ⋯ ; O ; U_j`,
    or `U₀ ; ⋯ ; U_q` when `j ≥ q`. -/
def preChain (O : QComp d Unit) :
    (j q : ℕ) → (Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) → QComp d Unit
  | 0, _, U => unitaryChannel (U 0)
  | _ + 1, 0, U => unitaryChannel (U 0)
  | j + 1, q + 1, U =>
    QComp.qbind (unitaryChannel (U 0)) fun _ => QComp.qbind O fun _ => preChain O j q (Fin.tail U)

/-- The unitary of the suffix of `measChain` after its instrument, for unitary
    oracles `g` (after the measured query) and `r` (at the measured query):
    `U_q g ⋯ g U_{j+1} r`, the identity when `j ≥ q`. -/
def sufU (g r : Matrix.unitaryGroup (Fin d) ℂ) :
    (j q : ℕ) → (Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) → Matrix.unitaryGroup (Fin d) ℂ
  | 0, 0, _ => 1
  | 0, q + 1, U => chainU g q (Fin.tail U) * r
  | _ + 1, 0, _ => 1
  | j + 1, q + 1, U => sufU g r j q (Fin.tail U)

/-- `measChain` with unitary oracles is its prefix, the instrument with outcome
    `a`, and the suffix unitary for `a`. -/
theorem measChain_eq_split (o : Matrix.unitaryGroup (Fin d) ℂ) (M : QComp d α)
    (g r : α → Matrix.unitaryGroup (Fin d) ℂ) (j q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    measChain (unitaryChannel o) M (fun a => unitaryChannel (g a)) (fun a => unitaryChannel (r a))
        j q U =
      QComp.qbind (preChain (unitaryChannel o) j q U) fun _ => QComp.qbind M fun a =>
        QComp.qbind (unitaryChannel (sufU (g a) (r a) j q U)) fun _ => QComp.qpure a := by
  induction j generalizing q with
  | zero =>
    cases q with
    | zero =>
      simp only [measChain, preChain, sufU, unitaryChannel_one_eq_qpure_unit,
        QComp.qpure_qbind]
      exact congrArg _ (funext fun _ => (QComp.qbind_qpure M).symm)
    | succ q =>
      simp only [measChain, preChain, sufU, oracleChain_unitaryChannel_eq, QComp.qbind_assoc,
        ← unitaryChannel_compose]
  | succ j ih =>
    cases q with
    | zero =>
      simp only [measChain, preChain, sufU, unitaryChannel_one_eq_qpure_unit,
        QComp.qpure_qbind]
      exact congrArg _ (funext fun _ => (QComp.qbind_qpure M).symm)
    | succ q =>
      simp only [measChain, preChain, sufU, ih, QComp.qbind_assoc]

end Split

/-! ## The interactive game as one program -/

section Interactive

variable {m n w q : ℕ} [NeZero n]

/-- The suffix unitary of the simulator on the slot `t` for the commitment `x`
    and the challenge `θ`: `mrOracleAt H θ t x` at the measured query, then the
    remaining unitaries of `A` with the oracle `H[x ↦ θ]`. -/
def fsSufU (A : QAdv m n w q) (H : Fin m → Fin n) (t : Option (Fin q × Bool)) (x : Fin m)
    (θ : Fin n) : Matrix.unitaryGroup (Fin (m * n * w)) ℂ :=
  sufU (oracleU m n w (Function.update H x θ)) (oracleU m n w (mrOracleAt H θ t x)) (mrSlot t) q
    A.U

/-- The commitment measurement followed by a uniform challenge: the query
    register is measured with outcome `x`, then `θ` is drawn uniformly. -/
def measXChal (m n w : ℕ) [NeZero n] : QComp (m * n * w) (Fin m × Fin n) :=
  QComp.qbind (measX m n w) fun x => QComp.qbind (uniformQ (Fin n)) fun θ => QComp.qpure (x, θ)

/-- The interactive commit–challenge–respond game of the prover `A` against the
    verifier `V` as one program: a uniform slot `t` among the `2q + 1` slots;
    the run of `A` against `H` up to the slot; the measurement of the commitment
    `x`; a uniform challenge `θ`; the rest of the run against `H[x ↦ θ]`
    (against `H` at the measured query on the slots `some (i, true)`); the
    measurement of the query register; and the verifier projector `V(x, θ)`. -/
def fsInteractive (A : QAdv m n w q) (V : QVerifier m n w) (H : Fin m → Fin n) :
    QComp (m * n * w) Bool :=
  QComp.qbind (uniformQ (Option (Fin q × Bool))) fun t =>
    QComp.qbind (measChain (oracleQ m n w H) (measXChal m n w)
        (fun c => oracleQ m n w (Function.update H c.1 c.2))
        (fun c => oracleQ m n w (mrOracleAt H c.2 t c.1)) (mrSlot t) q A.U) fun c =>
      QComp.qbind (measX m n w) fun _ => (A.withVerifier V c.1 c.2).measure

/-- The interactive game with the commitment phase split at the measurement of
    the commitment. -/
theorem fsInteractive_eq_split (A : QAdv m n w q) (V : QVerifier m n w) (H : Fin m → Fin n) :
    fsInteractive A V H =
      QComp.qbind (uniformQ (Option (Fin q × Bool))) fun t =>
        QComp.qbind (preChain (oracleQ m n w H) (mrSlot t) q A.U) fun _ =>
          QComp.qbind (measX m n w) fun x => QComp.qbind (uniformQ (Fin n)) fun θ =>
            QComp.qbind (unitaryChannel (fsSufU A H t x θ)) fun _ =>
              QComp.qbind (measX m n w) fun _ => (A.withVerifier V x θ).measure := by
  unfold fsInteractive
  refine congrArg _ (funext fun t => ?_)
  simp only [oracleQ, measChain_eq_split, measXChal, fsSufU, QComp.qbind_assoc,
    QComp.qpure_qbind]

/-- The interactive game with the challenge drawn before the run: the slot and
    the challenge are uniform, and the simulator `simChain` runs with them. -/
theorem fsInteractive_eq_simChain (A : QAdv m n w q) (V : QVerifier m n w)
    (H : Fin m → Fin n) :
    fsInteractive A V H =
      QComp.qbind (uniformQ (Option (Fin q × Bool))) fun t =>
        QComp.qbind (uniformQ (Fin n)) fun θ =>
          QComp.qbind (simChain A H θ t) fun x =>
            QComp.qbind (measX m n w) fun _ => (A.withVerifier V x θ).measure := by
  rw [fsInteractive_eq_split]
  refine congrArg _ (funext fun t => ?_)
  simp only [simChain, oracleQ, fsSufU, measChain_eq_split, QComp.qbind_assoc, QComp.qpure_qbind]
  simp only [qbind_uniformQ_comm]

/-- The acceptance probability of the interactive game is the averaged success
    probability `∑ x, prInt A V H x` of the measure-and-reprogram simulator. -/
theorem prTrue_fsInteractive (A : QAdv m n w q) (V : QVerifier m n w) (H : Fin m → Fin n) :
    prTrue_Q (fsInteractive A V H) A.init = ∑ x, prInt A V H x := by
  have hS : ∀ t θ, prTrue_Q (QComp.qbind (simChain A H θ t) fun x =>
      QComp.qbind (measX m n w) fun _ => (A.withVerifier V x θ).measure) A.init =
        ∑ x, prSimAcc (A.withVerifier V x θ) H θ x t := by
    intro t θ
    rw [prTrue_Q_qbind_eq_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold prSimAcc prTrue_Q
    rw [prSimAcc_branch]
    rfl
  rw [fsInteractive_eq_simChain, prTrue_Q_uniformQ_bind]
  simp only [prTrue_Q_uniformQ_bind, hS, prInt, prIntAt, card_mrIndex, Fintype.card_fin,
    Finset.mul_sum]
  rw [eq_comm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- The Fiat–Shamir reduction against the interactive game: the Fiat–Shamir
    success probability is at most `(2q + 1)²` times the acceptance probability
    of `fsInteractive A V H`. -/
theorem fiatShamir_interactive (A : QAdv m n w q) (V : QVerifier m n w) (H : Fin m → Fin n) :
    ∑ x, prFSAt A V H x ≤
      ((2 * q + 1 : ℕ) : ℝ≥0∞) ^ 2 * prTrue_Q (fsInteractive A V H) A.init := by
  rw [prTrue_fsInteractive]
  exact fiatShamir_measure_reprogram_sum A V H

/-- The Fiat–Shamir reduction for a uniformly random oracle against the
    interactive game: over a uniform `H`, the probability that `A^H` outputs a
    commitment `x` accepted by `V(x, H x)` is at most `(2q + 1)²` times the
    average acceptance probability of `fsInteractive A V H`. -/
theorem fiatShamir_random_oracle_interactive (A : QAdv m n w q) (V : QVerifier m n w) :
    (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
        ∑ H : Fin m → Fin n, ∑ x, prOutAt (A.withVerifier V x (H x)) H x ≤
      ((2 * q + 1 : ℕ) : ℝ≥0∞) ^ 2 *
        ((Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
          ∑ H : Fin m → Fin n, prTrue_Q (fsInteractive A V H) A.init) := by
  simp only [prTrue_fsInteractive]
  exact fiatShamir_random_oracle A V

/-- If every commitment has at most one challenge with a nonzero verifier
    projector, the interactive game accepts with probability at most `1/n`. -/
theorem prTrue_fsInteractive_le_inv_of_unique_challenge (A : QAdv m n w q)
    (V : QVerifier m n w) (H : Fin m → Fin n) (c : Fin m → Fin n)
    (hV : ∀ x θ, θ ≠ c x → V.proj x θ = 0) :
    prTrue_Q (fsInteractive A V H) A.init ≤ (n : ℝ≥0∞)⁻¹ := by
  rw [prTrue_fsInteractive]
  exact sum_prInt_le_inv_of_unique_challenge A V H c hV

end Interactive

end CatCrypt.Quantum.QROM
