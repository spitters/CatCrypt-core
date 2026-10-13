/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.TTransformQROM

/-!
# The quantum OW-CPA game and the T-transform reduction

The reprogrammed game of `Quantum/QROM/TTransformQROM.lean` is OW-CPA of `P`
against an adversary that also queries a random oracle `G` unrelated to the
challenge. An adversary of this library is unbounded, so the reduction samples
`G` itself and runs `A` with the oracle unitary multiplied into `A`'s own
unitaries; the resulting adversary makes no oracle query. This module defines
the quantum OW-CPA game for adversaries with internal randomness and proves
that `tOwAdvantage'` is that game at the absorbing reduction, so the
one-way-to-hiding step becomes a bound in terms of a named reduction.

## Main definitions

* `absorbU G q U` — the unitary `U_q O_G U_{q-1} ⋯ O_G U_0`
* `absorbOracle A G` — the `0`-query adversary with the single unitary
  `absorbU G q A.U`, the initial state and the final projector of `A`
* `QOWAdv m n w PK C` — a quantum OW-CPA adversary with internal randomness:
  a finite coin type with a weight summing to one, and at each coin a
  `0`-query adversary for each public key, challenge ciphertext and target
  message, with final projector `winProj` at the target and a pure initial state
* `qOwcpaAdvantage P eM B` — the quantum OW-CPA game of `P` against `B`
* `tReduction eM eR A` — the reduction from a `TAdv` to a `QOWAdv` whose coins
  are the oracle table

## Main results

* `absorbU_val` — the value of `absorbU` is `chainOp (oracleU G)`
* `prOut_absorbOracle` — the absorbed adversary wins as `A` does against `G`,
  whatever oracle it is run against
* `tOwAdvantage'_eq_qOwcpa` — `tOwAdvantage' P A = qOwcpaAdvantage P (tReduction A)`
* `tOw_le_qOwcpa_add_find` —
  `tOwAdvantage P A ≤ qOwcpaAdvantage P (tReduction A) + 4 √(q · tFind P A)`

## Scope

`qOwcpaAdvantage` is the quantum counterpart of `PKE.Games.owcpaAdvantage`: the
key pair is drawn from `keygen`, the message `m*` and the coins `r` uniformly
(as `tSample` does), and the win event `output = m*` is read off `winProj`.
The two advantages are not related here; a classical adversary embeds as a
`QAdv` with a diagonal unitary, which is not in this module. The reduction's
coins are the whole oracle table, the unbounded-adversary form; a bounded
reduction would draw `G` from a `2q`-wise independent family (Zhandry, CRYPTO
2012). Bounding `tFind` by a second reduction needs the measured query, which
`runSC` does not return; that belongs to the next module.

## References

* [Hofheinz, Hövelmanns, Kiltz — A Modular Analysis of the Fujisaki–Okamoto
  Transformation, TCC 2017], §4.1, Theorem 4.4
* [Zhandry — Secure Identity-Based Encryption in the Quantum Random Oracle
  Model, CRYPTO 2012], Theorem 3.1
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Absorbing the oracle into the adversary's unitaries -/

section Absorb

variable {m n w q : ℕ} [NeZero n]

/-- The unitary `U_q O_G U_{q-1} ⋯ O_G U_0` of a `q`-query adversary with the
    standard oracle for `G` at each query. -/
def absorbU (G : Fin m → Fin n) :
    (q : ℕ) → (Fin (q + 1) → Matrix.unitaryGroup (Fin (m * n * w)) ℂ) →
      Matrix.unitaryGroup (Fin (m * n * w)) ℂ
  | 0, U => U 0
  | q + 1, U => absorbU G q (Fin.tail U) * oracleU m n w G * U 0

/-- The value of `absorbU` is the chain operator of the oracle unitary. -/
theorem absorbU_val (G : Fin m → Fin n) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin (m * n * w)) ℂ) :
    (absorbU G q U : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) =
      chainOp (oracleU m n w G : Matrix _ _ ℂ) q U := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [absorbU, chainOp, Submonoid.coe_mul, ih]

/-- The `0`-query adversary with the single unitary `absorbU G q A.U`, the
    initial state and the final projector of `A`. -/
def absorbOracle (A : QAdv m n w q) (G : Fin m → Fin n) : QAdv m n w 0 where
  U _ := absorbU G q A.U
  init := A.init
  final := A.final
  final_conjTranspose := A.final_conjTranspose
  final_mul_self := A.final_mul_self

/-- The run operator of a `0`-query adversary is its unitary, whatever the
    oracle. -/
theorem runOp_zero (A : QAdv m n w 0) (H : Fin m → Fin n) :
    runOp A H = (A.U 0 : Matrix _ _ ℂ) := rfl

/-- The run operator of the absorbed adversary is the run operator of `A`
    against `G`. -/
theorem runOp_absorbOracle (A : QAdv m n w q) (G H : Fin m → Fin n) :
    runOp (absorbOracle A G) H = runOp A G := by
  rw [runOp_zero]
  exact absorbU_val G q A.U

/-- A `0`-query adversary wins with the same probability against every oracle. -/
theorem prOut_zero (A : QAdv m n w 0) (H H' : Fin m → Fin n) : prOut A H = prOut A H' := by
  unfold prOut prTrue_Q
  rw [run_branch_true, run_branch_true, runOp_zero, runOp_zero]

/-- The absorbed adversary wins, against any oracle, with the probability of
    `A` against `G`. -/
theorem prOut_absorbOracle (A : QAdv m n w q) (G H : Fin m → Fin n) :
    prOut (absorbOracle A G) H = prOut A G := by
  unfold prOut prTrue_Q
  rw [run_branch_true, run_branch_true, runOp_absorbOracle]
  simp only [absorbOracle]

end Absorb

/-! ## The quantum OW-CPA adversary and game -/

/-- A quantum OW-CPA adversary with internal randomness: a finite coin type
    with a weight summing to one, and at each coin, public key, challenge
    ciphertext and target message `x`, a `0`-query adversary on the register
    `Fin (m * n * (m * w))` whose final projector is `winProj x` and whose
    initial state is pure. -/
structure QOWAdv (m n w : ℕ) (PK C : Type) where
  /-- The coin type. -/
  Coins : Type
  [fintypeCoins : Fintype Coins]
  /-- The weight of each coin. -/
  weight : Coins → ℝ≥0∞
  /-- The weights sum to one. -/
  weight_sum : ∑ ω, weight ω = 1
  /-- The adversary at a coin, a public key, a challenge ciphertext and a target
      message. -/
  run : Coins → PK → C → Fin m → QAdv m n (m * w) 0
  /-- The final projector is the projector onto the target message. -/
  final_eq : ∀ ω pk c x, (run ω pk c x).final = winProj m n w x
  /-- The initial state is pure. -/
  pure : ∀ ω pk c x, ∃ ψ : Fin (m * n * (m * w)) → ℂ,
    (run ω pk c x).init.val = Matrix.vecMulVec ψ (star ψ)

attribute [instance] QOWAdv.fintypeCoins

section Game

variable {m n w q : ℕ} {PK SK M C R : Type} [Fintype PK] [Fintype SK] [Fintype M] [Fintype R]
  [Nonempty M] [Nonempty R] (P : Scheme PK SK M C R) (eM : M ≃ Fin m) (eR : R ≃ Fin n) [NeZero n]

/-- The quantum OW-CPA game of `P` against `B`: the key pair is drawn from
    `keygen`, the message `x` and the coins `r` uniformly, the adversary's coin
    `ω` from `B.weight`, and the winning probability is that of
    `B.run ω pk (enc pk x r) (eM x)`, which makes no oracle query. -/
def qOwcpaAdvantage (B : QOWAdv m n w PK C) : ℝ≥0∞ :=
  ∑ ks : PK × SK, ∑ x : M, ∑ r : R, ∑ ω : B.Coins,
    P.keygen ks * (Fintype.card M : ℝ≥0∞)⁻¹ * (Fintype.card R : ℝ≥0∞)⁻¹ * B.weight ω *
      prOut (B.run ω ks.1 (P.enc ks.1 x r) (eM x)) (fun _ => 0)

omit [Nonempty M] [NeZero n] in
include eM eR in
/-- The uniform weight on oracle tables sums to one. -/
theorem sum_card_pow_inv :
    ∑ _G : Fin m → Fin n, ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹ = 1 := by
  have hM : Fintype.card M = m := (Fintype.card_congr eM).trans (Fintype.card_fin m)
  have hR : Fintype.card R = n := (Fintype.card_congr eR).trans (Fintype.card_fin n)
  have hn : n ≠ 0 := hR ▸ Fintype.card_ne_zero
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul, hM, hR, Nat.cast_pow]
  exact ENNReal.mul_inv_cancel (pow_ne_zero _ (by exact_mod_cast hn))
    (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))

/-- The reduction from a `TAdv` to a `QOWAdv`: the coins are the oracle table
    `G`, drawn uniformly, and the adversary at `G` is `A` with `G` absorbed into
    its unitaries. -/
def tReduction (A : TAdv m n w q PK C) : QOWAdv m n w PK C where
  Coins := Fin m → Fin n
  weight _ := ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹
  weight_sum := sum_card_pow_inv (M := M) (R := R) eM eR
  run G pk c x := absorbOracle (A.run pk c x) G
  final_eq _ pk c x := A.final_eq pk c x
  pure _ pk c x := A.pure pk c x

/-- The reprogrammed T game is the quantum OW-CPA game of `P` against the
    absorbing reduction. -/
theorem tOwAdvantage'_eq_qOwcpa (A : TAdv m n w q PK C) :
    tOwAdvantage' P eM eR A = qOwcpaAdvantage P eM (tReduction eM eR A) := by
  rw [tOwAdvantage'_eq]
  simp only [qOwcpaAdvantage, tReduction, tSample, Fintype.sum_prod_type, prOut_absorbOracle]
  rfl

/-- The one-way-to-hiding step of Theorem 4.4 (Hofheinz–Hövelmanns–Kiltz, TCC
    2017) with the reprogrammed game replaced by the OW-CPA game against the
    reduction: `tOwAdvantage ≤ qOwcpaAdvantage (tReduction A) + 4 √(q · tFind)`. -/
theorem tOw_le_qOwcpa_add_find (A : TAdv m n w q PK C) :
    tOwAdvantage P eM eR A ≤
      qOwcpaAdvantage P eM (tReduction eM eR A) +
        4 * ((q : ℝ≥0∞) * tFind P eM eR A) ^ (1 / 2 : ℝ) := by
  rw [← tOwAdvantage'_eq_qOwcpa]
  exact tOw_le_reprogrammed_add_find P eM eR A

end Game

end CatCrypt.Quantum.QROM
