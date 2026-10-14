/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.TTransformQROM
public import CatCryptCore.Quantum.QROM.FindToGuessGeneral

/-!
# The quantum OW-CPA game and the T-transform reduction

The reprogrammed game of `Quantum/QROM/TTransformQROM.lean` is OW-CPA of `P`
against an adversary that also queries a random oracle `G` unrelated to the
challenge. An adversary of this library is unbounded, so the reduction samples
`G` itself and runs `A` with the oracle unitary multiplied into `A`'s own
unitaries; the resulting adversary makes no oracle query. This module defines
the quantum OW-CPA game for adversaries with internal randomness and proves
that `tOwAdvantage'` is that game at the absorbing reduction, so the
one-way-to-hiding step becomes a bound in terms of a named reduction. The
absorbing adversary `absorbOracle A G` and its unitary `absorbU` are defined in
`Quantum/QROM/FindToGuessGeneral.lean`.

## Main definitions

* `QOWAdv m n w PK C` — a quantum OW-CPA adversary with internal randomness:
  a finite coin type with a weight summing to one, and at each coin a
  `0`-query adversary for each public key, challenge ciphertext and target
  message, with final projector `winProj` at the target and a pure initial state
* `qOwcpaAdvantage P eM B` — the quantum OW-CPA game of `P` against `B`
* `tReduction eM eR A` — the reduction from a `TAdv` to a `QOWAdv` whose coins
  are the oracle table

## Main results

* `tOwAdvantage'_eq_qOwcpa` — `tOwAdvantage' P A = qOwcpaAdvantage P (tReduction A)`
* `tOw_le_qOwcpa_add_find` —
  `tOwAdvantage P A ≤ qOwcpaAdvantage P (tReduction A) + 4 √(q · tFind P A)`

## The game

`qOwcpaAdvantage` is the quantum counterpart of `PKE.Games.owcpaAdvantage`: the
key pair is drawn from `keygen`, the message `m*` and the coins `r` uniformly
(as `tSample` does), and the win event `output = m*` is read off `winProj`.
The coins of `tReduction A` are the whole oracle table `G`.

## References

* [Hofheinz, Hövelmanns, Kiltz — A Modular Analysis of the Fujisaki–Okamoto
  Transformation, TCC 2017], §4.1, Theorem 4.4
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

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
