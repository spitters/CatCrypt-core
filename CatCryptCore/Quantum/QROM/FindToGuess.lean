/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.FindToGuessGeneral
public import CatCryptCore.Quantum.QROM.QuantumOWCPA

/-!
# The T transform: `tFind` against the quantum OW-CPA game

Search in a semi-classical oracle (`prFind_le_four_sum_guess` of
`Quantum/QROM/FindToGuessGeneral.lean`, Ambainis–Hamburg–Unruh, CRYPTO 2019,
Theorem 2) bounds the `Find` probability by `4` times the sum over the queries
of the probability of measuring the punctured set before that query. For the
T transform this bounds `tFind` by the quantum OW-CPA advantage of the
adversary that runs `A` up to a uniformly chosen query, swaps the query
register into the output register, and outputs it.

## Main definitions

* `guessRun A j G pk c t` — the `0`-query adversary that runs the prefix of
  `A.run pk c t` up to query `j` against `G` and swaps the query register into
  the output register
* `guessReduction eM eR A` — the `QOWAdv` with coins `Fin q × (Fin m → Fin n)`
  that runs `guessRun A j G` at the coin `(j, G)`

## Main results

* `winProj_mul_swapU` — `winProj t * swapU = swapU * projS {t}`
* `prOut_guessRun` — the adversary at `(j, G)` wins with `guessProb` of
  `A` against `G` at `{t}` and `j`
* `tFind_le_qOwcpa` — `tFind P A ≤ 4 q · qOwcpaAdvantage P (guessReduction A)`
* `tOw_le_qOwcpa_two` — the T transform in the QROM with both reductions
  named

## The model

The adversary's initial state is pure, as in `O2HTheorem`. The coins of
`guessReduction` include the oracle table, as do those of `tReduction` in
`QuantumOWCPA`. The constant `4q` of `tFind_le_qOwcpa` is that of
Ambainis–Hamburg–Unruh, Theorem 2; the instance `[NeZero q]` makes the coin type
`Fin q × (Fin m → Fin n)` of the reduction non-empty.

## References

* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], Theorem 2 (Lemma 7)
* [Hofheinz, Hövelmanns, Kiltz — A Modular Analysis of the Fujisaki–Okamoto
  Transformation, TCC 2017], §4.1, Theorem 4.4
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The swap carries the query projector to the output projector -/

section Swap

variable (m n w : ℕ)

theorem winProj_eq_diagonal (x : Fin m) :
    winProj m n w x = Matrix.diagonal (fun k => indS m {x} (oPart m n w k)) := by
  unfold winProj
  rw [diagonal_kronecker_one, one_kronecker_diagonal]
  rfl

/-- Conjugating the query projector by the register swap gives the output
    projector. -/
theorem swapU_conj_projS (t : Fin m) :
    (swapU m n w : Matrix (Fin (m * n * (m * w))) (Fin (m * n * (m * w))) ℂ) *
        projS m n (m * w) {t} *
        (swapU m n w : Matrix (Fin (m * n * (m * w))) (Fin (m * n * (m * w))) ℂ)ᴴ =
      winProj m n w t := by
  rw [projS_eq_diagonal, swapU, permUnitary_conj_diagonal, winProj_eq_diagonal]
  congr 1
  funext k
  rw [← oPart_swapPerm m n w ((swapPerm m n w).symm k)]
  simp

/-- `winProj t * swapU = swapU * projS {t}`: the swap carries the query
    projector to the output projector. -/
theorem winProj_mul_swapU (t : Fin m) :
    winProj m n w t * (swapU m n w : Matrix _ _ ℂ) =
      (swapU m n w : Matrix _ _ ℂ) * projS m n (m * w) {t} := by
  rw [← swapU_conj_projS m n w t, Matrix.mul_assoc, Matrix.mul_assoc, swapU,
    star_permUnitary_mul (swapPerm m n w), Matrix.mul_one]

end Swap

/-! ## The guessing reduction -/

section Reduction

variable {m n w q : ℕ} {PK SK M C R : Type} [Fintype PK] [Fintype SK] [Fintype M] [Fintype R]
  [Nonempty M] [Nonempty R] (P : Scheme PK SK M C R) (eM : M ≃ Fin m) (eR : R ≃ Fin n) [NeZero n]

/-- The `0`-query adversary at coins `(j, G)`: the prefix of `A.run pk c t` up
    to query `j` against `G`, then the swap of the query factor into the output
    factor, measured by `winProj t`. -/
def guessRun (A : TAdv m n w q PK C) (j : Fin q) (G : Fin m → Fin n) (pk : PK) (c : C)
    (t : Fin m) : QAdv m n (m * w) 0 where
  U _ := swapU m n w * prefixU (A.run pk c t) G j
  init := (A.run pk c t).init
  final := winProj m n w t
  final_conjTranspose := winProj_conjTranspose m n w t
  final_mul_self := winProj_mul_self m n w t

omit [Fintype PK] in
/-- The guessing adversary at `(j, G)` wins with the probability that the query
    register of the plain run of `A` against `G` lies in `{t}` before query
    `j`, whatever oracle it is run against. -/
theorem prOut_guessRun (A : TAdv m n w q PK C) (j : Fin q) (G H : Fin m → Fin n) (pk : PK)
    (c : C) (t : Fin m) :
    prOut (guessRun A j G pk c t) H = guessProb (A.run pk c t) G {t} j := by
  unfold guessProb prOut prTrue_Q
  rw [run_branch_true, run_branch_true, runOp_zero, runOp_zero]
  simp only [guessRun, prefixAdv, Submonoid.coe_mul]
  have hsw : winProj m n w t * ((swapU m n w : Matrix _ _ ℂ) * (prefixU (A.run pk c t) G j :
      Matrix _ _ ℂ)) = (swapU m n w : Matrix _ _ ℂ) * (projS m n (m * w) {t} *
      (prefixU (A.run pk c t) G j : Matrix _ _ ℂ)) := by
    rw [← Matrix.mul_assoc, winProj_mul_swapU, Matrix.mul_assoc]
  rw [hsw]
  have key : ∀ Y : Matrix (Fin (m * n * (m * w))) (Fin (m * n * (m * w))) ℂ,
      ((swapU m n w : Matrix _ _ ℂ) * Y) * (A.run pk c t).init.val *
        ((swapU m n w : Matrix _ _ ℂ) * Y)ᴴ =
      (swapU m n w : Matrix _ _ ℂ) * (Y * (A.run pk c t).init.val * Yᴴ) *
        (swapU m n w : Matrix _ _ ℂ)ᴴ := by
    intro Y
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [key, trace_mul_mul_conjTranspose_of_mem_unitaryGroup (swapU m n w).prop]

/-- `tFind` is the average over `((pk, sk), m*, r, G)` of the `Find` probability
    of `A.run pk (enc pk m* r) m*` against `G` at `{m*}`: the oracle at `m*`
    is independent of the challenge coins. -/
theorem tFind_eq (A : TAdv m n w q PK C) :
    tFind P eM eR A =
      ∑ i : TInput PK SK M R m n,
        tSample P i * prFind (A.run i.1.1 (P.enc i.1.1 i.2.1 i.2.2.1) (eM i.2.1)) i.2.2.2
          {eM i.2.1} := by
  simp only [tFind, prFindAvg, tGame, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun pk _ => Finset.sum_congr rfl fun sk _ =>
    Finset.sum_congr rfl fun x _ => ?_
  refine (Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun G _ => ?_).trans
    (sum_swapAt eR (eM x) (fun r G => tSample P (((pk, sk), x, r, G) : TInput PK SK M R m n) *
      prFind (A.run pk (P.enc pk x r) (eM x)) G {eM x}))
  obtain ⟨ψ, hψ⟩ := A.pure pk (P.enc pk x (eR.symm (G (eM x)))) (eM x)
  show _ = tSample P (((pk, sk), x, eR.symm (G (eM x)), Function.update G (eM x) (eR r)) :
      TInput PK SK M R m n) * prFind (A.run pk (P.enc pk x (eR.symm (G (eM x)))) (eM x))
      (Function.update G (eM x) (eR r)) {eM x}
  rw [prFind_congr _ G (Function.update G (eM x) (eR r)) {eM x}
    (fun y hy => (Function.update_of_ne (by simpa using hy) _ _).symm) hψ]
  rfl

variable [NeZero q]

omit [Nonempty M] [NeZero n] in
include eM eR in
/-- The uniform weight on `Fin q × (Fin m → Fin n)` sums to one. -/
theorem sum_guess_weight :
    ∑ _p : Fin q × (Fin m → Fin n),
      (q : ℝ≥0∞)⁻¹ * ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹ = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum]
  rw [sum_card_pow_inv (M := M) (R := R) eM eR, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast NeZero.ne q) (ENNReal.natCast_ne_top q)

/-- The reduction from a `TAdv` to a `QOWAdv` that guesses the found query: the
    coins are a uniform query index `j` and a uniform oracle table `G`, and the
    adversary at `(j, G)` is `guessRun A j G`. -/
def guessReduction (A : TAdv m n w q PK C) : QOWAdv m n w PK C where
  Coins := Fin q × (Fin m → Fin n)
  weight _ := (q : ℝ≥0∞)⁻¹ * ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹
  weight_sum := sum_guess_weight eM eR
  run p pk c t := guessRun A p.1 p.2 pk c t
  final_eq _ _ _ _ := rfl
  pure _ pk c t := A.pure pk c t

/-- `q · (q⁻¹ · s) = s` in `ℝ≥0∞` for `q ≠ 0`. -/
theorem natCast_mul_inv_mul (s : ℝ≥0∞) : (q : ℝ≥0∞) * ((q : ℝ≥0∞)⁻¹ * s) = s := by
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast NeZero.ne q)
    (ENNReal.natCast_ne_top q), one_mul]

omit [Nonempty M] in
/-- The quantum OW-CPA game against the guessing reduction, as a sum over the
    key pair, the message, the coins, the query index and the oracle table. -/
theorem qOwcpaAdvantage_guessReduction (A : TAdv m n w q PK C) :
    qOwcpaAdvantage P eM (guessReduction eM eR A) =
      ∑ ks : PK × SK, ∑ x : M, ∑ r : R, ∑ j : Fin q, ∑ G : Fin m → Fin n,
        P.keygen ks * (Fintype.card M : ℝ≥0∞)⁻¹ * (Fintype.card R : ℝ≥0∞)⁻¹ *
          ((q : ℝ≥0∞)⁻¹ * ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹) *
          guessProb (A.run ks.1 (P.enc ks.1 x r) (eM x)) G {eM x} j := by
  unfold qOwcpaAdvantage
  refine Finset.sum_congr rfl fun ks _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun r _ => ?_
  refine (Fintype.sum_equiv (Equiv.refl _) _
    (fun p : Fin q × (Fin m → Fin n) =>
      P.keygen ks * (Fintype.card M : ℝ≥0∞)⁻¹ * (Fintype.card R : ℝ≥0∞)⁻¹ *
        ((q : ℝ≥0∞)⁻¹ * ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹) *
        guessProb (A.run ks.1 (P.enc ks.1 x r) (eM x)) p.2 {eM x} p.1)
    fun p => by simp only [guessReduction, prOut_guessRun, Equiv.refl_apply]).trans
    (Fintype.sum_prod_type' fun j G =>
      P.keygen ks * (Fintype.card M : ℝ≥0∞)⁻¹ * (Fintype.card R : ℝ≥0∞)⁻¹ *
        ((q : ℝ≥0∞)⁻¹ * ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹) *
        guessProb (A.run ks.1 (P.enc ks.1 x r) (eM x)) G {eM x} j)

/-- Theorem 2 of Ambainis–Hamburg–Unruh for the T transform:
    `tFind P A ≤ 4 q · qOwcpaAdvantage P (guessReduction A)`. -/
theorem tFind_le_qOwcpa (A : TAdv m n w q PK C) :
    tFind P eM eR A ≤ 4 * q * qOwcpaAdvantage P eM (guessReduction eM eR A) := by
  rw [tFind_eq, qOwcpaAdvantage_guessReduction]
  simp only [Fintype.sum_prod_type, tSample, Finset.mul_sum]
  refine Finset.sum_le_sum fun pk _ => Finset.sum_le_sum fun sk _ =>
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun r _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun G _ => ?_
  obtain ⟨ψ, hψ⟩ := A.pure pk (P.enc pk x r) (eM x)
  calc P.keygen (pk, sk) * (Fintype.card M : ℝ≥0∞)⁻¹ * (Fintype.card R : ℝ≥0∞)⁻¹ *
        ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹ *
        prFind (A.run pk (P.enc pk x r) (eM x)) G {eM x}
      ≤ P.keygen (pk, sk) * (Fintype.card M : ℝ≥0∞)⁻¹ * (Fintype.card R : ℝ≥0∞)⁻¹ *
        ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹ *
        (4 * ∑ j, guessProb (A.run pk (P.enc pk x r) (eM x)) G {eM x} j) := by
        gcongr
        exact prFind_le_four_sum_guess _ G {eM x} hψ
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show 4 * (q : ℝ≥0∞) * (P.keygen (pk, sk) * (Fintype.card M : ℝ≥0∞)⁻¹ *
            (Fintype.card R : ℝ≥0∞)⁻¹ * ((q : ℝ≥0∞)⁻¹ *
            ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹) *
            guessProb (A.run pk (P.enc pk x r) (eM x)) G {eM x} j) =
          (q : ℝ≥0∞) * ((q : ℝ≥0∞)⁻¹ * (P.keygen (pk, sk) * (Fintype.card M : ℝ≥0∞)⁻¹ *
            (Fintype.card R : ℝ≥0∞)⁻¹ * ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹ *
            (4 * guessProb (A.run pk (P.enc pk x r) (eM x)) G {eM x} j))) by ring,
          natCast_mul_inv_mul]

/-- The T transform in the QROM with both reductions named (Theorem 4.4 of
    Hofheinz–Hövelmanns–Kiltz with the `Find` term bounded by Theorem 2 of
    Ambainis–Hamburg–Unruh):
    `tOwAdvantage ≤ qOwcpaAdvantage (tReduction A) + 4 √(q · 4q · qOwcpaAdvantage (guessReduction A))`. -/
theorem tOw_le_qOwcpa_two (A : TAdv m n w q PK C) :
    tOwAdvantage P eM eR A ≤
      qOwcpaAdvantage P eM (tReduction eM eR A) +
        4 * ((q : ℝ≥0∞) * (4 * q * qOwcpaAdvantage P eM (guessReduction eM eR A))) ^
          (1 / 2 : ℝ) := by
  refine (tOw_le_qOwcpa_add_find P eM eR A).trans ?_
  have := tFind_le_qOwcpa P eM eR A
  gcongr

end Reduction

end CatCrypt.Quantum.QROM
