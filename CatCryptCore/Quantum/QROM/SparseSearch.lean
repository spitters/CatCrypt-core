/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.FindToGuess

/-!
# Search in an unstructured function

The bound of Ambainis–Hamburg–Unruh (CRYPTO 2019, §4.1) on the probability
that a `q`-query adversary outputs a point `x` at which the oracle value is
bad: when for every `x` the weight of the oracles with `bad x (H x)` is at
most `λ`, the averaged probability is at most `4 (q + 1)² λ`. The adversary is
extended by one query at its output, so that the `Find` event of the
semi-classical run at the bad set contains the bad-output event; the
square-root form of the one-way-to-hiding inequality bounds the latter by
`(q + 1) · Pr[Find]`; `Pr[Find]` is bounded by the guessing probabilities of
the run against a fixed reference oracle, whose average over the oracle is the
marginal bound.

## Main definitions

* `outProj m n w S` — the projector `1 ⊗ |S⟩⟨S| ⊗ 1` onto the states whose
  output factor lies in `S`
* `extendU A`, `extend A S` — the unitaries of `A` with `swapU` appended to
  the last one and an identity after the extra query, and the `q + 1`-query
  adversary with final projector `projS S`
* `badSet bad H` — the points `x` with `bad x (H x)`
* `prBad bad A H` — `prOut (extend A (badSet bad H)) H`, the probability that
  `A` against `H` outputs a bad point

## Main results

* `abs_nrm_sub_le_sqrt`, `o2h_sqrt` — the square-root one-way-to-hiding
  inequality `|√Pr[out = 1 : H] − √Pr[out = 1 ∧ ¬Find : H \ S]| ≤ √(q · Pr[Find])`
* `prOut_le_of_noFind_zero` — `Pr[out = 1 ∧ ¬Find] = 0 → Pr[out = 1] ≤ q · Pr[Find]`
* `prOutNoFind_extend` — the extended adversary never outputs `1` on the
  `Find = false` branch at its own set
* `prBad_eq_nrm_sq` — `prBad` is the squared norm of the output projection of
  the final state of `A`
* `prBad_le_prFind`, `prBad_le_four_sum_guess` — `prBad ≤ (q + 1) · Pr[Find]`
  and `prBad ≤ 4 (q + 1) ∑ⱼ guessProb (extend A) H₀ (badSet bad H) j`
* `guessProb_eq_sum` — `guessProb A H S j = ∑ x ∈ S, guessProb A H {x} j`
* `sparse_search` — `∑ H, w H · prBad bad A H ≤ 4 (q + 1) (q + 1) λ`

## The hypotheses

The hypotheses of `sparse_search` are: the adversary's initial state is pure
(`hpure`), as in `O2HTheorem`; the predicate `bad` reads the oracle value at the
output only; the weights `μ` on the oracles satisfy the marginal bound
`∑ H, μ H · [bad x (H x)] ≤ λ` at every `x` (`hlam`), with no further condition
relating different points; and the oracles of nonzero weight agree with the
reference oracle `H₀` outside their bad set (`hagree`). The reference has oracle
values in `{0, 1}`, `bad x y = (y = 1)` and `H₀ = 0`.

## References

* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], §4.1
* [Hofheinz, Hövelmanns, Kiltz — A Modular Analysis of the Fujisaki–Okamoto
  Transformation, TCC 2017], Lemma 4.3
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The square-root one-way-to-hiding inequality -/

section Sqrt

variable {m n w q : ℕ} [NeZero n]

/-- The real-valued core: `|‖M R ψ‖ − ‖M S ψ‖| ≤ √(q · ∑ᵢ ‖Π θᵢ‖²)`. -/
theorem abs_nrm_sub_le_sqrt (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m))
    (ψ : Fin (m * n * w) → ℂ) :
    |nrm (A.final *ᵥ (runOp A H *ᵥ ψ)) - nrm (A.final *ᵥ (scOp A H S *ᵥ ψ))| ≤
      Real.sqrt ((q : ℝ) * ∑ i, nrm (projS m n w S *ᵥ scState A H S ψ i) ^ 2) := by
  have hcs := sum_le_sqrt_card_mul_sum_sq (fun i => nrm (projS m n w S *ᵥ scState A H S ψ i))
    (fun i => nrm_nonneg _)
  rw [Fintype.card_fin] at hcs
  calc |nrm (A.final *ᵥ (runOp A H *ᵥ ψ)) - nrm (A.final *ᵥ (scOp A H S *ᵥ ψ))|
      ≤ nrm (A.final *ᵥ (runOp A H *ᵥ ψ) - A.final *ᵥ (scOp A H S *ᵥ ψ)) :=
        abs_nrm_sub_nrm_le _ _
    _ = nrm (A.final *ᵥ (runOp A H *ᵥ ψ - scOp A H S *ᵥ ψ)) := by rw [mulVec_sub]
    _ ≤ nrm (runOp A H *ᵥ ψ - scOp A H S *ᵥ ψ) :=
        nrm_proj_mulVec_le A.final_mul_self A.final_conjTranspose _
    _ ≤ ∑ i, nrm (projS m n w S *ᵥ scState A H S ψ i) :=
        nrm_chainOp_sub_le (projS m n w S) (oracleU m n w H).prop q A.U ψ
    _ ≤ _ := hcs

/-- The square-root one-way-to-hiding inequality for a pure initial state:
    `|√Pr[out = 1 : A^H] − √Pr[out = 1 ∧ ¬Find : A^{H \ S}]| ≤ √(q · Pr[Find])`, in `ℝ`. -/
theorem o2h_sqrt (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m))
    {ψ : Fin (m * n * w) → ℂ} (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    |Real.sqrt (prOut A H).toReal - Real.sqrt (prOutNoFind A H S).toReal| ≤
      Real.sqrt ((q : ℝ) * (prFind A H S).toReal) := by
  rw [prOut_eq_nrm_sq A H hpure, prOutNoFind_eq_nrm_sq A H S hpure, prFind_eq_sum A H S hpure,
    ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Real.sqrt_sq (nrm_nonneg _), Real.sqrt_sq (nrm_nonneg _)]
  exact abs_nrm_sub_le_sqrt A H S ψ

/-- The square-root one-way-to-hiding inequality in `ℝ≥0∞`:
    `|Pr[out = 1 : A^H]^½ − Pr[out = 1 ∧ ¬Find : A^{H \ S}]^½| ≤ (q · Pr[Find])^½`. -/
theorem o2h_sqrt_ennreal (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m))
    {ψ : Fin (m * n * w) → ℂ} (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    absDiff ((prOut A H) ^ (1 / 2 : ℝ)) ((prOutNoFind A H S) ^ (1 / 2 : ℝ)) ≤
      ((q : ℝ≥0∞) * prFind A H S) ^ (1 / 2 : ℝ) := by
  have hF : 0 ≤ ∑ i, nrm (projS m n w S *ᵥ scState A H S ψ i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hr : ((q : ℝ≥0∞) * ENNReal.ofReal (∑ i, nrm (projS m n w S *ᵥ scState A H S ψ i) ^ 2)) ^
      (1 / 2 : ℝ) = ENNReal.ofReal
        (Real.sqrt ((q : ℝ) * ∑ i, nrm (projS m n w S *ᵥ scState A H S ψ i) ^ 2)) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hF)
      (by norm_num), ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [prOut_eq_nrm_sq A H hpure, prOutNoFind_eq_nrm_sq A H S hpure, prFind_eq_sum A H S hpure, hr,
    ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num),
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq (nrm_nonneg _),
    Real.sqrt_sq (nrm_nonneg _)]
  refine (absDiff_ofReal_le (nrm_nonneg _) (nrm_nonneg _)).trans (ENNReal.ofReal_le_ofReal ?_)
  exact abs_nrm_sub_le_sqrt A H S ψ

/-- When the `Find = false` branch never outputs `1`, `Pr[out = 1] ≤ q · Pr[Find]`. -/
theorem prOut_le_of_noFind_zero (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m))
    {ψ : Fin (m * n * w) → ℂ} (hpure : A.init.val = vecMulVec ψ (star ψ))
    (h0 : prOutNoFind A H S = 0) : prOut A H ≤ (q : ℝ≥0∞) * prFind A H S := by
  have h := abs_nrm_sub_le_sqrt A H S ψ
  rw [prOutNoFind_eq_nrm_sq A H S hpure, ENNReal.ofReal_eq_zero] at h0
  have hb : nrm (A.final *ᵥ (scOp A H S *ᵥ ψ)) = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h0 (sq_nonneg _))
  rw [hb, sub_zero, abs_of_nonneg (nrm_nonneg _)] at h
  rw [prOut_eq_nrm_sq A H hpure, prFind_eq_sum A H S hpure, ← ENNReal.ofReal_natCast q,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.sqrt_le_sqrt_iff (mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg fun i _ => sq_nonneg _)), Real.sqrt_sq (nrm_nonneg _)]
  exact h

end Sqrt

/-! ## Appending a unitary to the last step and a query after it -/

section Chain

variable {d : ℕ}

/-- `chainOp` of `Fin.snoc U V`: the extra query and the extra unitary act last. -/
theorem chainOp_snoc (O : Matrix (Fin d) (Fin d) ℂ) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (V : Matrix.unitaryGroup (Fin d) ℂ) :
    chainOp O (q + 1) (Fin.snoc U V) = (V : Matrix _ _ ℂ) * O * chainOp O q U := by
  induction q with
  | zero =>
    simp only [chainOp, Fin.tail]
    rfl
  | succ q ih =>
    have ht : Fin.tail (Fin.snoc U V : Fin (q + 3) → Matrix.unitaryGroup (Fin d) ℂ) =
        Fin.snoc (Fin.tail U) V := by
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [Fin.tail, Fin.snoc_last]
      · rw [Fin.snoc_castSucc]
        show (Fin.snoc U V : Fin (q + 3) → Matrix.unitaryGroup (Fin d) ℂ) i.castSucc.succ =
          U i.succ
        rw [Fin.succ_castSucc, Fin.snoc_castSucc]
    have h0 : (Fin.snoc U V : Fin (q + 3) → Matrix.unitaryGroup (Fin d) ℂ) 0 = U 0 := by simp
    rw [chainOp, ht, ih, h0, chainOp]
    simp only [Matrix.mul_assoc]

/-- `chainOp` of `U` with `V` composed after its last unitary. -/
theorem chainOp_update_last (O : Matrix (Fin d) (Fin d) ℂ) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (V : Matrix.unitaryGroup (Fin d) ℂ) :
    chainOp O q (Function.update U (Fin.last q) (V * U (Fin.last q))) =
      (V : Matrix _ _ ℂ) * chainOp O q U := by
  induction q with
  | zero =>
    simp only [chainOp, Fin.last_zero, Function.update_self, Submonoid.coe_mul]
  | succ q ih =>
    have h0 : Function.update U (Fin.last (q + 1)) (V * U (Fin.last (q + 1))) 0 = U 0 :=
      Function.update_of_ne (Fin.last_pos).ne _ _
    have ht : Fin.tail (Function.update U (Fin.last (q + 1)) (V * U (Fin.last (q + 1)))) =
        Function.update (Fin.tail U) (Fin.last q) (V * Fin.tail U (Fin.last q)) := by
      rw [← Fin.succ_last, Fin.tail_update_succ]
      rfl
    rw [chainOp, h0, ht, ih, chainOp]
    simp only [Matrix.mul_assoc]

end Chain

/-! ## The output projector for a set and its commutation with the swap -/

section OutProj

variable (m n w : ℕ)

/-- The projector `1 ⊗ |S⟩⟨S| ⊗ 1` onto the states whose work register has first
    factor in `S`, on the total register `Fin (m * n * (m * w))`. -/
def outProj (S : Finset (Fin m)) : Matrix (Fin (m * n * (m * w))) (Fin (m * n * (m * w))) ℂ :=
  (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℂ) ⊗ₖ
    (Matrix.diagonal (indS m S) ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℂ))

theorem outProj_eq_diagonal (S : Finset (Fin m)) :
    outProj m n w S = Matrix.diagonal (fun k => indS m S (oPart m n w k)) := by
  unfold outProj
  rw [diagonal_kronecker_one, one_kronecker_diagonal]
  rfl

/-- `outProj S * swapU = swapU * projS S`: the swap carries the query projector
    to the output projector. -/
theorem outProj_mul_swapU (S : Finset (Fin m)) :
    outProj m n w S * (swapU m n w : Matrix _ _ ℂ) =
      (swapU m n w : Matrix _ _ ℂ) * projS m n (m * w) S := by
  have h : ∀ k, (outProj m n w S * (swapU m n w : Matrix _ _ ℂ)) *ᵥ Pi.single k 1 =
      ((swapU m n w : Matrix _ _ ℂ) * projS m n (m * w) S) *ᵥ Pi.single k 1 := by
    intro k
    have hs : (Pi.single k (indS m S (xPart m n (m * w) k)) : Fin (m * n * (m * w)) → ℂ) =
        indS m S (xPart m n (m * w) k) • Pi.single k 1 := by
      ext i; simp [Pi.single_apply]
    rw [← mulVec_mulVec, ← mulVec_mulVec, swapU, permUnitary_mulVec_single, outProj_eq_diagonal,
      projS_eq_diagonal, diagonal_mulVec_single, diagonal_mulVec_single, mul_one, mul_one, hs,
      mulVec_smul, permUnitary_mulVec_single, oPart_swapPerm]
    ext i; simp [Pi.single_apply]
  ext i k
  simpa [mulVec_single_one] using congrFun (h k) i

theorem xPart_swapPerm (k : Fin (m * n * (m * w))) :
    xPart m n (m * w) (swapPerm m n w k) = oPart m n w k := by
  simp [oPart, xPart, swapPerm, totalIndex, swapXO, Equiv.permCongr_apply]

/-- `projS S * swapU = swapU * outProj S`: the swap carries the output
    projector to the query projector. -/
theorem projS_mul_swapU (S : Finset (Fin m)) :
    projS m n (m * w) S * (swapU m n w : Matrix _ _ ℂ) =
      (swapU m n w : Matrix _ _ ℂ) * outProj m n w S := by
  have h : ∀ k, (projS m n (m * w) S * (swapU m n w : Matrix _ _ ℂ)) *ᵥ Pi.single k 1 =
      ((swapU m n w : Matrix _ _ ℂ) * outProj m n w S) *ᵥ Pi.single k 1 := by
    intro k
    have hs : (Pi.single k (indS m S (oPart m n w k)) : Fin (m * n * (m * w)) → ℂ) =
        indS m S (oPart m n w k) • Pi.single k 1 := by
      ext i; simp [Pi.single_apply]
    rw [← mulVec_mulVec, ← mulVec_mulVec, swapU, permUnitary_mulVec_single, outProj_eq_diagonal,
      projS_eq_diagonal, diagonal_mulVec_single, diagonal_mulVec_single, mul_one, mul_one, hs,
      mulVec_smul, permUnitary_mulVec_single, xPart_swapPerm]
    ext i; simp [Pi.single_apply]
  ext i k
  simpa [mulVec_single_one] using congrFun (h k) i

end OutProj

/-! ## The query projector commutes with the oracle -/

section Comm

variable (m n w : ℕ) [NeZero n]

omit [NeZero n] in
/-- The first factor of the row-major index of `((x, y), z)` is `x`. -/
theorem xPart_finProdEquiv (x : Fin m) (y : Fin n) (z : Fin w) :
    xPart m n w (finProdEquiv (m * n) w (fixedIndex m n (x, y), z)) = x := by
  simp [xPart, fixedIndex, finProdEquiv]

/-- The column of the oracle at the basis ket `|x, y⟩` is the ket `|x, y + H x⟩`. -/
theorem stdOracleFixedG_apply_fixedIndex (H : Fin m → Fin n) (i : Fin (m * n)) (x : Fin m)
    (y : Fin n) :
    stdOracleFixedG m n H i (fixedIndex m n (x, y)) =
      if i = fixedIndex m n (x, y + H x) then 1 else 0 := by
  have := congrFun (stdOracleFixedG_ket m n H x y) i
  rwa [Matrix.mulVec_single_one, Pi.single_apply] at this

/-- `projS S * U_H = U_H * projS S`: the oracle preserves the query register's
    first factor. -/
theorem projS_mul_oracleU (S : Finset (Fin m)) (H : Fin m → Fin n) :
    projS m n w S * (oracleU m n w H : Matrix _ _ ℂ) =
      (oracleU m n w H : Matrix _ _ ℂ) * projS m n w S := by
  rw [projS_eq_diagonal]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  obtain ⟨⟨p, z⟩, rfl⟩ := (finProdEquiv (m * n) w).surjective j
  obtain ⟨⟨x, y⟩, rfl⟩ := (fixedIndex m n).surjective p
  obtain ⟨⟨p', z'⟩, rfl⟩ := (finProdEquiv (m * n) w).surjective i
  obtain ⟨⟨x', y'⟩, rfl⟩ := (fixedIndex m n).surjective p'
  simp only [oracleU_val, kronecker_apply, Equiv.symm_apply_apply, xPart_finProdEquiv,
    stdOracleFixedG_apply_fixedIndex]
  by_cases hxy : fixedIndex m n (x', y') = fixedIndex m n (x, y + H x)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj ((fixedIndex m n).injective hxy)
    ring
  · simp [hxy]

/-- `projS S * U_H * (1 − projS S) = 0`. -/
theorem projS_mul_oracleU_mul_one_sub (S : Finset (Fin m)) (H : Fin m → Fin n) :
    projS m n w S * (oracleU m n w H : Matrix _ _ ℂ) * (1 - projS m n w S) = 0 := by
  rw [projS_mul_oracleU, Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, projS_mul_self,
    sub_self, Matrix.mul_zero]

/-- The oracle does not change the norm of the query projection. -/
theorem nrm_projS_mulVec_oracleU (S : Finset (Fin m)) (H : Fin m → Fin n)
    (v : Fin (m * n * w) → ℂ) :
    nrm (projS m n w S *ᵥ ((oracleU m n w H : Matrix _ _ ℂ) *ᵥ v)) = nrm (projS m n w S *ᵥ v) := by
  rw [mulVec_mulVec, projS_mul_oracleU, ← mulVec_mulVec,
    nrm_mulVec_of_mem_unitaryGroup (oracleU m n w H).prop]

end Comm

/-! ## The extended adversary -/

section Extend

variable {m n w q : ℕ} [NeZero n]

/-- The unitaries of the extended adversary: those of `A` with `swapU` composed
    after the last one, then the identity after the extra query. -/
def extendU (A : QAdv m n (m * w) q) :
    Fin (q + 2) → Matrix.unitaryGroup (Fin (m * n * (m * w))) ℂ :=
  Fin.snoc (Function.update A.U (Fin.last q) (swapU m n w * A.U (Fin.last q))) 1

/-- The `q + 1`-query adversary that runs `A`, swaps the output factor into the
    query register, queries once more, and measures whether the query register
    lies in `S`. -/
def extend (A : QAdv m n (m * w) q) (S : Finset (Fin m)) : QAdv m n (m * w) (q + 1) where
  U := extendU A
  init := A.init
  final := projS m n (m * w) S
  final_conjTranspose := projS_conjTranspose m n (m * w) S
  final_mul_self := projS_mul_self m n (m * w) S

/-- The points at which the oracle value is bad. -/
def badSet (bad : Fin m → Fin n → Bool) (H : Fin m → Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun x => bad x (H x)

/-- The probability that `A` against `H` outputs a point `x` with `bad x (H x)`:
    the acceptance probability of the extended adversary at `badSet bad H`. -/
def prBad (bad : Fin m → Fin n → Bool) (A : QAdv m n (m * w) q) (H : Fin m → Fin n) : ℝ≥0∞ :=
  prOut (extend A (badSet bad H)) H

/-- The run operator of the extended adversary. -/
theorem runOp_extend (A : QAdv m n (m * w) q) (S : Finset (Fin m)) (H : Fin m → Fin n) :
    runOp (extend A S) H =
      (oracleU m n (m * w) H : Matrix _ _ ℂ) * (swapU m n w : Matrix _ _ ℂ) * runOp A H := by
  unfold runOp
  simp only [extend, extendU]
  rw [chainOp_snoc, chainOp_update_last, OneMemClass.coe_one, Matrix.one_mul, Matrix.mul_assoc]

/-- The projected chain operator of the extended adversary. -/
theorem scOp_extend (A : QAdv m n (m * w) q) (S : Finset (Fin m)) (H : Fin m → Fin n)
    (S' : Finset (Fin m)) :
    scOp (extend A S) H S' =
      (oracleU m n (m * w) H : Matrix _ _ ℂ) * (1 - projS m n (m * w) S') *
        (swapU m n w : Matrix _ _ ℂ) * scOp A H S' := by
  unfold scOp
  simp only [extend, extendU]
  rw [chainOp_snoc, chainOp_update_last, OneMemClass.coe_one, Matrix.one_mul]
  simp only [Matrix.mul_assoc]

omit [NeZero n] in
/-- The swap carries the norm of the query projection to the output projection. -/
theorem nrm_projS_mulVec_swapU (S : Finset (Fin m)) (v : Fin (m * n * (m * w)) → ℂ) :
    nrm (projS m n (m * w) S *ᵥ ((swapU m n w : Matrix _ _ ℂ) *ᵥ v)) =
      nrm (outProj m n w S *ᵥ v) := by
  rw [mulVec_mulVec, projS_mul_swapU, ← mulVec_mulVec,
    nrm_mulVec_of_mem_unitaryGroup (swapU m n w).prop]

/-- The extended adversary accepts with the squared norm of the output
    projection of the final state of `A`. -/
theorem prOut_extend_eq_nrm_sq (A : QAdv m n (m * w) q) (S : Finset (Fin m))
    (H : Fin m → Fin n) {ψ : Fin (m * n * (m * w)) → ℂ}
    (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    prOut (extend A S) H = ENNReal.ofReal (nrm (outProj m n w S *ᵥ (runOp A H *ᵥ ψ)) ^ 2) := by
  rw [prOut_eq_nrm_sq (extend A S) H hpure]
  show ENNReal.ofReal (nrm (projS m n (m * w) S *ᵥ (runOp (extend A S) H *ᵥ ψ)) ^ 2) = _
  rw [runOp_extend, ← mulVec_mulVec, ← mulVec_mulVec, nrm_projS_mulVec_oracleU,
    nrm_projS_mulVec_swapU]

/-- `prBad` is the squared norm of the projection of the final state of `A`
    onto the outputs in `badSet bad H`. -/
theorem prBad_eq_nrm_sq (bad : Fin m → Fin n → Bool) (A : QAdv m n (m * w) q)
    (H : Fin m → Fin n) {ψ : Fin (m * n * (m * w)) → ℂ}
    (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    prBad bad A H =
      ENNReal.ofReal (nrm (outProj m n w (badSet bad H) *ᵥ (runOp A H *ᵥ ψ)) ^ 2) :=
  prOut_extend_eq_nrm_sq A _ H hpure

/-- On the `Find = false` branch at its own set, the extended adversary never
    outputs `1`, whatever the oracle: the last query is made at the output, so
    the semi-classical measurement before it has excluded the set. -/
theorem prOutNoFind_extend (A : QAdv m n (m * w) q) (S : Finset (Fin m)) (K : Fin m → Fin n)
    {ψ : Fin (m * n * (m * w)) → ℂ} (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    prOutNoFind (extend A S) K S = 0 := by
  rw [prOutNoFind_eq_nrm_sq (extend A S) K S hpure]
  show ENNReal.ofReal (nrm (projS m n (m * w) S *ᵥ (scOp (extend A S) K S *ᵥ ψ)) ^ 2) = 0
  rw [scOp_extend, mulVec_mulVec]
  simp only [← Matrix.mul_assoc, projS_mul_oracleU_mul_one_sub, Matrix.zero_mul, zero_mulVec,
    nrm_zero]
  simp

/-- The guessing probability of the extended adversary does not depend on its
    final set. -/
theorem guessProb_extend (A : QAdv m n (m * w) q) (S S' : Finset (Fin m)) (H : Fin m → Fin n)
    (T : Finset (Fin m)) (j : Fin (q + 1)) :
    guessProb (extend A S) H T j = guessProb (extend A S') H T j := rfl

end Extend

/-! ## The bad-output probability against `Pr[Find]` and the guessing probabilities -/

section Bound

variable {m n w q : ℕ} [NeZero n]

/-- `prBad bad A H ≤ (q + 1) · Pr[Find : (extend A)^{H \ badSet bad H}]`. -/
theorem prBad_le_prFind (bad : Fin m → Fin n → Bool) (A : QAdv m n (m * w) q)
    (H : Fin m → Fin n) {ψ : Fin (m * n * (m * w)) → ℂ}
    (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    prBad bad A H ≤
      ((q : ℝ≥0∞) + 1) * prFind (extend A (badSet bad H)) H (badSet bad H) := by
  have h := prOut_le_of_noFind_zero (extend A (badSet bad H)) H (badSet bad H) hpure
    (prOutNoFind_extend A _ H hpure)
  push_cast at h
  exact h

/-- `prBad bad A H ≤ 4 (q + 1) ∑ⱼ guessProb (extend A) H₀ (badSet bad H) j` for a
    reference oracle `H₀` agreeing with `H` outside the bad set. -/
theorem prBad_le_four_sum_guess (bad : Fin m → Fin n → Bool) (A : QAdv m n (m * w) q)
    (H H₀ : Fin m → Fin n) (hagree : ∀ x, bad x (H x) = false → H x = H₀ x)
    {ψ : Fin (m * n * (m * w)) → ℂ} (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    prBad bad A H ≤ 4 * ((q : ℝ≥0∞) + 1) *
      ∑ j, guessProb (extend A (badSet bad H)) H₀ (badSet bad H) j := by
  refine (prBad_le_prFind bad A H hpure).trans ?_
  rw [prFind_congr (extend A (badSet bad H)) H H₀ _
    (fun x hx => hagree x (by simpa [badSet] using hx)) hpure]
  calc ((q : ℝ≥0∞) + 1) * prFind (extend A (badSet bad H)) H₀ (badSet bad H)
      ≤ ((q : ℝ≥0∞) + 1) *
          (4 * ∑ j, guessProb (extend A (badSet bad H)) H₀ (badSet bad H) j) := by
        gcongr
        exact prFind_le_four_sum_guess _ H₀ _ hpure
    _ = _ := by ring

omit [NeZero n] in
theorem norm_boole_mul_sq (p : Prop) [Decidable p] (c : ℂ) :
    ‖(if p then (1 : ℂ) else 0) * c‖ ^ 2 = if p then ‖c‖ ^ 2 else 0 := by
  split_ifs <;> simp

omit [NeZero n] in
/-- The squared norm of the projection onto `S` is the sum over `x ∈ S` of the
    squared norms of the projections onto `{x}`. -/
theorem nrm_sq_projS_eq_sum (S : Finset (Fin m)) (v : Fin (m * n * w) → ℂ) :
    nrm (projS m n w S *ᵥ v) ^ 2 = ∑ x ∈ S, nrm (projS m n w {x} *ᵥ v) ^ 2 := by
  have hn : ∀ u : Fin (m * n * w) → ℂ, nrm u ^ 2 = ∑ k, ‖u k‖ ^ 2 := fun u => by
    unfold nrm
    rw [EuclideanSpace.norm_sq_eq]
  simp only [hn, projS_eq_diagonal, mulVec_diagonal, indS, Finset.mem_singleton,
    norm_boole_mul_sq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.sum_ite_eq]

/-- `guessProb A H S j = ∑ x ∈ S, guessProb A H {x} j`. -/
theorem guessProb_eq_sum (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m))
    (j : Fin q) {ψ : Fin (m * n * w) → ℂ} (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    guessProb A H S j = ∑ x ∈ S, guessProb A H {x} j := by
  simp only [guessProb_eq_nrm_sq A H _ j hpure]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => sq_nonneg _), nrm_sq_projS_eq_sum]

/-- The guessing probabilities at the singletons sum to at most one. -/
theorem sum_guessProb_singleton_le_one (A : QAdv m n w q) (H : Fin m → Fin n) (j : Fin q)
    {ψ : Fin (m * n * w) → ℂ} (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    ∑ x, guessProb A H {x} j ≤ 1 := by
  rw [← guessProb_eq_sum A H Finset.univ j hpure, guessProb_eq_nrm_sq A H _ j hpure,
    ENNReal.ofReal_le_one]
  have h1 : nrm (plainState A H ψ j) = 1 := by
    unfold plainState
    rw [← chainOp_castLE_mulVec,
      nrm_chainOp_mulVec_eq _ (nrm_mulVec_of_mem_unitaryGroup (oracleU m n w H).prop),
      nrm_eq_one_of_init A hpure]
  calc nrm (projS m n w Finset.univ *ᵥ plainState A H ψ j) ^ 2
      ≤ nrm (plainState A H ψ j) ^ 2 :=
        pow_le_pow_left₀ (nrm_nonneg _)
          (nrm_proj_mulVec_le (projS_mul_self m n w _) (projS_conjTranspose m n w _) _) 2
    _ = 1 := by rw [h1, one_pow]

/-- Search in an unstructured function (Ambainis–Hamburg–Unruh, CRYPTO 2019,
    §4.1): for weights `μ` on the oracles with `∑ H, μ H · [bad x (H x)] ≤ λ`
    at every `x`, and a reference oracle `H₀` agreeing with every oracle of
    nonzero weight outside its bad set,
    `∑ H, μ H · prBad bad A H ≤ 4 (q + 1) (q + 1) λ`. -/
theorem sparse_search (bad : Fin m → Fin n → Bool) (A : QAdv m n (m * w) q)
    (H₀ : Fin m → Fin n) (μ : (Fin m → Fin n) → ℝ≥0∞) (lam : ℝ≥0∞)
    (hagree : ∀ H, μ H ≠ 0 → ∀ x, bad x (H x) = false → H x = H₀ x)
    (hlam : ∀ x, ∑ H, μ H * (if bad x (H x) then 1 else 0) ≤ lam)
    {ψ : Fin (m * n * (m * w)) → ℂ} (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    ∑ H, μ H * prBad bad A H ≤ 4 * ((q : ℝ≥0∞) + 1) * ((q : ℝ≥0∞) + 1) * lam := by
  calc ∑ H, μ H * prBad bad A H
      ≤ ∑ H, μ H * (4 * ((q : ℝ≥0∞) + 1) * ∑ j, ∑ x,
          (if bad x (H x) then 1 else 0) * guessProb (extend A ∅) H₀ {x} j) := by
        refine Finset.sum_le_sum fun H _ => ?_
        by_cases hμ : μ H = 0
        · simp [hμ]
        gcongr
        refine (prBad_le_four_sum_guess bad A H H₀ (hagree H hμ) hpure).trans (le_of_eq ?_)
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [guessProb_extend A _ ∅, guessProb_eq_sum _ H₀ _ j hpure]
        simp only [badSet, Finset.sum_filter, boole_mul]
    _ = 4 * ((q : ℝ≥0∞) + 1) * ∑ j, ∑ x, guessProb (extend A ∅) H₀ {x} j *
          ∑ H, μ H * (if bad x (H x) then 1 else 0) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun H _ => ?_
        ring
    _ ≤ 4 * ((q : ℝ≥0∞) + 1) * ∑ j, ∑ x, guessProb (extend A ∅) H₀ {x} j * lam := by
        gcongr with j _ x _
        exact hlam x
    _ = 4 * ((q : ℝ≥0∞) + 1) * ∑ j : Fin (q + 1), lam * ∑ x, guessProb (extend A ∅) H₀ {x} j := by
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    _ ≤ 4 * ((q : ℝ≥0∞) + 1) * ∑ j : Fin (q + 1), lam * 1 := by
        gcongr with j _
        exact sum_guessProb_singleton_le_one (extend A ∅) H₀ j hpure
    _ = 4 * ((q : ℝ≥0∞) + 1) * ((q : ℝ≥0∞) + 1) * lam := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        push_cast
        ring

end Bound

end CatCrypt.Quantum.QROM
