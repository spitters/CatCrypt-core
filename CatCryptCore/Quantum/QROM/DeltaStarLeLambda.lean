/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.CoinBadNumeric

/-!
# The challenge-message failure weight is at most `Λ`

The weight `δ*` of the inputs of the KEM game whose challenge message `m*` is
outside `kemGood` is bounded by `Λ = E λ`, the average over key generation of a
per-key bound `λ` on the bad fraction `|badVals (kemBad pk sk) x| / n` at every
point `x`. Under `kemSample` the `G`-table is uniform, so its value at the
challenge point `(m*, hpk pk)` is uniform, and `m* ∉ kemGood` holds exactly when
that value is bad for the key pair.

## Main results

* `sum_uniform_bad_at` — the uniform weight of the tables whose value at `t` is
  bad is `|badVals bad t| / n`
* `not_mem_kemGood_iff` — `m* ∉ kemGood` at `kemJoin r G` is `kemBad` at the
  challenge point and the value `G` takes there
* `deltaStar_le_Lambda` — `δ* ≤ Λ`

## Scope

`hlam` is used at the challenge point only, and only on the support of key
generation.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The uniform table at one point -/

section Point

variable {m n : ℕ}

/-- The uniform weight of the tables whose value at `t` is bad is the fraction
of bad values at `t`. -/
theorem sum_uniform_bad_at [NeZero n] (bad : Fin m → Fin n → Bool) (t : Fin m) :
    ∑ G : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * (if bad t (G t) then 1 else 0) =
      ((badVals bad t).card : ℝ≥0∞) / (n : ℝ≥0∞) := by
  have h1 : ∑ _H' : {x // x ≠ t} → Fin n, ((n : ℝ≥0∞) ^ (m - 1))⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_subtype_compl,
      Fintype.card_fin, Fintype.card_fin, Fintype.card_subtype_eq, nsmul_eq_mul, Nat.cast_pow]
    exact ENNReal.mul_inv_cancel (pow_ne_zero _ (NeZero.ne _)) (ENNReal.pow_ne_top
      (ENNReal.natCast_ne_top n))
  rw [sum_split_point_uniform t]
  simp only [Equiv.piSplitAt_symm_apply, dite_true, ← Finset.sum_mul, h1, one_mul,
    ← Finset.mul_sum, Finset.sum_boole, badVals, div_eq_mul_inv]
  rw [mul_comm]

end Point

/-! ## The challenge message outside `kemGood` -/

section KEM

variable {m₁ m₂ n : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Fintype Z] [Fintype K] [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁)
  (eKR : (K × R) ≃ Fin n)

omit [Fintype PK] [Fintype SK] [Fintype Z] [Fintype K] in
/-- The challenge message of `kemJoin r G` is outside `kemGood` exactly when the
value of `G` at the challenge point `(m*, hpk pk)` is bad for the key pair. -/
theorem not_mem_kemGood_iff (r : KEMRest PK SK Z M K m₂ n) (G : Fin m₁ → Fin n) :
    (kemJoin r G).2.2.1 ∉ kemGood P hpk eG eKR (kemJoin r G) ↔
      kemBad P hpk eG eKR r.1.1 r.1.2 (eG (r.2.2.1, hpk r.1.1))
        (G (eG (r.2.2.1, hpk r.1.1))) = true := by
  simp only [kemGood, mem_good_iff, encAt, coinsOf, kemTab, kemG, kemJoin, kemBad,
    Equiv.symm_apply_apply, decide_true, Bool.true_and, Bool.not_eq_true',
    decide_eq_false_iff_not]

/-- **`δ* ≤ Λ`.** The weight of the inputs whose challenge message is outside
`kemGood` is at most the average over key generation of a bound `λ` on the bad
fraction at every point. -/
theorem deltaStar_le_Lambda [NeZero n] (lam : PK × SK → ℝ≥0∞)
    (hlam : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam (pk, sk)) :
    ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
        (if i.2.2.1 ∈ kemGood P hpk eG eKR i then 0 else 1) ≤
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 := by
  rw [sum_kemSample_kemJoin P, sum_kemSample_kemJoin P (fun i => lam i.1)]
  refine Finset.sum_le_sum fun r _ => ?_
  by_cases hk : P.keygen r.1 = 0
  · simp [kemRestWeight, hk]
  refine mul_le_mul_right ?_ _
  have hind : ∀ G : Fin m₁ → Fin n,
      (if (kemJoin r G).2.2.1 ∈ kemGood P hpk eG eKR (kemJoin r G) then (0 : ℝ≥0∞) else 1) =
        if kemBad P hpk eG eKR r.1.1 r.1.2 (eG (r.2.2.1, hpk r.1.1))
          (G (eG (r.2.2.1, hpk r.1.1))) then 1 else 0 := fun G => by
    by_cases h : (kemJoin r G).2.2.1 ∈ kemGood P hpk eG eKR (kemJoin r G)
    · have h' := mt (not_mem_kemGood_iff P hpk eG eKR r G).2 (not_not.2 h)
      simp [h, h']
    · simp [h, (not_mem_kemGood_iff P hpk eG eKR r G).1 h]
  have hconst : ∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ * lam (kemJoin r G).1 = lam r.1 := by
    rw [← Finset.mul_sum]
    change ((n : ℝ≥0∞) ^ m₁)⁻¹ * ∑ _G : Fin m₁ → Fin n, lam r.1 = lam r.1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, ← mul_assoc,
      ENNReal.inv_mul_cancel (pow_ne_zero _ (NeZero.ne _))
        (ENNReal.pow_ne_top (ENNReal.natCast_ne_top n)), one_mul]
  simp only [hind, hconst, sum_uniform_bad_at]
  exact hlam r.1.1 r.1.2 hk _

end KEM

end CatCrypt.Quantum.QROM

end

end
