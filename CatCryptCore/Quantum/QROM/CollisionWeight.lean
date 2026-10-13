/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.HopCoinChallenge
public import CatCryptCore.Quantum.QROM.CompositePerTable
public import CatCryptCore.Quantum.QROM.SearchOffChallenge

/-!
# The key-averaged coin-collision weight

The coin hop of `Quantum/QROM/HopCoinChallenge.lean` pays, at the exchange of the
two challenge bits, the probability that a fresh uniform coin encrypts the
challenge message to the challenge ciphertext. Under the input distribution of
the KEM game the coin at the challenge point of the `G`-table is itself uniform
and independent of the fresh coin, so that probability is the expectation over
key generation and a uniform message of the collision probability of two
independent uniform coins, `collWeight`. Spreadness (`Scheme.IsSpread`) bounds
the collision probability at every generated key, message and ciphertext, so
`collWeight ≤ ε` follows from `ε`-spreadness; the converse fails, and the
averaged quantity is the one the bound uses.

## Main definitions

* `collProb P pk m` — the probability that two independent uniform coins give
  the same encryption of `m` under `pk`
* `collWeight P` — the expectation of `collProb` over key generation and a
  uniform message

## Main results

* `collWeight_le_of_isSpread` — an `ε`-spread scheme has `collWeight ≤ ε`
* `sum_tableMass_eval_fun`, `sum_unif_eval_fun` — a function of one table entry
  averaged over a `tableMass` weight whose point is fully good, or over the
  uniform table, is its uniform average over the entry
* `sum_kemRestWeight_mul_msg` — a `kemRestWeight`-weighted sum of a function of
  the key pair and the message is its `keygen`-and-uniform-message expectation
* `coinSpreadWeight_eq_collWeight` — the weight of the inputs and fresh coins at
  which the challenge message encrypts to the challenge ciphertext is
  `collWeight`
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open CatCrypt.Quantum
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The collision weight -/

section Def

variable {PK SK M C R : Type} [Fintype M] [Nonempty M] [Fintype R] [Nonempty R] [DecidableEq C]
  (P : Scheme PK SK M C R)

/-- The probability that two independent uniform coins give the same encryption
of `m` under `pk`. -/
def collProb (pk : PK) (m : M) : ℝ≥0∞ :=
  ∑ r : R, (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ r' : R, (Fintype.card R : ℝ≥0∞)⁻¹ *
    (if P.enc pk m r' = P.enc pk m r then 1 else 0)

/-- The coin-collision weight of the scheme: the expectation over key generation
and a uniform message of the probability that two independent uniform coins give
the same ciphertext.

References: Hofheinz, Hövelmanns, Kiltz, "A modular analysis of the
Fujisaki-Okamoto transformation", TCC 2017, ePrint 2017/604, and Targhi, Unruh,
"Post-quantum security of the Fujisaki-Okamoto and OAEP transforms", TCC 2016,
ePrint 2015/1210 (γ-spreadness, the worst-case notion over keys and messages
that this key-averaged quantity relaxes). -/
def collWeight : ℝ≥0∞ :=
  ∑' ks : PK × SK, P.keygen ks * ∑ m : M, (Fintype.card M : ℝ≥0∞)⁻¹ * collProb P ks.1 m

omit [Fintype M] [Nonempty M] in
/-- At a generated key pair of an `ε`-spread scheme, the collision probability of
every message is at most `ε`. -/
theorem collProb_le_of_isSpread (ε : ℝ≥0∞) (hε : P.IsSpread ε) {ks : PK × SK}
    (hks : ks ∈ P.keygen.support) (m : M) : collProb P ks.1 m ≤ ε := by
  unfold collProb
  calc _ ≤ ∑ r : R, (Fintype.card R : ℝ≥0∞)⁻¹ * ε := by
        refine Finset.sum_le_sum fun r _ => mul_le_mul_right ?_ _
        refine le_trans (le_of_eq ?_) (hε ks hks m (P.enc ks.1 m r))
        rw [PMF.toOuterMeasure_apply, tsum_fintype]
        refine Finset.sum_congr rfl fun r' _ => ?_
        simp [Set.indicator_apply, PMF.uniformOfFintype_apply]
    _ = ε := by rw [← Finset.sum_mul, sum_inv_card R, one_mul]

/-- An `ε`-spread scheme has coin-collision weight at most `ε`. -/
theorem collWeight_le_of_isSpread (ε : ℝ≥0∞) (hε : P.IsSpread ε) : collWeight P ≤ ε := by
  unfold collWeight
  calc _ ≤ ∑' ks : PK × SK, P.keygen ks * ε := by
        refine ENNReal.tsum_le_tsum fun ks => ?_
        by_cases h0 : P.keygen ks = 0
        · simp [h0]
        refine mul_le_mul_right ?_ _
        calc _ ≤ ∑ m : M, (Fintype.card M : ℝ≥0∞)⁻¹ * ε :=
              Finset.sum_le_sum fun m _ => mul_le_mul_right
                (collProb_le_of_isSpread P ε hε ((PMF.mem_support_iff _ _).mpr h0) m) _
          _ = ε := by rw [← Finset.sum_mul, sum_inv_card M, one_mul]
    _ = ε := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Def

/-! ## Averages of a function of one table entry -/

section Table

variable {m n : ℕ}

/-- Under a `tableMass` weight whose point `t` is fully good, a function of the
entry at `t` averages to its uniform average. -/
theorem sum_tableMass_eval_fun (bad : Fin m → Fin n → Bool) (hgood : ∀ x, ∃ y, bad x y = false)
    (t : Fin m) (ht : ∀ v, bad t v = false) (f : Fin n → ℝ≥0∞) :
    ∑ G : Fin m → Fin n, tableMass bad G * f (G t) = ∑ v : Fin n, (n : ℝ≥0∞)⁻¹ * f v := by
  have hf : ∀ G : Fin m → Fin n, f (G t) = ∑ v : Fin n, (if G t = v then 1 else 0) * f v := by
    intro G
    simp [ite_mul, Finset.sum_ite_eq]
  have hg : ∀ v, goodMass bad t v = (n : ℝ≥0∞)⁻¹ := by
    intro v
    have hu : goodVals bad t = Finset.univ := by
      ext y
      simp [goodVals, ht]
    simp [goodMass, ht, hu]
  simp_rw [hf, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, sum_tableMass_eval hgood t v, hg]

/-- Under the uniform table, a function of the entry at `t` averages to its
uniform average. -/
theorem sum_unif_eval_fun [NeZero n] (t : Fin m) (f : Fin n → ℝ≥0∞) :
    ∑ G : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * f (G t) = ∑ v : Fin n, (n : ℝ≥0∞)⁻¹ * f v := by
  have hmass : ∀ G : Fin m → Fin n, tableMass (fun _ _ => false) G = ((n : ℝ≥0∞) ^ m)⁻¹ := by
    intro G
    simp [tableMass, goodMass, goodVals, Finset.prod_const, ENNReal.inv_pow]
  rw [← sum_tableMass_eval_fun (fun _ _ => false) (fun _ => ⟨0, rfl⟩) t (fun _ => rfl) f]
  simp_rw [hmass]

end Table

/-! ## The collision weight as the coin-hop weight -/

section KEM

variable {m₁ m₂ n : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Fintype K] [Nonempty K] [Fintype R]
  [Nonempty R] [DecidableEq C]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁)
  (eKR : (K × R) ≃ Fin n)

omit [Nonempty M] [Fintype R] [Nonempty R] [DecidableEq C] in
/-- A `kemRestWeight`-weighted sum of a function of the key pair and the
challenge message is its expectation over key generation and a uniform message. -/
theorem sum_kemRestWeight_mul_msg [NeZero n] (f : PK × SK → M → ℝ≥0∞) :
    ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r * f r.1 r.2.2.1 =
      ∑ ks : PK × SK, P.keygen ks * ∑ m : M, (Fintype.card M : ℝ≥0∞)⁻¹ * f ks m := by
  have hc : ∀ t : ℕ, t ≠ 0 → (t : ℝ≥0∞) * (t : ℝ≥0∞)⁻¹ = 1 := fun t ht =>
    ENNReal.mul_inv_cancel (by exact_mod_cast ht) (ENNReal.natCast_ne_top t)
  have hp : (n : ℝ≥0∞) ^ m₂ * ((n : ℝ≥0∞) ^ m₂)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (pow_ne_zero _ (by exact_mod_cast NeZero.ne n))
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
  have hZ := hc _ (Fintype.card_ne_zero (α := Z))
  have hK := hc _ (Fintype.card_ne_zero (α := K))
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ks _ => ?_
  simp only [kemRestWeight, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul,
    Nat.cast_pow]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  calc _ = ((Fintype.card Z : ℝ≥0∞) * (Fintype.card Z : ℝ≥0∞)⁻¹) *
        ((Fintype.card K : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹) *
        ((n : ℝ≥0∞) ^ m₂ * ((n : ℝ≥0∞) ^ m₂)⁻¹) *
        (P.keygen ks * ((Fintype.card M : ℝ≥0∞)⁻¹ * f ks m)) := by ring
    _ = _ := by rw [hZ, hK, hp]; ring

omit [Fintype PK] [Fintype SK] [Fintype M] [Nonempty M] in
/-- `collProb` as a double uniform average over `Fin n` of the coins of
`eKR.symm`. -/
theorem collProb_eq_fin (pk : PK) (m : M) :
    collProb P pk m = ∑ v : Fin n, (n : ℝ≥0∞)⁻¹ * ∑ u : Fin n, (n : ℝ≥0∞)⁻¹ *
      (if P.enc pk m (eKR.symm u).2 = P.enc pk m (eKR.symm v).2 then 1 else 0) := by
  unfold collProb
  rw [sum_coin_avg eKR]
  refine Finset.sum_congr rfl fun v _ => congrArg _ ?_
  exact sum_coin_avg eKR fun r' => if P.enc pk m r' = P.enc pk m (eKR.symm v).2 then 1 else 0

omit [Nonempty M] in
/-- The weight of the pairs (input, fresh value) at which the challenge message
encrypted under the coin of the fresh value is the challenge ciphertext is the
coin-collision weight of the scheme. -/
theorem coinSpreadWeight_eq_collWeight [NeZero n] :
    ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ u : Fin n, kemSample P i * (n : ℝ≥0∞)⁻¹ *
        (if P.enc i.1.1 i.2.2.1 (eKR.symm u).2 = kemChal P hpk eG eKR i then 1 else 0) =
      collWeight P := by
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [sum_kemSample_kemJoin, collWeight, tsum_fintype,
    ← sum_kemRestWeight_mul_msg (Z := Z) (K := K) (m₂ := m₂) (n := n) P
      (fun ks m => collProb P ks.1 m)]
  refine Finset.sum_congr rfl fun r _ => congrArg _ ?_
  rw [collProb_eq_fin P eKR,
    ← sum_unif_eval_fun (eG (r.2.2.1, hpk r.1.1)) (fun v => ∑ u : Fin n, (n : ℝ≥0∞)⁻¹ *
      (if P.enc r.1.1 r.2.2.1 (eKR.symm u).2 = P.enc r.1.1 r.2.2.1 (eKR.symm v).2 then 1
        else 0))]
  simp only [Finset.mul_sum, kemChal, kemG, kemJoin]
  rfl

end KEM

end CatCrypt.Quantum.QROM

end

end
