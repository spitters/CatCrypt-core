/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.KEMOwcpaReduction
public import CatCryptCore.Quantum.QROM.KEMGuessReduction
public import CatCryptCore.Crypto.PKE.FOTransformT

/-!
# The coin-only challenge hop

In the game `prWinKEMHq` of `Quantum/QROM/KEMOwcpaReduction.lean` the adversary
queries the `G`-table whose key part on the public-key slice is `Hq` at the
ciphertext, and its decapsulation answers are `decapsHq Hq c*`. This module
replaces the `G`-entry at the challenge point `eG (m*, hpk pk)` by a fresh value
`u` before the key part is replaced, so the coin there is the coin of `u` and
the key part there is `Hq` at the encryption of `m*` under that coin. The two
oracles agree outside the challenge point, and the averaged one-way-to-hiding
bound of `Quantum/QROM/QAdvGame.lean` applies. The `Find` probability of the hop
is bounded by a one-wayness advantage in `Quantum/QROM/QOwcpaAux.lean`
(`prFindCoin_le_qOwcpaAux`), from the auxiliary results collected here.

## Main definitions

* `coinUpd i u`, `kemOracleCoin i Hq T u` — the input with its `G`-entry at the
  challenge point replaced by `u`, and the oracle of `prWinKEMHq` at it
* `hopCoinGame A b` — the hop as a `QGame` over `(i, u, Hq, T)`
* `prWinKEMHqCoin`, `prFindCoin` — the reprogrammed game and the averaged `Find`
  probability of the hop
* `kfSwap` — the exchange of the fake key with `Hq c*`
* `coinBadWeight` — the weight of the pairs `(i, u)` at which `c*` is the
  ciphertext of a message under the coins of the reprogrammed table
* `ptSwap` — the exchange of the `G`-entry at the challenge point with `u`
* `decodeG` — the message of an oracle point

## Main results

* `hopCoin_o2h` — `|prWinKEMHq − prWinKEMHqCoin| ≤ 4 √(q' · prFindCoin A b)`
* `prWinKEMHqCoin_indep` — the two bits of `prWinKEMHqCoin` differ by at most
  `coinBadWeight`
* `coinBadWeight_le` — `coinBadWeight` is at most the decryption-failure weight
  plus the weight of `P.enc pk m* (coin u) = c*`
* `absDiff_prWinKEMHq_le` — the advantage in `prWinKEMHq` is at most the two
  one-way-to-hiding terms and `coinBadWeight`
* `prFindAvg_le_four_sum_guess` — the bound of `HopChallengeKey.prFindAvgK_le`
  for any `QGame`
* `sum_hopCoinGame_sample_fst`, `sum_coin_avg`, `sum_reorder8` — the finite-sum
  rearrangements of the averaged `Find` probability

## Scope

`δ*`, the weight of the inputs whose challenge message is outside `kemGood`, is
at most the decryption-failure weight `δ_fail` of `qINDCCA_le_hopJDH_Hq`.
`coinBadWeight` is bounded by `δ_fail` plus the probability that two independent
coins give the same encryption of the challenge message, which is at most the
spreadness bound `P.IsSpread` (`FIPS203QROM.coinSpreadWeight_le`). `δ_fail`
quantifies over every message and carries the union bound recorded in
`KEMOwcpaReduction`.

## References

* [Hofheinz, Hövelmanns, Kiltz — A Modular Analysis of the Fujisaki–Okamoto
  Transformation, TCC 2017], §4.2
* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], §3
* [Jiang, Zhang, Chen, Wang, Ma — IND-CCA-Secure Key Encapsulation Mechanism in
  the Quantum Random Oracle Model, Revisited, CRYPTO 2018]
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The reprogrammed oracle -/

section Reprogram

variable {m₁ m₂ n : ℕ} {PK SK M C R K Hash Z : Type} [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n)

omit [DecidableEq Hash] in
/-- The input with the `G`-table entry at the challenge point replaced by `u`. -/
def coinUpd (i : KEMInput PK SK Z M K m₁ m₂ n) (u : Fin n) : KEMInput PK SK Z M K m₁ m₂ n :=
  (i.1, i.2.1, i.2.2.1, i.2.2.2.1, Function.update i.2.2.2.2.1 (kemPt hpk eG i) u, i.2.2.2.2.2)

omit [DecidableEq Hash] in
/-- `keyHop` is pointwise: off the updated point it does not see the update. -/
theorem keyHop_update_of_ne {X V : Type} [DecidableEq X] (S : X → Prop) [DecidablePred S]
    (e : X → R → C) (ε : V ≃ K × R) (Hq : C → K) (g : X → V) (p : X) (v : V) {y : X}
    (hy : y ≠ p) : keyHop S e ε Hq (Function.update g p v) y = keyHop S e ε Hq g y := by
  simp only [keyHop, coinCt, Function.update_of_ne hy]

variable [DecidableEq Z]

/-- The oracle of `prWinKEMHq` with the `G`-entry at the challenge point
replaced by `u` before the key part on the public-key slice is replaced by `Hq`
at the ciphertext: the coin at the challenge point is the coin of `u`, and the
key part there is `Hq` at the encryption of the challenge message under that
coin. -/
def kemOracleCoin (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq : C → K) (T : C → Fin n) (u : Fin n) :
    Fin (m₁ + m₂) → Fin n :=
  kemOracle' eJ (inputH P hpk eG eKR (coinUpd hpk eG i u) Hq) T

/-- The oracle of `prWinKEMHq` and `kemOracleCoin` agree outside the challenge
point. -/
theorem kemOracleCoin_agree (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq : C → K) (T : C → Fin n)
    (u : Fin n) : ∀ x, x ∉ mergeSet {kemPt hpk eG i} (∅ : Finset (Fin m₂)) →
      kemOracle' eJ (inputH P hpk eG eKR i Hq) T x = kemOracleCoin P hpk eG eJ eKR i Hq T u x :=
  mergeOracle_agree
    (fun x hx => (keyHop_update_of_ne _ _ _ Hq _ _ u (by simpa using hx)).symm) (fun _ _ => rfl)

end Reprogram

/-! ## The one-way-to-hiding step -/

section Game

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c]

omit [Fintype PK] [Fintype SK] [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z]
  [Nonempty Z] [DecidableEq Z] [Fintype K] [Nonempty R] [Fintype C] [DecidableEq C]
  [DecidableEq Hash] [NeZero n] [NeZero c] in
/-- A uniform weight sums to one. -/
theorem sum_inv_card (α : Type) [Fintype α] [Nonempty α] :
    ∑ _x : α, (Fintype.card α : ℝ≥0∞)⁻¹ = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)

omit [Fintype PK] [Fintype SK] [DecidableEq M] [Nonempty M] [Nonempty Z] [DecidableEq Z]
  [Nonempty R] in
/-- The weights of the fresh value, `Hq` and `T` sum to one. -/
theorem sum_rest_weight (i : KEMInput PK SK Z M K m₁ m₂ n) :
    ∑ _r : Fin n × (C → K) × (C → Fin n),
        kemSample P i * (n : ℝ≥0∞)⁻¹ * (Fintype.card (C → K) : ℝ≥0∞)⁻¹ * tabWeight n C =
      kemSample P i := by
  have hU : (n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ = 1 := by simpa using sum_inv_card (Fin n)
  have hK : (Fintype.card (C → K) : ℝ≥0∞) * (Fintype.card (C → K) : ℝ≥0∞)⁻¹ = 1 := by
    simpa using sum_inv_card (C → K)
  have hT : (Fintype.card (C → Fin n) : ℝ≥0∞) * tabWeight n C = 1 := by
    simpa using sum_tabWeight n C
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_mul]
  calc _ = ((n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) *
          ((Fintype.card (C → K) : ℝ≥0∞) * (Fintype.card (C → K) : ℝ≥0∞)⁻¹) *
          ((Fintype.card (C → Fin n) : ℝ≥0∞) * tabWeight n C) * kemSample P i := by ring
    _ = kemSample P i := by rw [hU, hK, hT]; simp

/-- The hop as a `QGame` over the input, the fresh value `u`, the table `Hq`
and the prefix table `T`: the oracle is that of `prWinKEMHq`, the reprogrammed
oracle is `kemOracleCoin`, and the punctured set is the challenge point. -/
def hopCoinGame (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    QGame (m₁ + m₂) n (ancW c k (2 * w)) (flatQ q k q)
      (KEMInput PK SK Z M K m₁ m₂ n × Fin n × (C → K) × (C → Fin n)) where
  sample p := kemSample P p.1 * (n : ℝ≥0∞)⁻¹ * (Fintype.card (C → K) : ℝ≥0∞)⁻¹ * tabWeight n C
  sample_sum := by
    rw [Fintype.sum_prod_type]
    exact (Finset.sum_congr rfl fun i _ => sum_rest_weight P i).trans
      (kemSample_sum (Z := Z) (K := K) P eKR)
  adv p := toQAdv (A.run p.1.1.1 (kemChal P hpk eG eKR p.1)
      (if b then p.2.2.1 (kemChal P hpk eG eKR p.1) else p.1.2.2.2.1))
    (decapsHq eC eKa p.2.2.1 (kemChal P hpk eG eKR p.1))
  oracle p := kemOracle' eJ (inputH P hpk eG eKR p.1 p.2.2.1) p.2.2.2
  oracle' p := kemOracleCoin P hpk eG eJ eKR p.1 p.2.2.1 p.2.2.2 p.2.1
  S p := mergeSet {kemPt hpk eG p.1} ∅
  agree p := kemOracleCoin_agree P hpk eG eJ eKR p.1 p.2.2.1 p.2.2.2 p.2.1
  pure p := by
    obtain ⟨ψ, hψ⟩ := A.pure p.1.1.1 (kemChal P hpk eG eKR p.1)
      (if b then p.2.2.1 (kemChal P hpk eG eKR p.1) else p.1.2.2.2.1)
    exact pure_toQAdv _ _ hψ

/-- The game `prWinKEMHq` with the coin at the challenge point reprogrammed: the
input, a fresh value `u`, the table `Hq` and the prefix table `T` are drawn; the
adversary receives `pk`, `c*` and `Hq c*` or the fake key, queries
`kemOracleCoin`, and its classical rounds are answered by `decapsHq Hq c*`. -/
def prWinKEMHqCoin (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) : ℝ≥0∞ :=
  ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ u : Fin n, ∑ Hq : C → K, ∑ T : C → Fin n,
    kemSample P i * (n : ℝ≥0∞)⁻¹ * (Fintype.card (C → K) : ℝ≥0∞)⁻¹ * tabWeight n C *
      prOutMR (A.run i.1.1 (kemChal P hpk eG eKR i)
          (if b then Hq (kemChal P hpk eG eKR i) else i.2.2.2.1))
        (kemOracleCoin P hpk eG eJ eKR i Hq T u) (decapsHq eC eKa Hq (kemChal P hpk eG eKR i))

omit [DecidableEq M] in
/-- `prWinKEMHq` is `prWin` of the hop game. -/
theorem prWinKEMHq_eq_prWin (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    prWinKEMHq P hpk eG eJ eKR eC eKa A b =
      prWin (hopCoinGame P hpk eG eJ eKR eC eKa A b) := by
  have hU : (n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ = 1 := by simpa using sum_inv_card (Fin n)
  unfold prWinKEMHq prWin
  conv_rhs => rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fintype.sum_prod_type, hopCoinGame, ← prOutMR_eq]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Hq _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  calc _ = ((n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) * (kemSample P i * (Fintype.card (C → K) : ℝ≥0∞)⁻¹ *
        (tabWeight n C * prOutMR (A.run i.1.1 (kemChal P hpk eG eKR i)
          (if b then Hq (kemChal P hpk eG eKR i) else i.2.2.2.1))
        (kemOracle' eJ (inputH P hpk eG eKR i Hq) T)
        (decapsHq eC eKa Hq (kemChal P hpk eG eKR i)))) := by rw [hU, one_mul]
    _ = _ := by ring

omit [DecidableEq M] in
/-- `prWinKEMHqCoin` is `prWin'` of the hop game. -/
theorem prWinKEMHqCoin_eq_prWin' (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    prWinKEMHqCoin P hpk eG eJ eKR eC eKa A b =
      prWin' (hopCoinGame P hpk eG eJ eKR eC eKa A b) := by
  simp only [prWinKEMHqCoin, prWin', hopCoinGame, Fintype.sum_prod_type, prOutMR_eq]

/-- The averaged `Find` probability of the coin hop. -/
def prFindCoin (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) : ℝ≥0∞ :=
  prFindAvg (hopCoinGame P hpk eG eJ eKR eC eKa A b)

omit [DecidableEq M] in
/-- The one-way-to-hiding step of the coin hop:
`|prWinKEMHq − prWinKEMHqCoin| ≤ 4 √(q' · prFindCoin A b)` with `q' = flatQ q k q`.

References: Ambainis, Hamburg, Unruh, "Quantum security proofs using
semi-classical oracles", CRYPTO 2019, ePrint 2018/904, Theorem 1. The step
corresponds to the derandomisation of the encryption coin in the T transform of
Hofheinz, Hövelmanns, Kiltz, "A modular analysis of the Fujisaki-Okamoto
transformation", TCC 2017, ePrint 2017/604, in Targhi, Unruh, "Post-quantum
security of the Fujisaki-Okamoto and OAEP transforms", TCC 2016, ePrint
2015/1210, and in Hövelmanns, Kiltz, Schäge, Unruh, "Generic authenticated key
exchange in the quantum random oracle model", PKC 2020, ePrint 2018/928; the
worst-case γ-spreadness of those papers is replaced by the key-averaged
coin-collision weight `collWeight` of `CollisionWeight.lean`. -/
theorem hopCoin_o2h (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    absDiff (prWinKEMHq P hpk eG eJ eKR eC eKa A b) (prWinKEMHqCoin P hpk eG eJ eKR eC eKa A b) ≤
      4 * ((flatQ q k q : ℝ≥0∞) * prFindCoin P hpk eG eJ eKR eC eKa A b) ^ (1 / 2 : ℝ) := by
  rw [prWinKEMHq_eq_prWin, prWinKEMHqCoin_eq_prWin']
  exact o2h_avg _

end Game

/-! ## The challenge bit in the reprogrammed game -/

section Indep

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

/-- The pair (input, `Hq`) with the fake key and the value of `Hq` at the
challenge ciphertext exchanged. -/
def kfSwap (p : KEMInput PK SK Z M K m₁ m₂ n × (C → K)) :
    KEMInput PK SK Z M K m₁ m₂ n × (C → K) :=
  ((p.1.1, p.1.2.1, p.1.2.2.1, p.2 (kemChal P hpk eG eKR p.1), p.1.2.2.2.2),
    Function.update p.2 (kemChal P hpk eG eKR p.1) p.1.2.2.2.1)

omit [Fintype PK] [Fintype SK] [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z]
  [Fintype K] [Nonempty K] [Nonempty R] [Fintype C] [DecidableEq Hash] in
theorem kemChal_kfSwap (p : KEMInput PK SK Z M K m₁ m₂ n × (C → K)) :
    kemChal P hpk eG eKR (kfSwap P hpk eG eKR p).1 = kemChal P hpk eG eKR p.1 := rfl

omit [Fintype PK] [Fintype SK] [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z]
  [Fintype K] [Nonempty K] [Nonempty R] [Fintype C] [DecidableEq Hash] in
theorem kfSwap_involutive : Function.Involutive (kfSwap (Z := Z) (m₂ := m₂) P hpk eG eKR) := by
  rintro ⟨i, Hq⟩
  have h : ∀ x : K, kemChal P hpk eG eKR (i.1, i.2.1, i.2.2.1, x, i.2.2.2.2) =
      kemChal P hpk eG eKR i := fun _ => rfl
  simp only [kfSwap, h, Function.update_self, Function.update_idem, Function.update_eq_self]

omit [Fintype K] [Fintype C] in
/-- The decapsulation of `decapsHq` does not read its table at the excluded
ciphertext. -/
theorem decapsHq_update_self (H : C → K) (cstar : C) (x : K) :
    decapsHq eC eKa (Function.update H cstar x) cstar = decapsHq eC eKa H cstar := by
  funext y
  unfold decapsHq
  split_ifs with h
  · rfl
  · rw [Function.update_of_ne h]

open scoped Classical in
/-- The weight of the pairs (input, fresh value) at which the challenge
ciphertext is the ciphertext of some message under the coins of the
reprogrammed table. -/
def coinBadWeight : ℝ≥0∞ :=
  ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ u : Fin n, kemSample P i * (n : ℝ≥0∞)⁻¹ *
    (if ∃ m, encOf (P.enc i.1.1) (kemTab hpk eG eKR (coinUpd hpk eG i u)) m =
      kemChal P hpk eG eKR i then 1 else 0)

variable [NeZero n] [NeZero c]

omit [Nonempty M] [Nonempty Z] [Nonempty R] [NeZero c] in
open scoped Classical in
/-- In the reprogrammed game the two challenge bits differ by at most
`coinBadWeight`: off that event `Hq` at the challenge ciphertext is read only as
the challenge key, and exchanging it with the fake key maps one bit to the
other. -/
theorem prWinKEMHqCoin_indep (A : KEMQAdv m₁ m₂ n w q k c a PK C K) :
    absDiff (prWinKEMHqCoin P hpk eG eJ eKR eC eKa A true)
        (prWinKEMHqCoin P hpk eG eJ eKR eC eKa A false) ≤
      coinBadWeight (Z := Z) (m₂ := m₂) P hpk eG eKR := by
  set Bad : KEMInput PK SK Z M K m₁ m₂ n → Fin n → Prop := fun i u =>
    ∃ m, encOf (P.enc i.1.1) (kemTab hpk eG eKR (coinUpd hpk eG i u)) m =
      kemChal P hpk eG eKR i with hBad
  set F : Bool → KEMInput PK SK Z M K m₁ m₂ n → Fin n → (C → K) → (C → Fin n) → ℝ≥0∞ :=
    fun b i u Hq T => kemSample P i * (n : ℝ≥0∞)⁻¹ * (Fintype.card (C → K) : ℝ≥0∞)⁻¹ *
      tabWeight n C * prOutMR (A.run i.1.1 (kemChal P hpk eG eKR i)
          (if b then Hq (kemChal P hpk eG eKR i) else i.2.2.2.1))
        (kemOracleCoin P hpk eG eJ eKR i Hq T u) (decapsHq eC eKa Hq (kemChal P hpk eG eKR i))
    with hF
  have hW : ∀ b, prWinKEMHqCoin P hpk eG eJ eKR eC eKa A b =
      (∑ i, ∑ u, ∑ Hq, ∑ T, if Bad i u then 0 else F b i u Hq T) +
        ∑ i, ∑ u, ∑ Hq, ∑ T, if Bad i u then F b i u Hq T else 0 := by
    intro b
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ =>
      Finset.sum_congr rfl fun Hq _ => Finset.sum_congr rfl fun T _ => ?_
    by_cases h : Bad i u
    · rw [if_pos h, if_pos h, zero_add]
    · rw [if_neg h, if_neg h, add_zero]
  have hX : (∑ i, ∑ u, ∑ Hq, ∑ T, if Bad i u then 0 else F true i u Hq T) =
      ∑ i, ∑ u, ∑ Hq, ∑ T, if Bad i u then 0 else F false i u Hq T := by
    have hc : ∀ f : KEMInput PK SK Z M K m₁ m₂ n → Fin n → (C → K) → ℝ≥0∞,
        ∑ i, ∑ u, ∑ Hq, f i u Hq = ∑ i, ∑ Hq, ∑ u, f i u Hq :=
      fun f => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [hc (fun i u Hq => ∑ T, if Bad i u then 0 else F true i u Hq T),
      hc (fun i u Hq => ∑ T, if Bad i u then 0 else F false i u Hq T)]
    rw [← Fintype.sum_prod_type' (f := fun i Hq => ∑ u, ∑ T,
        if Bad i u then 0 else F true i u Hq T),
      ← Fintype.sum_prod_type' (f := fun i Hq => ∑ u, ∑ T,
        if Bad i u then 0 else F false i u Hq T)]
    refine Fintype.sum_equiv ((kfSwap_involutive P hpk eG eKR).toPerm _) _ _ fun p => ?_
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun T _ => ?_
    change _ = if Bad (kfSwap P hpk eG eKR p).1 u then 0 else
      F false (kfSwap P hpk eG eKR p).1 u (kfSwap P hpk eG eKR p).2 T
    have hb : Bad (kfSwap P hpk eG eKR p).1 u ↔ Bad p.1 u := Iff.rfl
    by_cases h : Bad p.1 u
    · rw [if_pos h, if_pos (hb.2 h)]
    · rw [if_neg h, if_neg (fun h' => h (hb.1 h'))]
      have hH : ∀ y, (∃ m, encOf (P.enc p.1.1.1)
          (kemTab hpk eG eKR (coinUpd hpk eG (kfSwap P hpk eG eKR p).1 u)) m = y) →
          (kfSwap P hpk eG eKR p).2 y = p.2 y := by
        rintro y ⟨m, hm⟩
        refine Function.update_of_ne (fun hy => h ⟨m, ?_⟩) _ _
        rw [← hy]; exact hm
      have ho : kemOracleCoin P hpk eG eJ eKR (kfSwap P hpk eG eKR p).1
          (kfSwap P hpk eG eKR p).2 T u = kemOracleCoin P hpk eG eJ eKR p.1 p.2 T u := by
        unfold kemOracleCoin
        rw [inputH_congr P hpk eG eKR _ _ _ hH]
        rfl
      simp only [hF, ho]
      have hc2 : kemChal P hpk eG eKR
          (p.1.1, p.1.2.1, p.1.2.2.1, p.2 (kemChal P hpk eG eKR p.1), p.1.2.2.2.2) =
          kemChal P hpk eG eKR p.1 := rfl
      simp only [kfSwap, hc2, decapsHq_update_self, Bool.false_eq_true, if_false, if_true]
      rfl
  have hY : ∀ b, (∑ i, ∑ u, ∑ Hq, ∑ T, if Bad i u then F b i u Hq T else 0) ≤
      coinBadWeight (Z := Z) (m₂ := m₂) P hpk eG eKR := by
    intro b
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun u _ => ?_
    calc (∑ Hq, ∑ T, if Bad i u then F b i u Hq T else 0)
        ≤ ∑ _Hq : C → K, ∑ _T : C → Fin n, (if Bad i u then kemSample P i * (n : ℝ≥0∞)⁻¹ *
            (Fintype.card (C → K) : ℝ≥0∞)⁻¹ * tabWeight n C else 0) := by
          refine Finset.sum_le_sum fun Hq _ => Finset.sum_le_sum fun T _ => ?_
          split_ifs
          · exact mul_le_of_le_one_right' (prOutMR_le_one _ _ _)
          · exact le_rfl
      _ = kemSample P i * (n : ℝ≥0∞)⁻¹ * (if Bad i u then 1 else 0) := by
          split_ifs
          · simp only [← Finset.mul_sum, sum_tabWeight, mul_one, sum_inv_card]
          · simp
  rw [hW, hW, hX]
  refine absDiff_le_iff.mpr ⟨?_, ?_⟩
  · rw [add_assoc]; exact add_le_add le_rfl ((hY true).trans le_add_self)
  · rw [add_assoc]; exact add_le_add le_rfl ((hY false).trans le_add_self)

open scoped Classical in
/-- The advantage in `prWinKEMHq` is at most the two one-way-to-hiding terms of
the coin hop and `coinBadWeight`. -/
theorem absDiff_prWinKEMHq_le (A : KEMQAdv m₁ m₂ n w q k c a PK C K) :
    absDiff (prWinKEMHq P hpk eG eJ eKR eC eKa A true)
        (prWinKEMHq P hpk eG eJ eKR eC eKa A false) ≤
      4 * ((flatQ q k q : ℝ≥0∞) * prFindCoin P hpk eG eJ eKR eC eKa A true) ^ (1 / 2 : ℝ) +
        coinBadWeight (Z := Z) (m₂ := m₂) P hpk eG eKR +
        4 * ((flatQ q k q : ℝ≥0∞) * prFindCoin P hpk eG eJ eKR eC eKa A false) ^ (1 / 2 : ℝ) := by
  calc absDiff (prWinKEMHq P hpk eG eJ eKR eC eKa A true)
        (prWinKEMHq P hpk eG eJ eKR eC eKa A false)
      ≤ absDiff (prWinKEMHq P hpk eG eJ eKR eC eKa A true)
            (prWinKEMHqCoin P hpk eG eJ eKR eC eKa A true) +
          absDiff (prWinKEMHqCoin P hpk eG eJ eKR eC eKa A true)
            (prWinKEMHq P hpk eG eJ eKR eC eKa A false) := absDiff_triangle _ _ _
    _ ≤ absDiff (prWinKEMHq P hpk eG eJ eKR eC eKa A true)
            (prWinKEMHqCoin P hpk eG eJ eKR eC eKa A true) +
          (absDiff (prWinKEMHqCoin P hpk eG eJ eKR eC eKa A true)
            (prWinKEMHqCoin P hpk eG eJ eKR eC eKa A false) +
          absDiff (prWinKEMHqCoin P hpk eG eJ eKR eC eKa A false)
            (prWinKEMHq P hpk eG eJ eKR eC eKa A false)) := by
        gcongr; exact absDiff_triangle _ _ _
    _ ≤ _ := by
        rw [← add_assoc, absDiff_comm (prWinKEMHqCoin P hpk eG eJ eKR eC eKa A false)]
        gcongr
        · exact hopCoin_o2h P hpk eG eJ eKR eC eKa A true
        · exact prWinKEMHqCoin_indep P hpk eG eJ eKR eC eKa A
        · exact hopCoin_o2h P hpk eG eJ eKR eC eKa A false

end Indep

/-! ## The `Find` probability as a guessing probability -/

section FindGuess

variable {m n w q : ℕ} {ι : Type} [Fintype ι] [NeZero n]

/-- The averaged `Find` probability of a game is at most four times the averaged
probability that the measured query of the plain run against the reprogrammed
oracle lies in the punctured set, summed over the queries.

References: Ambainis, Hamburg, Unruh, "Quantum security proofs using
semi-classical oracles", CRYPTO 2019, ePrint 2018/904, Theorem 2 (the search
bound: `Pr[Find]` against the semi-classical oracle is at most four times the
query count times the guessing probability of the punctured set). -/
theorem prFindAvg_le_four_sum_guess (G : QGame m n w q ι) :
    prFindAvg G ≤ 4 * ∑ j : Fin q, ∑ p, G.sample p * guessProb (G.adv p) (G.oracle' p) (G.S p) j :=
  calc prFindAvg G
      ≤ ∑ p, G.sample p * (4 * ∑ j, guessProb (G.adv p) (G.oracle' p) (G.S p) j) := by
        refine Finset.sum_le_sum fun p _ => ?_
        obtain ⟨ψ, hψ⟩ := G.pure p
        rw [prFind_congr _ _ _ _ (G.agree p) hψ]
        gcongr
        exact prFind_le_four_sum_guess _ _ _ hψ
    _ = 4 * ∑ j, ∑ p, G.sample p * guessProb (G.adv p) (G.oracle' p) (G.S p) j := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ => by ring

end FindGuess

/-! ## The exchange of the challenge entry -/

section View

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c]

omit [Fintype PK] [Fintype SK] [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z]
  [DecidableEq Z] [Fintype K] [Nonempty K] [Nonempty R] [Fintype C] [DecidableEq C] [NeZero n]
  [NeZero c] in
/-- The exchange of the `G`-entry at the challenge point with the fresh value:
after it the challenge ciphertext is encrypted under the coin of the fresh
value, and the table read by the reprogrammed oracle is the input's own
`G`-table. -/
def ptSwap (p : KEMInput PK SK Z M K m₁ m₂ n × Fin n × (C → K) × (C → Fin n)) :
    KEMInput PK SK Z M K m₁ m₂ n × Fin n × (C → K) × (C → Fin n) :=
  ((p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1,
      Function.update p.1.2.2.2.2.1 (kemPt hpk eG p.1) p.2.1, p.1.2.2.2.2.2),
    p.1.2.2.2.2.1 (kemPt hpk eG p.1), p.2.2)

omit [Fintype PK] [Fintype SK] [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z]
  [DecidableEq Z] [Fintype K] [Nonempty K] [Nonempty R] [Fintype C] [DecidableEq C] [NeZero n]
  [NeZero c] [DecidableEq Hash] in
theorem ptSwap_involutive :
    Function.Involutive (ptSwap (PK := PK) (SK := SK) (Z := Z) (K := K) (C := C) (m₂ := m₂)
      (n := n) hpk eG) := by
  rintro ⟨⟨ks, z, m, kf, G, J⟩, u, Hq, T⟩
  simp only [ptSwap, kemPt, Function.update_self, Function.update_idem, Function.update_eq_self]

end View

/-! ## The message of an oracle point -/

section Reduction

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c] [NeZero (flatQ q k q)]

/-- The message of a point of the merged oracle domain: the message of the
`G`-index on the first summand, a fixed message on the second. -/
def decodeG (x : Fin (m₁ + m₂)) : M :=
  Fin.addCases (fun y => (eG.symm y).1) (fun _ => Classical.arbitrary M) x

omit [Fintype PK] [Fintype SK] [Fintype M] [DecidableEq M] [Fintype Z] [Nonempty Z]
  [DecidableEq Z] [Fintype K] [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C]
  [DecidableEq Hash] [NeZero n] [NeZero c] [NeZero (flatQ q k q)] in
theorem decodeG_kemPtMerged (i : KEMInput PK SK Z M K m₁ m₂ n) :
    decodeG (m₂ := m₂) eG (kemPtMerged hpk eG i) = i.2.2.1 := by
  simp [decodeG, kemPtMerged, kemPt]

end Reduction

/-! ## Finite-sum rearrangements -/

section Sums

/-- Eight nested finite sums with the second and the sixth moved to the front. -/
theorem sum_reorder8 {α β γ δ ε ζ η θ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Fintype ε] [Fintype ζ] [Fintype η] [Fintype θ]
    (f : α → β → γ → δ → ε → ζ → η → θ → ℝ≥0∞) :
    ∑ x₁, ∑ x₂, ∑ x₃, ∑ x₄, ∑ x₅, ∑ x₆, ∑ x₇, ∑ x₈, f x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ =
      ∑ x₂, ∑ x₆, ∑ x₁, ∑ x₃, ∑ x₄, ∑ x₅, ∑ x₇, ∑ x₈, f x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ := by
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun x₂ _ => ?_)
  refine (Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun x₃ _ =>
    Finset.sum_congr rfl fun x₄ _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun x₃ _ =>
    Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun x₁ _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

variable {n : ℕ} {K R : Type} [Fintype K] [Fintype R] (eKR : (K × R) ≃ Fin n)

/-- A sum over `Fin n` of a function of the coin of `eKR.symm u` is `card K`
times the sum over the coins. -/
theorem sum_coin (f : R → ℝ≥0∞) :
    ∑ u : Fin n, f (eKR.symm u).2 = (Fintype.card K : ℝ≥0∞) * ∑ r, f r := by
  rw [Fintype.sum_equiv eKR.symm (fun u => f (eKR.symm u).2) (fun x => f x.2) fun _ => rfl,
    Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

include eKR in
/-- `card K / n = 1 / card R`. -/
theorem card_mul_inv_eq [Nonempty K] [Nonempty R] :
    (Fintype.card K : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ = (Fintype.card R : ℝ≥0∞)⁻¹ := by
  have hn : (n : ℝ≥0∞) = (Fintype.card K : ℝ≥0∞) * (Fintype.card R : ℝ≥0∞) := by
    rw [← Nat.cast_mul, ← Fintype.card_prod, Fintype.card_congr eKR, Fintype.card_fin]
  have hK : (Fintype.card K : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hn, ENNReal.mul_inv (Or.inl hK) (Or.inl (ENNReal.natCast_ne_top _)), ← mul_assoc,
    ENNReal.mul_inv_cancel hK (ENNReal.natCast_ne_top _), one_mul]

/-- The uniform average over the coins is the uniform average over `Fin n` of
the coin of `eKR.symm u`. -/
theorem sum_coin_avg [Nonempty K] [Nonempty R] (f : R → ℝ≥0∞) :
    ∑ r, (Fintype.card R : ℝ≥0∞)⁻¹ * f r = ∑ u : Fin n, (n : ℝ≥0∞)⁻¹ * f (eKR.symm u).2 := by
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_coin eKR, ← card_mul_inv_eq eKR, mul_comm _ (n : ℝ≥0∞)⁻¹,
    mul_assoc]

end Sums

/-! ## The input average and the coin-bad weight -/

section Final

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c]

omit [DecidableEq M] [Fintype R] in
/-- A function of the input averaged over the index of `hopCoinGame` is its
average under `kemSample`. -/
theorem sum_hopCoinGame_sample_fst (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (f : KEMInput PK SK Z M K m₁ m₂ n → ℝ≥0∞) :
    ∑ p, (hopCoinGame P hpk eG eJ eKR eC eKa A b).sample p * f p.1 =
      ∑ i, kemSample P i * f i := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ∑ r : Fin n × (C → K) × (C → Fin n), kemSample P i * (n : ℝ≥0∞)⁻¹ *
    (Fintype.card (C → K) : ℝ≥0∞)⁻¹ * tabWeight n C * f i = _
  rw [← Finset.sum_mul, sum_rest_weight]

omit [Nonempty M] [Nonempty Z] [DecidableEq Z] [Nonempty K] [Fintype R] [Nonempty R] [Fintype C]
  [DecidableEq Hash] [NeZero c] in
open scoped Classical in
/-- `coinBadWeight` is at most the decryption-failure weight plus the weight of
the pairs (input, fresh value) at which the challenge message encrypted under
the coin of the fresh value is the challenge ciphertext; the second term is at
most the spreadness bound of the scheme. -/
theorem coinBadWeight_le :
    coinBadWeight (Z := Z) (m₂ := m₂) P hpk eG eKR ≤
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
          (if ∀ m, m ∈ kemGood P hpk eG eKR i then 0 else 1) +
        ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ u : Fin n, kemSample P i * (n : ℝ≥0∞)⁻¹ *
          (if P.enc i.1.1 i.2.2.1 (eKR.symm u).2 = kemChal P hpk eG eKR i then 1 else 0) := by
  have hU : ∑ _u : Fin n, (n : ℝ≥0∞)⁻¹ = 1 := by simpa using sum_inv_card (Fin n)
  have hpt : ∀ (i : KEMInput PK SK Z M K m₁ m₂ n) (u : Fin n) (m : M),
      encOf (P.enc i.1.1) (kemTab hpk eG eKR (coinUpd hpk eG i u)) m =
        if m = i.2.2.1 then P.enc i.1.1 i.2.2.1 (eKR.symm u).2
        else encOf (P.enc i.1.1) (kemTab hpk eG eKR i) m := by
    intro i u m
    split_ifs with hm
    · subst hm
      simp [encOf, encAt, coinsOf, kemTab, kemG, coinUpd, kemPt]
    · have hne : eG (m, hpk i.1.1) ≠ kemPt hpk eG i := fun h =>
        hm (congrArg Prod.fst (eG.injective h))
      simp only [encOf, encAt, coinsOf, kemTab, kemG, coinUpd, Function.update_of_ne hne]
  have hpw : ∀ (i : KEMInput PK SK Z M K m₁ m₂ n) (u : Fin n),
      (if ∃ m, encOf (P.enc i.1.1) (kemTab hpk eG eKR (coinUpd hpk eG i u)) m =
          kemChal P hpk eG eKR i then (1 : ℝ≥0∞) else 0) ≤
        (if ∀ m, m ∈ kemGood P hpk eG eKR i then 0 else 1) +
          (if P.enc i.1.1 i.2.2.1 (eKR.symm u).2 = kemChal P hpk eG eKR i then 1 else 0) := by
    intro i u
    split_ifs with hb hg hs hs <;> try simp
    · obtain ⟨m, hm⟩ := hb
      rw [hpt] at hm
      split_ifs at hm with hmm
      · exact hs hm
      · have hinj : Function.Injective (encOf (P.enc i.1.1) (kemTab hpk eG eKR i)) :=
          encAt_injective_of_good_eq_univ (P.enc i.1.1) (P.dec i.1.2) _
            (Finset.eq_univ_iff_forall.mpr hg)
        exact hmm (hinj hm)
  unfold coinBadWeight
  calc _ ≤ ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ u : Fin n,
        (kemSample P i * (n : ℝ≥0∞)⁻¹ * (if ∀ m, m ∈ kemGood P hpk eG eKR i then 0 else 1) +
          kemSample P i * (n : ℝ≥0∞)⁻¹ *
            (if P.enc i.1.1 i.2.2.1 (eKR.symm u).2 = kemChal P hpk eG eKR i then 1 else 0)) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun u _ => ?_
        rw [← mul_add]
        exact mul_le_mul_right (hpw i u) _
    _ = _ := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hU, mul_one]

end Final

end CatCrypt.Quantum.QROM
