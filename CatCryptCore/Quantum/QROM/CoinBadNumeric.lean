/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.NumericCorrectness
public import CatCryptCore.Quantum.QROM.CollisionWeight

/-!
# The challenge bit of the coin-reprogrammed game through a resampled table

In the coin-reprogrammed game `prWinKEMHqCoin` of
`Quantum/QROM/HopCoinChallenge.lean` the two challenge bits are exchanged by the
involution that swaps the fake key with `Hq c*`. The exchange fails on the event
of `coinBadWeight`: some message `m` has ciphertext `c*` under the coins of the
reprogrammed table. For `m = m*` this is the spreadness event; for `m ≠ m*` it
makes the ciphertext map of the `G`-table non-injective on the public-key slice,
and `coinBadWeight_le` bounds it by the all-message failure weight `δ_fail`.

This module bounds the bit difference through the `G`-table resampled to good
values with the challenge point exempted (`restBad`):

`|P_true − P_false| ≤ |P_true(G) − P_true(G')| + |P_true(G') − P_false(G')|
  + |P_false(G') − P_false(G)|`.

The game reads the `G`-table through the adversary's oracle, a pointwise
function of the table updated at the challenge point, and through the challenge
ciphertext, which reads the exempted challenge point only; the outer terms are
therefore bounded by `absDiff_resample_map_off_point`. On the resampled table
every message other than `m*` decrypts correctly, the ciphertext map fails to be
injective on the slice with weight at most `δ*` (`sum_tableMass_not_sliceInj_le`),
and the middle term is at most `δ* + ε`.

## Main definitions

* `prWinCoinW μ A b`, `coinBadW μ` — the game `prWinKEMHqCoin` and the weight
  `coinBadWeight` with the input drawn with a weight `μ`
* `winCoin A b i` — the winning probability of the coin-reprogrammed game at an
  input
* `resWeight` — the input weight with the `G`-table resampled off the challenge
  point

## Main results

* `prWinCoinW_indep` — for a weight that does not read the fake key, the two
  bits of `prWinCoinW μ` differ by at most `coinBadW μ`
* `absDiff_winCoin_resample_le` — the outer term at a fixed rest is at most
  `8 q' λ^(1/2)`, with `q' = flatQ q k q`
* `sum_resWeight_coll`, `sum_resWeightCoin_coll` — on the resampled table, the
  weight of the inputs and fresh values at which the challenge message
  encrypted under the coin of the fresh value is the challenge ciphertext is
  the coin-collision weight `collWeight P`
* `coinBad_ind_le`, `coinBadW_resWeight_le` — on the resampled table
  `coinBadW ≤ Λ + ε`
* `absDiff_prWinKEMHqCoin_le_of_lam` —
  `|prWinKEMHqCoin true − prWinKEMHqCoin false| ≤ 8 q' Λ^(1/2) + (Λ + ε) + 8 q' Λ^(1/2)`
* `absDiff_prWinKEMHq_le_numeric_of_lam` — the bound of `absDiff_prWinKEMHq_le`
  with `coinBadWeight` replaced by that term
* `qINDCCA_le_find_numeric_of_lam` — the quantum IND-CCA advantage through the
  coin hop, with every correctness term numeric in `Λ` and the `Find`
  probability of the hop bounded by `4 q' (F b + δ*)` for any `F` bounding the
  one-wayness step

## The hypotheses

In `qINDCCA_le_find_numeric_of_lam` no correctness term quantifies over every
message. The terms `8 q' / √|Z|` and the multiples of `Λ^(1/2)` and `Λ` are
numeric once `Λ` and the query counts are given; `Λ` is the expectation over key
generation of a per-key bound `λ` on the worst-message decryption-failure
fraction, carried as the hypothesis `hlam`. The parameter `ε` bounds the
coin-collision weight `collWeight P` of `Quantum/QROM/CollisionWeight.lean`,
carried as the hypothesis `hcoll` in the forms with suffix `_coll`; the forms
without the suffix take `ε`-spreadness `hε`, which implies `hcoll`
(`collWeight_le_of_isSpread`). No form carries a coin hypothesis: the `G`-table
is resampled only at the key pairs that are `CoinGood`, and at the others `hlam`
gives `λ ≥ 1`. `qINDCCA_le_find_numeric_coll` restates
`qINDCCA_le_find_numeric_of_lam_coll` with an additional coin hypothesis that
its proof does not use. `δ*`, the weight of the inputs whose
challenge message is outside `kemGood`, stays inside the two one-wayness terms;
it is a failure probability of the challenge message alone, and
`deltaStar_le_Lambda` (`Quantum/QROM/DeltaStarLeLambda.lean`) bounds it by `Λ`.
The structural hypotheses `hw`, `hrounds`, `hseg`, `hinit` on the adversary's
decapsulation rounds are those of `absDiff_winReal_resample_le`.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The coin-reprogrammed game under an input weight -/

section Weighted

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [Fintype Z] [DecidableEq Z] [Fintype K] [Nonempty K] [Fintype C] [DecidableEq C]
  [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c]

/-- The game `prWinKEMHqCoin` with the input drawn with the weight `μ`. -/
def prWinCoinW (μ : KEMInput PK SK Z M K m₁ m₂ n → ℝ≥0∞) (A : KEMQAdv m₁ m₂ n w q k c a PK C K)
    (b : Bool) : ℝ≥0∞ :=
  ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ u : Fin n, ∑ Hq : C → K, ∑ T : C → Fin n,
    μ i * (n : ℝ≥0∞)⁻¹ * (Fintype.card (C → K) : ℝ≥0∞)⁻¹ * tabWeight n C *
      prOutMR (A.run i.1.1 (kemChal P hpk eG eKR i)
          (if b then Hq (kemChal P hpk eG eKR i) else i.2.2.2.1))
        (kemOracleCoin P hpk eG eJ eKR i Hq T u) (decapsHq eC eKa Hq (kemChal P hpk eG eKR i))

open scoped Classical in
/-- `coinBadWeight` with the input drawn with the weight `μ`. -/
def coinBadW (μ : KEMInput PK SK Z M K m₁ m₂ n → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ u : Fin n, μ i * (n : ℝ≥0∞)⁻¹ *
    (if ∃ m, encOf (P.enc i.1.1) (kemTab hpk eG eKR (coinUpd hpk eG i u)) m =
      kemChal P hpk eG eKR i then 1 else 0)

omit [NeZero c] in
open scoped Classical in
/-- `prWinKEMHqCoin_indep` for an input weight that does not read the fake key:
the two challenge bits of `prWinCoinW μ` differ by at most `coinBadW μ`. -/
theorem prWinCoinW_indep (μ : KEMInput PK SK Z M K m₁ m₂ n → ℝ≥0∞)
    (hμ : ∀ (i : KEMInput PK SK Z M K m₁ m₂ n) (x : K),
      μ (i.1, i.2.1, i.2.2.1, x, i.2.2.2.2) = μ i)
    (A : KEMQAdv m₁ m₂ n w q k c a PK C K) :
    absDiff (prWinCoinW P hpk eG eJ eKR eC eKa μ A true)
        (prWinCoinW P hpk eG eJ eKR eC eKa μ A false) ≤
      coinBadW (Z := Z) (m₂ := m₂) P hpk eG eKR μ := by
  set Bad : KEMInput PK SK Z M K m₁ m₂ n → Fin n → Prop := fun i u =>
    ∃ m, encOf (P.enc i.1.1) (kemTab hpk eG eKR (coinUpd hpk eG i u)) m =
      kemChal P hpk eG eKR i with hBad
  set F : Bool → KEMInput PK SK Z M K m₁ m₂ n → Fin n → (C → K) → (C → Fin n) → ℝ≥0∞ :=
    fun b i u Hq T => μ i * (n : ℝ≥0∞)⁻¹ * (Fintype.card (C → K) : ℝ≥0∞)⁻¹ *
      tabWeight n C * prOutMR (A.run i.1.1 (kemChal P hpk eG eKR i)
          (if b then Hq (kemChal P hpk eG eKR i) else i.2.2.2.1))
        (kemOracleCoin P hpk eG eJ eKR i Hq T u) (decapsHq eC eKa Hq (kemChal P hpk eG eKR i))
    with hF
  have hW : ∀ b, prWinCoinW P hpk eG eJ eKR eC eKa μ A b =
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
      simp only [kfSwap, hc2, decapsHq_update_self, Bool.false_eq_true, if_false, if_true, hμ]
  have hY : ∀ b, (∑ i, ∑ u, ∑ Hq, ∑ T, if Bad i u then F b i u Hq T else 0) ≤
      coinBadW (Z := Z) (m₂ := m₂) P hpk eG eKR μ := by
    intro b
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun u _ => ?_
    calc (∑ Hq, ∑ T, if Bad i u then F b i u Hq T else 0)
        ≤ ∑ _Hq : C → K, ∑ _T : C → Fin n, (if Bad i u then μ i * (n : ℝ≥0∞)⁻¹ *
            (Fintype.card (C → K) : ℝ≥0∞)⁻¹ * tabWeight n C else 0) := by
          refine Finset.sum_le_sum fun Hq _ => Finset.sum_le_sum fun T _ => ?_
          split_ifs
          · exact mul_le_of_le_one_right' (prOutMR_le_one _ _ _)
          · exact le_rfl
      _ = μ i * (n : ℝ≥0∞)⁻¹ * (if Bad i u then 1 else 0) := by
          split_ifs
          · simp only [← Finset.mul_sum, sum_tabWeight, mul_one, sum_inv_card]
          · simp
  rw [hW, hW, hX]
  refine absDiff_le_iff.mpr ⟨?_, ?_⟩
  · rw [add_assoc]; exact add_le_add le_rfl ((hY true).trans le_add_self)
  · rw [add_assoc]; exact add_le_add le_rfl ((hY false).trans le_add_self)

/-- The winning probability of the coin-reprogrammed game at an input, averaged
over the fresh value `u`, the table `Hq` and the prefix table `T`. -/
def winCoin (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (i : KEMInput PK SK Z M K m₁ m₂ n) : ℝ≥0∞ :=
  ∑ u : Fin n, (n : ℝ≥0∞)⁻¹ * ∑ Hq : C → K, (Fintype.card (C → K) : ℝ≥0∞)⁻¹ *
    ∑ T : C → Fin n, tabWeight n C *
      prOutMR (A.run i.1.1 (kemChal P hpk eG eKR i)
          (if b then Hq (kemChal P hpk eG eKR i) else i.2.2.2.1))
        (kemOracleCoin P hpk eG eJ eKR i Hq T u) (decapsHq eC eKa Hq (kemChal P hpk eG eKR i))

omit [NeZero c] in
/-- `prWinCoinW μ` is the `μ`-average of `winCoin`. -/
theorem prWinCoinW_eq_sum (μ : KEMInput PK SK Z M K m₁ m₂ n → ℝ≥0∞)
    (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    prWinCoinW P hpk eG eJ eKR eC eKa μ A b =
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, μ i * winCoin P hpk eG eJ eKR eC eKa A b i := by
  unfold prWinCoinW winCoin
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ =>
    Finset.sum_congr rfl fun Hq _ => Finset.sum_congr rfl fun T _ => by ring

end Weighted

/-! ## The resampled input weight -/

section Resampled

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c]

/-- The input weight with the `G`-table resampled off the challenge point: the
rest weight times `tableMass (restBad r)` at the `G`-table. -/
def resWeight (i : KEMInput PK SK Z M K m₁ m₂ n) : ℝ≥0∞ :=
  kemRestWeight P (kemJoinEquiv.symm i).1 *
    tableMass (restBad P hpk eG eKR (kemJoinEquiv.symm i).1) (kemJoinEquiv.symm i).2

omit [Nonempty M] [Nonempty Z] [DecidableEq Z] [Nonempty K] [Fintype R] [Nonempty R] [Fintype C]
  [DecidableEq C] [NeZero n] in
/-- A `resWeight`-weighted sum is a `kemRestWeight`-weighted sum of
`tableMass`-weighted sums over the `G`-table. -/
theorem sum_resWeight_mul (X : KEMInput PK SK Z M K m₁ m₂ n → ℝ≥0∞) :
    ∑ i : KEMInput PK SK Z M K m₁ m₂ n, resWeight P hpk eG eKR i * X i =
      ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
        ∑ G : Fin m₁ → Fin n, tableMass (restBad P hpk eG eKR r) G * X (kemJoin r G) := by
  rw [← Fintype.sum_equiv kemJoinEquiv (fun p => resWeight P hpk eG eKR (kemJoin p.1 p.2) *
    X (kemJoin p.1 p.2)) _ fun _ => rfl, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun G _ => mul_assoc _ _ _

omit [Fintype PK] [Fintype SK] [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Fintype R]
  [Nonempty R] in
/-- The outer term at a fixed rest: the coin-reprogrammed game reads the
`G`-table through the oracle `mergeOracle (keyHop Hq (update G t u)) J'`, whose
value at a point of the first summand reads `G` at that point only, and through
the challenge ciphertext, which reads `G` at the exempted challenge point `t`
only. The distance between the uniform and the resampled table is at most
`8 q' λ^(1/2)` with `q' = flatQ q k q`. -/
theorem absDiff_winCoin_resample_le (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (r : KEMRest PK SK Z M K m₂ n)
    (hcoin : ∀ m, ∃ ρ, P.dec r.1.2 (P.enc r.1.1 m ρ) = some m) (lam : ℝ≥0∞)
    (hlam : ∀ x, x ≠ eG (r.2.2.1, hpk r.1.1) →
      ((badVals (kemBad P hpk eG eKR r.1.1 r.1.2) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam) :
    absDiff (∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
          winCoin P hpk eG eJ eKR eC eKa A b (kemJoin r G))
        (∑ G : Fin m₁ → Fin n, tableMass (restBad P hpk eG eKR r) G *
          winCoin P hpk eG eJ eKR eC eKa A b (kemJoin r G)) ≤
      8 * (flatQ q k q : ℝ≥0∞) * lam ^ (1 / 2 : ℝ) := by
  have hgood : ∀ x, ∃ y, restBad P hpk eG eKR r x y = false :=
    offPoint_good _ fun x _ => kemBad_good P hpk eG eKR hcoin x
  have hU : ∑ _u : Fin n, (n : ℝ≥0∞)⁻¹ = 1 := by simpa using sum_inv_card (Fin n)
  have hκ : ∑ _Hq : C → K, (Fintype.card (C → K) : ℝ≥0∞)⁻¹ = 1 := sum_inv_card (C → K)
  rw [← resampleAvg_eq_sum_tableMass hgood, absDiff_comm]
  unfold winCoin
  refine absDiff_resampleAvg_avg_le _ (fun _ => (n : ℝ≥0∞)⁻¹) hU _ _ fun u => ?_
  refine absDiff_resampleAvg_avg_le _ (fun _ => (Fintype.card (C → K) : ℝ≥0∞)⁻¹) hκ _ _
    fun Hq => ?_
  refine absDiff_resampleAvg_avg_le _ (fun _ => tabWeight n C) (sum_tabWeight n C) _ _
    fun T => ?_
  let t : Fin m₁ := eG (r.2.2.1, hpk r.1.1)
  let csu : Fin n → C := fun v => P.enc r.1.1 r.2.2.1 (eKR.symm v).2
  let A' : Fin n → QAdv (m₁ + m₂) n (ancW c k (2 * w)) (flatQ q k q) := fun v =>
    toQAdv (A.run r.1.1 (csu v) (if b then Hq (csu v) else r.2.2.2.1))
      (decapsHq eC eKa Hq (csu v))
  let Φ : (Fin m₁ → Fin n) → Fin (m₁ + m₂) → Fin n := fun G =>
    mergeOracle (keyHop (kemSlice hpk eG r.1.1) (kemEncAt P eG r.1.1) eKR.symm Hq
        (Function.update G t u))
      (prefixUpdate eJ r.2.1 r.2.2.2.2 T)
  have hfun : ∀ G : Fin m₁ → Fin n,
      prOutMR (A.run (kemJoin r G).1.1 (kemChal P hpk eG eKR (kemJoin r G))
          (if b = true then Hq (kemChal P hpk eG eKR (kemJoin r G)) else (kemJoin r G).2.2.2.1))
        (kemOracleCoin P hpk eG eJ eKR (kemJoin r G) Hq T u)
        (decapsHq eC eKa Hq (kemChal P hpk eG eKR (kemJoin r G))) =
      prOut (A' (G t)) (Φ G) := fun G => prOutMR_eq _ _ _
  have hΦ : ∀ (G G' : Fin m₁ → Fin n) (y : Fin (m₁ + m₂)),
      (∀ x, Fin.castAdd m₂ x = y → G x = G' x) → Φ G y = Φ G' y := by
    intro G G' y h
    induction y using Fin.addCases with
    | left x =>
      simp only [Φ, mergeOracle_castAdd]
      unfold keyHop coinCt
      simp only [Function.update_apply, h x rfl]
    | right j =>
      simp [Φ]
  simp only [hfun]
  rw [absDiff_comm]
  exact absDiff_resample_map_off_point (kemBad P hpk eG eKR r.1.1 r.1.2) _ A' lam
    (fun x _ => kemBad_good P hpk eG eKR hcoin x) hlam
    ⟨Fin.castAdd m₂, Fin.castAdd_injective _ _⟩ Φ hΦ
    (fun v => by
      obtain ⟨ψ, hψ⟩ := A.pure r.1.1 (csu v) (if b then Hq (csu v) else r.2.2.2.1)
      exact pure_toQAdv _ _ hψ)

omit [Fintype PK] [Fintype SK] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq Hash] [NeZero n] in
open scoped Classical in
/-- The event of `coinBadWeight` at an input and a fresh value is contained in
the union of two events: the ciphertext map of the `G`-table is not injective on
the public-key slice, or the challenge message encrypted under the coin of the
fresh value is the challenge ciphertext. -/
theorem coinBad_ind_le (i : KEMInput PK SK Z M K m₁ m₂ n) (u : Fin n) :
    (if ∃ m, encOf (P.enc i.1.1) (kemTab hpk eG eKR (coinUpd hpk eG i u)) m =
        kemChal P hpk eG eKR i then (1 : ℝ≥0∞) else 0) ≤
      (if kemInj P hpk eG eKR i then 0 else 1) +
        (if P.enc i.1.1 i.2.2.1 (eKR.symm u).2 = kemChal P hpk eG eKR i then 1 else 0) := by
  have hpt : ∀ m : M,
      encOf (P.enc i.1.1) (kemTab hpk eG eKR (coinUpd hpk eG i u)) m =
        if m = i.2.2.1 then P.enc i.1.1 i.2.2.1 (eKR.symm u).2
        else encOf (P.enc i.1.1) (kemTab hpk eG eKR i) m := by
    intro m
    split_ifs with hm
    · subst hm
      simp [encOf, encAt, coinsOf, kemTab, kemG, coinUpd, kemPt]
    · have hne : eG (m, hpk i.1.1) ≠ kemPt hpk eG i := fun h =>
        hm (congrArg Prod.fst (eG.injective h))
      simp only [encOf, encAt, coinsOf, kemTab, kemG, coinUpd, Function.update_of_ne hne]
  split_ifs with hb hg hs hs <;> try simp
  obtain ⟨m, hm⟩ := hb
  rw [hpt] at hm
  split_ifs at hm with hmm
  · exact hs hm
  · apply hmm
    have h := hg (eG (m, hpk i.1.1)) (eG (i.2.2.1, hpk i.1.1)) (by simp [kemSlice])
      (by simp [kemSlice])
      (by simpa [coinCt, kemEncAt, encOf, encAt, coinsOf, kemTab, kemG, kemChal] using hm)
    exact congrArg Prod.fst (eG.injective h)

omit [Nonempty M] [DecidableEq Z] [Fintype C] [NeZero c] in
/-- On the table resampled off the challenge point, the weight of the inputs and
fresh values at which the challenge message encrypted under the coin of the fresh
value is the challenge ciphertext is the coin-collision weight: the entry of the
resampled table at the exempted challenge point is uniform. -/
theorem sum_resWeight_coll
    (hcoin : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ m, ∃ ρ, P.dec sk (P.enc pk m ρ) = some m) :
    ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ u : Fin n, resWeight P hpk eG eKR i * (n : ℝ≥0∞)⁻¹ *
        (if P.enc i.1.1 i.2.2.1 (eKR.symm u).2 = kemChal P hpk eG eKR i then 1 else 0) =
      collWeight P := by
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [sum_resWeight_mul, collWeight, tsum_fintype,
    ← sum_kemRestWeight_mul_msg (Z := Z) (K := K) (m₂ := m₂) (n := n) P
      (fun ks m => collProb P ks.1 m)]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hk : P.keygen r.1 = 0
  · simp [kemRestWeight, hk]
  refine congrArg _ ?_
  have hgood : ∀ x, ∃ y, restBad P hpk eG eKR r x y = false :=
    offPoint_good _ fun x _ => kemBad_good P hpk eG eKR (hcoin _ _ hk) x
  rw [collProb_eq_fin P eKR,
    ← sum_tableMass_eval_fun _ hgood (eG (r.2.2.1, hpk r.1.1)) (fun v => by simp [restBad])
      (fun v => ∑ u : Fin n, (n : ℝ≥0∞)⁻¹ *
        (if P.enc r.1.1 r.2.2.1 (eKR.symm u).2 = P.enc r.1.1 r.2.2.1 (eKR.symm v).2 then 1
          else 0))]
  simp only [Finset.mul_sum, kemChal, kemG, kemJoin]
  rfl

omit [Nonempty M] [DecidableEq Z] [Fintype C] in
open scoped Classical in
/-- On the table resampled off the challenge point, `coinBadW` is at most the
average of the per-key failure bound `λ` plus a bound `ε` on the coin-collision
weight: the non-injectivity of the ciphertext map costs `δ*` at each rest
(`sum_tableMass_not_sliceInj_le`), and `δ* ≤ λ`. -/
theorem coinBadW_resWeight_le_coll
    (hcoin : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ m, ∃ ρ, P.dec sk (P.enc pk m ρ) = some m)
    (lam : PK × SK → ℝ≥0∞)
    (hlam : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam (pk, sk))
    (ε : ℝ≥0∞) (hcoll : collWeight P ≤ ε) :
    coinBadW (Z := Z) (m₂ := m₂) P hpk eG eKR (resWeight P hpk eG eKR) ≤
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 + ε := by
  have hU : ∑ _u : Fin n, (n : ℝ≥0∞)⁻¹ = 1 := by simpa using sum_inv_card (Fin n)
  have h1 : coinBadW (Z := Z) (m₂ := m₂) P hpk eG eKR (resWeight P hpk eG eKR) ≤
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, resWeight P hpk eG eKR i *
          (if kemInj P hpk eG eKR i then 0 else 1) +
        ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ u : Fin n, resWeight P hpk eG eKR i *
          (n : ℝ≥0∞)⁻¹ *
          (if P.enc i.1.1 i.2.2.1 (eKR.symm u).2 = kemChal P hpk eG eKR i then 1 else 0) := by
    unfold coinBadW
    calc _ ≤ ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ u : Fin n,
          (resWeight P hpk eG eKR i * (n : ℝ≥0∞)⁻¹ *
              (if kemInj P hpk eG eKR i then 0 else 1) +
            resWeight P hpk eG eKR i * (n : ℝ≥0∞)⁻¹ *
              (if P.enc i.1.1 i.2.2.1 (eKR.symm u).2 = kemChal P hpk eG eKR i then 1 else 0)) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun u _ => ?_
          rw [← mul_add]
          exact mul_le_mul_right (coinBad_ind_le P hpk eG eKR i u) _
      _ = _ := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hU, mul_one]
  have h2 : ∑ i : KEMInput PK SK Z M K m₁ m₂ n, resWeight P hpk eG eKR i *
      (if kemInj P hpk eG eKR i then 0 else 1) ≤
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 := by
    rw [sum_resWeight_mul, ← sum_kemRestWeight_mul (m₁ := m₁)]
    refine Finset.sum_le_sum fun r _ => ?_
    by_cases hk : P.keygen r.1 = 0
    · simp [kemRestWeight, hk]
    · gcongr
      refine (sum_tableMass_not_sliceInj_le P hpk eG eKR r.1.1 r.1.2 _ (hcoin _ _ hk)).trans ?_
      rw [← div_eq_mul_inv]
      exact hlam _ _ hk _
  exact h1.trans (add_le_add h2 ((sum_resWeight_coll P hpk eG eKR hcoin).le.trans hcoll))

omit [DecidableEq Z] [Fintype C] in
open scoped Classical in
/-- `coinBadW_resWeight_le_coll` under `ε`-spreadness. -/
theorem coinBadW_resWeight_le
    (hcoin : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ m, ∃ ρ, P.dec sk (P.enc pk m ρ) = some m)
    (lam : PK × SK → ℝ≥0∞)
    (hlam : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam (pk, sk))
    (ε : ℝ≥0∞) (hε : P.IsSpread ε) :
    coinBadW (Z := Z) (m₂ := m₂) P hpk eG eKR (resWeight P hpk eG eKR) ≤
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 + ε :=
  coinBadW_resWeight_le_coll P hpk eG eKR hcoin lam hlam ε (collWeight_le_of_isSpread P ε hε)

open scoped Classical in
/-- The input weight with the `G`-table resampled off the challenge point at the
key pairs that are `CoinGood`, and uniform at the other key pairs. -/
def resWeightCoin (i : KEMInput PK SK Z M K m₁ m₂ n) : ℝ≥0∞ :=
  kemRestWeight P (kemJoinEquiv.symm i).1 *
    (if CoinGood P (kemJoinEquiv.symm i).1.1 then
      tableMass (restBad P hpk eG eKR (kemJoinEquiv.symm i).1) (kemJoinEquiv.symm i).2
    else ((n : ℝ≥0∞) ^ m₁)⁻¹)

omit [Nonempty M] [Nonempty Z] [DecidableEq Z] [Nonempty K] [Fintype R] [Nonempty R] [Fintype C]
  [DecidableEq C] [NeZero n] in
open scoped Classical in
/-- A `resWeightCoin`-weighted sum is a `kemRestWeight`-weighted sum over the
rests of `tableMass`-weighted sums at `CoinGood` key pairs and uniform averages
at the others. -/
theorem sum_resWeightCoin_mul (X : KEMInput PK SK Z M K m₁ m₂ n → ℝ≥0∞) :
    ∑ i : KEMInput PK SK Z M K m₁ m₂ n, resWeightCoin P hpk eG eKR i * X i =
      ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
        ∑ G : Fin m₁ → Fin n, (if CoinGood P r.1 then tableMass (restBad P hpk eG eKR r) G
          else ((n : ℝ≥0∞) ^ m₁)⁻¹) * X (kemJoin r G) := by
  rw [← Fintype.sum_equiv kemJoinEquiv (fun p => resWeightCoin P hpk eG eKR (kemJoin p.1 p.2) *
    X (kemJoin p.1 p.2)) _ fun _ => rfl, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun G _ => mul_assoc _ _ _

omit [Fintype PK] [Fintype SK] [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Fintype R]
  [Nonempty R] [NeZero c] in
/-- The uniform `G`-average at a rest is at most one for a function bounded by
one. -/
theorem sum_unifG_le_one (f : (Fin m₁ → Fin n) → ℝ≥0∞) (hf : ∀ G, f G ≤ 1) :
    ∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ * f G ≤ 1 := by
  refine (Finset.sum_le_sum fun G _ => mul_le_of_le_one_right' (hf G)).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ]
  simp only [Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  exact ENNReal.mul_inv_cancel (pow_ne_zero _ (by exact_mod_cast NeZero.ne n))
    (ENNReal.pow_ne_top (ENNReal.natCast_ne_top n))

omit [Nonempty M] [DecidableEq Z] [Fintype C] [NeZero c] in
open scoped Classical in
/-- `sum_resWeight_coll` at the weight `resWeightCoin`, with no coin hypothesis:
at a key pair that is not `CoinGood` the table is uniform. -/
theorem sum_resWeightCoin_coll :
    ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ u : Fin n,
        resWeightCoin P hpk eG eKR i * (n : ℝ≥0∞)⁻¹ *
        (if P.enc i.1.1 i.2.2.1 (eKR.symm u).2 = kemChal P hpk eG eKR i then 1 else 0) =
      collWeight P := by
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [sum_resWeightCoin_mul, collWeight, tsum_fintype,
    ← sum_kemRestWeight_mul_msg (Z := Z) (K := K) (m₂ := m₂) (n := n) P
      (fun ks m => collProb P ks.1 m)]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hk : P.keygen r.1 = 0
  · simp [kemRestWeight, hk]
  refine congrArg _ ?_
  rw [collProb_eq_fin P eKR]
  by_cases hg : CoinGood P r.1
  · simp only [if_pos hg]
    have hgood : ∀ x, ∃ y, restBad P hpk eG eKR r x y = false :=
      offPoint_good _ fun x _ => kemBad_good P hpk eG eKR hg x
    rw [← sum_tableMass_eval_fun _ hgood (eG (r.2.2.1, hpk r.1.1)) (fun v => by simp [restBad])
      (fun v => ∑ u : Fin n, (n : ℝ≥0∞)⁻¹ *
        (if P.enc r.1.1 r.2.2.1 (eKR.symm u).2 = P.enc r.1.1 r.2.2.1 (eKR.symm v).2 then 1
          else 0))]
    simp only [Finset.mul_sum, kemChal, kemG, kemJoin]
    rfl
  · simp only [if_neg hg]
    rw [← sum_unif_eval_fun (eG (r.2.2.1, hpk r.1.1))
      (fun v => ∑ u : Fin n, (n : ℝ≥0∞)⁻¹ *
        (if P.enc r.1.1 r.2.2.1 (eKR.symm u).2 = P.enc r.1.1 r.2.2.1 (eKR.symm v).2 then 1
          else 0))]
    simp only [Finset.mul_sum, kemChal, kemG, kemJoin]
    rfl

omit [Nonempty M] [DecidableEq Z] [Fintype C] in
open scoped Classical in
/-- `coinBadW_resWeight_le_coll` at the weight `resWeightCoin`, with no coin
hypothesis: at a key pair that is not `CoinGood` the bound `hlam` gives `λ ≥ 1`,
which pays for the event there. -/
theorem coinBadW_resWeightCoin_le_coll (lam : PK × SK → ℝ≥0∞)
    (hlam : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam (pk, sk))
    (ε : ℝ≥0∞) (hcoll : collWeight P ≤ ε) :
    coinBadW (Z := Z) (m₂ := m₂) P hpk eG eKR (resWeightCoin P hpk eG eKR) ≤
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 + ε := by
  have hU : ∑ _u : Fin n, (n : ℝ≥0∞)⁻¹ = 1 := by simpa using sum_inv_card (Fin n)
  have h1 : coinBadW (Z := Z) (m₂ := m₂) P hpk eG eKR (resWeightCoin P hpk eG eKR) ≤
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, resWeightCoin P hpk eG eKR i *
          (if kemInj P hpk eG eKR i then 0 else 1) +
        ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ u : Fin n, resWeightCoin P hpk eG eKR i *
          (n : ℝ≥0∞)⁻¹ *
          (if P.enc i.1.1 i.2.2.1 (eKR.symm u).2 = kemChal P hpk eG eKR i then 1 else 0) := by
    unfold coinBadW
    calc _ ≤ ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ u : Fin n,
          (resWeightCoin P hpk eG eKR i * (n : ℝ≥0∞)⁻¹ *
              (if kemInj P hpk eG eKR i then 0 else 1) +
            resWeightCoin P hpk eG eKR i * (n : ℝ≥0∞)⁻¹ *
              (if P.enc i.1.1 i.2.2.1 (eKR.symm u).2 = kemChal P hpk eG eKR i then 1 else 0)) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun u _ => ?_
          rw [← mul_add]
          exact mul_le_mul_right (coinBad_ind_le P hpk eG eKR i u) _
      _ = _ := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hU, mul_one]
  have h2 : ∑ i : KEMInput PK SK Z M K m₁ m₂ n, resWeightCoin P hpk eG eKR i *
      (if kemInj P hpk eG eKR i then 0 else 1) ≤
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 := by
    rw [sum_resWeightCoin_mul, ← sum_kemRestWeight_mul (m₁ := m₁)]
    refine Finset.sum_le_sum fun r _ => ?_
    by_cases hk : P.keygen r.1 = 0
    · simp [kemRestWeight, hk]
    · gcongr
      by_cases hg : CoinGood P r.1
      · simp only [if_pos hg]
        refine (sum_tableMass_not_sliceInj_le P hpk eG eKR r.1.1 r.1.2 _ hg).trans ?_
        rw [← div_eq_mul_inv]
        exact hlam _ _ hk _
      · simp only [if_neg hg]
        exact (sum_unifG_le_one _ fun G => by split_ifs <;> simp).trans
          (one_le_of_not_coinGood P hpk eG eKR hg (lam r.1) (hlam _ _ hk))
  exact h1.trans (add_le_add h2 ((sum_resWeightCoin_coll P hpk eG eKR).le.trans hcoll))

omit [DecidableEq Z] [Fintype C] in
open scoped Classical in
/-- `coinBadW_resWeightCoin_le_coll` under `ε`-spreadness. -/
theorem coinBadW_resWeightCoin_le (lam : PK × SK → ℝ≥0∞)
    (hlam : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam (pk, sk))
    (ε : ℝ≥0∞) (hε : P.IsSpread ε) :
    coinBadW (Z := Z) (m₂ := m₂) P hpk eG eKR (resWeightCoin P hpk eG eKR) ≤
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 + ε :=
  coinBadW_resWeightCoin_le_coll P hpk eG eKR lam hlam ε (collWeight_le_of_isSpread P ε hε)

end Resampled

/-! ## The challenge bit of the coin-reprogrammed game -/

section Numeric

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c]

/-- The two challenge bits of the coin-reprogrammed game differ by at most
`8 q' Λ^(1/2) + (Λ + ε) + 8 q' Λ^(1/2)`, with `q' = flatQ q k q`, `λ (pk, sk)` a
bound on the decryption-failure fraction of every message under the key pair,
`Λ = E λ` and `ε` a bound on the coin-collision weight `collWeight P`. The two
outer terms compare the uniform and the resampled `G`-table; the middle term is
the exchange of the fake key with `Hq c*` on the resampled table. The table is
resampled at the key pairs that are `CoinGood` only (`resWeightCoin`); at the
other key pairs `hlam` gives `λ ≥ 1`, so no coin hypothesis is required. -/
theorem absDiff_prWinKEMHqCoin_le_of_lam_coll (A : KEMQAdv m₁ m₂ n w q k c a PK C K)
    (lam : PK × SK → ℝ≥0∞)
    (hlam : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam (pk, sk))
    (ε : ℝ≥0∞) (hcoll : collWeight P ≤ ε) :
    absDiff (prWinKEMHqCoin P hpk eG eJ eKR eC eKa A true)
        (prWinKEMHqCoin P hpk eG eJ eKR eC eKa A false) ≤
      8 * (flatQ q k q : ℝ≥0∞) *
          (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) +
        (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 + ε) +
        8 * (flatQ q k q : ℝ≥0∞) *
          (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) := by
  have hW := sum_kemRestWeight (Z := Z) (M := M) (K := K) (m₂ := m₂) P eKR
  have hΛ := sum_kemRestWeight_mul (Z := Z) (M := M) (K := K) (m₁ := m₁) (m₂ := m₂) (n := n) P lam
  have hJ : ∀ C₀ : ℝ≥0∞, ∑ r : KEMRest PK SK Z M K m₂ n,
      kemRestWeight P r * (C₀ * lam r.1 ^ (1 / 2 : ℝ)) ≤
        C₀ * (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) := by
    intro C₀
    calc _ = C₀ * ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r * lam r.1 ^ (1 / 2 : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun r _ => by ring
      _ ≤ C₀ * (∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r * lam r.1) ^ (1 / 2 : ℝ) := by
          gcongr
          exact sum_mul_rpow_half_le _ (fun r => lam r.1) hW
      _ = _ := by rw [hΛ]
  have hout : ∀ b, absDiff (prWinKEMHqCoin P hpk eG eJ eKR eC eKa A b)
      (prWinCoinW P hpk eG eJ eKR eC eKa (resWeightCoin P hpk eG eKR) A b) ≤
      8 * (flatQ q k q : ℝ≥0∞) *
        (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) := by
    intro b
    rw [show prWinKEMHqCoin P hpk eG eJ eKR eC eKa A b =
        prWinCoinW P hpk eG eJ eKR eC eKa (kemSample P) A b from rfl,
      prWinCoinW_eq_sum, prWinCoinW_eq_sum, sum_kemSample_kemJoin, sum_resWeightCoin_mul]
    refine (absDiff_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun r _ => ?_) (hJ _))
    refine (absDiff_mul_left_le _ _ _).trans ?_
    by_cases hk : P.keygen r.1 = 0
    · simp [kemRestWeight, hk]
    · by_cases hg : CoinGood P r.1
      · simp only [if_pos hg]
        gcongr
        exact absDiff_winCoin_resample_le P hpk eG eJ eKR eC eKa A b r hg (lam r.1)
          (fun x _ => hlam _ _ hk x)
      · simp only [if_neg hg, absDiff_self, mul_zero]
        exact zero_le
  have hmid := (prWinCoinW_indep P hpk eG eJ eKR eC eKa (resWeightCoin P hpk eG eKR)
    (fun _ _ => rfl) A).trans (coinBadW_resWeightCoin_le_coll P hpk eG eKR lam hlam ε hcoll)
  refine (absDiff_triangle _
    (prWinCoinW P hpk eG eJ eKR eC eKa (resWeightCoin P hpk eG eKR) A true) _).trans ?_
  refine (add_le_add le_rfl (absDiff_triangle _
    (prWinCoinW P hpk eG eJ eKR eC eKa (resWeightCoin P hpk eG eKR) A false) _)).trans ?_
  rw [← add_assoc,
    absDiff_comm (prWinCoinW P hpk eG eJ eKR eC eKa (resWeightCoin P hpk eG eKR) A false)]
  exact add_le_add (add_le_add (hout true) hmid) (hout false)

/-- `absDiff_prWinKEMHqCoin_le_of_lam_coll` under `ε`-spreadness. -/
theorem absDiff_prWinKEMHqCoin_le_of_lam (A : KEMQAdv m₁ m₂ n w q k c a PK C K)
    (lam : PK × SK → ℝ≥0∞)
    (hlam : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam (pk, sk))
    (ε : ℝ≥0∞) (hε : P.IsSpread ε) :
    absDiff (prWinKEMHqCoin P hpk eG eJ eKR eC eKa A true)
        (prWinKEMHqCoin P hpk eG eJ eKR eC eKa A false) ≤
      8 * (flatQ q k q : ℝ≥0∞) *
          (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) +
        (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 + ε) +
        8 * (flatQ q k q : ℝ≥0∞) *
          (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) :=
  absDiff_prWinKEMHqCoin_le_of_lam_coll P hpk eG eJ eKR eC eKa A lam hlam ε
    (collWeight_le_of_isSpread P ε hε)

/-- The advantage in `prWinKEMHq` bounded by the two one-way-to-hiding terms of
the coin hop and the bound of `absDiff_prWinKEMHqCoin_le_of_lam_coll`. -/
theorem absDiff_prWinKEMHq_le_numeric_of_lam_coll (A : KEMQAdv m₁ m₂ n w q k c a PK C K)
    (lam : PK × SK → ℝ≥0∞)
    (hlam : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam (pk, sk))
    (ε : ℝ≥0∞) (hcoll : collWeight P ≤ ε) :
    absDiff (prWinKEMHq P hpk eG eJ eKR eC eKa A true)
        (prWinKEMHq P hpk eG eJ eKR eC eKa A false) ≤
      4 * ((flatQ q k q : ℝ≥0∞) * prFindCoin P hpk eG eJ eKR eC eKa A true) ^ (1 / 2 : ℝ) +
        (8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) +
          (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 + ε) +
          8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ)) +
        4 * ((flatQ q k q : ℝ≥0∞) * prFindCoin P hpk eG eJ eKR eC eKa A false) ^ (1 / 2 : ℝ) := by
  refine (absDiff_triangle _ (prWinKEMHqCoin P hpk eG eJ eKR eC eKa A true) _).trans ?_
  refine (add_le_add le_rfl (absDiff_triangle _
    (prWinKEMHqCoin P hpk eG eJ eKR eC eKa A false) _)).trans ?_
  rw [← add_assoc, absDiff_comm (prWinKEMHqCoin P hpk eG eJ eKR eC eKa A false)]
  exact add_le_add (add_le_add (hopCoin_o2h P hpk eG eJ eKR eC eKa A true)
    (absDiff_prWinKEMHqCoin_le_of_lam_coll P hpk eG eJ eKR eC eKa A lam hlam ε hcoll))
    (hopCoin_o2h P hpk eG eJ eKR eC eKa A false)

/-- `absDiff_prWinKEMHq_le_numeric_of_lam_coll` under `ε`-spreadness. -/
theorem absDiff_prWinKEMHq_le_numeric_of_lam (A : KEMQAdv m₁ m₂ n w q k c a PK C K)
    (lam : PK × SK → ℝ≥0∞)
    (hlam : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam (pk, sk))
    (ε : ℝ≥0∞) (hε : P.IsSpread ε) :
    absDiff (prWinKEMHq P hpk eG eJ eKR eC eKa A true)
        (prWinKEMHq P hpk eG eJ eKR eC eKa A false) ≤
      4 * ((flatQ q k q : ℝ≥0∞) * prFindCoin P hpk eG eJ eKR eC eKa A true) ^ (1 / 2 : ℝ) +
        (8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) +
          (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 + ε) +
          8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ)) +
        4 * ((flatQ q k q : ℝ≥0∞) * prFindCoin P hpk eG eJ eKR eC eKa A false) ^ (1 / 2 : ℝ) :=
  absDiff_prWinKEMHq_le_numeric_of_lam_coll P hpk eG eJ eKR eC eKa A lam hlam ε
    (collWeight_le_of_isSpread P ε hε)

variable [NeZero (m₁ + m₂)]

open scoped Classical in
/-- The quantum IND-CCA advantage through the coin hop with every correctness
term numeric in `Λ` and the `Find` probability of the hop at bit `b` bounded by
`4 q' (F b + δ*)` for a function `F : Bool → ℝ≥0∞` (`hF`): with
`q' = flatQ q k q`, `q'' = flatQ (q + 4) k q`, `Λ = E λ` and `ε` a bound on the
coin-collision weight `collWeight P`,

`Adv ≤ 4 √(4 q'² (F true + δ*)) + (8 q' Λ^(1/2) + (Λ + ε) + 8 q' Λ^(1/2))
  + 4 √(4 q'² (F false + δ*))
  + 2 (8 q' / √|Z| + 8 q'' Λ^(1/2) + Λ + 8 q' Λ^(1/2))`.

The remaining hypotheses are the failure bound `hlam`, the collision bound
`hcoll` and the structural hypotheses `hw`, `hrounds`, `hseg`, `hinit` of
`absDiff_winReal_resample_le`; no coin hypothesis is required. -/
theorem qINDCCA_le_find_numeric_of_lam_coll [NeZero (flatQ q k q)]
    (A : KEMQAdv m₁ m₂ n w q k c a PK C K)
    (lam : PK × SK → ℝ≥0∞)
    (hlam : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam (pk, sk))
    (ε : ℝ≥0∞) (hcoll : collWeight P ≤ ε) (F : Bool → ℝ≥0∞)
    (hF : ∀ b, prFindCoin P hpk eG eJ eKR eC eKa A b ≤
      4 * (flatQ q k q : ℝ≥0∞) *
        (F b + ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
          (if i.2.2.1 ∈ kemGood P hpk eG eKR i then 0 else 1)))
    (w₀ : ℕ) (hw : 2 * w = w₀ * ancDim (m₁ + m₂) n c)
    (Ans : PK → C → K → Fin a → Equiv.Perm ((Fin (m₁ + m₂) × Fin n) × Fin w₀))
    (hseg : ∀ pk cs κ j i, ((castMR hw (A.run pk cs κ)).seg j i : Matrix _ _ ℂ) *
        cleanProjM (m₁ + m₂) n w₀ c =
      cleanProjM (m₁ + m₂) n w₀ c * ((castMR hw (A.run pk cs κ)).seg j i : Matrix _ _ ℂ))
    (hrounds : ∀ pk cs κ j,
      (castMR hw (A.run pk cs κ)).rounds j = permRound (m₁ + m₂) n w₀ c (Ans pk cs κ))
    (hinit : ∀ pk cs κ,
      SupportedOn (cleanProjM (m₁ + m₂) n w₀ c) (castMR hw (A.run pk cs κ)).init.val) :
    qINDCCAAdvantage P hpk eG eJ eKR eC eKa A ≤
      (4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (F true +
            ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
              (if i.2.2.1 ∈ kemGood P hpk eG eKR i then 0 else 1)))) ^ (1 / 2 : ℝ) +
        (8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) +
          (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 + ε) +
          8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ)) +
        4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (F false +
            ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
              (if i.2.2.1 ∈ kemGood P hpk eG eKR i then 0 else 1)))) ^ (1 / 2 : ℝ)) +
      2 * (8 * (flatQ q k q : ℝ≥0∞) * ((Fintype.card Z : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) +
        (8 * (flatQ (q + 4) k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) +
          ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 +
          8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ))) := by
  have hb : ∀ b, absDiff (prWinKEM P hpk eG eJ eKR eC eKa A b)
      (prWinKEMHq P hpk eG eJ eKR eC eKa A b) ≤
      8 * (flatQ q k q : ℝ≥0∞) * ((Fintype.card Z : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) +
        (8 * (flatQ (q + 4) k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) +
          ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 +
          8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ)) :=
    fun b => (absDiff_triangle _ (prWinKEM' P hpk eG eJ eKR eC eKa A b) _).trans
      (add_le_add (hopJ' P hpk eG eJ eKR eC eKa A b)
        (absDiff_prWinKEM'_prWinKEMHq_le_of_lam P hpk eG eJ eKR eC eKa A b lam hlam w₀ hw Ans
          hseg hrounds hinit))
  unfold qINDCCAAdvantage
  refine (absDiff_triangle _ (prWinKEMHq P hpk eG eJ eKR eC eKa A true) _).trans ?_
  refine (add_le_add le_rfl (absDiff_triangle _ (prWinKEMHq P hpk eG eJ eKR eC eKa A false)
    _)).trans ?_
  rw [absDiff_comm (prWinKEMHq P hpk eG eJ eKR eC eKa A false)]
  have hHq := absDiff_prWinKEMHq_le_numeric_of_lam_coll P hpk eG eJ eKR eC eKa A lam hlam ε hcoll
  have hT := hF true
  have hF' := hF false
  calc _ ≤ _ + (_ + _) := add_le_add (hb true) (add_le_add hHq (hb false))
    _ ≤ _ + ((4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (F true +
            ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
              (if i.2.2.1 ∈ kemGood P hpk eG eKR i then 0 else 1)))) ^ (1 / 2 : ℝ) +
        (8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) +
          (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 + ε) +
          8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ)) +
        4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (F false +
            ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
              (if i.2.2.1 ∈ kemGood P hpk eG eKR i then 0 else 1)))) ^ (1 / 2 : ℝ)) + _) := by
        gcongr
    _ = _ := by ring

open scoped Classical in
/-- `qINDCCA_le_find_numeric_of_lam_coll` under `ε`-spreadness. -/
theorem qINDCCA_le_find_numeric_of_lam [NeZero (flatQ q k q)]
    (A : KEMQAdv m₁ m₂ n w q k c a PK C K)
    (lam : PK × SK → ℝ≥0∞)
    (hlam : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam (pk, sk))
    (ε : ℝ≥0∞) (hε : P.IsSpread ε) (F : Bool → ℝ≥0∞)
    (hF : ∀ b, prFindCoin P hpk eG eJ eKR eC eKa A b ≤
      4 * (flatQ q k q : ℝ≥0∞) *
        (F b + ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
          (if i.2.2.1 ∈ kemGood P hpk eG eKR i then 0 else 1)))
    (w₀ : ℕ) (hw : 2 * w = w₀ * ancDim (m₁ + m₂) n c)
    (Ans : PK → C → K → Fin a → Equiv.Perm ((Fin (m₁ + m₂) × Fin n) × Fin w₀))
    (hseg : ∀ pk cs κ j i, ((castMR hw (A.run pk cs κ)).seg j i : Matrix _ _ ℂ) *
        cleanProjM (m₁ + m₂) n w₀ c =
      cleanProjM (m₁ + m₂) n w₀ c * ((castMR hw (A.run pk cs κ)).seg j i : Matrix _ _ ℂ))
    (hrounds : ∀ pk cs κ j,
      (castMR hw (A.run pk cs κ)).rounds j = permRound (m₁ + m₂) n w₀ c (Ans pk cs κ))
    (hinit : ∀ pk cs κ,
      SupportedOn (cleanProjM (m₁ + m₂) n w₀ c) (castMR hw (A.run pk cs κ)).init.val) :
    qINDCCAAdvantage P hpk eG eJ eKR eC eKa A ≤
      (4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (F true +
            ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
              (if i.2.2.1 ∈ kemGood P hpk eG eKR i then 0 else 1)))) ^ (1 / 2 : ℝ) +
        (8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) +
          (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 + ε) +
          8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ)) +
        4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (F false +
            ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
              (if i.2.2.1 ∈ kemGood P hpk eG eKR i then 0 else 1)))) ^ (1 / 2 : ℝ)) +
      2 * (8 * (flatQ q k q : ℝ≥0∞) * ((Fintype.card Z : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) +
        (8 * (flatQ (q + 4) k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) +
          ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 +
          8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ))) :=
  qINDCCA_le_find_numeric_of_lam_coll P hpk eG eJ eKR eC eKa A lam hlam ε
    (collWeight_le_of_isSpread P ε hε) F hF w₀ hw Ans hseg hrounds hinit

open scoped Classical in
/-- `qINDCCA_le_find_numeric_of_lam_coll` under the coin hypothesis at every key
pair in the support of key generation. The proof does not use the coin hypothesis;
it is kept because `FIPS203QROMQuantumMLWE` passes it along the headline chain
(the coin conjunct of `ChainGood(Coll)`).

References: Hövelmanns, Kiltz, Schäge, Unruh, "Generic authenticated key
exchange in the quantum random oracle model", PKC 2020, ePrint 2018/928, and
Bindel, Hamburg, Hövelmanns, Hülsing, Persichetti, "Tighter proofs of CCA
security in the quantum random oracle model", TCC 2019, ePrint 2019/590 (the
`q √(ε + δ)` shape of the FO⊥̸ bounds built on the semi-classical
one-way-to-hiding theorem of Ambainis, Hamburg, Unruh, CRYPTO 2019). -/
theorem qINDCCA_le_find_numeric_coll [NeZero (flatQ q k q)]
    (A : KEMQAdv m₁ m₂ n w q k c a PK C K)
    (_hcoin : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ m, ∃ ρ, P.dec sk (P.enc pk m ρ) = some m)
    (lam : PK × SK → ℝ≥0∞)
    (hlam : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam (pk, sk))
    (ε : ℝ≥0∞) (hcoll : collWeight P ≤ ε) (F : Bool → ℝ≥0∞)
    (hF : ∀ b, prFindCoin P hpk eG eJ eKR eC eKa A b ≤
      4 * (flatQ q k q : ℝ≥0∞) *
        (F b + ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
          (if i.2.2.1 ∈ kemGood P hpk eG eKR i then 0 else 1)))
    (w₀ : ℕ) (hw : 2 * w = w₀ * ancDim (m₁ + m₂) n c)
    (Ans : PK → C → K → Fin a → Equiv.Perm ((Fin (m₁ + m₂) × Fin n) × Fin w₀))
    (hseg : ∀ pk cs κ j i, ((castMR hw (A.run pk cs κ)).seg j i : Matrix _ _ ℂ) *
        cleanProjM (m₁ + m₂) n w₀ c =
      cleanProjM (m₁ + m₂) n w₀ c * ((castMR hw (A.run pk cs κ)).seg j i : Matrix _ _ ℂ))
    (hrounds : ∀ pk cs κ j,
      (castMR hw (A.run pk cs κ)).rounds j = permRound (m₁ + m₂) n w₀ c (Ans pk cs κ))
    (hinit : ∀ pk cs κ,
      SupportedOn (cleanProjM (m₁ + m₂) n w₀ c) (castMR hw (A.run pk cs κ)).init.val) :
    qINDCCAAdvantage P hpk eG eJ eKR eC eKa A ≤
      (4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (F true +
            ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
              (if i.2.2.1 ∈ kemGood P hpk eG eKR i then 0 else 1)))) ^ (1 / 2 : ℝ) +
        (8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) +
          (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 + ε) +
          8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ)) +
        4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (F false +
            ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
              (if i.2.2.1 ∈ kemGood P hpk eG eKR i then 0 else 1)))) ^ (1 / 2 : ℝ)) +
      2 * (8 * (flatQ q k q : ℝ≥0∞) * ((Fintype.card Z : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) +
        (8 * (flatQ (q + 4) k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) +
          ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 +
          8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ))) :=
  qINDCCA_le_find_numeric_of_lam_coll P hpk eG eJ eKR eC eKa A lam hlam ε hcoll F hF w₀ hw Ans
    hseg hrounds hinit

end Numeric

end CatCrypt.Quantum.QROM

end

end
