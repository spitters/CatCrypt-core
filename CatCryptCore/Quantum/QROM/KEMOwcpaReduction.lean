/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.HopJPrefix
public import CatCryptCore.Quantum.QROM.HopKeyFromCiphertext
public import CatCryptCore.Quantum.QROM.HopChallengeKey

/-!
# The rejection-prefix hop and the key-from-ciphertext hop composed

The IND-CCA game of `Quantum/QROM/KEMQuantumGame.lean` is carried through three
hops in this order: the adversary's view of the rejection prefix `J(z, ·)` is
replaced by an independent table `T` (`HopJPrefix.hopJ'`), decapsulation is
simulated from the `G`-table (`HopDecaps.hopD`, restated at the reprogrammed
oracle), and the key part of the `G`-table on the public-key slice is replaced
by `Hq` at the ciphertext (`HopKeyFromCiphertext.hopH`, restated at the
reprogrammed oracle). In the resulting game the rejection prefix is read by the
decapsulation answers only, so it is an independent uniform table, and by
`sum_mergeOn` the decapsulation table `mergeOn (image) Hq J(z, ·)` has the law
of `Hq`: the game equals the one whose decapsulation answers are `Hq` off the
challenge ciphertext.

## Main definitions

* `winSimJ A b i` — the winning probability at an input, averaged over `T`, of
  the game with reprogrammed prefix and simulated decapsulation
* `prWinKEMSimJ`, `prWinKEMHJ` — the game with reprogrammed prefix and
  simulated decapsulation, and the same game after the key-from-ciphertext hop
* `prWinKEMHq` — the game whose decapsulation answers are `Hq` off the
  challenge ciphertext and whose challenge key is `Hq c*` or the fake key
* `prefixSwap eJ z` — the involution exchanging the prefix `z` of a table with
  a table on the ciphertexts
* `oracleTabHK i Hq u` — the key-and-coin table on the public-key slice of the
  hopped `G`-table updated at the challenge point by `u`

## Main results

* `hopDJ` — the decapsulation hop at the reprogrammed oracle, at the cost of the
  decryption-failure weight
* `absDiff_relabel_inputH`, `hopHJ` — the key-from-ciphertext hop at the
  reprogrammed oracle, at the cost of the non-injectivity weight
* `hopJDH`, `qINDCCA_le_hopJDH` — the three hops composed:
  `|prWinKEM − prWinKEMHJ| ≤ 8 q' / √|Z| + δ_fail + δ_inj`
* `sum_prefix_indep` — the prefix of a table read nowhere else is an independent
  uniform table
* `sum_keyProj` — the key projection of a uniform table `C → Fin n` is a uniform
  table `C → K`
* `sum_mergeOn_keyProj` — `sum_mergeOn` at a merged table drawn as the key
  projection of a uniform table
* `prWinKEMHJ_eq_prWinKEMHq` — the composed game equals `prWinKEMHq`
* `qINDCCA_le_hopJDH_Hq` — the quantum IND-CCA advantage is at most the
  advantage in `prWinKEMHq` plus twice the three hop costs
* `decapsHq_oracleTabHK_iff` — in `prWinKEMHq`, updating the whole `G`-entry at
  the challenge point by `u` makes the decapsulation answer at the ciphertext of
  a message differ from the oracle's key there exactly at the challenge message,
  unless `Hq` at that ciphertext equals the key of `u`

## The game `prWinKEMHq`

In `prWinKEMHq` the decapsulation answers are a function of `Hq` and the
challenge ciphertext, the oracle is a function of `Hq`, the `G`-table, the
table `T` and the `J`-table off the prefix `z`, and `z` itself is read nowhere.
By `decapsHq_oracleTabHK_iff`, the reprogramming of `HopChallengeKey.hopKGame`,
which replaces the whole `G`-entry at the challenge point by a fresh value, makes
the pair of oracle table and decapsulation answers in `prWinKEMHq` locate the
challenge message. The hop of `HopCoinChallenge` reprograms the challenge point
so that the coin there is the coin of a fresh value `u` and the key part there is
`Hq` at the encryption of `m*` under that coin. The quantum
IND-CCA bound of the FIPS 203 key encapsulation is
`CoinBadNumeric.qINDCCA_le_find_numeric_coll`.

The two correctness terms quantify over every message: the failure term `δ_fail`
weighs the inputs on which some message is outside `kemGood`, and the injectivity
term `δ_inj` the inputs on which the encryption map is not injective.

## References

* [Hofheinz, Hövelmanns, Kiltz — A Modular Analysis of the Fujisaki–Okamoto
  Transformation, TCC 2017], §4.2
* [Saito, Xagawa, Yamakawa — Tightly-Secure Key-Encapsulation Mechanism in the
  Quantum Random Oracle Model, EUROCRYPT 2018]
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open CatCrypt.Quantum
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The decapsulation and key hops at the reprogrammed oracle -/

section Hops

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c]

/-- The winning probability at an input, averaged over the table `T` that
reprograms the prefix `z`, with simulated decapsulation. -/
def winSimJ (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (i : KEMInput PK SK Z M K m₁ m₂ n) : ℝ≥0∞ :=
  ∑ T : C → Fin n, tabWeight n C *
    prOutMR (A.run i.1.1 (kemChal P hpk eG eKR i) (kemKey hpk eG eKR i b)) (kemOracle' eJ i T)
      (decapsSim P hpk eG eJ eKR eC eKa i)

omit [Fintype PK] [Fintype SK] [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z]
  [Fintype K] [Nonempty R] [DecidableEq Hash] [NeZero c] in
theorem winSimJ_le_one (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (i : KEMInput PK SK Z M K m₁ m₂ n) : winSimJ P hpk eG eJ eKR eC eKa A b i ≤ 1 := by
  calc winSimJ P hpk eG eJ eKR eC eKa A b i ≤ ∑ _T : C → Fin n, tabWeight n C * 1 :=
        Finset.sum_le_sum fun T _ => by gcongr; exact prOutMR_le_one _ _ _
    _ = 1 := by simp only [mul_one]; exact sum_tabWeight n C

/-- The game with the prefix `z` reprogrammed by `T` and simulated
decapsulation. -/
def prWinKEMSimJ (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) : ℝ≥0∞ :=
  ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * winSimJ P hpk eG eJ eKR eC eKa A b i

omit [Nonempty M] [Nonempty Z] [Nonempty R] [DecidableEq Hash] [NeZero c] in
/-- The decapsulation hop at the reprogrammed oracle: the two games differ by
at most the weight of the inputs whose `G`-table has a decryption failure. -/
theorem hopDJ (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    absDiff (prWinKEM' P hpk eG eJ eKR eC eKa A b) (prWinKEMSimJ P hpk eG eJ eKR eC eKa A b) ≤
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
        (if ∀ m, m ∈ kemGood P hpk eG eKR i then 0 else 1) := by
  have hL : prWinKEM' P hpk eG eJ eKR eC eKa A b = ∑ i : KEMInput PK SK Z M K m₁ m₂ n,
      kemSample P i * ∑ T : C → Fin n, tabWeight n C *
        prOutMR (A.run i.1.1 (kemChal P hpk eG eKR i) (kemKey hpk eG eKR i b))
          (kemOracle' eJ i T) (kemDecaps P hpk eG eJ eKR eC eKa i) := by
    unfold prWinKEM'
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun T _ => by ring
  rw [hL]
  refine le_trans (absDiff_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  refine le_trans (absDiff_mul_left_le _ _ _) ?_
  gcongr
  by_cases hg : ∀ m, m ∈ kemGood P hpk eG eKR i
  · rw [ite_eq_left hg, winSimJ, decapsSim_eq_of_good P hpk eG eJ eKR eC eKa i hg, absDiff_self]
  · rw [ite_eq_right hg]
    have hK : ∑ T : C → Fin n, tabWeight n C *
        prOutMR (A.run i.1.1 (kemChal P hpk eG eKR i) (kemKey hpk eG eKR i b))
          (kemOracle' eJ i T) (kemDecaps P hpk eG eJ eKR eC eKa i) ≤ 1 :=
      calc _ ≤ ∑ _T : C → Fin n, tabWeight n C * 1 :=
            Finset.sum_le_sum fun T _ => by gcongr; exact prOutMR_le_one _ _ _
        _ = 1 := by simp only [mul_one]; exact sum_tabWeight n C
    exact absDiff_le_iff.mpr ⟨le_trans hK le_add_self,
      le_trans (winSimJ_le_one P hpk eG eJ eKR eC eKa A b i) le_add_self⟩

omit [DecidableEq M] [Nonempty M] [Nonempty Z] [DecidableEq Z] [Nonempty R] [NeZero n]
  [NeZero c] in
open scoped Classical in
/-- The relabelling of `HopKeyFromCiphertext.sum_inputH` as a bound: for a
function `Φ ≤ 1` of the input, its average at the hopped input under an
independent uniform `Hq` differs from its average at the input by at most the
weight of the inputs whose ciphertext map is not injective. -/
theorem absDiff_relabel_inputH
    (Φ : KEMInput PK SK Z M K m₁ m₂ n → ℝ≥0∞) (hΦ : ∀ j, Φ j ≤ 1) :
    absDiff (∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ Hq : C → K,
        kemSample P i * (Fintype.card (C → K) : ℝ≥0∞)⁻¹ * Φ (inputH P hpk eG eKR i Hq))
      (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * Φ i) ≤
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
        (if Function.Injective (encOf (P.enc i.1.1) (kemTab hpk eG eKR i)) then 0 else 1) := by
  set κ : ℝ≥0∞ := (Fintype.card (C → K) : ℝ≥0∞)⁻¹ with hκ
  have hκsum : ∀ t : ℝ≥0∞, ∑ _Hq : C → K, κ * t = t := by
    intro t
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hκ,
      ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
      one_mul]
  set I : KEMInput PK SK Z M K m₁ m₂ n → Prop := kemInj P hpk eG eKR with hI
  have hcost : ∀ i : KEMInput PK SK Z M K m₁ m₂ n,
      (if Function.Injective (encOf (P.enc i.1.1) (kemTab hpk eG eKR i)) then (0 : ℝ≥0∞) else 1) =
        if I i then 0 else 1 := fun i => by
    rw [hI]; exact if_congr (kemInj_iff P hpk eG eKR i).symm rfl rfl
  simp only [hcost]
  set D := ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * (if I i then 0 else 1)
  have hsplit : ∀ (p : Prop) [Decidable p] (x : ℝ≥0∞),
      x = (if p then x else 0) + (if p then 0 else x) := by
    intro p _ x; split_ifs <;> simp
  set A0 := ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * (if I i then Φ i else 0)
  have hH : ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ Hq : C → K,
        kemSample P i * κ * Φ (inputH P hpk eG eKR i Hq) =
      A0 + ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ Hq : C → K,
        kemSample P i * (if I i then 0 else κ * Φ (inputH P hpk eG eKR i Hq)) := by
    have hA := sum_inputH P hpk eG eKR (fun j => κ * Φ j)
    have hA' : ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ _Hq : C → K,
        kemSample P i * (if I i then κ * Φ i else 0) = A0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have : kemSample P i * (if I i then κ * Φ i else 0) =
          κ * (kemSample P i * (if I i then Φ i else 0)) := by
        split_ifs <;> ring
      rw [Finset.sum_congr rfl fun (_ : C → K) _ => this, hκsum]
    rw [← hA', ← hA, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun Hq _ => ?_
    rw [← mul_add, ← hsplit, mul_assoc]
  have hS : ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * Φ i =
      A0 + ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * (if I i then 0 else Φ i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_add, ← hsplit]
  have hB1 : ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ Hq : C → K,
      kemSample P i * (if I i then 0 else κ * Φ (inputH P hpk eG eKR i Hq)) ≤ D := by
    refine Finset.sum_le_sum fun i _ => ?_
    calc ∑ Hq : C → K, kemSample P i * (if I i then 0 else κ * Φ (inputH P hpk eG eKR i Hq))
        ≤ ∑ _Hq : C → K, κ * (kemSample P i * (if I i then 0 else 1)) := by
          refine Finset.sum_le_sum fun Hq _ => ?_
          split_ifs
          · simp
          · rw [mul_one, mul_left_comm]
            gcongr
            exact mul_le_of_le_one_right' (hΦ _)
      _ = kemSample P i * (if I i then 0 else 1) := hκsum _
  have hB2 : ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * (if I i then 0 else Φ i) ≤ D := by
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs
    · simp
    · gcongr; exact hΦ _
  rw [hH, hS]
  refine absDiff_le_iff.mpr ⟨?_, ?_⟩
  · calc _ ≤ A0 + D := add_le_add le_rfl hB1
      _ ≤ _ := by rw [add_assoc]; exact add_le_add le_rfl le_add_self
  · calc _ ≤ A0 + D := add_le_add le_rfl hB2
      _ ≤ _ := by rw [add_assoc]; exact add_le_add le_rfl le_add_self

/-- The game with the prefix `z` reprogrammed by `T`, simulated decapsulation,
and the key part of the `G`-table on the public-key slice replaced by `Hq` at
the ciphertext. -/
def prWinKEMHJ (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) : ℝ≥0∞ :=
  ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ Hq : C → K,
    kemSample P i * (Fintype.card (C → K) : ℝ≥0∞)⁻¹ *
      winSimJ P hpk eG eJ eKR eC eKa A b (inputH P hpk eG eKR i Hq)

omit [DecidableEq M] [Nonempty M] [Nonempty Z] [Nonempty R] [NeZero c] in
open scoped Classical in
/-- The key-from-ciphertext hop at the reprogrammed oracle: the two games differ
by at most the weight of the inputs whose ciphertext map is not injective. -/
theorem hopHJ (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    absDiff (prWinKEMHJ P hpk eG eJ eKR eC eKa A b) (prWinKEMSimJ P hpk eG eJ eKR eC eKa A b) ≤
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
        (if Function.Injective (encOf (P.enc i.1.1) (kemTab hpk eG eKR i)) then 0 else 1) :=
  absDiff_relabel_inputH P hpk eG eKR _ (winSimJ_le_one P hpk eG eJ eKR eC eKa A b)

open scoped Classical in
/-- The three hops composed: with `q' = flatQ q k q`,
`|prWinKEM − prWinKEMHJ| ≤ 8 q' / √|Z| + δ_fail + δ_inj`, where `δ_fail` is the
weight of the inputs with a decryption failure and `δ_inj` the weight of the
inputs whose ciphertext map is not injective. -/
theorem hopJDH (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    absDiff (prWinKEM P hpk eG eJ eKR eC eKa A b) (prWinKEMHJ P hpk eG eJ eKR eC eKa A b) ≤
      8 * (flatQ q k q : ℝ≥0∞) * ((Fintype.card Z : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) +
        ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
          (if ∀ m, m ∈ kemGood P hpk eG eKR i then 0 else 1) +
        ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
          (if Function.Injective (encOf (P.enc i.1.1) (kemTab hpk eG eKR i)) then 0 else 1) := by
  calc absDiff (prWinKEM P hpk eG eJ eKR eC eKa A b) (prWinKEMHJ P hpk eG eJ eKR eC eKa A b)
      ≤ absDiff (prWinKEM P hpk eG eJ eKR eC eKa A b) (prWinKEM' P hpk eG eJ eKR eC eKa A b) +
          absDiff (prWinKEM' P hpk eG eJ eKR eC eKa A b)
            (prWinKEMHJ P hpk eG eJ eKR eC eKa A b) := absDiff_triangle _ _ _
    _ ≤ absDiff (prWinKEM P hpk eG eJ eKR eC eKa A b) (prWinKEM' P hpk eG eJ eKR eC eKa A b) +
          (absDiff (prWinKEM' P hpk eG eJ eKR eC eKa A b)
            (prWinKEMSimJ P hpk eG eJ eKR eC eKa A b) +
          absDiff (prWinKEMSimJ P hpk eG eJ eKR eC eKa A b)
            (prWinKEMHJ P hpk eG eJ eKR eC eKa A b)) := by
        gcongr; exact absDiff_triangle _ _ _
    _ ≤ _ := by
        rw [← add_assoc]
        gcongr
        · exact hopJ' P hpk eG eJ eKR eC eKa A b
        · exact hopDJ P hpk eG eJ eKR eC eKa A b
        · rw [absDiff_comm]; exact hopHJ P hpk eG eJ eKR eC eKa A b

open scoped Classical in
/-- The quantum IND-CCA advantage is at most the advantage in the composed game
plus twice the three hop costs. -/
theorem qINDCCA_le_hopJDH (A : KEMQAdv m₁ m₂ n w q k c a PK C K) :
    qINDCCAAdvantage P hpk eG eJ eKR eC eKa A ≤
      absDiff (prWinKEMHJ P hpk eG eJ eKR eC eKa A true)
          (prWinKEMHJ P hpk eG eJ eKR eC eKa A false) +
        2 * (8 * (flatQ q k q : ℝ≥0∞) * ((Fintype.card Z : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) +
          ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
            (if ∀ m, m ∈ kemGood P hpk eG eKR i then 0 else 1) +
          ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
            (if Function.Injective (encOf (P.enc i.1.1) (kemTab hpk eG eKR i)) then 0 else 1)) := by
  unfold qINDCCAAdvantage
  calc absDiff (prWinKEM P hpk eG eJ eKR eC eKa A true) (prWinKEM P hpk eG eJ eKR eC eKa A false)
      ≤ absDiff (prWinKEM P hpk eG eJ eKR eC eKa A true)
            (prWinKEMHJ P hpk eG eJ eKR eC eKa A true) +
          absDiff (prWinKEMHJ P hpk eG eJ eKR eC eKa A true)
            (prWinKEM P hpk eG eJ eKR eC eKa A false) := absDiff_triangle _ _ _
    _ ≤ absDiff (prWinKEM P hpk eG eJ eKR eC eKa A true)
            (prWinKEMHJ P hpk eG eJ eKR eC eKa A true) +
          (absDiff (prWinKEMHJ P hpk eG eJ eKR eC eKa A true)
            (prWinKEMHJ P hpk eG eJ eKR eC eKa A false) +
          absDiff (prWinKEMHJ P hpk eG eJ eKR eC eKa A false)
            (prWinKEM P hpk eG eJ eKR eC eKa A false)) := by
        gcongr; exact absDiff_triangle _ _ _
    _ ≤ _ := by
        rw [two_mul, absDiff_comm (prWinKEMHJ P hpk eG eJ eKR eC eKa A false)]
        have h1 := hopJDH P hpk eG eJ eKR eC eKa A true
        have h2 := hopJDH P hpk eG eJ eKR eC eKa A false
        calc _ ≤ _ + (_ + _) := add_le_add h1 (add_le_add le_rfl h2)
          _ = _ := by ring

end Hops

/-! ## The rejection prefix read by decapsulation alone -/

section PrefixMerge

variable {m₂ n : ℕ} {Z C K R : Type} [DecidableEq Z] (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n)

theorem prefixUpdate_prefixUpdate_same (z : Z) (J : Fin m₂ → Fin n) (T T' : C → Fin n) :
    prefixUpdate eJ z (prefixUpdate eJ z J T') T = prefixUpdate eJ z J T := by
  funext y
  simp only [prefixUpdate]
  split_ifs <;> rfl

/-- The exchange of the prefix `z` of a table with a table on the ciphertexts. -/
def prefixSwap (z : Z) (p : (Fin m₂ → Fin n) × (C → Fin n)) :
    (Fin m₂ → Fin n) × (C → Fin n) :=
  (prefixUpdate eJ z p.1 p.2, fun c => p.1 (eJ (z, c)))

theorem prefixSwap_involutive (z : Z) : Function.Involutive (prefixSwap (n := n) eJ z) := by
  rintro ⟨J, T⟩
  exact Prod.ext (prefixUpdate_prefixUpdate eJ z J T) (prefixUpdate_prefix eJ z J T)

omit [DecidableEq Z] in
/-- Three nested finite sums in reverse order. -/
theorem sum_rot3 {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ≥0∞) :
    ∑ x, ∑ y, ∑ t, ∑ u, f x y t u = ∑ t, ∑ y, ∑ x, ∑ u, f x y t u := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun y _ => Finset.sum_comm]
  exact Finset.sum_comm

variable [Fintype C] [DecidableEq C]

/-- The prefix `z` of a uniform table, read by `F` only through its second
argument, is an independent uniform table: the table updated on the prefix
together with an independent table has the law of the table updated on the
prefix together with its own prefix. -/
theorem sum_prefix_indep (z : Z) (T : C → Fin n)
    (F : (Fin m₂ → Fin n) → (C → Fin n) → ℝ≥0∞) :
    ∑ J : Fin m₂ → Fin n, ∑ T' : C → Fin n, F (prefixUpdate eJ z J T) T' =
      ∑ J : Fin m₂ → Fin n, ∑ _T' : C → Fin n,
        F (prefixUpdate eJ z J T) (fun c => J (eJ (z, c))) := by
  rw [← Fintype.sum_prod_type' (f := fun J T' => F (prefixUpdate eJ z J T) T'),
    ← Fintype.sum_prod_type' (f := fun J (_ : C → Fin n) =>
      F (prefixUpdate eJ z J T) (fun c => J (eJ (z, c))))]
  refine Fintype.sum_equiv ((prefixSwap_involutive eJ z).toPerm _) _ _ fun p => ?_
  change _ = F (prefixUpdate eJ z (prefixSwap eJ z p).1 T)
    (fun c => (prefixSwap eJ z p).1 (eJ (z, c)))
  simp only [prefixSwap, prefixUpdate_prefixUpdate_same, prefixUpdate_apply_prefix]

variable [Fintype K] [Fintype R]

/-- The key projection of a uniform table `C → Fin n` is a uniform table
`C → K`, with multiplicity the number of coin tables. -/
theorem sum_keyProj (f : (C → K) → ℝ≥0∞) :
    ∑ T : C → Fin n, f (fun c => (eKR.symm (T c)).1) = ∑ r : C → K, ∑ _s : C → R, f r := by
  rw [← Fintype.sum_prod_type' (f := fun r (_ : C → R) => f r)]
  exact Fintype.sum_equiv ((Equiv.arrowCongr (Equiv.refl C) eKR.symm).trans
    (Equiv.arrowProdEquivProdArrow C (fun _ => K) (fun _ => R))) _ _ fun T => rfl

/-- `sum_mergeOn` at a function that reads its first argument only on `Img`,
with the merged table drawn as the key projection of a uniform table. -/
theorem sum_mergeOn_keyProj (Img : C → Prop) [DecidablePred Img]
    (Φ : (C → K) → (C → K) → ℝ≥0∞)
    (hΦ : ∀ Hq Hq' H, (∀ y, Img y → Hq y = Hq' y) → Φ Hq H = Φ Hq' H) :
    ∑ Hq : C → K, ∑ T : C → Fin n, Φ Hq (mergeOn Img Hq (fun c => (eKR.symm (T c)).1)) =
      ∑ Hq : C → K, ∑ _T : C → Fin n, Φ Hq Hq := by
  have h1 : ∀ Hq r, Φ Hq (mergeOn Img Hq r) = Φ (mergeOn Img Hq r) (mergeOn Img Hq r) :=
    fun Hq r => hΦ _ _ _ fun y hy => by simp [mergeOn, hy]
  have hL : ∀ Hq : C → K, ∑ T : C → Fin n, Φ Hq (mergeOn Img Hq (fun c => (eKR.symm (T c)).1)) =
      Fintype.card (C → R) • ∑ r : C → K, Φ Hq (mergeOn Img Hq r) := fun Hq => by
    rw [sum_keyProj eKR (fun r => Φ Hq (mergeOn Img Hq r)), Finset.smul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [Finset.sum_const, Finset.card_univ]
  have hR : ∀ Hq : C → K, ∑ _T : C → Fin n, Φ Hq Hq =
      Fintype.card (C → R) • ∑ _r : C → K, Φ Hq Hq := fun Hq => by
    rw [sum_keyProj eKR (fun _ => Φ Hq Hq), Finset.smul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [Finset.sum_const, Finset.card_univ]
  rw [Finset.sum_congr rfl fun Hq _ => hL Hq, Finset.sum_congr rfl fun Hq _ => hR Hq,
    ← Finset.smul_sum, ← Finset.smul_sum]
  congr 1
  rw [Finset.sum_congr rfl fun Hq _ => Finset.sum_congr rfl fun r _ => h1 Hq r]
  exact sum_mergeOn Img (fun _ H => Φ H H)

/-- The rejection prefix merged into `Hq`: when the prefix `z` of the table is
read only through the merged table `mergeOn Img Hq J(z, ·)`, and `Hq` is read
elsewhere only on `Img`, the merged table can be replaced by `Hq`. -/
theorem sum_prefix_merge (z : Z) (Img : C → Prop) [DecidablePred Img]
    (Φ : (Fin m₂ → Fin n) → (C → K) → (C → K) → ℝ≥0∞)
    (hΦ : ∀ Jo Hq Hq' H, (∀ y, Img y → Hq y = Hq' y) → Φ Jo Hq H = Φ Jo Hq' H) :
    ∑ J : Fin m₂ → Fin n, ∑ Hq : C → K, ∑ T : C → Fin n,
        Φ (prefixUpdate eJ z J T) Hq (mergeOn Img Hq (fun y => (eKR.symm (J (eJ (z, y)))).1)) =
      ∑ J : Fin m₂ → Fin n, ∑ Hq : C → K, ∑ T : C → Fin n, Φ (prefixUpdate eJ z J T) Hq Hq := by
  by_cases hN : Fintype.card (C → Fin n) = 0
  · have : IsEmpty (C → Fin n) := Fintype.card_eq_zero_iff.mp hN
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero]
  have key : ∑ J : Fin m₂ → Fin n, ∑ Hq : C → K, ∑ T : C → Fin n, ∑ _T' : C → Fin n,
        Φ (prefixUpdate eJ z J T) Hq (mergeOn Img Hq (fun y => (eKR.symm (J (eJ (z, y)))).1)) =
      ∑ J : Fin m₂ → Fin n, ∑ Hq : C → K, ∑ T : C → Fin n, ∑ _T' : C → Fin n,
        Φ (prefixUpdate eJ z J T) Hq Hq := by
    rw [sum_rot3]
    rw [Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun Hq _ =>
      (sum_prefix_indep eJ z T (fun Jo T' =>
        Φ Jo Hq (mergeOn Img Hq (fun y => (eKR.symm (T' y)).1)))).symm]
    rw [Finset.sum_congr rfl fun T _ => Finset.sum_comm]
    rw [Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun J _ =>
      sum_mergeOn_keyProj eKR Img (Φ (prefixUpdate eJ z J T)) (hΦ (prefixUpdate eJ z J T))]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun J _ => Finset.sum_comm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] at key
  exact (ENNReal.mul_right_inj (by exact_mod_cast hN) (ENNReal.natCast_ne_top _)).mp key

end PrefixMerge

/-! ## The composed game with decapsulation answered by `Hq` -/

section KEMMerge

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

omit [Fintype PK] [Fintype SK] [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z]
  [DecidableEq Z] [Fintype K] [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C] in
/-- The challenge key of the hopped input: `Hq c*` at `true`, the fake key at
`false`. -/
theorem kemKey_inputH (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq : C → K) (b : Bool) :
    kemKey hpk eG eKR (inputH P hpk eG eKR i Hq) b =
      if b then Hq (kemChal P hpk eG eKR i) else i.2.2.2.1 := by
  cases b
  · rfl
  · exact kemKey_inputH_true P hpk eG eKR i Hq

omit [Fintype PK] [Fintype SK] [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z]
  [DecidableEq Z] [Fintype K] [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C] in
/-- The hopped input reads `Hq` only on the ciphertexts of the messages. -/
theorem inputH_congr (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq Hq' : C → K)
    (h : ∀ y, (∃ m, encOf (P.enc i.1.1) (kemTab hpk eG eKR i) m = y) → Hq y = Hq' y) :
    inputH P hpk eG eKR i Hq = inputH P hpk eG eKR i Hq' := by
  have hk : keyHop (kemSlice hpk eG i.1.1) (kemEncAt P eG i.1.1) eKR.symm Hq i.2.2.2.2.1 =
      keyHop (kemSlice hpk eG i.1.1) (kemEncAt P eG i.1.1) eKR.symm Hq' i.2.2.2.2.1 := by
    funext x
    simp only [keyHop]
    split_ifs with hx
    · rw [h]
      refine ⟨(eG.symm x).1, ?_⟩
      have hx' : eG ((eG.symm x).1, hpk i.1.1) = x := by
        rw [← (show (eG.symm x).2 = hpk i.1.1 from hx), Prod.mk.eta, Equiv.apply_symm_apply]
      simp only [encOf, encAt, coinsOf, kemTab, kemG, coinCt, kemEncAt, hx']
    · rfl
  simp only [inputH, hk]

omit [Fintype PK] [Fintype SK] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z]
  [DecidableEq Z] [Fintype K] [Fintype R] [Nonempty R] [Fintype C] in
open scoped Classical in
/-- The simulated decapsulation of the hopped input, restated from
`decapsH_eq_decapsHq`. -/
theorem decapsSim_inputH (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq : C → K) :
    decapsSim P hpk eG eJ eKR eC eKa (inputH P hpk eG eKR i Hq) =
      decapsHq eC eKa (mergeOn (fun y => ∃ m, encOf (P.enc i.1.1) (kemTab hpk eG eKR i) m = y)
        Hq (fun y => kemJ eJ eKR i (i.2.1, y))) (kemChal P hpk eG eKR i) := by
  convert decapsH_eq_decapsHq P hpk eG eJ eKR eC eKa i Hq
  unfold decapsH
  congr

variable [NeZero n] [NeZero c]

/-- The composed game with the decapsulation answers `Hq` off the challenge
ciphertext: the input, an independent uniform `Hq : C → K` and an independent
uniform `T : C → Fin n` are drawn; the adversary receives `pk`, `c*` and the key
`Hq c*` at `true` or the fake key at `false`, queries the `G`-table with key part
`Hq` at the ciphertext on the public-key slice and the `J`-table with prefix `z`
replaced by `T`, and its classical rounds are answered by `decapsHq Hq c*`. -/
def prWinKEMHq (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) : ℝ≥0∞ :=
  ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ Hq : C → K,
    kemSample P i * (Fintype.card (C → K) : ℝ≥0∞)⁻¹ * ∑ T : C → Fin n, tabWeight n C *
      prOutMR (A.run i.1.1 (kemChal P hpk eG eKR i)
          (if b then Hq (kemChal P hpk eG eKR i) else i.2.2.2.1))
        (kemOracle' eJ (inputH P hpk eG eKR i Hq) T) (decapsHq eC eKa Hq (kemChal P hpk eG eKR i))

omit [DecidableEq M] [Nonempty M] [Nonempty Z] [Nonempty R] [NeZero c] in
open scoped Classical in
/-- In the composed game the rejection prefix is read only by decapsulation, so
the decapsulation table `mergeOn (image) Hq J(z, ·)` can be replaced by `Hq`. -/
theorem prWinKEMHJ_eq_prWinKEMHq (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    prWinKEMHJ P hpk eG eJ eKR eC eKa A b = prWinKEMHq P hpk eG eJ eKR eC eKa A b := by
  unfold prWinKEMHJ prWinKEMHq winSimJ
  simp only [kemChal_inputH, kemKey_inputH, decapsSim_inputH, Finset.mul_sum]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun pk _ => Finset.sum_congr rfl fun sk _ =>
    Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun ms _ =>
    Finset.sum_congr rfl fun kf _ => Finset.sum_congr rfl fun G _ => ?_
  simp only [kemSample, kemChal, kemJ, kemOracle', kemJ', inputH, encOf, encAt, coinsOf, kemTab,
    kemG]
  set cs := P.enc pk ms (eKR.symm (G (eG (ms, hpk pk)))).2
  set w := P.keygen (pk, sk) * (Fintype.card Z : ℝ≥0∞)⁻¹ * (Fintype.card M : ℝ≥0∞)⁻¹ *
    (Fintype.card K : ℝ≥0∞)⁻¹ * ((n : ℝ≥0∞) ^ m₁)⁻¹ * ((n : ℝ≥0∞) ^ m₂)⁻¹ *
    (Fintype.card (C → K) : ℝ≥0∞)⁻¹
  have hk : ∀ Hq Hq' : C → K,
      (∀ y, (∃ m', P.enc pk m' (eKR.symm (G (eG (m', hpk pk)))).2 = y) → Hq y = Hq' y) →
      keyHop (kemSlice hpk eG pk) (kemEncAt P eG pk) eKR.symm Hq G =
        keyHop (kemSlice hpk eG pk) (kemEncAt P eG pk) eKR.symm Hq' G := fun Hq Hq' h =>
    congrArg (fun i : KEMInput PK SK Z M K m₁ m₂ n => i.2.2.2.2.1)
      (inputH_congr P hpk eG eKR ((pk, sk), z, ms, kf, G, fun _ => 0) Hq Hq' h)
  exact sum_prefix_merge eJ eKR z
    (fun y => ∃ m', P.enc pk m' (eKR.symm (G (eG (m', hpk pk)))).2 = y)
    (fun Jo Hq H => w * (tabWeight n C *
        prOutMR (A.run pk cs (if b = true then Hq cs else kf))
          (mergeOracle (keyHop (kemSlice hpk eG pk) (kemEncAt P eG pk) eKR.symm Hq G) Jo)
          (decapsHq eC eKa H cs)))
    (fun Jo Hq Hq' H h => by
      have hc : Hq cs = Hq' cs := h _ ⟨ms, rfl⟩
      rw [hc, hk Hq Hq' h])

open scoped Classical in
/-- The quantum IND-CCA advantage is at most the advantage in `prWinKEMHq` plus
twice the three hop costs. -/
theorem qINDCCA_le_hopJDH_Hq (A : KEMQAdv m₁ m₂ n w q k c a PK C K) :
    qINDCCAAdvantage P hpk eG eJ eKR eC eKa A ≤
      absDiff (prWinKEMHq P hpk eG eJ eKR eC eKa A true)
          (prWinKEMHq P hpk eG eJ eKR eC eKa A false) +
        2 * (8 * (flatQ q k q : ℝ≥0∞) * ((Fintype.card Z : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) +
          ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
            (if ∀ m, m ∈ kemGood P hpk eG eKR i then 0 else 1) +
          ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
            (if Function.Injective (encOf (P.enc i.1.1) (kemTab hpk eG eKR i)) then 0 else 1)) := by
  rw [← prWinKEMHJ_eq_prWinKEMHq, ← prWinKEMHJ_eq_prWinKEMHq]
  exact qINDCCA_le_hopJDH P hpk eG eJ eKR eC eKa A

end KEMMerge

/-! ## Reprogramming the whole `G`-entry at the challenge point -/

section Locate

variable {m₁ m₂ n c a : ℕ} {PK SK M C R K Hash Z : Type} [Nonempty K] [DecidableEq C]
  [DecidableEq Hash] (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

/-- The key-and-coin table on the public-key slice of the hopped `G`-table,
updated at the challenge point by `u`: the table an oracle reprogrammed as in
`HopChallengeKey.kemOracleK` carries in `prWinKEMHq`. -/
def oracleTabHK (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq : C → K) (u : Fin n) : M → K × R :=
  fun m => eKR.symm (Function.update
    (keyHop (kemSlice hpk eG i.1.1) (kemEncAt P eG i.1.1) eKR.symm Hq i.2.2.2.2.1)
    (kemPt hpk eG i) u (eG (m, hpk i.1.1)))

/-- In `prWinKEMHq` with the whole `G`-entry at the challenge point replaced by
`u`, the decapsulation answer at the ciphertext of a message under the oracle's
coin, when that ciphertext is not the challenge ciphertext, is the oracle's key
at that message exactly when the message is not the challenge message or `Hq`
at that ciphertext equals the key of `u`. -/
theorem decapsHq_oracleTabHK_iff (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq : C → K) (u : Fin n)
    (m : M) (hne : P.enc i.1.1 m (oracleTabHK P hpk eG eKR i Hq u m).2 ≠ kemChal P hpk eG eKR i) :
    decapsHq eC eKa Hq (kemChal P hpk eG eKR i)
        (eC (P.enc i.1.1 m (oracleTabHK P hpk eG eKR i Hq u m).2)) =
        eKa (oracleTabHK P hpk eG eKR i Hq u m).1 ↔
      m ≠ i.2.2.1 ∨ Hq (P.enc i.1.1 i.2.2.1 (eKR.symm u).2) = (eKR.symm u).1 := by
  simp only [decapsHq, Equiv.symm_apply_apply, ite_eq_right hne, EmbeddingLike.apply_eq_iff_eq]
  by_cases hm : m = i.2.2.1
  · subst hm
    have ht : oracleTabHK P hpk eG eKR i Hq u i.2.2.1 = eKR.symm u := by
      simp [oracleTabHK, kemPt]
    rw [ht]
    simp
  · have hpt : eG (m, hpk i.1.1) ≠ kemPt hpk eG i := fun h =>
      hm (congrArg Prod.fst (eG.injective h))
    have hs : kemSlice hpk eG i.1.1 (eG (m, hpk i.1.1)) := by simp [kemSlice]
    have ht : oracleTabHK P hpk eG eKR i Hq u m =
        (Hq (P.enc i.1.1 m (eKR.symm (i.2.2.2.2.1 (eG (m, hpk i.1.1)))).2),
          (eKR.symm (i.2.2.2.2.1 (eG (m, hpk i.1.1)))).2) := by
      simp only [oracleTabHK, Function.update_of_ne hpt, keyHop, ite_eq_left hs,
        Equiv.symm_symm, coinCt, kemEncAt, Equiv.symm_apply_apply]
    rw [ht]
    exact iff_of_true rfl (Or.inl hm)

end Locate

end CatCrypt.Quantum.QROM
