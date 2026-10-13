/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.SearchOffChallenge
public import CatCryptCore.Quantum.QROM.QAdvGame
public import CatCryptCore.Quantum.QROM.HopDecapsSharp

/-!
# Distinguishing a uniform table from its resampling to good values

The step of Hofheinz–Hövelmanns–Kiltz (TCC 2017, §4.2) that replaces a random
oracle `G` by the oracle `G'` obtained by resampling every bad value of `G` to a
good one. The pair `(G, G')` is drawn with `pairMass`: `G` uniform and `G'` the
table `resampleTable bad a`. The two tables agree outside the bad set of `G`, so
one-way-to-hiding (`QAdvGame.o2h_avg`) bounds the distinguishing advantage of a
`q`-query adversary by the `Find` probability on the bad set. That probability
is at most `4 ∑ⱼ guessProb` against `G'` (`FindToGuess.prFind_le_four_sum_guess`),
and the resampling identity `sum_pairMass_resample` averages the guessing
probabilities to at most `4 q λ`.

## Main definitions

* `resampleAvg bad f` — the average of `f` at the resampled table
  `resampleTable bad a` under the pair weight `pairMass bad`
* `resampleGame bad adv` — the `QGame` over pairs of tables whose two oracles
  are the uniform table and its resampling

## Main results

* `prFindAvg_resampleGame_le` — the `Find` probability on the bad set, averaged
  over the pair weight, is at most `4 q λ`
* `absDiff_resample_le` — `|E_G Pr[out = 1 : adv G ^ G] − E_{G'} Pr[out = 1 :
  adv G' ^ G']| ≤ 4 (q · 4 q λ)^(1/2)` for an adversary family that reads the
  table only where the resampling leaves it unchanged
* `absDiff_resample_le_eight` — the same bound written as `8 q λ^(1/2)`
* `absDiff_resample_off_point` — the bound for an adversary family chosen from
  the value of the table at a point `t` that is exempted from the bad set
  (`SearchOffChallenge.offPoint`)

## The hypotheses

The adversary is a `q`-query `QAdv` against the table with a pure initial state
(`hpure`). The predicate `bad` has a good value at every point (`hgood`), and the
bad values at every point are at most a `λ` fraction of `Fin n` (`hlam`); in
`absDiff_resample_off_point` both hypotheses are required only away from `t`.

## References

* [Hofheinz, Hövelmanns, Kiltz — A Modular Analysis of the Fujisaki–Okamoto
  Transformation, TCC 2017], §4.2
* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], Theorems 1 and 2
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

section Resampled

variable {m n w q : ℕ} [NeZero n]

/-- The average of `f` at the resampled table under the pair weight. -/
def resampleAvg (bad : Fin m → Fin n → Bool) (f : (Fin m → Fin n) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ a : Fin m → Fin n × Fin n, pairMass bad a * f (resampleTable bad a)

omit [NeZero n] in
/-- The resampled table agrees with the first component outside the bad set of
    the first component. -/
theorem resampleTable_eq_of_not_mem_badSet (bad : Fin m → Fin n → Bool)
    (a : Fin m → Fin n × Fin n) (x : Fin m) (hx : x ∉ badSet bad fun x => (a x).1) :
    (a x).1 = resampleTable bad a x := by
  simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hx
  simp [resampleTable, hx]

/-- The pair weight sums to one. -/
theorem sum_pairMass (bad : Fin m → Fin n → Bool) (hgood : ∀ x, ∃ y, bad x y = false) :
    ∑ a : Fin m → Fin n × Fin n, pairMass bad a = 1 := by
  have h := sum_pairMass_fst hgood fun _ => (1 : ℝ≥0∞)
  simp only [mul_one] at h
  rw [h, Finset.sum_const, Finset.card_univ, Fintype.card_fun]
  simp only [Fintype.card_fin]
  rw [nsmul_eq_mul, Nat.cast_pow, ENNReal.mul_inv_cancel (pow_ne_zero _ (by exact_mod_cast NeZero.ne n))
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top n))]

/-- The one-way-to-hiding game over pairs of tables: the adversary
    `adv (fun x => (a x).1)` runs against the first component or against the
    resampled table, which agree outside the bad set of the first component. -/
def resampleGame (bad : Fin m → Fin n → Bool) (hgood : ∀ x, ∃ y, bad x y = false)
    (adv : (Fin m → Fin n) → QAdv m n w q)
    (hpure : ∀ H, ∃ ψ : Fin (m * n * w) → ℂ, (adv H).init.val = vecMulVec ψ (star ψ)) :
    QGame m n w q (Fin m → Fin n × Fin n) where
  sample := pairMass bad
  sample_sum := sum_pairMass bad hgood
  adv a := adv fun x => (a x).1
  oracle a := fun x => (a x).1
  oracle' a := resampleTable bad a
  S a := badSet bad fun x => (a x).1
  agree a x hx := resampleTable_eq_of_not_mem_badSet bad a x hx
  pure _ := hpure _

/-- The `Find` probability on the bad set, averaged over the pair weight, is at
    most `4 q λ`, when the adversary reads the table only where the resampling
    leaves it unchanged. -/
theorem prFindAvg_resampleGame_le (bad : Fin m → Fin n → Bool)
    (hgood : ∀ x, ∃ y, bad x y = false) (lam : ℝ≥0∞)
    (hlam : ∀ x, ((badVals bad x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam)
    (adv : (Fin m → Fin n) → QAdv m n w q)
    (hpure : ∀ H, ∃ ψ : Fin (m * n * w) → ℂ, (adv H).init.val = vecMulVec ψ (star ψ))
    (hadv : ∀ a : Fin m → Fin n × Fin n, adv (fun x => (a x).1) = adv (resampleTable bad a)) :
    prFindAvg (resampleGame bad hgood adv hpure) ≤ 4 * (q : ℝ≥0∞) * lam := by
  have key : ∀ a : Fin m → Fin n × Fin n,
      prFind (adv fun x => (a x).1) (fun x => (a x).1) (badSet bad fun x => (a x).1) ≤
        4 * ∑ j, ∑ x, (if bad x (a x).1 then 1 else 0) *
          guessProb (adv (resampleTable bad a)) (resampleTable bad a) {x} j := by
    intro a
    obtain ⟨ψ, hψ⟩ := hpure (resampleTable bad a)
    rw [hadv a, prFind_congr _ _ (resampleTable bad a) _
      (resampleTable_eq_of_not_mem_badSet bad a) hψ]
    refine (prFind_le_four_sum_guess _ _ _ hψ).trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [guessProb_eq_sum _ _ _ j hψ]
    simp only [badSet, Finset.sum_filter, boole_mul]
  have hcomm : ∀ F : (Fin m → Fin n × Fin n) → Fin q → Fin m → ℝ≥0∞,
      ∑ a, ∑ j, ∑ x, F a j x = ∑ j, ∑ x, ∑ a, F a j x := by
    intro F
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
  set g : (Fin m → Fin n) → Fin m → Fin q → ℝ≥0∞ := fun K x j => guessProb (adv K) K {x} j
  calc prFindAvg (resampleGame bad hgood adv hpure)
      = ∑ a : Fin m → Fin n × Fin n, pairMass bad a *
          prFind (adv fun x => (a x).1) (fun x => (a x).1) (badSet bad fun x => (a x).1) := rfl
    _ ≤ ∑ a : Fin m → Fin n × Fin n, pairMass bad a * (4 * ∑ j, ∑ x,
          (if bad x (a x).1 then 1 else 0) * g (resampleTable bad a) x j) :=
        Finset.sum_le_sum fun a _ => mul_le_mul' le_rfl (key a)
    _ = 4 * ∑ j, ∑ x, ∑ a : Fin m → Fin n × Fin n,
          pairMass bad a * (if bad x (a x).1 then 1 else 0) * g (resampleTable bad a) x j := by
        rw [← hcomm fun a j x => pairMass bad a * (if bad x (a x).1 then 1 else 0) *
          g (resampleTable bad a) x j, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [mul_left_comm]
        congr 1
        simp only [Finset.mul_sum, ← mul_assoc]
    _ = 4 * ∑ j, ∑ x, ((badVals bad x).card : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ *
          ∑ K, tableMass bad K * g K x j := by
        refine congrArg _ (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => ?_)
        exact sum_pairMass_resample hgood x fun K => g K x j
    _ ≤ 4 * ∑ _j : Fin q, lam * 1 := by
        gcongr with j _
        calc ∑ x, ((badVals bad x).card : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ * ∑ K, tableMass bad K * g K x j
            ≤ ∑ x, lam * ∑ K, tableMass bad K * g K x j := by
              gcongr with x _
              rw [← div_eq_mul_inv]
              exact hlam x
          _ = lam * ∑ K, tableMass bad K * ∑ x, g K x j := by
              rw [← Finset.mul_sum, Finset.sum_comm]
              refine congrArg _ (Finset.sum_congr rfl fun K _ => ?_)
              rw [Finset.mul_sum]
          _ ≤ lam * ∑ K : Fin m → Fin n, tableMass bad K * 1 := by
              gcongr with K _
              obtain ⟨ψ, hψ⟩ := hpure K
              exact sum_guessProb_singleton_le_one (adv K) K j hψ
          _ = lam * 1 := by simp only [mul_one, sum_tableMass hgood]
    _ = 4 * (q : ℝ≥0∞) * lam := by
        simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Distinguishing a uniform table from its resampling to good values
    (Hofheinz–Hövelmanns–Kiltz, TCC 2017, §4.2, with the semi-classical
    one-way-to-hiding of Ambainis–Hamburg–Unruh): for an adversary family that
    reads the table only where the resampling leaves it unchanged,
    `|E_G Pr[out = 1 : adv G ^ G] − E_{G'} Pr[out = 1 : adv G' ^ G']| ≤
    4 (q · 4 q λ)^(1/2)`. -/
theorem absDiff_resample_le (bad : Fin m → Fin n → Bool)
    (hgood : ∀ x, ∃ y, bad x y = false) (lam : ℝ≥0∞)
    (hlam : ∀ x, ((badVals bad x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam)
    (adv : (Fin m → Fin n) → QAdv m n w q)
    (hpure : ∀ H, ∃ ψ : Fin (m * n * w) → ℂ, (adv H).init.val = vecMulVec ψ (star ψ))
    (hadv : ∀ a : Fin m → Fin n × Fin n, adv (fun x => (a x).1) = adv (resampleTable bad a)) :
    absDiff (∑ H : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * prOut (adv H) H)
        (resampleAvg bad fun K => prOut (adv K) K) ≤
      4 * ((q : ℝ≥0∞) * (4 * (q : ℝ≥0∞) * lam)) ^ (1 / 2 : ℝ) := by
  set G := resampleGame bad hgood adv hpure
  have hL : ∑ H : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * prOut (adv H) H = prWin G :=
    (sum_pairMass_fst hgood fun H => prOut (adv H) H).symm
  have hR : resampleAvg bad (fun K => prOut (adv K) K) = prWin' G :=
    Finset.sum_congr rfl fun a _ => by
      simp only [G, resampleGame, hadv a]
  rw [hL, hR]
  refine (o2h_avg G).trans ?_
  gcongr
  exact prFindAvg_resampleGame_le bad hgood lam hlam adv hpure hadv

/-- `4 (q · 4 q λ)^(1/2) = 8 q λ^(1/2)`. -/
theorem four_mul_rpow_half_eq (q lam : ℝ≥0∞) :
    4 * (q * (4 * q * lam)) ^ (1 / 2 : ℝ) = 8 * q * lam ^ (1 / 2 : ℝ) := by
  have hsq : q * (4 * q * lam) = (2 * q) ^ (2 : ℝ) * lam := by
    rw [ENNReal.rpow_two]
    ring
  have h2q : ((2 * q) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = 2 * q := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hsq, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), h2q]
  ring

/-- `absDiff_resample_le` with the constant written as `8 q λ^(1/2)`. -/
theorem absDiff_resample_le_eight (bad : Fin m → Fin n → Bool)
    (hgood : ∀ x, ∃ y, bad x y = false) (lam : ℝ≥0∞)
    (hlam : ∀ x, ((badVals bad x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam)
    (adv : (Fin m → Fin n) → QAdv m n w q)
    (hpure : ∀ H, ∃ ψ : Fin (m * n * w) → ℂ, (adv H).init.val = vecMulVec ψ (star ψ))
    (hadv : ∀ a : Fin m → Fin n × Fin n, adv (fun x => (a x).1) = adv (resampleTable bad a)) :
    absDiff (∑ H : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * prOut (adv H) H)
        (resampleAvg bad fun K => prOut (adv K) K) ≤
      8 * (q : ℝ≥0∞) * lam ^ (1 / 2 : ℝ) := by
  rw [← four_mul_rpow_half_eq]
  exact absDiff_resample_le bad hgood lam hlam adv hpure hadv

omit [NeZero n] in
/-- The resampling of `offPoint bad t` leaves the entry at `t` unchanged. -/
theorem resampleTable_offPoint_self (bad : Fin m → Fin n → Bool) (t : Fin m)
    (a : Fin m → Fin n × Fin n) : resampleTable (offPoint bad t) a t = (a t).1 := by
  simp [resampleTable]

/-- Distinguishing away from a point: for an adversary family `A` chosen from
    the value of the table at `t`, with `t` exempted from resampling,
    `|E_G Pr[out = 1 : A (G t) ^ G] − E_{G'} Pr[out = 1 : A (G' t) ^ G']| ≤
    8 q λ^(1/2)`, where `λ` bounds the fraction of bad values at every `x ≠ t`. -/
theorem absDiff_resample_off_point (bad : Fin m → Fin n → Bool) (t : Fin m)
    (A : Fin n → QAdv m n w q) (lam : ℝ≥0∞)
    (hgood : ∀ x, x ≠ t → ∃ y, bad x y = false)
    (hlam : ∀ x, x ≠ t → ((badVals bad x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam)
    (hpure : ∀ u, ∃ ψ : Fin (m * n * w) → ℂ, (A u).init.val = vecMulVec ψ (star ψ)) :
    absDiff (∑ H : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * prOut (A (H t)) H)
        (resampleAvg (offPoint bad t) fun K => prOut (A (K t)) K) ≤
      8 * (q : ℝ≥0∞) * lam ^ (1 / 2 : ℝ) :=
  absDiff_resample_le_eight (offPoint bad t) (offPoint_good t hgood) lam
    (card_badVals_offPoint_le t lam hlam) (fun K => A (K t)) (fun K => hpure (K t))
    (fun a => by simp only [resampleTable_offPoint_self])

end Resampled

/-! ## The decapsulation and injectivity costs with the challenge message exempted -/

section ChallengeExempt

variable {m₁ m₂ n c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype M] [DecidableEq M]
  [DecidableEq C] [Nonempty K] (P : Scheme PK SK M C R) (hpk : PK → Hash)
  (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n)
  (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

omit [Nonempty K] in
/-- When every message other than the challenge message is good, the only
    possible bad ciphertext is the challenge ciphertext. -/
theorem badCts_subset_kemChal (i : KEMInput PK SK Z M K m₁ m₂ n)
    (h : ∀ m, m ≠ i.2.2.1 → m ∈ kemGood P hpk eG eKR i) :
    badCts P hpk eG eKR i ⊆ {kemChal P hpk eG eKR i} := by
  intro c' hc
  obtain ⟨m, hm, rfl⟩ := (mem_badImage_iff _ _ _ c').1 hc
  have hm' : m = i.2.2.1 := by
    by_contra hne
    exact hm (h m hne)
  rw [hm', Finset.mem_singleton]
  rfl

/-- When every message other than the challenge message is good, the simulated
    and the real classical functions of the decapsulation rounds coincide. -/
theorem decapsSim_eq_of_good_off_chal (i : KEMInput PK SK Z M K m₁ m₂ n)
    (h : ∀ m, m ≠ i.2.2.1 → m ∈ kemGood P hpk eG eKR i) :
    decapsSim P hpk eG eJ eKR eC eKa i = kemDecaps P hpk eG eJ eKR eC eKa i := by
  funext x
  by_cases hc : eC.symm x = kemChal P hpk eG eKR i
  · simp only [decapsSim, kemDecaps, decapsOracle, if_pos hc]
  · exact decapsSim_apply_eq_of_not_mem P hpk eG eJ eKR eC eKa i x fun hx =>
      hc (Finset.mem_singleton.1 (badCts_subset_kemChal P hpk eG eKR i h hx))

omit [DecidableEq C] [Nonempty K] in
/-- When every message other than the challenge message is good, the ciphertext
    map is injective away from the challenge message. -/
theorem encOf_injOn_ne_chal (i : KEMInput PK SK Z M K m₁ m₂ n)
    (h : ∀ m, m ≠ i.2.2.1 → m ∈ kemGood P hpk eG eKR i) :
    Set.InjOn (encOf (P.enc i.1.1) (kemTab hpk eG eKR i)) {m | m ≠ i.2.2.1} :=
  (encOf_injOn_good (P.enc i.1.1) (P.dec i.1.2) (kemTab hpk eG eKR i)).mono fun m hm => h m hm

end ChallengeExempt

end CatCrypt.Quantum.QROM

end

end
