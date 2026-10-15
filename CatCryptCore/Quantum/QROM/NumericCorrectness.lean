/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.ResampleKeyHop
public import CatCryptCore.Quantum.QROM.HopDecapsNumericClose
public import CatCryptCore.Quantum.QROM.HopCoinChallenge

/-!
# The composite KEM hop through a table resampled to good values

The game `prWinKEM'` (the IND-CCA game after the rejection-prefix hop) and the
game `prWinKEMHq` (decapsulation answered by an independent table `Hq`) are
compared through the `G`-table resampled to good values with the challenge
point exempted (`restBad`):

`|P_real − P_Hq| ≤ |P_real(G) − P_real(G')| + |P_real(G') − P_Hq(G')| + |P_Hq(G') − P_Hq(G)|`.

On the resampled table every message other than the challenge message decrypts
correctly, so real and simulated decapsulation coincide there; the
key-from-ciphertext relabelling costs `δ*`; the rejection row averages out. The
game `prWinKEMHq` reads the `G`-table only through the adversary's oracle, which
is a pointwise function of the table, so its distance between the uniform and
the resampled table is bounded by one-way-to-hiding. The game `prWinKEM'` also
reads the table through real decapsulation; with each decapsulation round
compiled into four oracle queries (`prOutMR_eq_compiledMRH`) and the chain
flattened, it is again an adversary against a pointwise function of the table.

## Main definitions

* `winReal A b i` — the winning probability at an input of the game
  `prWinKEM'`, averaged over the reprogramming table `T`
* `castMR h A` — a multi-round adversary transported along an equality of
  work-register sizes

## Main results

* `absDiff_resample_map_le`, `absDiff_resample_map_off_point` — the
  distinguishing bound `8 q λ^(1/2)` between a uniform and a resampled table for
  an adversary against an oracle that is a pointwise function of the table
* `resampleAvg_winReal_eq_winSimJ` — on the resampled table real and simulated
  decapsulation give the same winning probability
* `sum_restWeight_resampleAvg_winHJ_eq_winHq` — the resampled averages of the
  games `prWinKEMHJ` and `prWinKEMHq` agree once the `J`-table is summed
* `absDiff_prWinKEM'_prWinKEMHq_triangle` — the triangle, with middle term the
  average of `δ*`
* `absDiff_resample_winHq_le` — the right outer term at a fixed rest is at most
  `8 q' λ^(1/2)`, with `q' = flatQ q k q`
* `prTrue_mrChain_eq_prOut_flatten` — the multi-round chain of a head-tail
  adversary accepts with the output probability of its flattening
* `absDiff_winReal_resample_le` — the left outer term at a fixed rest is at most
  `8 q'' λ^(1/2)`, with `q'' = flatQ (q + 4) k q`
* `absDiff_sum_ite_triangle_le`, `absDiff_prWinKEM'_prWinKEMHq_triangle_coinGood` —
  the triangle with the table resampled only at the key pairs that are `CoinGood`
* `absDiff_prWinKEM'_prWinKEMHq_le_of_lam` —
  `|prWinKEM' − prWinKEMHq| ≤ 8 q'' Λ^(1/2) + Λ + 8 q' Λ^(1/2)`, with `Λ` the
  average over key generation of a per-key bound `λ` on the decryption-failure
  fraction of every message

## The hypotheses

`absDiff_winReal_resample_le` takes the adversary's decapsulation rounds in the
compiled form of `Quantum/QROM/HopDecapsNumericClose.lean`: work register
`w₀ * ancDim (m₁ + m₂) n c`, every round `permRound`, segment unitaries commuting
with `cleanProjM`, and an initial state supported by `cleanProjM`. The per-rest
lemmas take a key pair that has, for each message, a coin that decrypts
correctly (`CoinGood`); `absDiff_prWinKEM'_prWinKEMHq_le_of_lam` has no such
hypothesis, since a key pair that is not `CoinGood` has `λ ≥ 1` under `hlam`
(`one_le_of_not_coinGood`).

The terms `8 q'' Λ^(1/2) + Λ + 8 q' Λ^(1/2)` are numeric once `λ` is
instantiated: `Λ` is the expectation over key generation of the worst-case
per-message decryption-failure probability, the δ-correctness figure of the
Fujisaki–Okamoto analysis.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Resampling under an oracle that is a pointwise function of the table -/

section MapResample

variable {m m' n w q : ℕ} [NeZero n]

/-- Distinguishing a uniform table from its resampling to good values when the
adversary queries an oracle `Φ G` whose value at `y` reads the table only at the
preimages of `y` under an embedding `ι`: the bound is `8 q λ^(1/2)`.

References: Hofheinz, Hövelmanns, Kiltz, "A modular analysis of the
Fujisaki-Okamoto transformation", TCC 2017, ePrint 2017/604 (the `√δ`
correctness loss of the T transform); Hövelmanns, Hülsing, Majenz, "Failing
gracefully: decryption failures and the Fujisaki-Okamoto transform", ASIACRYPT
2022, ePrint 2022/365 (the adversary's search for failing ciphertexts). -/
theorem absDiff_resample_map_le (bad : Fin m → Fin n → Bool)
    (hgood : ∀ x, ∃ y, bad x y = false) (lam : ℝ≥0∞)
    (hlam : ∀ x, ((badVals bad x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam)
    (ι : Fin m ↪ Fin m') (Φ : (Fin m → Fin n) → Fin m' → Fin n)
    (hΦ : ∀ (G G' : Fin m → Fin n) (y : Fin m'), (∀ x, ι x = y → G x = G' x) → Φ G y = Φ G' y)
    (adv : (Fin m → Fin n) → QAdv m' n w q)
    (hpure : ∀ H, ∃ ψ : Fin (m' * n * w) → ℂ, (adv H).init.val = vecMulVec ψ (star ψ))
    (hadv : ∀ a : Fin m → Fin n × Fin n, adv (fun x => (a x).1) = adv (resampleTable bad a)) :
    absDiff (∑ H : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * prOut (adv H) (Φ H))
        (resampleAvg bad fun K => prOut (adv K) (Φ K)) ≤
      8 * (q : ℝ≥0∞) * lam ^ (1 / 2 : ℝ) := by
  have hagree : ∀ (a : Fin m → Fin n × Fin n) (y : Fin m'),
      y ∉ (badSet bad fun x => (a x).1).map ι →
        Φ (fun x => (a x).1) y = Φ (resampleTable bad a) y := fun a y hy =>
    hΦ _ _ y fun x hx => resampleTable_eq_of_not_mem_badSet bad a x fun hm =>
      hy (hx ▸ Finset.mem_map_of_mem ι hm)
  let Gm : QGame m' n w q (Fin m → Fin n × Fin n) :=
    { sample := pairMass bad
      sample_sum := sum_pairMass bad hgood
      adv := fun a => adv fun x => (a x).1
      oracle := fun a => Φ fun x => (a x).1
      oracle' := fun a => Φ (resampleTable bad a)
      S := fun a => (badSet bad fun x => (a x).1).map ι
      agree := hagree
      pure := fun _ => hpure _ }
  have hL : ∑ H : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * prOut (adv H) (Φ H) = prWin Gm :=
    (sum_pairMass_fst hgood fun H => prOut (adv H) (Φ H)).symm
  have hR : resampleAvg bad (fun K => prOut (adv K) (Φ K)) = prWin' Gm :=
    Finset.sum_congr rfl fun a _ => by simp only [Gm, hadv a]
  set g : (Fin m → Fin n) → Fin m → Fin q → ℝ≥0∞ := fun K x j =>
    guessProb (adv K) (Φ K) {ι x} j
  have key : ∀ a : Fin m → Fin n × Fin n,
      prFind (adv fun x => (a x).1) (Φ fun x => (a x).1) ((badSet bad fun x => (a x).1).map ι) ≤
        4 * ∑ j, ∑ x, (if bad x (a x).1 then 1 else 0) * g (resampleTable bad a) x j := by
    intro a
    obtain ⟨ψ, hψ⟩ := hpure (resampleTable bad a)
    rw [hadv a, prFind_congr _ _ (Φ (resampleTable bad a)) _ (hagree a) hψ]
    refine (prFind_le_four_sum_guess _ _ _ hψ).trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [guessProb_eq_sum _ _ _ j hψ, Finset.sum_map]
    simp only [g, badSet, Finset.sum_filter, boole_mul]
  have hcomm : ∀ F : (Fin m → Fin n × Fin n) → Fin q → Fin m → ℝ≥0∞,
      ∑ a, ∑ j, ∑ x, F a j x = ∑ j, ∑ x, ∑ a, F a j x := by
    intro F
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
  have hfind : prFindAvg Gm ≤ 4 * (q : ℝ≥0∞) * lam := by
    calc prFindAvg Gm
        = ∑ a : Fin m → Fin n × Fin n, pairMass bad a *
            prFind (adv fun x => (a x).1) (Φ fun x => (a x).1)
              ((badSet bad fun x => (a x).1).map ι) := rfl
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
                calc ∑ x, g K x j = ∑ y ∈ Finset.univ.map ι, guessProb (adv K) (Φ K) {y} j := by
                      rw [Finset.sum_map]
                  _ ≤ ∑ y, guessProb (adv K) (Φ K) {y} j :=
                      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
                  _ ≤ 1 := sum_guessProb_singleton_le_one (adv K) (Φ K) j hψ
            _ = lam * 1 := by simp only [mul_one, sum_tableMass hgood]
      _ = 4 * (q : ℝ≥0∞) * lam := by
          simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  rw [hL, hR, ← four_mul_rpow_half_eq]
  refine (o2h_avg Gm).trans ?_
  gcongr

/-- `absDiff_resample_map_le` for an adversary family chosen from the value of
the table at a point `t` exempted from the bad set. -/
theorem absDiff_resample_map_off_point (bad : Fin m → Fin n → Bool) (t : Fin m)
    (A : Fin n → QAdv m' n w q) (lam : ℝ≥0∞)
    (hgood : ∀ x, x ≠ t → ∃ y, bad x y = false)
    (hlam : ∀ x, x ≠ t → ((badVals bad x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam)
    (ι : Fin m ↪ Fin m') (Φ : (Fin m → Fin n) → Fin m' → Fin n)
    (hΦ : ∀ (G G' : Fin m → Fin n) (y : Fin m'), (∀ x, ι x = y → G x = G' x) → Φ G y = Φ G' y)
    (hpure : ∀ u, ∃ ψ : Fin (m' * n * w) → ℂ, (A u).init.val = vecMulVec ψ (star ψ)) :
    absDiff (∑ H : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * prOut (A (H t)) (Φ H))
        (resampleAvg (offPoint bad t) fun K => prOut (A (K t)) (Φ K)) ≤
      8 * (q : ℝ≥0∞) * lam ^ (1 / 2 : ℝ) :=
  absDiff_resample_map_le (offPoint bad t) (offPoint_good t hgood) lam
    (card_badVals_offPoint_le t lam hlam) ι Φ hΦ (fun K => A (K t)) (fun K => hpure (K t))
    (fun a => by simp only [resampleTable_offPoint_self])

omit [NeZero n] in
/-- A resampled average of a convex combination is the convex combination of the
resampled averages. -/
theorem resampleAvg_sum_mul {ι : Type} [Fintype ι] (bad : Fin m → Fin n → Bool)
    (p : ι → ℝ≥0∞) (X : ι → (Fin m → Fin n) → ℝ≥0∞) :
    resampleAvg bad (fun G => ∑ i, p i * X i G) = ∑ i, p i * resampleAvg bad (X i) := by
  unfold resampleAvg
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring

omit [NeZero n] in
/-- A distance bound between the uniform and the resampled average that holds
for every component of a convex combination holds for the combination. -/
theorem absDiff_resampleAvg_avg_le {ι : Type} [Fintype ι] (bad : Fin m → Fin n → Bool)
    (p : ι → ℝ≥0∞) (hp : ∑ i, p i = 1) (X : ι → (Fin m → Fin n) → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ i, absDiff (resampleAvg bad (X i))
      (∑ G : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * X i G) ≤ c) :
    absDiff (resampleAvg bad fun G => ∑ i, p i * X i G)
      (∑ G : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * ∑ i, p i * X i G) ≤ c := by
  have hU : ∑ G : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * ∑ i, p i * X i G =
      ∑ i, p i * ∑ G : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * X i G := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun G _ => by ring
  rw [resampleAvg_sum_mul, hU]
  refine (absDiff_sum_le _ _).trans ?_
  calc _ ≤ ∑ i, p i * c := Finset.sum_le_sum fun i _ =>
        (absDiff_mul_left_le _ _ _).trans (mul_le_mul' le_rfl (h i))
    _ = c := by rw [← Finset.sum_mul, hp, one_mul]

end MapResample

/-! ## A triangle that resamples on a subset of the indices -/

section SubsetTriangle

variable {ι : Type} [Fintype ι]

/-- A triangle between two weighted sums `∑ w X` and `∑ w Y` through the
intermediate values `RX`, `RY` taken only at the indices satisfying `p`: where
`p` holds, the `w`-weighted `RX` and `SJ` sums, and the `RY` and `HJ` sums,
agree, and `SJ` and `HJ` differ by at most `δ`; where `p` fails, `X` and `Y`
differ by at most one. -/
theorem absDiff_sum_ite_triangle_le (p : ι → Prop) [DecidablePred p]
    (w X Y RX RY SJ HJ δ : ι → ℝ≥0∞)
    (hX : ∑ i, w i * (if p i then RX i else 0) = ∑ i, w i * (if p i then SJ i else 0))
    (hY : ∑ i, w i * (if p i then RY i else 0) = ∑ i, w i * (if p i then HJ i else 0))
    (hSH : ∀ i, p i → absDiff (SJ i) (HJ i) ≤ δ i)
    (hXY : ∀ i, ¬ p i → absDiff (X i) (Y i) ≤ 1) :
    absDiff (∑ i, w i * X i) (∑ i, w i * Y i) ≤
      ∑ i, w i * (if p i then absDiff (X i) (RX i) else 0) +
        ∑ i, w i * (if p i then δ i else 1) +
        ∑ i, w i * (if p i then absDiff (RY i) (Y i) else 0) := by
  have houter : ∀ U V : ι → ℝ≥0∞,
      absDiff (∑ i, w i * U i) (∑ i, w i * V i) ≤ ∑ i, w i * absDiff (U i) (V i) := fun U V =>
    (absDiff_sum_le _ _).trans (Finset.sum_le_sum fun i _ => absDiff_mul_left_le _ _ _)
  have hsplit : ∀ U V : ι → ℝ≥0∞, ∑ i, w i * (if p i then U i else V i) =
      ∑ i, w i * (if p i then U i else 0) + ∑ i, w i * (if p i then 0 else V i) := by
    intro U V
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have hL : absDiff (∑ i, w i * X i) (∑ i, w i * (if p i then RX i else X i)) ≤
      ∑ i, w i * (if p i then absDiff (X i) (RX i) else 0) :=
    (houter _ _).trans (Finset.sum_le_sum fun i _ => by split_ifs <;> simp [absDiff_self])
  have hR : absDiff (∑ i, w i * (if p i then RY i else Y i)) (∑ i, w i * Y i) ≤
      ∑ i, w i * (if p i then absDiff (RY i) (Y i) else 0) :=
    (houter _ _).trans (Finset.sum_le_sum fun i _ => by split_ifs <;> simp [absDiff_self])
  have hM : absDiff (∑ i, w i * (if p i then RX i else X i))
      (∑ i, w i * (if p i then RY i else Y i)) ≤ ∑ i, w i * (if p i then δ i else 1) := by
    rw [hsplit RX X, hsplit RY Y, hX, hY, ← hsplit, ← hsplit]
    refine (houter _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    by_cases hp : p i
    · simp only [if_pos hp]
      exact mul_le_mul_right (hSH i hp) _
    · simp only [if_neg hp]
      exact mul_le_mul_right (hXY i hp) _
  refine (absDiff_triangle _ (∑ i, w i * (if p i then RX i else X i)) _).trans ?_
  refine (add_le_add le_rfl (absDiff_triangle _ (∑ i, w i * (if p i then RY i else Y i))
    _)).trans ?_
  rw [← add_assoc]
  exact add_le_add (add_le_add hL hM) hR

end SubsetTriangle

/-! ## The triangle around the composite KEM hop -/

section KEMTriangle

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c]

/-- The winning probability at an input of the game `prWinKEM'`, averaged over
the table `T` that reprograms the prefix `z`. -/
def winReal (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (i : KEMInput PK SK Z M K m₁ m₂ n) : ℝ≥0∞ :=
  ∑ T : C → Fin n, tabWeight n C *
    prOutMR (A.run i.1.1 (kemChal P hpk eG eKR i) (kemKey hpk eG eKR i b)) (kemOracle' eJ i T)
      (kemDecaps P hpk eG eJ eKR eC eKa i)

omit [Nonempty M] [Nonempty Z] [Fintype R] [Nonempty R] [DecidableEq Hash] [DecidableEq M]
  [NeZero c] in
theorem prWinKEM'_eq_sum_winReal (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    prWinKEM' P hpk eG eJ eKR eC eKa A b =
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * winReal P hpk eG eJ eKR eC eKa A b i := by
  unfold prWinKEM' winReal
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun T _ => by ring

omit [Fintype PK] [Fintype SK] [Nonempty M] [Fintype Z] [Nonempty Z] [Fintype K]
  [Fintype R] [Nonempty R] [NeZero c] in
/-- On the table resampled off the challenge point the real and the simulated
decapsulation give the same winning probability. -/
theorem resampleAvg_winReal_eq_winSimJ (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (r : KEMRest PK SK Z M K m₂ n)
    (hcoin : ∀ m, ∃ ρ, P.dec r.1.2 (P.enc r.1.1 m ρ) = some m) :
    (resampleAvg (restBad P hpk eG eKR r) fun G =>
        winReal P hpk eG eJ eKR eC eKa A b (kemJoin r G)) =
      resampleAvg (restBad P hpk eG eKR r) fun G =>
        winSimJ P hpk eG eJ eKR eC eKa A b (kemJoin r G) := by
  have hgood : ∀ x, ∃ y, restBad P hpk eG eKR r x y = false :=
    offPoint_good _ fun x _ => kemBad_good P hpk eG eKR hcoin x
  rw [resampleAvg_eq_sum_tableMass hgood, resampleAvg_eq_sum_tableMass hgood]
  refine Finset.sum_congr rfl fun G _ => ?_
  by_cases hz : tableMass (restBad P hpk eG eKR r) G = 0
  · simp [hz]
  have hG : ∀ x, restBad P hpk eG eKR r x (G x) = false := by
    intro x
    have hx := Finset.prod_ne_zero_iff.mp hz x (Finset.mem_univ x)
    by_contra hb
    simp [goodMass, hb] at hx
  have hm : ∀ m, m ≠ (kemJoin (m₁ := m₁) r G).2.2.1 →
      m ∈ kemGood P hpk eG eKR (kemJoin r G) := by
    intro m hm
    have hx : eG (m, hpk r.1.1) ≠ eG (r.2.2.1, hpk r.1.1) := fun h =>
      hm (congrArg Prod.fst (eG.injective h))
    have h1 := hG (eG (m, hpk r.1.1))
    rw [restBad, offPoint_of_ne hx] at h1
    have h2 := dec_of_kemBad_eq_false P hpk eG eKR (by simp) h1
    simp only [Equiv.symm_apply_apply] at h2
    rw [kemGood, mem_good_iff]
    exact h2
  unfold winReal winSimJ
  rw [decapsSim_eq_of_good_off_chal P hpk eG eJ eKR eC eKa (kemJoin r G) hm]

omit [Nonempty M] [Nonempty Z] [Nonempty R] [NeZero c] in
/-- The `kemRestWeight`-average, scaled by a function `g` of the key pair, of the
resampled averages of `winHJ` and of `winHq` agree: the weight, `g` and the bad
predicate do not read the `J`-table, and the sums over the `J`-table agree by
`sum_J_winHJ_eq_winHq`. -/
theorem sum_restWeight_mul_resampleAvg_winHJ_eq_winHq (A : KEMQAdv m₁ m₂ n w q k c a PK C K)
    (b : Bool) (g : PK × SK → ℝ≥0∞) :
    ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r * (g r.1 *
        resampleAvg (restBad P hpk eG eKR r)
          (fun G => winHJ P hpk eG eJ eKR eC eKa A b (kemJoin r G))) =
      ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r * (g r.1 *
        resampleAvg (restBad P hpk eG eKR r)
          (fun G => winHq P hpk eG eJ eKR eC eKa A b (kemJoin r G))) := by
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun pk _ => Finset.sum_congr rfl fun sk _ =>
    Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun ms _ =>
    Finset.sum_congr rfl fun kf _ => ?_
  simp only [mul_left_comm (kemRestWeight P _) (g _)]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  refine congrArg (g (pk, sk) * ·) ?_
  let J₀ : Fin m₂ → Fin n := fun _ => 0
  have hsplit : ∀ F : (Fin m₂ → Fin n) → (Fin m₁ → Fin n) → ℝ≥0∞,
      ∑ J : Fin m₂ → Fin n, kemRestWeight P ((pk, sk), z, ms, kf, J) *
          resampleAvg (restBad P hpk eG eKR ((pk, sk), z, ms, kf, J)) (F J) =
        kemRestWeight P ((pk, sk), z, ms, kf, J₀) *
          resampleAvg (restBad P hpk eG eKR ((pk, sk), z, ms, kf, J₀))
            (fun G => ∑ J, F J G) := by
    intro F
    unfold resampleAvg
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    rfl
  refine (hsplit fun J G => winHJ P hpk eG eJ eKR eC eKa A b ((pk, sk), z, ms, kf, G, J)).trans
    (Eq.trans ?_ (hsplit fun J G => winHq P hpk eG eJ eKR eC eKa A b
      ((pk, sk), z, ms, kf, G, J)).symm)
  exact congrArg (fun f => kemRestWeight P ((pk, sk), z, ms, kf, J₀) *
      resampleAvg (restBad P hpk eG eKR ((pk, sk), z, ms, kf, J₀)) f)
    (funext fun G => sum_J_winHJ_eq_winHq P hpk eG eJ eKR eC eKa A b (pk, sk) z ms kf G)

omit [Nonempty M] [Nonempty Z] [Nonempty R] [NeZero c] in
/-- The `kemRestWeight`-average of the resampled averages of `winHJ` and of
`winHq` agree. -/
theorem sum_restWeight_resampleAvg_winHJ_eq_winHq (A : KEMQAdv m₁ m₂ n w q k c a PK C K)
    (b : Bool) :
    ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
        resampleAvg (restBad P hpk eG eKR r)
          (fun G => winHJ P hpk eG eJ eKR eC eKa A b (kemJoin r G)) =
      ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
        resampleAvg (restBad P hpk eG eKR r)
          (fun G => winHq P hpk eG eJ eKR eC eKa A b (kemJoin r G)) := by
  simpa only [one_mul] using
    sum_restWeight_mul_resampleAvg_winHJ_eq_winHq P hpk eG eJ eKR eC eKa A b (fun _ => 1)

omit [Nonempty M] [Nonempty Z] [Nonempty R] [NeZero c] in
/-- The triangle around the composite hop `prWinKEM' → prWinKEMHq` through the
table resampled off the challenge point: the distance is at most the
`kemRestWeight`-average of the distance between the uniform and the resampled
table in `prWinKEM'`, of `δ*`, and of the distance between the resampled and the
uniform table in `prWinKEMHq`. The coin hypothesis is required at the key pairs
in the support of `keygen`. -/
theorem absDiff_prWinKEM'_prWinKEMHq_triangle (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (hcoin : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ m, ∃ ρ, P.dec sk (P.enc pk m ρ) = some m) :
    absDiff (prWinKEM' P hpk eG eJ eKR eC eKa A b) (prWinKEMHq P hpk eG eJ eKR eC eKa A b) ≤
      ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
          absDiff (∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
              winReal P hpk eG eJ eKR eC eKa A b (kemJoin r G))
            (resampleAvg (restBad P hpk eG eKR r) fun G =>
              winReal P hpk eG eJ eKR eC eKa A b (kemJoin r G)) +
        ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r * restDelta P hpk eG eKR r +
        ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
          absDiff (resampleAvg (restBad P hpk eG eKR r) fun G =>
              winHq P hpk eG eJ eKR eC eKa A b (kemJoin r G))
            (∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
              winHq P hpk eG eJ eKR eC eKa A b (kemJoin r G)) := by
  rw [prWinKEM'_eq_sum_winReal, prWinKEMHq_eq_sum_winHq, sum_kemSample_kemJoin,
    sum_kemSample_kemJoin]
  have houter : ∀ X Y : KEMRest PK SK Z M K m₂ n → ℝ≥0∞,
      absDiff (∑ r, kemRestWeight P r * X r) (∑ r, kemRestWeight P r * Y r) ≤
        ∑ r, kemRestWeight P r * absDiff (X r) (Y r) := fun X Y =>
    (absDiff_sum_le _ _).trans (Finset.sum_le_sum fun r _ => absDiff_mul_left_le _ _ _)
  have hRr : ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
      resampleAvg (restBad P hpk eG eKR r)
        (fun G => winReal P hpk eG eJ eKR eC eKa A b (kemJoin r G)) =
      ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
        resampleAvg (restBad P hpk eG eKR r)
          (fun G => winSimJ P hpk eG eJ eKR eC eKa A b (kemJoin r G)) :=
    Finset.sum_congr rfl fun r _ => by
      by_cases hk : P.keygen r.1 = 0
      · simp [kemRestWeight, hk]
      · rw [resampleAvg_winReal_eq_winSimJ P hpk eG eJ eKR eC eKa A b r (hcoin r.1.1 r.1.2 hk)]
  have hmid : absDiff (∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
      resampleAvg (restBad P hpk eG eKR r)
        (fun G => winReal P hpk eG eJ eKR eC eKa A b (kemJoin r G)))
      (∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
        resampleAvg (restBad P hpk eG eKR r)
          (fun G => winHq P hpk eG eJ eKR eC eKa A b (kemJoin r G))) ≤
      ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r * restDelta P hpk eG eKR r := by
    rw [hRr, ← sum_restWeight_resampleAvg_winHJ_eq_winHq]
    refine (houter _ _).trans (Finset.sum_le_sum fun r _ => ?_)
    by_cases hk : P.keygen r.1 = 0
    · simp [kemRestWeight, hk]
    · gcongr
      exact absDiff_winSimJ_winHJ_resampled P hpk eG eJ eKR eC eKa A b r (hcoin r.1.1 r.1.2 hk)
  refine (absDiff_triangle _ (∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
      resampleAvg (restBad P hpk eG eKR r)
        (fun G => winReal P hpk eG eJ eKR eC eKa A b (kemJoin r G))) _).trans ?_
  refine (add_le_add le_rfl (absDiff_triangle _ (∑ r : KEMRest PK SK Z M K m₂ n,
      kemRestWeight P r * resampleAvg (restBad P hpk eG eKR r)
        (fun G => winHq P hpk eG eJ eKR eC eKa A b (kemJoin r G))) _)).trans ?_
  rw [← add_assoc]
  exact add_le_add (add_le_add (houter _ _) hmid) (houter _ _)

omit [Fintype PK] [Fintype SK] [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z]
  [Fintype R] [Nonempty R] [NeZero c] in
/-- The uniform `G`-averages of `winReal` and of `winHq` at a rest differ by at
most one. -/
theorem absDiff_avg_winReal_avg_winHq_le_one (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (r : KEMRest PK SK Z M K m₂ n) :
    absDiff (∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
        winReal P hpk eG eJ eKR eC eKa A b (kemJoin r G))
      (∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
        winHq P hpk eG eJ eKR eC eKa A b (kemJoin r G)) ≤ 1 := by
  have hu : ∑ _G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ]
    simp only [Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
    exact ENNReal.mul_inv_cancel (pow_ne_zero _ (by exact_mod_cast NeZero.ne n))
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top n))
  have hT : ∀ f : (C → Fin n) → ℝ≥0∞, (∀ T, f T ≤ 1) → ∑ T : C → Fin n, tabWeight n C * f T ≤ 1 :=
    fun f hf => (Finset.sum_le_sum fun T _ => mul_le_of_le_one_right' (hf T)).trans
      (le_of_eq (sum_tabWeight n C))
  have hX : ∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
      winReal P hpk eG eJ eKR eC eKa A b (kemJoin r G) ≤ 1 :=
    (Finset.sum_le_sum fun G _ => mul_le_of_le_one_right'
      (hT _ fun T => prOutMR_le_one _ _ _)).trans (le_of_eq hu)
  have hY : ∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
      winHq P hpk eG eJ eKR eC eKa A b (kemJoin r G) ≤ 1 :=
    (Finset.sum_le_sum fun G _ => mul_le_of_le_one_right'
      ((Finset.sum_le_sum fun Hq _ => mul_le_of_le_one_right'
        (hT _ fun T => prOutMR_le_one _ _ _)).trans
        (le_of_eq (sum_inv_card (C → K))))).trans (le_of_eq hu)
  exact absDiff_le_iff.mpr ⟨hX.trans le_add_self, hY.trans le_add_self⟩

omit [Nonempty M] [Nonempty Z] [Nonempty R] [NeZero c] in
open scoped Classical in
/-- The triangle around the composite hop `prWinKEM' → prWinKEMHq` with the
`G`-table resampled at the key pairs that are `CoinGood` only: there the three
terms of `absDiff_prWinKEM'_prWinKEMHq_triangle`; at the other key pairs the two
games differ by at most one at each rest. No coin hypothesis is required. -/
theorem absDiff_prWinKEM'_prWinKEMHq_triangle_coinGood (A : KEMQAdv m₁ m₂ n w q k c a PK C K)
    (b : Bool) :
    absDiff (prWinKEM' P hpk eG eJ eKR eC eKa A b) (prWinKEMHq P hpk eG eJ eKR eC eKa A b) ≤
      ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
          (if CoinGood P r.1 then
            absDiff (∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
                winReal P hpk eG eJ eKR eC eKa A b (kemJoin r G))
              (resampleAvg (restBad P hpk eG eKR r) fun G =>
                winReal P hpk eG eJ eKR eC eKa A b (kemJoin r G))
          else 0) +
        ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
          (if CoinGood P r.1 then restDelta P hpk eG eKR r else 1) +
        ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
          (if CoinGood P r.1 then
            absDiff (resampleAvg (restBad P hpk eG eKR r) fun G =>
                winHq P hpk eG eJ eKR eC eKa A b (kemJoin r G))
              (∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
                winHq P hpk eG eJ eKR eC eKa A b (kemJoin r G))
          else 0) := by
  rw [prWinKEM'_eq_sum_winReal, prWinKEMHq_eq_sum_winHq, sum_kemSample_kemJoin,
    sum_kemSample_kemJoin]
  refine absDiff_sum_ite_triangle_le (fun r => CoinGood P r.1) (kemRestWeight P)
    (fun r => ∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
      winReal P hpk eG eJ eKR eC eKa A b (kemJoin r G))
    (fun r => ∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
      winHq P hpk eG eJ eKR eC eKa A b (kemJoin r G))
    (fun r => resampleAvg (restBad P hpk eG eKR r)
      (fun G => winReal P hpk eG eJ eKR eC eKa A b (kemJoin r G)))
    (fun r => resampleAvg (restBad P hpk eG eKR r)
      (fun G => winHq P hpk eG eJ eKR eC eKa A b (kemJoin r G)))
    (fun r => resampleAvg (restBad P hpk eG eKR r)
      (fun G => winSimJ P hpk eG eJ eKR eC eKa A b (kemJoin r G)))
    (fun r => resampleAvg (restBad P hpk eG eKR r)
      (fun G => winHJ P hpk eG eJ eKR eC eKa A b (kemJoin r G)))
    (restDelta P hpk eG eKR) ?_ ?_ ?_ ?_
  · refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hg : CoinGood P r.1
    · simp only [if_pos hg]
      rw [resampleAvg_winReal_eq_winSimJ P hpk eG eJ eKR eC eKa A b r hg]
    · simp only [if_neg hg]
  · have h := sum_restWeight_mul_resampleAvg_winHJ_eq_winHq P hpk eG eJ eKR eC eKa A b
      (fun ks => if CoinGood P ks then 1 else 0)
    simp only [ite_mul, one_mul, zero_mul] at h
    exact h.symm
  · exact fun r hg => absDiff_winSimJ_winHJ_resampled P hpk eG eJ eKR eC eKa A b r hg
  · exact fun r _ => absDiff_avg_winReal_avg_winHq_le_one P hpk eG eJ eKR eC eKa A b r

omit [Fintype PK] [Fintype SK] [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z]
  [Fintype R] [Nonempty R] in
/-- The right outer term at a fixed rest: in `prWinKEMHq` the `G`-table is read
by the oracle `mergeOracle (keyHop Hq G) J'`, whose value at a point of the
first summand reads `G` at that point only, and by the challenge ciphertext,
which reads `G` at the exempted challenge point only. The distance between the
resampled and the uniform table is at most `8 q' λ^(1/2)` with
`q' = flatQ q k q`, where `λ` bounds the fraction of bad values at every point
other than the challenge point. -/
theorem absDiff_resample_winHq_le (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (r : KEMRest PK SK Z M K m₂ n)
    (hcoin : ∀ m, ∃ ρ, P.dec r.1.2 (P.enc r.1.1 m ρ) = some m) (lam : ℝ≥0∞)
    (hlam : ∀ x, x ≠ eG (r.2.2.1, hpk r.1.1) →
      ((badVals (kemBad P hpk eG eKR r.1.1 r.1.2) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam) :
    absDiff (resampleAvg (restBad P hpk eG eKR r) fun G =>
          winHq P hpk eG eJ eKR eC eKa A b (kemJoin r G))
        (∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
          winHq P hpk eG eJ eKR eC eKa A b (kemJoin r G)) ≤
      8 * (flatQ q k q : ℝ≥0∞) * lam ^ (1 / 2 : ℝ) := by
  have hκ : ∑ _Hq : C → K, (Fintype.card (C → K) : ℝ≥0∞)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)]
  unfold winHq
  refine absDiff_resampleAvg_avg_le _ (fun _ => (Fintype.card (C → K) : ℝ≥0∞)⁻¹) hκ _ _
    fun Hq => ?_
  refine absDiff_resampleAvg_avg_le _ (fun _ => tabWeight n C) (sum_tabWeight n C) _ _
    fun T => ?_
  let csu : Fin n → C := fun u => P.enc r.1.1 r.2.2.1 (eKR.symm u).2
  let A' : Fin n → QAdv (m₁ + m₂) n (ancW c k (2 * w)) (flatQ q k q) := fun u =>
    toQAdv (A.run r.1.1 (csu u) (if b then Hq (csu u) else r.2.2.2.1))
      (decapsHq eC eKa Hq (csu u))
  let Φ : (Fin m₁ → Fin n) → Fin (m₁ + m₂) → Fin n := fun G =>
    mergeOracle (keyHop (kemSlice hpk eG r.1.1) (kemEncAt P eG r.1.1) eKR.symm Hq G)
      (prefixUpdate eJ r.2.1 r.2.2.2.2 T)
  have hfun : ∀ G : Fin m₁ → Fin n,
      prOutMR (A.run (kemJoin r G).1.1 (kemChal P hpk eG eKR (kemJoin r G))
          (if b = true then Hq (kemChal P hpk eG eKR (kemJoin r G)) else (kemJoin r G).2.2.2.1))
        (kemOracle' eJ (inputH P hpk eG eKR (kemJoin r G) Hq) T)
        (decapsHq eC eKa Hq (kemChal P hpk eG eKR (kemJoin r G))) =
      prOut (A' (G (eG (r.2.2.1, hpk r.1.1)))) (Φ G) := fun G => prOutMR_eq _ _ _
  have hΦ : ∀ (G G' : Fin m₁ → Fin n) (y : Fin (m₁ + m₂)),
      (∀ x, Fin.castAdd m₂ x = y → G x = G' x) → Φ G y = Φ G' y := by
    intro G G' y h
    induction y using Fin.addCases with
    | left x =>
      simp only [Φ, mergeOracle_castAdd]
      unfold keyHop coinCt
      rw [h x rfl]
    | right j =>
      simp [Φ]
  simp only [hfun]
  rw [absDiff_comm]
  exact absDiff_resample_map_off_point (kemBad P hpk eG eKR r.1.1 r.1.2) _ A' lam
    (fun x _ => kemBad_good P hpk eG eKR hcoin x) hlam
    ⟨Fin.castAdd m₂, Fin.castAdd_injective _ _⟩ Φ hΦ
    (fun u => by
      obtain ⟨ψ, hψ⟩ := A.pure r.1.1 (csu u) (if b then Hq (csu u) else r.2.2.2.1)
      exact pure_toQAdv _ _ hψ)

end KEMTriangle

/-! ## Multi-round adversaries in head-tail form and register casts -/

section MRHFlatten

variable {m n w q q₀ k c a : ℕ} [NeZero n] [NeZero c]

/-- The acceptance probability of the multi-round chain of a head-tail
adversary is the output probability of its flattening, at every classical
function of the rounds. -/
theorem prTrue_mrChain_eq_prOut_flatten (M : MRH m n w q q₀ k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) :
    prTrue_Q (QComp.qbind (mrChain (oracleQ m n w H) f k q₀ M.head M.tail M.rounds) fun _ =>
        measProj M.final M.final_conjTranspose M.final_mul_self) M.init =
      prOut (flatten f k M) H := by
  rw [prOut_eq_trace_scChain_empty]
  unfold prTrue_Q
  rw [qbind_unit_branch, measProj_branch_true, M.final_conjTranspose,
    trace_proj_mul_mul_proj M.final_mul_self, ← mrChainSC_empty_branch_false, flatten_final]
  exact congrArg (fun t : ℂ => ENNReal.ofReal t.re) (trace_flatten H ∅ f k M M.final false).symm

/-- A multi-round adversary transported along an equality of work-register
sizes. -/
def castMR {w₁ w₂ : ℕ} (h : w₁ = w₂) (A : QAdvMR m n w₁ q k c a) : QAdvMR m n w₂ q k c a :=
  h ▸ A

omit [NeZero c] in
theorem prOutMR_castMR {w₁ w₂ : ℕ} (h : w₁ = w₂) (A : QAdvMR m n w₁ q k c a)
    (H : Fin m → Fin n) (f : Fin c → Fin a) : prOutMR (castMR h A) H f = prOutMR A H f := by
  subst h
  rfl

omit [NeZero n] [NeZero c] in
theorem castMR_init_pure {w₁ w₂ : ℕ} (h : w₁ = w₂) (A : QAdvMR m n w₁ q k c a)
    (hA : ∃ ψ : Fin (m * n * w₁) → ℂ, A.init.val = vecMulVec ψ (star ψ)) :
    ∃ ψ : Fin (m * n * w₂) → ℂ, (castMR h A).init.val = vecMulVec ψ (star ψ) := by
  subst h
  exact hA

end MRHFlatten

/-! ## The left outer term: real decapsulation compiled into oracle queries -/

section KEMLeft

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [DecidableEq M] [DecidableEq Z]
  [Nonempty K] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c] [NeZero (m₁ + m₂)]

/-- The left outer term at a fixed rest: when the work register of every run of
`A` is `w₀ * ancDim (m₁ + m₂) n c` (`hw`), its rounds are `permRound` (`hrounds`),
its segment unitaries commute with `cleanProjM` (`hseg`) and its initial state is
supported by `cleanProjM` (`hinit`), each real decapsulation round is compiled
into four queries to the adversary's oracle (`prOutMR_eq_compiledMRH`); the
decapsulation reads the `G`-table at the re-encryption point of the decrypted
message only, and the challenge ciphertext at the exempted challenge point only.
The distance between the uniform and the resampled table is at most
`8 q'' λ^(1/2)` with `q'' = flatQ (q + 4) k q`. -/
theorem absDiff_winReal_resample_le (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (r : KEMRest PK SK Z M K m₂ n)
    (hcoin : ∀ m, ∃ ρ, P.dec r.1.2 (P.enc r.1.1 m ρ) = some m) (lam : ℝ≥0∞)
    (hlam : ∀ x, x ≠ eG (r.2.2.1, hpk r.1.1) →
      ((badVals (kemBad P hpk eG eKR r.1.1 r.1.2) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam)
    (w₀ : ℕ) (hw : 2 * w = w₀ * ancDim (m₁ + m₂) n c)
    (Ans : PK → C → K → Fin a → Equiv.Perm ((Fin (m₁ + m₂) × Fin n) × Fin w₀))
    (hseg : ∀ pk cs κ j i, ((castMR hw (A.run pk cs κ)).seg j i : Matrix _ _ ℂ) *
        cleanProjM (m₁ + m₂) n w₀ c =
      cleanProjM (m₁ + m₂) n w₀ c * ((castMR hw (A.run pk cs κ)).seg j i : Matrix _ _ ℂ))
    (hrounds : ∀ pk cs κ j,
      (castMR hw (A.run pk cs κ)).rounds j = permRound (m₁ + m₂) n w₀ c (Ans pk cs κ))
    (hinit : ∀ pk cs κ,
      SupportedOn (cleanProjM (m₁ + m₂) n w₀ c) (castMR hw (A.run pk cs κ)).init.val) :
    absDiff (∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
          winReal P hpk eG eJ eKR eC eKa A b (kemJoin r G))
        (resampleAvg (restBad P hpk eG eKR r) fun G =>
          winReal P hpk eG eJ eKR eC eKa A b (kemJoin r G)) ≤
      8 * (flatQ (q + 4) k q : ℝ≥0∞) * lam ^ (1 / 2 : ℝ) := by
  rw [absDiff_comm]
  unfold winReal
  refine absDiff_resampleAvg_avg_le _ (fun _ => tabWeight n C) (sum_tabWeight n C) _ _
    fun T => ?_
  let t : Fin m₁ := eG (r.2.2.1, hpk r.1.1)
  let csu : Fin n → C := fun u => P.enc r.1.1 r.2.2.1 (eKR.symm u).2
  let keyu : Fin n → K := fun u => if b then (eKR.symm u).1 else r.2.2.2.1
  let jf : Z × C → K := fun p => (eKR.symm (r.2.2.2.2 (eJ p))).1
  let ν : Fin c → Fin (m₁ + m₂) := fun x =>
    match P.dec r.1.2 (eC.symm x) with
    | some m' => Fin.castAdd m₂ (eG (m', hpk r.1.1))
    | none => Fin.castAdd m₂ t
  let φ : Fin n → Fin c → Fin n → Fin n → Fin a := fun u x h₁ _ =>
    decapsOracle P hpk eC eKa (fun _ => eKR.symm h₁) jf (r.1.2, r.1.1, r.2.1) (csu u) x
  let Φ : (Fin m₁ → Fin n) → Fin (m₁ + m₂) → Fin n := fun G =>
    mergeOracle G (prefixUpdate eJ r.2.1 r.2.2.2.2 T)
  let B : Fin n → QAdvMR (m₁ + m₂) n (w₀ * ancDim (m₁ + m₂) n c) q k c a := fun u =>
    castMR hw (A.run r.1.1 (csu u) (keyu u))
  let A' : Fin n → QAdv (m₁ + m₂) n (ancW c k (w₀ * ancDim (m₁ + m₂) n c)) (flatQ (q + 4) k q) :=
    fun u => flatten (fun x => φ u x 0 0) k
      (compiledMRH (m₁ + m₂) n w₀ c ν ν (B u) (φ u) (Ans r.1.1 (csu u) (keyu u)))
  have hdec : ∀ G : Fin m₁ → Fin n, kemDecaps P hpk eG eJ eKR eC eKa (kemJoin r G) =
      queryFun (m₁ + m₂) n c ν ν (φ (G t)) (Φ G) := by
    intro G
    funext x
    show decapsOracle P hpk eC eKa (fun p => eKR.symm (G (eG p))) jf (r.1.2, r.1.1, r.2.1)
        (csu (G t)) x =
      decapsOracle P hpk eC eKa (fun _ => eKR.symm (Φ G (ν x))) jf (r.1.2, r.1.1, r.2.1)
        (csu (G t)) x
    unfold decapsOracle
    split_ifs with hc
    · rfl
    · congr 1
      unfold decapsFixed
      cases hd : P.dec r.1.2 (eC.symm x) with
      | none => rfl
      | some m' => simp only [Φ, ν, hd, mergeOracle_castAdd]
  have hfun : ∀ G : Fin m₁ → Fin n,
      prOutMR (A.run (kemJoin r G).1.1 (kemChal P hpk eG eKR (kemJoin r G))
          (kemKey hpk eG eKR (kemJoin r G) b))
        (kemOracle' eJ (kemJoin r G) T) (kemDecaps P hpk eG eJ eKR eC eKa (kemJoin r G)) =
      prOut (A' (G t)) (Φ G) := by
    intro G
    rw [hdec G, ← prOutMR_castMR hw]
    exact (prOutMR_eq_compiledMRH (m₁ + m₂) n w₀ c ν ν (B (G t)) (φ (G t))
      (Ans r.1.1 (csu (G t)) (keyu (G t))) (Φ G) (fun x => φ (G t) x 0 0)
      (hseg _ _ _) (hrounds _ _ _) (hinit _ _ _)).trans
      (prTrue_mrChain_eq_prOut_flatten _ _ _)
  have hΦ : ∀ (G G' : Fin m₁ → Fin n) (y : Fin (m₁ + m₂)),
      (∀ x, Fin.castAdd m₂ x = y → G x = G' x) → Φ G y = Φ G' y := by
    intro G G' y h
    induction y using Fin.addCases with
    | left x =>
      simp only [Φ, mergeOracle_castAdd]
      exact h x rfl
    | right j =>
      simp [Φ]
  simp only [hfun]
  rw [absDiff_comm]
  exact absDiff_resample_map_off_point (kemBad P hpk eG eKR r.1.1 r.1.2) t A' lam
    (fun x _ => kemBad_good P hpk eG eKR hcoin x) hlam
    ⟨Fin.castAdd m₂, Fin.castAdd_injective _ _⟩ Φ hΦ
    (fun u => flatten_init_pure _ k _
      (castMR_init_pure hw _ (A.pure r.1.1 (csu u) (keyu u))))

end KEMLeft

/-! ## The composite hop with a numeric correctness term -/

section KEMNumeric

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c] [NeZero (m₁ + m₂)]

omit [DecidableEq M] [DecidableEq Z] [Fintype C] [DecidableEq C] [DecidableEq Hash] [NeZero c]
  [NeZero (m₁ + m₂)] [Fintype R] [NeZero n] in
include eKR in
/-- The rest weights sum to one. -/
theorem sum_kemRestWeight : ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r = 1 := by
  have hu : ∑ _G : Fin 0 → Fin n, ((n : ℝ≥0∞) ^ 0)⁻¹ = 1 := by simp
  have h := sum_kemSample_kemJoin (m₁ := 0) P
    (fun _ : KEMInput PK SK Z M K 0 m₂ n => (1 : ℝ≥0∞))
  simp only [mul_one, hu] at h
  rw [← h, kemSample_sum P eKR]

omit [DecidableEq M] [DecidableEq Z] [Fintype C] [DecidableEq C] [DecidableEq Hash] [NeZero c]
  [NeZero (m₁ + m₂)] [Fintype R] [Nonempty M] [Nonempty Z] [Nonempty K] [Nonempty R] in
/-- The rest-weighted average of a function of the key pair is its
`kemSample`-weighted average. -/
theorem sum_kemRestWeight_mul (lam : PK × SK → ℝ≥0∞) :
    ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r * lam r.1 =
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 := by
  have hu : ∀ t : ℝ≥0∞, ∑ _G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ * t = t := by
    intro t
    rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ]
    simp only [Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
    rw [ENNReal.mul_inv_cancel (pow_ne_zero _ (by exact_mod_cast NeZero.ne n))
        (ENNReal.pow_ne_top (ENNReal.natCast_ne_top n)), one_mul]
  rw [sum_kemSample_kemJoin]
  exact Finset.sum_congr rfl fun r _ => congrArg _ (hu (lam r.1)).symm

open scoped Classical in
/-- The composite hop with a numeric correctness term: with `λ (pk, sk)` a bound
on the decryption-failure fraction of every message under the key pair, and
`Λ = E λ` its average over the input distribution,
`|prWinKEM' − prWinKEMHq| ≤ 8 q'' Λ^(1/2) + Λ + 8 q' Λ^(1/2)` with
`q' = flatQ q k q` and `q'' = flatQ (q + 4) k q`. The structural hypotheses
`hw`, `hrounds`, `hseg`, `hinit` are those of `absDiff_winReal_resample_le`.
No coin hypothesis is required: at a key pair that is not `CoinGood` the bound
`hlam` forces `λ ≥ 1` (`one_le_of_not_coinGood`), which pays for that key pair.

References: Saito, Xagawa, Yamakawa, "Tightly-secure key encapsulation
mechanism in the quantum random oracle model", EUROCRYPT 2018, ePrint
2017/1005, and Jiang, Zhang, Chen, Wang, Ma, "IND-CCA-secure key encapsulation
mechanism in the quantum random oracle model, revisited", CRYPTO 2018, ePrint
2017/1096 (decapsulation simulated by the key-from-ciphertext oracle `Hq`);
Hofheinz, Hövelmanns, Kiltz, "A modular analysis of the Fujisaki-Okamoto
transformation", TCC 2017, ePrint 2017/604 (the `√δ` correctness loss);
Hövelmanns, Hülsing, Majenz, "Failing gracefully: decryption failures and the
Fujisaki-Okamoto transform", ASIACRYPT 2022, ePrint 2022/365 (the search for
failing ciphertexts). -/
theorem absDiff_prWinKEM'_prWinKEMHq_le_of_lam (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (lam : PK × SK → ℝ≥0∞)
    (hlam : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam (pk, sk))
    (w₀ : ℕ) (hw : 2 * w = w₀ * ancDim (m₁ + m₂) n c)
    (Ans : PK → C → K → Fin a → Equiv.Perm ((Fin (m₁ + m₂) × Fin n) × Fin w₀))
    (hseg : ∀ pk cs κ j i, ((castMR hw (A.run pk cs κ)).seg j i : Matrix _ _ ℂ) *
        cleanProjM (m₁ + m₂) n w₀ c =
      cleanProjM (m₁ + m₂) n w₀ c * ((castMR hw (A.run pk cs κ)).seg j i : Matrix _ _ ℂ))
    (hrounds : ∀ pk cs κ j,
      (castMR hw (A.run pk cs κ)).rounds j = permRound (m₁ + m₂) n w₀ c (Ans pk cs κ))
    (hinit : ∀ pk cs κ,
      SupportedOn (cleanProjM (m₁ + m₂) n w₀ c) (castMR hw (A.run pk cs κ)).init.val) :
    absDiff (prWinKEM' P hpk eG eJ eKR eC eKa A b) (prWinKEMHq P hpk eG eJ eKR eC eKa A b) ≤
      8 * (flatQ (q + 4) k q : ℝ≥0∞) *
          (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) +
        ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 +
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
  refine (absDiff_prWinKEM'_prWinKEMHq_triangle_coinGood P hpk eG eJ eKR eC eKa A b).trans ?_
  have hL : ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
      (if CoinGood P r.1 then
        absDiff (∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
            winReal P hpk eG eJ eKR eC eKa A b (kemJoin r G))
          (resampleAvg (restBad P hpk eG eKR r) fun G =>
            winReal P hpk eG eJ eKR eC eKa A b (kemJoin r G))
      else 0) ≤
      ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
        (8 * (flatQ (q + 4) k q : ℝ≥0∞) * lam r.1 ^ (1 / 2 : ℝ)) :=
    Finset.sum_le_sum fun r _ => by
      by_cases hk : P.keygen r.1 = 0
      · simp [kemRestWeight, hk]
      · by_cases hg : CoinGood P r.1
        · rw [if_pos hg]
          gcongr
          exact absDiff_winReal_resample_le P hpk eG eJ eKR eC eKa A b r hg (lam r.1)
            (fun x _ => hlam _ _ hk x) w₀ hw Ans hseg hrounds hinit
        · rw [if_neg hg, mul_zero]
          exact zero_le
  have hM : ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
      (if CoinGood P r.1 then restDelta P hpk eG eKR r else 1) ≤
      ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r * lam r.1 :=
    Finset.sum_le_sum fun r _ => by
      by_cases hk : P.keygen r.1 = 0
      · simp [kemRestWeight, hk]
      · gcongr
        by_cases hg : CoinGood P r.1
        · rw [if_pos hg, restDelta, ← div_eq_mul_inv]
          exact hlam _ _ hk _
        · rw [if_neg hg]
          exact one_le_of_not_coinGood P hpk eG eKR hg (lam r.1) (hlam _ _ hk)
  have hR : ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
      (if CoinGood P r.1 then
        absDiff (resampleAvg (restBad P hpk eG eKR r) fun G =>
            winHq P hpk eG eJ eKR eC eKa A b (kemJoin r G))
          (∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
            winHq P hpk eG eJ eKR eC eKa A b (kemJoin r G))
      else 0) ≤
      ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
        (8 * (flatQ q k q : ℝ≥0∞) * lam r.1 ^ (1 / 2 : ℝ)) :=
    Finset.sum_le_sum fun r _ => by
      by_cases hk : P.keygen r.1 = 0
      · simp [kemRestWeight, hk]
      · by_cases hg : CoinGood P r.1
        · rw [if_pos hg]
          gcongr
          exact absDiff_resample_winHq_le P hpk eG eJ eKR eC eKa A b r hg (lam r.1)
            (fun x _ => hlam _ _ hk x)
        · rw [if_neg hg, mul_zero]
          exact zero_le
  refine (add_le_add (add_le_add hL hM) hR).trans ?_
  rw [hΛ]
  exact add_le_add (add_le_add (hJ _) le_rfl) (hJ _)

end KEMNumeric

end CatCrypt.Quantum.QROM

end

end
