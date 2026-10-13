/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.PRFBadTable
public import CatCryptCore.Crypto.MLKEM.PRFKEMChain
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The averaged KEM bound with a key-dependent failure bound

The chain of `PRFChain` states the correctness hypothesis of
`qINDCCA_le_qOwcpaAux_numeric_coll` at a constant failure bound `Λ`. That theorem
accepts a failure bound `lam` that depends on the key pair and pays its
expectation over key generation. This module carries the failure term of the
chain at such a `lam` averaged over the noise table, and instantiates `lam` for
the scheme with noise from the table at the worst bad-coin fraction of each key
pair; `PRFCoinWeak` states the chain itself at that `lam`.

For the key pair generated from the key-noise row `v`, let `x(v)` be the largest
fraction over messages of encryption-noise rows on which decryption fails. With
the threshold `kk(v) = ⌈6 N x(v)⌉ + t` (`N = |Sd|`), the probability over the
table that at least `kk(v)` seeds make decryption fail is at most
`C(N - 1, kk) · x ^ kk ≤ 2⁻ᵗ`, and outside that event the bad-coin fraction is at
most `(kk(v) + 1) / N ≤ 6 x(v) + (t + 2) / N`. Averaged over `v`, the failure
term of the chain is at most `6 · corrWorst + (t + 2) / N + |M| · 2⁻ᵗ`, with
`corrWorst` the correctness error of the scheme with uniform noise rows.

## Main definitions

* `keyAvg P lam` — the expectation of `lam` over key generation
* `lamSup P ks` — the largest bad-value fraction over the points of the `G`-table
* `kkOf t N x` — the threshold `⌈6 N x⌉ + t`
* `idealScheme` — the K-PKE whose key-noise and encryption-noise rows are uniform

## Main results

* `avg_card_badSeeds_ge_keyed_le` — the tail bound at a threshold that depends on
  the row at the key seed
* `avg_keyAvg_lamSup_prfScheme_le` — the averaged failure term for the scheme
  with noise from the table at thresholds `kk φ v`
* `choose_mul_pow_le_half_pow` — `C(n, k) · p ^ k ≤ 2⁻ᵏ` when `6 n p ≤ k`
* `chainBound_mono_keyed` — `chainBound` is monotone in the failure bound and
  the one-wayness terms
* `corrWorst_idealScheme` — `corrWorst` of `idealScheme` as an average of
  row fractions
* `avg_keyAvg_lamSup_le_corrWorst` — the averaged failure term is at most
  `6 · corrWorst + (t + 2) / N + |M| · 2⁻ᵗ`

## Scope

The coin hypothesis of `qINDCCA_le_qOwcpaAux_numeric_coll` (every generated key
pair has a correctly decrypting coin for every message) quantifies over every
key pair in the support of key generation, which for `prfScheme F` is every seed
of the table. `PRFCoinWeak` removes it: at `lam = lamSup` the failure of a key
pair is paid inside the failure term, so the correctness error enters only that
term.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.QROM
open CatCrypt.Crypto.PKE.Games (Scheme)
open CatCrypt.Crypto.MLKEM.PRFOracle (avg avg_mono avg_const avg_add avg_mul_left
  avg_le_one)
open CatCrypt.Quantum.QROM.PRFChain (chainBound)

noncomputable section

namespace CatCrypt.Crypto.MLKEM.PRFBadTableKeyed

/-! ## One scheme at a key-dependent failure bound -/

section OneScheme

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

/-- The expectation over key generation of a function of the key pair. -/
def keyAvg (P : Scheme PK SK M C R) (lam : PK × SK → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ ks, P.keygen ks * lam ks

/-- The largest fraction of bad `G`-values over the points of the `G`-table under
the key pair `ks`. -/
def lamSup (P : Scheme PK SK M C R) (ks : PK × SK) : ℝ≥0∞ :=
  ⨆ x : Fin m₁, ((badVals (kemBad P hpk eG eKR ks.1 ks.2) x).card : ℝ≥0∞) / (n : ℝ≥0∞)

end OneScheme

/-! ## The number of bad seeds at a threshold that depends on the key row -/

section Tail

open CatCrypt.Crypto.MLKEM.PRFBadTable (badSeeds indicator_le_sum_powersetCard avg_pi_prod)

variable {S V : Type} [Fintype S] [DecidableEq S] [Fintype V] [Nonempty V] [DecidableEq V]

/-- An average of a sum over a finite set is the sum of the averages. -/
theorem avg_finset_sum {α ι : Type} [Fintype α] (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    avg (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, avg (f i) := by
  simp only [CatCrypt.Crypto.MLKEM.PRFOracle.avg, Finset.mul_sum]
  exact Finset.sum_comm

omit [DecidableEq V] in
/-- The average over a uniform family of rows of a function of the row at `σ` is
the average of the function. -/
theorem avg_eval (σ : S) (h : V → ℝ≥0∞) : avg (fun G : S → V => h (G σ)) = avg h := by
  have hG : ∀ G : S → V, h (G σ) = ∏ s, (if s = σ then h (G s) else 1) := fun G => by
    rw [Finset.prod_ite_eq']; simp
  simp_rw [hG]
  have := avg_pi_prod (fun s w => if s = σ then h w else 1)
  rw [show (fun G : S → V => ∏ s, if s = σ then h (G s) else 1) =
      fun G : S → V => ∏ s, (fun s w => if s = σ then h w else (1 : ℝ≥0∞)) s (G s) from rfl, this]
  have hs : ∀ s, (avg fun w => if s = σ then h w else 1) = if s = σ then avg h else 1 := by
    intro s
    split_ifs <;> simp [avg_const]
  simp_rw [hs]
  rw [Finset.prod_ite_eq']
  simp

/-- For a row `v` and a set `T` of seeds not containing `σ`, the probability over a
uniform family of rows that the row at `σ` is `v` and every seed in `T` is related
to `v` is at most `|V|⁻¹ · p ^ |T|`, when the fraction of rows related to `v` is at
most `p`. -/
theorem avg_eq_prod_bad_le (B : V → V → Bool) (v : V) (p : ℝ≥0∞)
    (hp : avg (fun w => if B v w then (1 : ℝ≥0∞) else 0) ≤ p) (σ : S) (T : Finset S)
    (hσ : σ ∉ T) :
    avg (fun G : S → V => (if G σ = v then (1 : ℝ≥0∞) else 0) *
        ∏ r ∈ T, if B v (G r) then (1 : ℝ≥0∞) else 0) ≤
      (Fintype.card V : ℝ≥0∞)⁻¹ * p ^ T.card := by
  have hsplit : ∀ G : S → V, (if G σ = v then (1 : ℝ≥0∞) else 0) *
      (∏ r ∈ T, if B v (G r) then (1 : ℝ≥0∞) else 0) =
      ∏ s, ((if s = σ then (if G s = v then (1 : ℝ≥0∞) else 0) else 1) *
        (if s ∈ T then (if B v (G s) then (1 : ℝ≥0∞) else 0) else 1)) := by
    intro G
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_mem]
    simp
  simp_rw [hsplit]
  rw [avg_pi_prod (fun s w => (if s = σ then (if w = v then (1 : ℝ≥0∞) else 0) else 1) *
    (if s ∈ T then (if B v w then (1 : ℝ≥0∞) else 0) else 1))]
  calc ∏ s, avg (fun w => (if s = σ then (if w = v then (1 : ℝ≥0∞) else 0) else 1) *
          (if s ∈ T then (if B v w then (1 : ℝ≥0∞) else 0) else 1))
      ≤ ∏ s : S, ((if s = σ then (Fintype.card V : ℝ≥0∞)⁻¹ else 1) *
          (if s ∈ T then p else 1)) := by
        refine Finset.prod_le_prod' fun s _ => ?_
        by_cases hs : s = σ
        · subst hs
          simp only [if_true, hσ, if_false, mul_one]
          rw [CatCrypt.Crypto.MLKEM.PRFOracle.avg_eq_inv_mul_sum]
          simp
        · by_cases hT : s ∈ T
          · simpa [hs, hT] using hp
          · simp [hs, hT, avg_const]
    _ = (Fintype.card V : ℝ≥0∞)⁻¹ * p ^ T.card := by
        rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_mem]
        simp

/-- **Tail bound at a threshold that depends on the row at `σ`.** If the fraction
of rows related to `v` is at most `p v`, the probability over a uniform family of
rows that at least `kk (G σ)` seeds other than `σ` are bad is at most the average
over `v` of `C(|S| - 1, kk v) · p v ^ kk v`. -/
theorem avg_card_badSeeds_ge_keyed_le (B : V → V → Bool) (p : V → ℝ≥0∞)
    (hp : ∀ v, avg (fun w => if B v w then (1 : ℝ≥0∞) else 0) ≤ p v) (σ : S) (kk : V → ℕ) :
    avg (fun G : S → V => if kk (G σ) ≤ (badSeeds B σ G).card then (1 : ℝ≥0∞) else 0) ≤
      avg (fun v => ((Fintype.card S - 1).choose (kk v) : ℝ≥0∞) * p v ^ kk v) := by
  have hpt : ∀ G : S → V,
      (if kk (G σ) ≤ (badSeeds B σ G).card then (1 : ℝ≥0∞) else 0) ≤
        ∑ v, ∑ T ∈ (Finset.univ.erase σ).powersetCard (kk v),
          (if G σ = v then (1 : ℝ≥0∞) else 0) * ∏ r ∈ T, if B v (G r) then (1 : ℝ≥0∞) else 0 := by
    intro G
    refine (indicator_le_sum_powersetCard (Finset.univ.erase σ) (fun r => B (G σ) (G r))
      (kk (G σ))).trans ?_
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun v =>
      ∑ T ∈ (Finset.univ.erase σ).powersetCard (kk v),
        (if G σ = v then (1 : ℝ≥0∞) else 0) * ∏ r ∈ T, if B v (G r) then (1 : ℝ≥0∞) else 0)
      (fun _ _ => zero_le) (Finset.mem_univ (G σ)))
    simp
  refine (avg_mono hpt).trans ?_
  rw [CatCrypt.Crypto.MLKEM.PRFOracle.avg_sum]
  simp_rw [avg_finset_sum]
  calc ∑ v, ∑ T ∈ (Finset.univ.erase σ).powersetCard (kk v),
        avg (fun G : S → V => (if G σ = v then (1 : ℝ≥0∞) else 0) *
          ∏ r ∈ T, if B v (G r) then (1 : ℝ≥0∞) else 0)
      ≤ ∑ v, ∑ _T ∈ (Finset.univ.erase σ).powersetCard (kk v),
          (Fintype.card V : ℝ≥0∞)⁻¹ * p v ^ kk v := by
        refine Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun T hT => ?_
        obtain ⟨hsub, hc⟩ := Finset.mem_powersetCard.1 hT
        rw [← hc]
        exact avg_eq_prod_bad_le B v (p v) (hp v) σ T fun h => by simpa using hsub h
    _ = _ := by
        rw [CatCrypt.Crypto.MLKEM.PRFOracle.avg_eq_inv_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_const, Finset.card_powersetCard,
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, nsmul_eq_mul]
        ring

end Tail

/-! ## The scheme with noise from the table -/

section Scheme

open CatCrypt.Crypto.MLKEM.PRFOracle (prfRow keygenPrf encPrf avg_comm avg_fst avg_sum)
open CatCrypt.Crypto.MLKEM.PRFAuxHop (prfScheme)
open CatCrypt.Crypto.MLKEM.PRFBadTable (badSeeds failRel rowEquiv avg_equiv
  card_filter_le_badSeeds toOuterMeasure_uniform_le)
open CatCrypt.Crypto.MLKEM.MLKEM512FailureBound (card_badVals_kemBad_div_le)

variable {Sd Nc PK SK M C R KS K Hash Φ : Type} {m₁ m₃ nF nK : ℕ}
  [Fintype Φ] [Nonempty Φ] [Fintype Sd] [Nonempty Sd] [DecidableEq Sd] [Fintype Nc]
  [DecidableEq Nc] [NeZero nF] [Fintype PK] [DecidableEq PK] [Fintype SK] [DecidableEq SK]
  [Fintype M] [DecidableEq M] [Fintype C] [DecidableEq C]
  [Fintype K] [Nonempty K] [DecidableEq Hash] [NeZero nK]
  (eD : (Sd × Nc) ≃ Fin m₃) (kg : Φ → KS → PK × SK) (enc : PK → M → R → C)
  (dec : SK → C → Option M) (eK : (Nc → Fin nF) → KS) (eE : (Nc → Fin nF) → R)
  (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eKR : (K × Sd) ≃ Fin nK)

omit [Fintype Nc] [DecidableEq Nc] [NeZero nF] [Fintype PK] [DecidableEq PK] [Fintype SK]
  [DecidableEq SK] [Fintype C] [DecidableEq C] [NeZero nK] in
/-- At the key pair generated at the public coins `φ` and the seed `σ`, the largest
bad-coin fraction is at most `(kk + 1) / |Sd|` plus the number of messages at which
at least `kk` seeds other than `σ` make decryption fail. -/
theorem lamSup_prfScheme_le (F : Fin m₃ → Fin nF) (φ : Φ) (σ : Sd) (kk : ℕ) :
    lamSup hpk eG eKR (prfScheme eD kg enc dec eK eE F) (keygenPrf eD kg eK F φ σ) ≤
      ((kk + 1 : ℕ) : ℝ≥0∞) / Fintype.card Sd +
        ∑ m, if kk ≤ (badSeeds (failRel kg enc dec eK eE φ m) σ (prfRow eD F)).card
          then (1 : ℝ≥0∞) else 0 := by
  refine iSup_le fun x => (card_badVals_kemBad_div_le _ hpk eG eKR _ _ x).trans ?_
  by_cases hb : kk ≤ (badSeeds (failRel kg enc dec eK eE φ (eG.symm x).1) σ (prfRow eD F)).card
  · refine ((toOuterMeasure_uniform_le _ (Fintype.card Sd) (Finset.card_le_univ _)).trans
      ENNReal.div_self_le_one).trans (le_add_left ?_)
    exact le_trans (le_of_eq (by simp [hb])) (Finset.single_le_sum (f := fun m =>
      if kk ≤ (badSeeds (failRel kg enc dec eK eE φ m) σ (prfRow eD F)).card
        then (1 : ℝ≥0∞) else 0) (fun _ _ => zero_le) (Finset.mem_univ (eG.symm x).1))
  · refine le_add_right ?_
    refine toOuterMeasure_uniform_le _ (kk + 1) ?_
    have h := card_filter_le_badSeeds (failRel kg enc dec eK eE φ (eG.symm x).1) σ (prfRow eD F)
    simp only [failRel, decide_eq_true_eq] at h
    exact h.trans (by omega)

omit [DecidableEq Sd] [Fintype Nc] [DecidableEq Nc] [NeZero nF] [Fintype M] [DecidableEq M]
  [Fintype C] [DecidableEq C] in
/-- The expectation over key generation of `prfScheme F` is the average over the
public coins and the seed. -/
theorem keyAvg_prfScheme (F : Fin m₃ → Fin nF) (g : PK × SK → ℝ≥0∞) :
    keyAvg (prfScheme eD kg enc dec eK eE F) g =
      avg fun p : Φ × Sd => g (keygenPrf eD kg eK F p.1 p.2) := by
  unfold keyAvg
  exact CatCrypt.Crypto.MLKEM.PRFKEMChain.sum_map_uniform _ g

omit [Fintype C] [DecidableEq C] [NeZero nK] in
/-- **The averaged failure term at the key-dependent failure bound.** For
thresholds `kk φ v` that depend on the public coins and the key-noise row, and
bounds `pf φ m v` on the fraction of encryption-noise rows on which decryption of
`m` fails under the key pair from `v`, the average over a uniform table of
`keyAvg` at `lamSup` is at most the average over `φ` and `v` of
`(kk φ v + 1) / N + ∑ m, C(N - 1, kk φ v) · pf φ m v ^ kk φ v`, with `N = |Sd|`. -/
theorem avg_keyAvg_lamSup_prfScheme_le (kk : Φ → (Nc → Fin nF) → ℕ)
    (pf : Φ → M → (Nc → Fin nF) → ℝ≥0∞)
    (hp : ∀ φ m v, avg (fun w => if failRel kg enc dec eK eE φ m v w then (1 : ℝ≥0∞) else 0) ≤
      pf φ m v) :
    (avg fun F : Fin m₃ → Fin nF => keyAvg (prfScheme eD kg enc dec eK eE F)
        (lamSup hpk eG eKR (prfScheme eD kg enc dec eK eE F))) ≤
      avg fun φ => avg fun v => ((kk φ v + 1 : ℕ) : ℝ≥0∞) / Fintype.card Sd +
        ∑ m, ((Fintype.card Sd - 1).choose (kk φ v) : ℝ≥0∞) * pf φ m v ^ kk φ v := by
  calc (avg fun F : Fin m₃ → Fin nF => keyAvg (prfScheme eD kg enc dec eK eE F)
        (lamSup hpk eG eKR (prfScheme eD kg enc dec eK eE F)))
      = avg fun F : Fin m₃ → Fin nF => avg fun p : Φ × Sd =>
          lamSup hpk eG eKR (prfScheme eD kg enc dec eK eE F) (keygenPrf eD kg eK F p.1 p.2) := by
        congr 1
        funext F
        exact keyAvg_prfScheme eD kg enc dec eK eE F _
    _ ≤ avg fun F : Fin m₃ → Fin nF => avg fun p : Φ × Sd =>
          ((kk p.1 (prfRow eD F p.2) + 1 : ℕ) : ℝ≥0∞) / Fintype.card Sd +
            ∑ m, if kk p.1 (prfRow eD F p.2) ≤
              (badSeeds (failRel kg enc dec eK eE p.1 m) p.2 (prfRow eD F)).card
              then (1 : ℝ≥0∞) else 0 :=
        avg_mono fun F => avg_mono fun p =>
          lamSup_prfScheme_le eD kg enc dec eK eE hpk eG eKR F p.1 p.2 _
    _ = avg fun p : Φ × Sd => avg fun F : Fin m₃ → Fin nF =>
          ((kk p.1 (prfRow eD F p.2) + 1 : ℕ) : ℝ≥0∞) / Fintype.card Sd +
            ∑ m, if kk p.1 (prfRow eD F p.2) ≤
              (badSeeds (failRel kg enc dec eK eE p.1 m) p.2 (prfRow eD F)).card
              then (1 : ℝ≥0∞) else 0 := avg_comm _
    _ ≤ avg fun p : Φ × Sd => avg fun v => ((kk p.1 v + 1 : ℕ) : ℝ≥0∞) / Fintype.card Sd +
          ∑ m, ((Fintype.card Sd - 1).choose (kk p.1 v) : ℝ≥0∞) * pf p.1 m v ^ kk p.1 v :=
        avg_mono fun p => ?_
    _ = _ := avg_fst (fun φ => avg fun v => ((kk φ v + 1 : ℕ) : ℝ≥0∞) / Fintype.card Sd +
          ∑ m, ((Fintype.card Sd - 1).choose (kk φ v) : ℝ≥0∞) * pf φ m v ^ kk φ v)
  refine (avg_equiv (rowEquiv eD) (fun G => ((kk p.1 (G p.2) + 1 : ℕ) : ℝ≥0∞) /
      Fintype.card Sd + ∑ m, if kk p.1 (G p.2) ≤
        (badSeeds (failRel kg enc dec eK eE p.1 m) p.2 G).card then (1 : ℝ≥0∞) else 0)).trans_le
    ?_
  rw [avg_add, avg_add, avg_sum, avg_sum, avg_eval p.2 (fun v =>
    ((kk p.1 v + 1 : ℕ) : ℝ≥0∞) / Fintype.card Sd)]
  refine add_le_add le_rfl (Finset.sum_le_sum fun m _ => ?_)
  exact avg_card_badSeeds_ge_keyed_le _ (pf p.1 m) (hp p.1 m) p.2 (kk p.1)

end Scheme

/-! ## The binomial tail at a threshold proportional to the failure fraction -/

section Numeric

/-- `k ^ k ≤ 3 ^ k · k!`. -/
theorem pow_self_le_three_pow_mul_factorial (k : ℕ) : k ^ k ≤ 3 ^ k * k.factorial := by
  have h := Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k
  have he : Real.exp k ≤ 3 ^ k := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le
      Real.exp_one_lt_three.le k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hf] at h
  have h' : ((k ^ k : ℕ) : ℝ) ≤ ((3 ^ k * k.factorial : ℕ) : ℝ) := by
    push_cast
    exact h.trans (by gcongr)
  exact_mod_cast h'

/-- `C(n, k) · p ^ k ≤ 2⁻ᵏ` when `6 n p ≤ k`. -/
theorem choose_mul_pow_le_half_pow (n k : ℕ) (p : ℝ≥0∞) (h : 6 * ((n : ℝ≥0∞) * p) ≤ k) :
    (n.choose k : ℝ≥0∞) * p ^ k ≤ 2⁻¹ ^ k := by
  refine (CatCrypt.Crypto.MLKEM.PRFBadTable.choose_mul_pow_le n k p).trans ?_
  have hf : (k.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [ENNReal.div_le_iff hf (ENNReal.natCast_ne_top _)]
  have h6 : (n : ℝ≥0∞) * p ≤ (k : ℝ≥0∞) / 6 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_comm]
    exact h
  have h3 : ((k ^ k : ℕ) : ℝ≥0∞) ≤ ((3 ^ k * k.factorial : ℕ) : ℝ≥0∞) := by
    exact_mod_cast pow_self_le_three_pow_mul_factorial k
  push_cast at h3
  calc ((n : ℝ≥0∞) * p) ^ k ≤ ((k : ℝ≥0∞) / 6) ^ k := by gcongr
    _ = (k : ℝ≥0∞) ^ k * 6⁻¹ ^ k := by rw [div_eq_mul_inv, mul_pow]
    _ ≤ 3 ^ k * (k.factorial : ℝ≥0∞) * 6⁻¹ ^ k := by gcongr
    _ = (3 * 6⁻¹) ^ k * (k.factorial : ℝ≥0∞) := by ring
    _ = 2⁻¹ ^ k * (k.factorial : ℝ≥0∞) := by
        congr 2
        rw [show (6 : ℝ≥0∞) = 3 * 2 by norm_num, ENNReal.mul_inv (Or.inl (by norm_num))
          (Or.inl (by norm_num)), ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
          one_mul]

/-- The threshold `⌈6 N x⌉ + t`. -/
def kkOf (t N : ℕ) (x : ℝ≥0∞) : ℕ := ⌈(6 * (N : ℝ≥0∞) * x).toReal⌉₊ + t

/-- `6 N x ≤ kkOf t N x` for finite `x`. -/
theorem le_kkOf (t N : ℕ) {x : ℝ≥0∞} (hx : x ≠ ⊤) : 6 * (N : ℝ≥0∞) * x ≤ kkOf t N x := by
  have hne : 6 * (N : ℝ≥0∞) * x ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top N)) hx
  unfold kkOf
  push_cast
  refine le_trans ?_ le_self_add
  set y := 6 * (N : ℝ≥0∞) * x
  calc y = ENNReal.ofReal y.toReal := (ENNReal.ofReal_toReal hne).symm
    _ ≤ ENNReal.ofReal (⌈y.toReal⌉₊ : ℝ) := ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
    _ = (⌈y.toReal⌉₊ : ℝ≥0∞) := ENNReal.ofReal_natCast _

/-- At the threshold `kkOf t N x`, the binomial tail term of a failure fraction
`p ≤ x` among `N - 1` seeds is at most `2⁻ᵗ`. -/
theorem choose_mul_pow_kkOf_le (t N : ℕ) {x p : ℝ≥0∞} (hx : x ≠ ⊤) (hp : p ≤ x) :
    ((N - 1).choose (kkOf t N x) : ℝ≥0∞) * p ^ kkOf t N x ≤ 2⁻¹ ^ t := by
  refine (choose_mul_pow_le_half_pow _ _ _ ?_).trans ?_
  · refine le_trans ?_ (le_kkOf t N hx)
    rw [← mul_assoc]
    gcongr
    exact_mod_cast Nat.sub_le N 1
  · exact pow_le_pow_right_of_le_one' (by norm_num) (Nat.le_add_left t _)

/-- `(kkOf t N x + 1) / N ≤ 6 x + (t + 2) / N`. -/
theorem kkOf_add_one_div_le (t N : ℕ) (hN : N ≠ 0) {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    ((kkOf t N x + 1 : ℕ) : ℝ≥0∞) / N ≤ 6 * x + ((t + 2 : ℕ) : ℝ≥0∞) / N := by
  have hne : 6 * (N : ℝ≥0∞) * x ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top N)) hx
  have hceil : (⌈(6 * (N : ℝ≥0∞) * x).toReal⌉₊ : ℝ≥0∞) ≤ 6 * (N : ℝ≥0∞) * x + 1 := by
    set y := 6 * (N : ℝ≥0∞) * x
    calc (⌈y.toReal⌉₊ : ℝ≥0∞) = ENNReal.ofReal (⌈y.toReal⌉₊ : ℝ) := (ENNReal.ofReal_natCast _).symm
      _ ≤ ENNReal.ofReal (y.toReal + 1) :=
          ENNReal.ofReal_le_ofReal (Nat.ceil_lt_add_one ENNReal.toReal_nonneg).le
      _ = y + 1 := by
          rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal hne,
            ENNReal.ofReal_one]
  have hN' : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN
  calc ((kkOf t N x + 1 : ℕ) : ℝ≥0∞) / N
      ≤ (6 * (N : ℝ≥0∞) * x + ((t + 2 : ℕ) : ℝ≥0∞)) / N := by
        gcongr
        unfold kkOf
        push_cast
        calc (⌈(6 * (N : ℝ≥0∞) * x).toReal⌉₊ : ℝ≥0∞) + t + 1
            ≤ 6 * (N : ℝ≥0∞) * x + 1 + t + 1 := by gcongr
          _ = 6 * (N : ℝ≥0∞) * x + (t + 2) := by ring
    _ = 6 * x + ((t + 2 : ℕ) : ℝ≥0∞) / N := by
        rw [ENNReal.add_div, mul_right_comm 6 (N : ℝ≥0∞) x,
          ENNReal.mul_div_cancel_right hN' (ENNReal.natCast_ne_top N)]

/-- `chainBound` is monotone in the failure bound and the one-wayness terms. -/
theorem chainBound_mono_keyed (q₁ q₂ : ℕ) (ε ζ : ℝ≥0∞) {Λ Λ' x₁ x₁' x₀ x₀' : ℝ≥0∞}
    (hΛ : Λ ≤ Λ') (h₁ : x₁ ≤ x₁') (h₀ : x₀ ≤ x₀') :
    chainBound q₁ q₂ Λ ε ζ x₁ x₀ ≤ chainBound q₁ q₂ Λ' ε ζ x₁' x₀' := by
  unfold chainBound
  gcongr

end Numeric

/-! ## The bound at the correctness error of the scheme with uniform noise rows -/

section Ideal

open CatCrypt.Crypto.MLKEM.PRFOracle (prfRow avg_prod)
open CatCrypt.Crypto.MLKEM.PRFAuxHop (prfScheme)
open CatCrypt.Crypto.MLKEM.PRFBadTable (failRel avg_boole)
open CatCrypt.Crypto.MLKEM.PRFKEMChain (sum_map_uniform)

variable {Sd Nc PK SK M C KS K Hash Z Φ : Type} {m₁ m₂ m₃ n w q k c a : ℕ}
  [Fintype Φ] [Nonempty Φ] [Fintype Sd] [DecidableEq Sd] [Nonempty Sd] [Fintype Nc]
  [DecidableEq Nc] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype C] [DecidableEq C]
  [Fintype K] [Nonempty K] [DecidableEq Hash] [Fintype PK] [DecidableEq PK] [Fintype SK]
  [DecidableEq SK] [Fintype M] [DecidableEq M] [Nonempty M]
  [NeZero n] [NeZero c] [NeZero a] [NeZero (m₁ + m₂)]
  (eD : (Sd × Nc) ≃ Fin m₃) (kg : Φ → KS → PK × SK) (enc : PK → M → (Nc → Fin n) → C)
  (dec : SK → C → Option M) (eK : (Nc → Fin n) → KS)
  (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × Sd) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

/-- The K-PKE with uniform noise rows: key generation draws public coins `φ` and a
key-noise row `v` uniformly and returns `kg φ (eK v)`; encryption with the
encryption-noise row `w` is `enc pk m w`; decryption is `dec`. -/
def idealScheme : Scheme PK SK M C (Nc → Fin n) where
  keygen := (PMF.uniformOfFintype (Φ × (Nc → Fin n))).map fun p => kg p.1 (eK p.2)
  enc := enc
  dec := dec

omit [Fintype C] [DecidableEq C] [Fintype PK] [DecidableEq PK] [Fintype SK] [DecidableEq SK]
  [Fintype M] [Nonempty M] in
/-- The failure probability of `idealScheme` under the key pair from the
key-noise row `v` is the fraction of encryption-noise rows in `failRel`. -/
theorem failProb_idealScheme (φ : Φ) (m : M) (v : Nc → Fin n) :
    (idealScheme kg enc dec eK).failProb (kg φ (eK v)).1 (kg φ (eK v)).2 m =
      avg (fun w => if failRel kg enc dec eK id φ m v w then (1 : ℝ≥0∞) else 0) := by
  rw [Scheme.failProb, PMF.toOuterMeasure_uniformOfFintype_apply, avg_boole]
  congr 2
  simp [failRel, idealScheme]
  exact Fintype.card_subtype _

omit [Fintype C] [DecidableEq C] [Fintype M] [Nonempty M] in
/-- The correctness error of `idealScheme` is the average over the public coins
and the key-noise row of the largest fraction over messages of failing
encryption-noise rows. -/
theorem corrWorst_idealScheme :
    (idealScheme kg enc dec eK).corrWorst =
      avg fun φ : Φ => avg fun v : Nc → Fin n => ⨆ m : M,
        avg (fun w => if failRel kg enc dec eK id φ m v w then (1 : ℝ≥0∞) else 0) := by
  rw [Scheme.corrWorst, tsum_fintype]
  change ∑ ks, ((PMF.uniformOfFintype (Φ × (Nc → Fin n))).map fun p => kg p.1 (eK p.2)) ks *
    ⨆ m, (idealScheme kg enc dec eK).failProb ks.1 ks.2 m = _
  rw [sum_map_uniform, avg_prod]
  simp only [failProb_idealScheme]

omit [Fintype C] [DecidableEq C] [Nonempty M] in
/-- **The averaged failure term at the correctness error of the ideal scheme.**
At the threshold `kkOf t |Sd| x` with `x` the largest failure fraction over
messages of the key pair, the average over a uniform table of `keyAvg` at
`lamSup` is at most `6 · corrWorst + (t + 2) / |Sd| + |M| · 2⁻ᵗ`, where
`corrWorst` is the correctness error of `idealScheme`. -/
theorem avg_keyAvg_lamSup_le_corrWorst (t : ℕ) :
    (avg fun F : Fin m₃ → Fin n => keyAvg (prfScheme eD kg enc dec eK id F)
        (lamSup hpk eG eKR (prfScheme eD kg enc dec eK id F))) ≤
      6 * (idealScheme kg enc dec eK).corrWorst +
        ((t + 2 : ℕ) : ℝ≥0∞) / Fintype.card Sd + (Fintype.card M : ℝ≥0∞) * 2⁻¹ ^ t := by
  set pf : Φ → M → (Nc → Fin n) → ℝ≥0∞ := fun φ m v =>
    avg (fun w => if failRel kg enc dec eK id φ m v w then (1 : ℝ≥0∞) else 0) with hpf
  have hmax : ∀ φ v, (⨆ m, pf φ m v) ≠ ⊤ := fun φ v =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun m =>
      avg_le_one fun w => by split_ifs <;> simp)
  have hN : Fintype.card Sd ≠ 0 := Fintype.card_ne_zero
  refine (avg_keyAvg_lamSup_prfScheme_le eD kg enc dec eK id hpk eG eKR
    (fun φ v => kkOf t (Fintype.card Sd) (⨆ m, pf φ m v)) pf (fun _ _ _ => le_rfl)).trans ?_
  rw [corrWorst_idealScheme]
  calc (avg fun φ => avg fun v =>
        ((kkOf t (Fintype.card Sd) (⨆ m, pf φ m v) + 1 : ℕ) : ℝ≥0∞) / Fintype.card Sd +
          ∑ m, ((Fintype.card Sd - 1).choose (kkOf t (Fintype.card Sd) (⨆ m, pf φ m v)) :
            ℝ≥0∞) * pf φ m v ^ kkOf t (Fintype.card Sd) (⨆ m, pf φ m v))
      ≤ avg fun φ => avg fun v => 6 * (⨆ m, pf φ m v) +
          ((t + 2 : ℕ) : ℝ≥0∞) / Fintype.card Sd + (Fintype.card M : ℝ≥0∞) * 2⁻¹ ^ t := by
        refine avg_mono fun φ => avg_mono fun v => ?_
        refine add_le_add (kkOf_add_one_div_le t _ hN (hmax φ v)) ?_
        refine (Finset.sum_le_sum fun m _ => choose_mul_pow_kkOf_le t _ (hmax φ v)
          (le_iSup (fun m => pf φ m v) m)).trans (le_of_eq ?_)
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = _ := by simp only [avg_add, avg_const, avg_mul_left, hpf]

end Ideal

end CatCrypt.Crypto.MLKEM.PRFBadTableKeyed

end

end
