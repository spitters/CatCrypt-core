/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.PRFChain
public import CatCryptCore.Crypto.MLKEM.PRFAuxHop
public import CatCryptCore.Crypto.MLKEM.MLKEM512FailureBound

/-!
# The weight of the tables at which the scheme with noise from the table is bad

The averaged quantum IND-CCA bound `PRFChain.avg_qINDCCA_le` pays the weight of
the tables `F` at which `ChainGood (prfScheme F) Λ ε` fails. This module bounds
that weight for a uniform table by the idealised row-level quantities: the
fraction `p` of noise rows on which decryption fails and the fraction `ε` of
noise rows that hit a given ciphertext, each under the key pair generated from
any key-noise row.

For a key pair generated at the seed `σ` and a message `m`, the seeds `r ≠ σ` whose
rows make decryption fail are, given the row at `σ`, independent events of
probability at most `p`. The probability that at least `k` of them fail is at most
`C(N - 1, k) · p ^ k` for `N = |Sd|` (a union bound over the `k`-subsets of seeds).
Outside these events, together with the seed `σ` itself, at most `k` coins fail,
so the bad-coin fraction is at most `k / N`; for `k < N` some coin decrypts
correctly. Spreadness is treated in the same way at the threshold `j / N`. A union
bound over the points `(φ, σ, m)` and `(φ, σ, m, c)` gives the total.

## Main definitions

* `badSeeds B σ G` — the seeds `r ≠ σ` whose row `G r` is `B`-related to `G σ`
* `failRel φ m v w`, `hitRel φ m c v w` — decryption of `m` fails, respectively
  the ciphertext of `m` is `c`, under the key pair from the key-noise row `v` and
  the encryption-noise row `w`
* `rowEquiv eD` — a table is its family of rows

## Main results

* `avg_pi_prod` — the uniform average of a product over the coordinates of a
  function is the product of the averages
* `avg_card_badSeeds_ge_le` — the probability that at least `k` seeds other than
  `σ` are bad is at most `C(|S| - 1, k) · p ^ k`
* `chainGood_prfScheme_of_small` — when every point has fewer than `k` failing
  and fewer than `j` hitting seeds besides its key seed, and `k < N`,
  `ChainGood (prfScheme F) (k / N) (j / N)` holds
* `avg_not_chainGood_prfScheme_le` — the weight of the tables outside `ChainGood`
  at `(k / N, j / N)` is at most
  `|Φ × Sd × M| · C(N - 1, k) · p ^ k + |Φ × Sd × M × C| · C(N - 1, j) · ε ^ j`
* `avg_qINDCCA_prfScheme_le` — `avg_qINDCCA_le` for `prfScheme` with that weight
* `choose_mul_pow_le` — `C(n, k) · p ^ k ≤ (n p) ^ k / k!`

## The hypotheses

The hypotheses `hp` and `hε` of `avg_not_chainGood_prfScheme_le` bound the failure
and the hit fraction for every key-noise row `v`, every point `φ`, message `m` and
ciphertext `c`. The thresholds of `ChainGood` in the bound are `Λ = k / N` and
`ε' = j / N`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open CatCrypt.Quantum CatCrypt.Quantum.QROM
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Crypto.MLKEM.PRFBadTable

open CatCrypt.Crypto.MLKEM.PRFOracle
open CatCrypt.Crypto.MLKEM.PRFAuxHop (prfScheme)
open CatCrypt.Quantum.QROM.PRFChain (ChainGood chainBound avg_qINDCCA_le)
open CatCrypt.Crypto.MLKEM.MLKEM512FailureBound (card_badVals_kemBad_div_le)

/-! ## Averages over functions -/

section Avg

/-- `avg` is invariant under an equivalence of its domain. -/
theorem avg_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ≥0∞) :
    avg (fun x => f (e x)) = avg f := by
  unfold avg
  rw [Fintype.card_congr e]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- The uniform average of a product over the coordinates of a function is the
product of the averages. -/
theorem avg_pi_prod {S V : Type} [Fintype S] [DecidableEq S] [Fintype V]
    (h : S → V → ℝ≥0∞) :
    avg (fun G : S → V => ∏ s, h s (G s)) = ∏ s, avg (h s) := by
  unfold avg
  rw [← Finset.mul_sum, ← Fintype.prod_sum, Fintype.card_fun]
  simp only [← Finset.mul_sum, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [Nat.cast_pow, ENNReal.inv_pow]

/-- The average of a Boolean indicator is the fraction of its true values. -/
theorem avg_boole {α : Type} [Fintype α] (P : α → Bool) :
    avg (fun x => if P x then (1 : ℝ≥0∞) else 0) =
      ((Finset.univ.filter fun x => P x).card : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞) := by
  unfold avg
  rw [← Finset.mul_sum, Finset.sum_boole, div_eq_mul_inv, mul_comm]

end Avg

/-! ## The number of bad seeds -/

section Tail

variable {S V : Type} [Fintype S] [DecidableEq S] [Fintype V] [Nonempty V] [DecidableEq V]

/-- The seeds `r ≠ σ` whose row `G r` is `B`-related to the row `G σ`. -/
def badSeeds (B : V → V → Bool) (σ : S) (G : S → V) : Finset S :=
  (Finset.univ.erase σ).filter fun r => B (G σ) (G r)

omit [Fintype S] [DecidableEq S] in
/-- The indicator that at least `k` elements of `U` satisfy `P` is at most the
number of `k`-subsets of `U` all of whose elements satisfy `P`. -/
theorem indicator_le_sum_powersetCard (U : Finset S) (P : S → Bool) (k : ℕ) :
    (if k ≤ (U.filter fun r => P r).card then 1 else 0 : ℝ≥0∞) ≤
      ∑ T ∈ U.powersetCard k, ∏ r ∈ T, (if P r then 1 else 0 : ℝ≥0∞) := by
  split_ifs with h
  · obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq h
    have hTU : T ∈ U.powersetCard k :=
      Finset.mem_powersetCard.2 ⟨hT.trans (Finset.filter_subset _ _), hcard⟩
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum
      (f := fun T => ∏ r ∈ T, (if P r then 1 else 0 : ℝ≥0∞)) (fun _ _ => zero_le) hTU)
    refine (Finset.prod_eq_one fun r hr => ?_).symm
    simp [(Finset.mem_filter.1 (hT hr)).2]
  · exact zero_le

/-- **Independent rows.** If for every row `v` the fraction of rows `w` with
`B v w` is at most `p`, then for a set `T` of seeds not containing `σ` the
probability over a uniform family of rows that every seed in `T` is related to
the row at `σ` is at most `p ^ |T|`. -/
theorem avg_prod_bad_le (B : V → V → Bool) (p : ℝ≥0∞)
    (hp : ∀ v, avg (fun w => if B v w then (1 : ℝ≥0∞) else 0) ≤ p) (σ : S) (T : Finset S)
    (hσ : σ ∉ T) :
    avg (fun G : S → V => ∏ r ∈ T, if B (G σ) (G r) then (1 : ℝ≥0∞) else 0) ≤ p ^ T.card := by
  have hsplit : ∀ G : S → V, (∏ r ∈ T, if B (G σ) (G r) then (1 : ℝ≥0∞) else 0) =
      ∑ v, ∏ s, ((if s = σ then (if G s = v then (1 : ℝ≥0∞) else 0) else 1) *
        (if s ∈ T then (if B v (G s) then (1 : ℝ≥0∞) else 0) else 1)) := by
    intro G
    rw [Finset.sum_eq_single (G σ)]
    · rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_mem]
      simp
    · intro v _ hv
      refine Finset.prod_eq_zero (Finset.mem_univ σ) ?_
      simp [Ne.symm hv]
    · simp
  simp_rw [hsplit]
  rw [avg_sum]
  calc ∑ v, avg (fun G : S → V => ∏ s, ((if s = σ then (if G s = v then (1 : ℝ≥0∞) else 0)
          else 1) * (if s ∈ T then (if B v (G s) then (1 : ℝ≥0∞) else 0) else 1)))
      = ∑ v, ∏ s, avg (fun w => (if s = σ then (if w = v then (1 : ℝ≥0∞) else 0) else 1) *
          (if s ∈ T then (if B v w then (1 : ℝ≥0∞) else 0) else 1)) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        exact avg_pi_prod (fun s w => (if s = σ then (if w = v then (1 : ℝ≥0∞) else 0) else 1) *
          (if s ∈ T then (if B v w then (1 : ℝ≥0∞) else 0) else 1))
    _ ≤ ∑ v : V, ∏ s : S, ((if s = σ then (Fintype.card V : ℝ≥0∞)⁻¹ else 1) *
          (if s ∈ T then p else 1)) := by
        refine Finset.sum_le_sum fun v _ => Finset.prod_le_prod' fun s _ => ?_
        by_cases hs : s = σ
        · subst hs
          simp only [ite_true, hσ, ite_false, mul_one]
          rw [avg_eq_inv_mul_sum]
          simp
        · by_cases hT : s ∈ T
          · simpa [hs, hT] using hp v
          · simp [hs, hT, avg_const]
    _ = ∑ _v : V, (Fintype.card V : ℝ≥0∞)⁻¹ * p ^ T.card := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_mem]
        simp
    _ = p ^ T.card := sum_inv_mul_const _

/-- **Tail bound for the number of bad seeds.** Under the row bound `p`, the
probability over a uniform family of rows that at least `k` seeds other than `σ`
are bad is at most `C(|S| - 1, k) · p ^ k`. -/
theorem avg_card_badSeeds_ge_le (B : V → V → Bool) (p : ℝ≥0∞)
    (hp : ∀ v, avg (fun w => if B v w then (1 : ℝ≥0∞) else 0) ≤ p) (σ : S) (k : ℕ) :
    avg (fun G : S → V => if k ≤ (badSeeds B σ G).card then (1 : ℝ≥0∞) else 0) ≤
      ((Fintype.card S - 1).choose k : ℝ≥0∞) * p ^ k := by
  calc avg (fun G : S → V => if k ≤ (badSeeds B σ G).card then (1 : ℝ≥0∞) else 0)
      ≤ avg (fun G : S → V => ∑ T ∈ (Finset.univ.erase σ).powersetCard k,
          ∏ r ∈ T, if B (G σ) (G r) then (1 : ℝ≥0∞) else 0) :=
        avg_mono fun G => indicator_le_sum_powersetCard _ (fun r => B (G σ) (G r)) k
    _ = ∑ T ∈ (Finset.univ.erase σ).powersetCard k,
          avg (fun G : S → V => ∏ r ∈ T, if B (G σ) (G r) then (1 : ℝ≥0∞) else 0) := by
        unfold avg
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ ∑ _T ∈ (Finset.univ.erase σ).powersetCard k, p ^ k := by
        refine Finset.sum_le_sum fun T hT => ?_
        obtain ⟨hsub, hc⟩ := Finset.mem_powersetCard.1 hT
        rw [← hc]
        exact avg_prod_bad_le B p hp σ T fun h => by simpa using hsub h
    _ = _ := by
        rw [Finset.sum_const, Finset.card_powersetCard,
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, nsmul_eq_mul]

omit [Fintype V] [Nonempty V] [DecidableEq V] in
/-- The seeds related to the row at `σ`, including `σ`, are at most one more than
`badSeeds`. -/
theorem card_filter_le_badSeeds (B : V → V → Bool) (σ : S) (G : S → V) :
    (Finset.univ.filter fun r => B (G σ) (G r)).card ≤ (badSeeds B σ G).card + 1 := by
  refine (Finset.card_le_card (t := insert σ (badSeeds B σ G)) fun r hr => ?_).trans
    (Finset.card_insert_le _ _)
  by_cases h : r = σ
  · exact h ▸ Finset.mem_insert_self _ _
  · refine Finset.mem_insert_of_mem ?_
    simp only [badSeeds, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hr ⊢
    exact ⟨h, hr.2⟩

end Tail

/-! ## The scheme with noise from the table -/

section Scheme

variable {Sd Nc PK SK M C R KS K Hash Φ : Type} {m₁ m₃ nF nK : ℕ}
  [Fintype Φ] [Nonempty Φ] [Fintype Sd] [Nonempty Sd] [DecidableEq Sd] [Fintype Nc]
  [DecidableEq Nc] [NeZero nF] [Fintype M] [DecidableEq M] [Fintype C] [DecidableEq C]
  [Fintype K] [Nonempty K] [DecidableEq Hash] [NeZero nK]
  (eD : (Sd × Nc) ≃ Fin m₃) (kg : Φ → KS → PK × SK) (enc : PK → M → R → C)
  (dec : SK → C → Option M) (eK : (Nc → Fin nF) → KS) (eE : (Nc → Fin nF) → R)
  (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eKR : (K × Sd) ≃ Fin nK)

/-- Decryption of `m` fails under the key pair generated at the public coins `φ`
from the key-noise row `v`, with the encryption-noise row `w`. -/
def failRel (φ : Φ) (m : M) (v w : Nc → Fin nF) : Bool :=
  decide (dec (kg φ (eK v)).2 (enc (kg φ (eK v)).1 m (eE w)) ≠ some m)

/-- The ciphertext of `m` under the public key generated at the public coins `φ`
from the key-noise row `v`, with the encryption-noise row `w`, is `c`. -/
def hitRel (φ : Φ) (m : M) (c : C) (v w : Nc → Fin nF) : Bool :=
  decide (enc (kg φ (eK v)).1 m (eE w) = c)

/-- A table is the family of its rows. -/
def rowEquiv : (Fin m₃ → Fin nF) ≃ (Sd → Nc → Fin nF) :=
  (Equiv.arrowCongr eD.symm (Equiv.refl _)).trans (Equiv.curry _ _ _)

omit [Fintype Sd] [Nonempty Sd] [DecidableEq Sd] [Fintype Nc] [DecidableEq Nc] [NeZero nF] in
theorem rowEquiv_apply (F : Fin m₃ → Fin nF) : rowEquiv eD F = prfRow eD F := rfl

/-- The uniform probability of a set of coins whose indicator has at most `k`
true values is at most `k / |α|`. -/
theorem toOuterMeasure_uniform_le {α : Type} [Fintype α] [Nonempty α] (P : α → Prop)
    [DecidablePred P] (k : ℕ) (h : (Finset.univ.filter P).card ≤ k) :
    (PMF.uniformFintype α).toOuterMeasure {r | P r} ≤ (k : ℝ≥0∞) / Fintype.card α := by
  classical
  rw [PMF.toOuterMeasure_uniformFintype_apply]
  gcongr
  rw [Fintype.card_ofFinset]
  exact_mod_cast h

omit [Fintype Φ] [Nonempty Φ] [Fintype Sd] [Nonempty Sd] [DecidableEq Sd] [Fintype Nc]
  [DecidableEq Nc] [NeZero nF] [Fintype M] [DecidableEq M] [Fintype C] [DecidableEq C]
  [Fintype K] [Nonempty K] [DecidableEq Hash] [NeZero nK] in
/-- A key pair in the support of `prfScheme F` is generated at some public coins
and seed. -/
theorem exists_of_keygen_prfScheme [Fintype Φ] [Nonempty Φ] [Fintype Sd] [Nonempty Sd]
    (F : Fin m₃ → Fin nF) (ks : PK × SK)
    (h : (prfScheme eD kg enc dec eK eE F).keygen ks ≠ 0) :
    ∃ φ σ, kg φ (eK (prfRow eD F σ)) = ks := by
  rw [← PMF.mem_support_iff] at h
  simp only [prfScheme, PMF.support_map, Set.mem_image] at h
  obtain ⟨⟨φ, σ⟩, _, he⟩ := h
  exact ⟨φ, σ, he⟩

omit [Fintype Nc] [DecidableEq Nc] [NeZero nF] [Fintype M] [Fintype C] in
/-- **`ChainGood` outside the bad points.** If at every public coins `φ`, key seed
`σ` and message `m` fewer than `k` seeds other than `σ` make decryption fail and,
for every ciphertext `c`, fewer than `j` seeds other than `σ` hit `c`, and
`k < |Sd|`, then `prfScheme F` satisfies `ChainGood` at `Λ = k / |Sd|` and
`ε = j / |Sd|`. -/
theorem chainGood_prfScheme_of_small (k j : ℕ) (hk : k < Fintype.card Sd)
    (F : Fin m₃ → Fin nF)
    (hfail : ∀ φ σ m, (badSeeds (failRel kg enc dec eK eE φ m) σ (prfRow eD F)).card < k)
    (hhit : ∀ φ σ m c, (badSeeds (hitRel kg enc eK eE φ m c) σ (prfRow eD F)).card < j) :
    ChainGood hpk eG eKR (prfScheme eD kg enc dec eK eE F) ((k : ℝ≥0∞) / Fintype.card Sd)
      ((j : ℝ≥0∞) / Fintype.card Sd) := by
  -- the failing coins at a generated key pair number at most `k`
  have hcnt : ∀ φ σ m, (Finset.univ.filter fun r : Sd =>
      dec (kg φ (eK (prfRow eD F σ))).2
        (enc (kg φ (eK (prfRow eD F σ))).1 m (eE (prfRow eD F r))) ≠ some m).card ≤ k := by
    intro φ σ m
    have h := card_filter_le_badSeeds (failRel kg enc dec eK eE φ m) σ (prfRow eD F)
    have h2 := hfail φ σ m
    simp only [failRel, decide_eq_true_eq] at h
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro pk sk hne m
    obtain ⟨φ, σ, he⟩ := exists_of_keygen_prfScheme eD kg enc dec eK eE F _ hne
    by_contra hno
    push Not at hno
    have hall : (Finset.univ.filter fun r : Sd =>
        dec (kg φ (eK (prfRow eD F σ))).2
          (enc (kg φ (eK (prfRow eD F σ))).1 m (eE (prfRow eD F r))) ≠ some m) =
        Finset.univ := by
      refine Finset.filter_true_of_mem fun r _ => ?_
      rw [he]
      exact hno r
    have := hcnt φ σ m
    rw [hall, Finset.card_univ] at this
    omega
  · intro pk sk hne x
    obtain ⟨φ, σ, he⟩ := exists_of_keygen_prfScheme eD kg enc dec eK eE F _ hne
    refine (card_badVals_kemBad_div_le _ hpk eG eKR pk sk x).trans ?_
    refine toOuterMeasure_uniform_le _ k ?_
    have := hcnt φ σ (eG.symm x).1
    simp only [he] at this
    exact this
  · intro ks hks m c
    obtain ⟨φ, σ, he⟩ := exists_of_keygen_prfScheme eD kg enc dec eK eE F _
      ((PMF.mem_support_iff _ _).1 hks)
    refine toOuterMeasure_uniform_le _ j ?_
    have h := card_filter_le_badSeeds (hitRel kg enc eK eE φ m c) σ (prfRow eD F)
    have h2 := hhit φ σ m c
    simp only [hitRel, decide_eq_true_eq, he] at h
    refine le_trans (le_of_eq ?_) (h.trans (Nat.succ_le_of_lt h2))
    rfl

omit [Fintype Nc] [DecidableEq Nc] [NeZero nF] in
open scoped Classical in
/-- The indicator that `ChainGood` fails at `(k / |Sd|, j / |Sd|)` is at most the
number of bad points: the points `(φ, σ, m)` with at least `k` failing seeds other
than `σ`, and the points `(φ, σ, m, c)` with at least `j` seeds other than `σ`
hitting `c`. -/
theorem indicator_not_chainGood_le (k j : ℕ) (hk : k < Fintype.card Sd)
    (F : Fin m₃ → Fin nF) :
    (if ChainGood hpk eG eKR (prfScheme eD kg enc dec eK eE F) ((k : ℝ≥0∞) / Fintype.card Sd)
        ((j : ℝ≥0∞) / Fintype.card Sd) then 0 else 1 : ℝ≥0∞) ≤
      (∑ x : Φ × Sd × M,
        if k ≤ (badSeeds (failRel kg enc dec eK eE x.1 x.2.2) x.2.1 (prfRow eD F)).card
        then 1 else 0) +
      ∑ x : Φ × Sd × M × C,
        if j ≤ (badSeeds (hitRel kg enc eK eE x.1 x.2.2.1 x.2.2.2) x.2.1 (prfRow eD F)).card
        then 1 else 0 := by
  split_ifs with hg
  · exact zero_le
  by_cases hf : ∀ φ σ m, (badSeeds (failRel kg enc dec eK eE φ m) σ (prfRow eD F)).card < k
  · by_cases hh : ∀ φ σ m c,
        (badSeeds (hitRel kg enc eK eE φ m c) σ (prfRow eD F)).card < j
    · exact absurd (chainGood_prfScheme_of_small eD kg enc dec eK eE hpk eG eKR k j hk F hf hh)
        hg
    · push Not at hh
      obtain ⟨φ, σ, m, c, h⟩ := hh
      refine le_trans ?_ le_add_self
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun _ _ => zero_le)
        (Finset.mem_univ (φ, σ, m, c)))
      simp [h]
  · push Not at hf
    obtain ⟨φ, σ, m, h⟩ := hf
    refine le_trans ?_ le_self_add
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun _ _ => zero_le)
      (Finset.mem_univ (φ, σ, m)))
    simp [h]

open scoped Classical in
/-- **The weight of the bad tables.** For a uniform table `F`, if under every key
pair generated from a key-noise row the fraction of encryption-noise rows on which
decryption fails is at most `p` and the fraction hitting any given ciphertext is at
most `ε`, then for `k < N = |Sd|` the tables at which `ChainGood (prfScheme F)` fails
at `(k / N, j / N)` have weight at most
`|Φ × Sd × M| · C(N - 1, k) · p ^ k + |Φ × Sd × M × C| · C(N - 1, j) · ε ^ j`. -/
theorem avg_not_chainGood_prfScheme_le (k j : ℕ) (hk : k < Fintype.card Sd) (p ε : ℝ≥0∞)
    (hp : ∀ φ m v, avg (fun w => if failRel kg enc dec eK eE φ m v w then (1 : ℝ≥0∞) else 0) ≤ p)
    (hε : ∀ φ m c v, avg (fun w => if hitRel kg enc eK eE φ m c v w then (1 : ℝ≥0∞) else 0) ≤ ε) :
    (avg fun F => if ChainGood hpk eG eKR (prfScheme eD kg enc dec eK eE F)
        ((k : ℝ≥0∞) / Fintype.card Sd) ((j : ℝ≥0∞) / Fintype.card Sd) then 0 else 1) ≤
      (Fintype.card (Φ × Sd × M) : ℝ≥0∞) * (((Fintype.card Sd - 1).choose k : ℝ≥0∞) * p ^ k) +
        (Fintype.card (Φ × Sd × M × C) : ℝ≥0∞) *
          (((Fintype.card Sd - 1).choose j : ℝ≥0∞) * ε ^ j) := by
  refine (avg_mono (indicator_not_chainGood_le eD kg enc dec eK eE hpk eG eKR k j hk)).trans ?_
  rw [avg_add, avg_sum, avg_sum]
  refine add_le_add ?_ ?_
  · refine (Finset.sum_le_sum fun x _ => ?_).trans (le_of_eq (by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]))
    exact (avg_equiv (rowEquiv eD) (fun G => if k ≤ (badSeeds (failRel kg enc dec eK eE x.1 x.2.2)
      x.2.1 G).card then (1 : ℝ≥0∞) else 0)).trans_le
      (avg_card_badSeeds_ge_le _ p (hp x.1 x.2.2) x.2.1 k)
  · refine (Finset.sum_le_sum fun x _ => ?_).trans (le_of_eq (by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]))
    exact (avg_equiv (rowEquiv eD) (fun G => if j ≤ (badSeeds (hitRel kg enc eK eE x.1 x.2.2.1
      x.2.2.2) x.2.1 G).card then (1 : ℝ≥0∞) else 0)).trans_le
      (avg_card_badSeeds_ge_le _ ε (hε x.1 x.2.2.1 x.2.2.2) x.2.1 j)

end Scheme

/-! ## The averaged KEM bound -/

section KEM

variable {Sd Nc PK SK M C R KS K Hash Z Φ : Type} {m₁ m₂ m₃ nF nK w q l c a : ℕ}
  [Fintype Φ] [Nonempty Φ] [Fintype Sd] [Nonempty Sd] [DecidableEq Sd] [Fintype Nc]
  [DecidableEq Nc] [NeZero nF] [Fintype PK] [Fintype SK] [Fintype M] [DecidableEq M]
  [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype C] [DecidableEq C]
  [Fintype K] [Nonempty K] [DecidableEq Hash]
  [NeZero nK] [NeZero c] [NeZero a] [NeZero (m₁ + m₂)] [NeZero (flatQ q l q)]
  (eD : (Sd × Nc) ≃ Fin m₃) (kg : Φ → KS → PK × SK) (enc : PK → M → R → C)
  (dec : SK → C → Option M) (eK : (Nc → Fin nF) → KS) (eE : (Nc → Fin nF) → R)
  (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × Sd) ≃ Fin nK) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

/-- **The quantum IND-CCA bound averaged over the noise table.** For the scheme
with noise from a uniform table and a family of adversaries `A F`, under the row
bounds `p` and `ε` and for `k < N = |Sd|`, the average advantage is at most
`|Φ × Sd × M| · C(N - 1, k) · p ^ k + |Φ × Sd × M × C| · C(N - 1, j) · ε ^ j` plus
`chainBound` at `Λ = k / N`, `ε = j / N` and the average one-wayness
probabilities. -/
theorem avg_qINDCCA_prfScheme_le (A : (Fin m₃ → Fin nF) → KEMQAdv m₁ m₂ nK w q l c a PK C K)
    (k j : ℕ) (hk : k < Fintype.card Sd) (p ε : ℝ≥0∞)
    (hp : ∀ φ m v, avg (fun w => if failRel kg enc dec eK eE φ m v w then (1 : ℝ≥0∞) else 0) ≤ p)
    (hε : ∀ φ m c v, avg (fun w => if hitRel kg enc eK eE φ m c v w then (1 : ℝ≥0∞) else 0) ≤ ε) :
    (avg fun F => qINDCCAAdvantage (prfScheme eD kg enc dec eK eE F) hpk eG eJ eKR eC eKa (A F)) ≤
      ((Fintype.card (Φ × Sd × M) : ℝ≥0∞) * (((Fintype.card Sd - 1).choose k : ℝ≥0∞) * p ^ k) +
        (Fintype.card (Φ × Sd × M × C) : ℝ≥0∞) *
          (((Fintype.card Sd - 1).choose j : ℝ≥0∞) * ε ^ j)) +
        chainBound (flatQ q l q) (flatQ (q + 4) l q) ((k : ℝ≥0∞) / Fintype.card Sd)
          ((j : ℝ≥0∞) / Fintype.card Sd) (Fintype.card Z : ℝ≥0∞)⁻¹
          (avg fun F => qOwcpaAux (prfScheme eD kg enc dec eK eE F) hpk eG eJ eKR eC eKa
            (owRedQuery (nfKEM (A F)) true))
          (avg fun F => qOwcpaAux (prfScheme eD kg enc dec eK eE F) hpk eG eJ eKR eC eKa
            (owRedQuery (nfKEM (A F)) false)) :=
  (avg_qINDCCA_le (Z := Z) hpk eG eJ eKR eC eKa (fun F => prfScheme eD kg enc dec eK eE F) A
    _ _).trans (add_le_add (avg_not_chainGood_prfScheme_le eD kg enc dec eK eE hpk eG eKR k j hk
      p ε hp hε) le_rfl)

end KEM

/-! ## The binomial term -/

/-- `C(n, k) · p ^ k ≤ (n p) ^ k / k!`. -/
theorem choose_mul_pow_le (n k : ℕ) (p : ℝ≥0∞) :
    (n.choose k : ℝ≥0∞) * p ^ k ≤ ((n : ℝ≥0∞) * p) ^ k / (k.factorial : ℝ≥0∞) := by
  have hf : (k.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [ENNReal.le_div_iff_mul_le (Or.inl hf) (Or.inl (ENNReal.natCast_ne_top _)), mul_pow]
  have h : (k.factorial * n.choose k : ℕ) ≤ n ^ k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow n k
  have h' : (n.choose k : ℝ≥0∞) * (k.factorial : ℝ≥0∞) ≤ (n : ℝ≥0∞) ^ k := by
    rw [mul_comm]; exact_mod_cast h
  calc (n.choose k : ℝ≥0∞) * p ^ k * (k.factorial : ℝ≥0∞)
      = (n.choose k : ℝ≥0∞) * (k.factorial : ℝ≥0∞) * p ^ k := by ring
    _ ≤ (n : ℝ≥0∞) ^ k * p ^ k := by gcongr

end CatCrypt.Crypto.MLKEM.PRFBadTable
