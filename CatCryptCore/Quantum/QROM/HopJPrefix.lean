/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.KEMQuantumGame
public import CatCryptCore.Quantum.QROM.FindToGuess

/-!
# The first U-step hop: `J(z, ·)` replaced by an independent table

In the IND-CCA game of `Quantum/QROM/KEMQuantumGame.lean` the adversary's
quantum oracle carries `J` on its second summand and decapsulation rejects
with `J(z, c)`. The first hop of the U-step (Hofheinz–Hövelmanns–Kiltz, TCC
2017, §4.2) replaces the adversary's view of `J` on the prefix `z` by an
independent uniform table `T`, while decapsulation keeps rejecting with
`J(z, ·)`. The two oracles agree outside the embedded set `{z} × C`, so the
averaged one-way-to-hiding bound of `Quantum/QROM/QAdvGame.lean` applies, and
the `Find` probability is bounded by the guessing probability of
`Quantum/QROM/FindToGuess.lean`. In the reprogrammed game the run depends on
`z` only through the projector onto `{z} × C`: reindexing the tables by the
involution that exchanges the prefix `z` of `J` with `T` makes the plain state
independent of `z`, and the projectors onto `{z} × C` for distinct `z` are
orthogonal, so the guessing probabilities summed over `z` are at most one.

## Main definitions

* `prefixUpdate eJ z J T` — the table `J` with the entries on `{z} × C`
  replaced by `T`
* `hopSet eJ z` — the punctured set: `{z} × C` embedded on the second summand
* `tabWeight n C` — the uniform weight `(n ^ |C|)⁻¹` of a table `C → Fin n`
* `kemJ'`, `kemOracle'` — the reprogrammed table and the reprogrammed merged
  oracle at an input and a table
* `prWinKEM'` — the winning probability with the reprogrammed oracle
* `hopJGame A b` — the hop as a `QGame` over `KEMInput × (C → Fin n)`
* `HopOuter`, `hopInput`, `hopWeight` — the part of an input other than `z`
  and the `J`-table, the input assembled from it, and its weight
* `decapsTable`, `hopChal`, `hopKey`, `hopDecaps`, `hopAdv` — decapsulation
  with the rejection key read from a table on the ciphertexts, the challenge
  ciphertext, the challenge key, the decapsulation function and the embedded
  adversary, as functions of the outer part
* `hopReindex eJ` — the bijection
  `KEMInput × (C → Fin n) ≃ (HopOuter × tables) × Z` that exchanges the
  prefix `z` of `J` with `T`

## Main results

* `prefixUpdate_agree` — `J` and `prefixUpdate eJ z J T` agree outside `{z} × C`
* `prWinKEM_eq_prWin`, `prWinKEM'_eq_prWin'` — the two winning probabilities
  are those of `hopJGame`
* `hopJ_o2h` — `|prWinKEM − prWinKEM'| ≤ 4 √(q' · prFindAvg (hopJGame A b))`
* `sum_nrm_sq_projS_le` — for pairwise disjoint sets the squared norms of the
  projections sum to at most the squared norm
* `sum_guessProb_hopSet_le_one` — the guessing probabilities at `{z} × C`
  summed over `z` are at most one
* `kemDecaps_hopInput`, `hopJGame_summand` — the game at the reindexed input
  depends on `z` only through the punctured set
* `sum_prod_mul_le_inv_card` — a weighted sum over `α × β` with inner sums at
  most one and weights depending on `α` alone is at most `|β|⁻¹`
* `prFindAvg_hopJ_le` — `prFindAvg (hopJGame A b) ≤ 4 q' / |Z|`
* `hopJ`, `hopJ'` — `|prWinKEM − prWinKEM'| ≤ 4 √(q' · 4 q' / |Z|) = 8 q' / √|Z|`

## The model

In `prWinKEM'` the decapsulation oracle of the reprogrammed game uses the secret
key. The table `T` is a uniform table of range encodings `C → Fin n`, read
through `eKR` and projected to the key as `J` is, so that the key the adversary
sees on the prefix is uniform. The embedded query count is
`q' = flatQ q k q = (k + 1) q`.

## References

* [Hofheinz, Hövelmanns, Kiltz — A Modular Analysis of the Fujisaki–Okamoto
  Transformation, TCC 2017], §4.2
* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], §3, Theorem 2
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Reprogramming a table on a prefix -/

section Prefix

variable {m₂ n : ℕ} {Z C : Type} (eJ : (Z × C) ≃ Fin m₂)

/-- The table `J` with the entries on `{z} × C` replaced by `T`. -/
def prefixUpdate [DecidableEq Z] (z : Z) (J : Fin m₂ → Fin n) (T : C → Fin n) :
    Fin m₂ → Fin n :=
  fun y => if (eJ.symm y).1 = z then T (eJ.symm y).2 else J y

/-- The set `{z} × C` on the second summand. -/
def prefixSet [Fintype C] (z : Z) : Finset (Fin m₂) := Finset.univ.image fun c => eJ (z, c)

theorem mem_prefixSet [Fintype C] (z : Z) (y : Fin m₂) :
    y ∈ prefixSet eJ z ↔ (eJ.symm y).1 = z := by
  simp only [prefixSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, rfl⟩; simp
  · intro h
    refine ⟨(eJ.symm y).2, ?_⟩
    rw [← h, Prod.mk.eta, Equiv.apply_symm_apply]

variable [DecidableEq Z]

theorem prefixUpdate_apply_prefix (z : Z) (J : Fin m₂ → Fin n) (T : C → Fin n) (c : C) :
    prefixUpdate eJ z J T (eJ (z, c)) = T c := by
  simp [prefixUpdate]

theorem prefixUpdate_prefix (z : Z) (J : Fin m₂ → Fin n) (T : C → Fin n) :
    (fun c => prefixUpdate eJ z J T (eJ (z, c))) = T := by
  funext c; exact prefixUpdate_apply_prefix eJ z J T c

/-- Updating twice on the same prefix, the second time with the original
    entries, restores the table. -/
theorem prefixUpdate_prefixUpdate (z : Z) (J : Fin m₂ → Fin n) (T : C → Fin n) :
    prefixUpdate eJ z (prefixUpdate eJ z J T) (fun c => J (eJ (z, c))) = J := by
  funext y
  simp only [prefixUpdate]
  by_cases h : (eJ.symm y).1 = z
  · rw [ite_eq_left h, ← h, Prod.mk.eta, Equiv.apply_symm_apply]
  · rw [ite_eq_right h, ite_eq_right h]

/-- `J` and `prefixUpdate eJ z J T` agree outside `prefixSet eJ z`. -/
theorem prefixUpdate_agree [Fintype C] (z : Z) (J : Fin m₂ → Fin n) (T : C → Fin n) :
    ∀ y, y ∉ prefixSet eJ z → J y = prefixUpdate eJ z J T y := by
  intro y hy
  rw [mem_prefixSet] at hy
  simp [prefixUpdate, hy]

end Prefix

/-! ## The punctured set on the merged domain -/

section HopSet

variable {m₁ m₂ : ℕ} {Z C : Type} [Fintype C] (eJ : (Z × C) ≃ Fin m₂)

/-- The punctured set of the hop: `{z} × C` on the second summand. -/
def hopSet (z : Z) : Finset (Fin (m₁ + m₂)) := mergeSet ∅ (prefixSet eJ z)

theorem mem_hopSet (z : Z) (x : Fin (m₁ + m₂)) :
    x ∈ hopSet (m₁ := m₁) eJ z ↔ ∃ y ∈ prefixSet eJ z, Fin.natAdd m₁ y = x := by
  simp [hopSet, mergeSet]

/-- The punctured sets of distinct prefixes are disjoint. -/
theorem hopSet_disjoint (z z' : Z) (x : Fin (m₁ + m₂)) (hz : x ∈ hopSet (m₁ := m₁) eJ z)
    (hz' : x ∈ hopSet (m₁ := m₁) eJ z') : z = z' := by
  rw [mem_hopSet] at hz hz'
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨y', hy', h⟩ := hz'
  have hval := congrArg Fin.val h
  simp only [Fin.val_natAdd] at hval
  have hyy : y' = y := Fin.ext (by omega)
  subst hyy
  rw [mem_prefixSet] at hy hy'
  rw [← hy, ← hy']

end HopSet

/-! ## The uniform weight of a table -/

section TabWeight

variable (n : ℕ) (C : Type) [Fintype C] [DecidableEq C] [NeZero n]

/-- The uniform weight `(n ^ |C|)⁻¹` of a table `C → Fin n`. -/
def tabWeight : ℝ≥0∞ := ((n : ℝ≥0∞) ^ Fintype.card C)⁻¹

/-- The table weights sum to one. -/
theorem sum_tabWeight : ∑ _T : C → Fin n, tabWeight n C = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow, tabWeight]
  exact ENNReal.mul_inv_cancel (pow_ne_zero _ (by exact_mod_cast NeZero.ne n))
    (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))

end TabWeight

/-! ## The reprogrammed game -/

section Game

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K] [Nonempty K]
  [Nonempty R] [Fintype C] [DecidableEq C] (P : Scheme PK SK M C R) (hpk : PK → Hash)
  (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c)
  (eKa : K ≃ Fin a)

/-- The adversary's `J`-table at an input, reprogrammed on the prefix `z` by `T`. -/
def kemJ' (i : KEMInput PK SK Z M K m₁ m₂ n) (T : C → Fin n) : Fin m₂ → Fin n :=
  prefixUpdate eJ i.2.1 i.2.2.2.2.2 T

/-- The merged oracle at an input with the `J`-table reprogrammed by `T`. -/
def kemOracle' (i : KEMInput PK SK Z M K m₁ m₂ n) (T : C → Fin n) : Fin (m₁ + m₂) → Fin n :=
  mergeOracle i.2.2.2.2.1 (kemJ' eJ i T)

omit [Fintype PK] [Fintype SK] [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Fintype K]
  [Nonempty K] [DecidableEq C] in
/-- `kemOracle i` and `kemOracle' i T` agree outside `hopSet eJ z`. -/
theorem kemOracle_agree (i : KEMInput PK SK Z M K m₁ m₂ n) (T : C → Fin n) :
    ∀ x, x ∉ hopSet (m₁ := m₁) eJ i.2.1 → kemOracle i x = kemOracle' eJ i T x :=
  mergeOracle_agree (fun _ _ => rfl) (prefixUpdate_agree eJ i.2.1 i.2.2.2.2.2 T)

variable [NeZero n] [NeZero c]

/-- The probability that `A` outputs `1` in the game with bit `b` when the
    adversary's oracle is reprogrammed on the prefix `z` by an independent
    uniform table `T`; decapsulation still rejects with `J(z, ·)`. -/
def prWinKEM' (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) : ℝ≥0∞ :=
  ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ T : C → Fin n, tabWeight n C * kemSample P i *
    prOutMR (A.run i.1.1 (kemChal P hpk eG eKR i) (kemKey hpk eG eKR i b)) (kemOracle' eJ i T)
      (kemDecaps P hpk eG eJ eKR eC eKa i)

/-- The hop as a `QGame` over the input and the table: the adversary is the
    single-run embedding of `A` at the decapsulation function, the oracle is
    `kemOracle i`, the reprogrammed oracle is `kemOracle' i T`, and the
    punctured set is `hopSet eJ z`. -/
def hopJGame (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    QGame (m₁ + m₂) n (ancW c k (2 * w)) (flatQ q k q)
      (KEMInput PK SK Z M K m₁ m₂ n × (C → Fin n)) where
  sample p := tabWeight n C * kemSample P p.1
  sample_sum := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.sum_mul, sum_tabWeight, one_mul]
    exact kemSample_sum (Z := Z) (K := K) P eKR
  adv p := toQAdv (A.run p.1.1.1 (kemChal P hpk eG eKR p.1) (kemKey hpk eG eKR p.1 b))
    (kemDecaps P hpk eG eJ eKR eC eKa p.1)
  oracle p := kemOracle p.1
  oracle' p := kemOracle' eJ p.1 p.2
  S p := hopSet eJ p.1.2.1
  agree p := kemOracle_agree eJ p.1 p.2
  pure p := by
    obtain ⟨ψ, hψ⟩ := A.pure p.1.1.1 (kemChal P hpk eG eKR p.1) (kemKey hpk eG eKR p.1 b)
    exact pure_toQAdv _ _ hψ

/-- The winning probability of the IND-CCA game is `prWin` of the hop game. -/
theorem prWinKEM_eq_prWin (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    prWinKEM P hpk eG eJ eKR eC eKa A b = prWin (hopJGame P hpk eG eJ eKR eC eKa A b) := by
  unfold prWinKEM prWin
  conv_rhs => rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hopJGame, ← prOutMR_eq, mul_assoc, ← Finset.sum_mul, sum_tabWeight, one_mul]

/-- The reprogrammed winning probability is `prWin'` of the hop game. -/
theorem prWinKEM'_eq_prWin' (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    prWinKEM' P hpk eG eJ eKR eC eKa A b = prWin' (hopJGame P hpk eG eJ eKR eC eKa A b) := by
  simp only [prWinKEM', prWin', hopJGame, Fintype.sum_prod_type, prOutMR_eq]

/-- The one-way-to-hiding step of the hop:
    `|prWinKEM − prWinKEM'| ≤ 4 √(q' · prFindAvg (hopJGame A b))` with
    `q' = flatQ q k q`. -/
theorem hopJ_o2h (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    absDiff (prWinKEM P hpk eG eJ eKR eC eKa A b) (prWinKEM' P hpk eG eJ eKR eC eKa A b) ≤
      4 * ((flatQ q k q : ℝ≥0∞) * prFindAvg (hopJGame P hpk eG eJ eKR eC eKa A b)) ^
        (1 / 2 : ℝ) := by
  rw [prWinKEM_eq_prWin, prWinKEM'_eq_prWin']
  exact o2h_avg _

end Game

/-! ## Projections onto disjoint sets -/

section Orth

variable {d : ℕ}

/-- The squared norm is the sum of the squared moduli of the entries. -/
theorem nrm_sq_eq_sum (v : Fin d → ℂ) : nrm v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  unfold nrm
  rw [EuclideanSpace.norm_sq_eq]

variable (m n w : ℕ) {ι : Type} [Fintype ι]

/-- For pairwise disjoint sets `S i`, the squared norms of the projections
    `projS (S i) v` sum to at most the squared norm of `v`. -/
theorem sum_nrm_sq_projS_le (S : ι → Finset (Fin m))
    (hS : ∀ i i' x, x ∈ S i → x ∈ S i' → i = i') (v : Fin (m * n * w) → ℂ) :
    ∑ i, nrm (projS m n w (S i) *ᵥ v) ^ 2 ≤ nrm v ^ 2 := by
  simp only [nrm_sq_eq_sum, projS_eq_diagonal, mulVec_diagonal]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun k _ => ?_
  have hterm : ∀ i, ‖indS m (S i) (xPart m n w k) * v k‖ ^ 2 =
      if xPart m n w k ∈ S i then ‖v k‖ ^ 2 else 0 := by
    intro i
    simp only [indS, norm_mul]
    split_ifs <;> simp
  simp only [hterm]
  by_cases h : ∃ i, xPart m n w k ∈ S i
  · obtain ⟨i₀, hi₀⟩ := h
    rw [Finset.sum_eq_single i₀ (fun i _ hi => ite_eq_right fun hx => hi (hS i i₀ _ hx hi₀))
      (fun h => absurd (Finset.mem_univ _) h), ite_eq_left hi₀]
  · push Not at h
    simp only [h, ite_false, Finset.sum_const_zero]
    positivity

end Orth

/-! ## The guessing probabilities summed over the prefix -/

section Guess

variable {m₁ m₂ n w' q' : ℕ} [NeZero n] {Z C : Type} [Fintype Z] [Fintype C]
  (eJ : (Z × C) ≃ Fin m₂)

/-- The guessing probabilities of one adversary at the punctured sets
    `hopSet eJ z`, summed over `z`, are at most one: the projectors are
    orthogonal and the plain state has norm one. -/
theorem sum_guessProb_hopSet_le_one (A : QAdv (m₁ + m₂) n w' q') (H : Fin (m₁ + m₂) → Fin n)
    (j : Fin q') {ψ : Fin ((m₁ + m₂) * n * w') → ℂ} (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    ∑ z, guessProb A H (hopSet (m₁ := m₁) eJ z) j ≤ 1 := by
  simp only [guessProb_eq_nrm_sq A H _ j hpure]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => sq_nonneg _), ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  have hnrm : nrm (plainState A H ψ j) = 1 := by
    rw [← prefixU_mulVec, nrm_mulVec_of_mem_unitaryGroup (prefixU A H j).prop,
      nrm_eq_one_of_init A hpure]
  calc ∑ z, nrm (projS (m₁ + m₂) n w' (hopSet eJ z) *ᵥ plainState A H ψ j) ^ 2
      ≤ nrm (plainState A H ψ j) ^ 2 :=
        sum_nrm_sq_projS_le (m₁ + m₂) n w' (hopSet eJ) (hopSet_disjoint eJ) _
    _ = 1 := by rw [hnrm, one_pow]

end Guess

/-! ## The reindexed game -/

section Reindex

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K] [Nonempty K]
  [Nonempty R] [Fintype C] [DecidableEq C] (P : Scheme PK SK M C R) (hpk : PK → Hash)
  (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c)
  (eKa : K ≃ Fin a)

/-- The part of a game input other than `z` and the `J`-table: the key pair,
    the challenge message, the fake key and the `G`-table. -/
abbrev HopOuter (PK SK M K : Type) (m₁ n : ℕ) : Type :=
  (PK × SK) × M × K × (Fin m₁ → Fin n)

/-- The game input assembled from its outer part, the prefix and the `J`-table. -/
abbrev hopInput (o : HopOuter PK SK M K m₁ n) (z : Z) (J : Fin m₂ → Fin n) :
    KEMInput PK SK Z M K m₁ m₂ n :=
  (o.1, z, o.2.1, o.2.2.1, o.2.2.2, J)

/-- The weight of a game input as a function of its outer part: `keygen` on the
    key pair, the rest uniform. -/
def hopWeight (Z : Type) [Fintype Z] (m₂ : ℕ) (o : HopOuter PK SK M K m₁ n) : ℝ≥0∞ :=
  P.keygen o.1 * (Fintype.card Z : ℝ≥0∞)⁻¹ * (Fintype.card M : ℝ≥0∞)⁻¹ *
    (Fintype.card K : ℝ≥0∞)⁻¹ * ((n : ℝ≥0∞) ^ m₁)⁻¹ * ((n : ℝ≥0∞) ^ m₂)⁻¹

omit [Fintype PK] [Fintype SK] [Nonempty M] [Nonempty Z] [DecidableEq Z] [Nonempty K] [Nonempty R]
  [Fintype C] [DecidableEq C] in
theorem kemSample_hopInput (o : HopOuter PK SK M K m₁ n) (z : Z) (J : Fin m₂ → Fin n) :
    kemSample P (hopInput o z J) = hopWeight P Z m₂ o := rfl

/-- The involution on `KEMInput × (C → Fin n)`, written as a bijection onto
    `(HopOuter × tables) × Z`, that exchanges the prefix `z` of `J` with `T`. -/
def hopReindex : KEMInput PK SK Z M K m₁ m₂ n × (C → Fin n) ≃
    (HopOuter PK SK M K m₁ n × ((Fin m₂ → Fin n) × (C → Fin n))) × Z where
  toFun p := (((p.1.1, p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2.1),
    (prefixUpdate eJ p.1.2.1 p.1.2.2.2.2.2 p.2, fun c => p.1.2.2.2.2.2 (eJ (p.1.2.1, c)))), p.1.2.1)
  invFun r := (hopInput r.1.1 r.2 (prefixUpdate eJ r.2 r.1.2.1 r.1.2.2),
    fun c => r.1.2.1 (eJ (r.2, c)))
  left_inv p := by
    obtain ⟨⟨ks, z, x, Kf, G, J⟩, T⟩ := p
    simp only [prefixUpdate_prefixUpdate, prefixUpdate_prefix]
  right_inv r := by
    obtain ⟨⟨⟨ks, x, Kf, G⟩, ⟨J, T⟩⟩, z⟩ := r
    simp only [prefixUpdate_prefixUpdate, prefixUpdate_prefix]

/-- The challenge ciphertext as a function of the outer part. -/
def hopChal (o : HopOuter PK SK M K m₁ n) : C :=
  P.enc o.1.1 o.2.1 (eKR.symm (o.2.2.2 (eG (o.2.1, hpk o.1.1)))).2

/-- The challenge key as a function of the outer part and the bit. -/
def hopKey (o : HopOuter PK SK M K m₁ n) (b : Bool) : K :=
  if b then (eKR.symm (o.2.2.2 (eG (o.2.1, hpk o.1.1)))).1 else o.2.2.1

omit [Fintype PK] [Fintype SK] [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z]
  [Fintype K] [Nonempty K] [Nonempty R] [Fintype C] [DecidableEq C] in
theorem kemChal_hopInput (o : HopOuter PK SK M K m₁ n) (z : Z) (J : Fin m₂ → Fin n) :
    kemChal P hpk eG eKR (hopInput o z J) = hopChal P hpk eG eKR o := rfl

omit [Fintype PK] [Fintype SK] [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z]
  [Fintype K] [Nonempty K] [Nonempty R] [Fintype C] [DecidableEq C] in
theorem kemKey_hopInput (o : HopOuter PK SK M K m₁ n) (z : Z) (J : Fin m₂ → Fin n) (b : Bool) :
    kemKey hpk eG eKR (hopInput o z J) b = hopKey hpk eG eKR o b := rfl

omit [Fintype PK] [Fintype SK] [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z]
  [Fintype K] [Nonempty K] [Fintype C] [DecidableEq C] in
/-- Decapsulation of `fips203 P hpk` at the fixed oracle `g` with the rejection
    key read from the table `T` on the ciphertext: `decapsFixed` with
    `j (z, c) = T c`, as a function of `sk` and `pk` alone. -/
def decapsTable (g : M × Hash → K × R) (T : C → K) (sk : SK) (pk : PK) (c : C) : K :=
  match P.dec sk c with
  | none => T c
  | some m => if P.enc pk m (g (m, hpk pk)).2 = c then (g (m, hpk pk)).1 else T c

omit [Fintype PK] [Fintype SK] [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z]
  [Fintype K] [Nonempty K] [Nonempty R] [Fintype C] in
/-- `decapsFixed` at a rejection function that is `T` on the prefix `z` is
    `decapsTable` at `T`. -/
theorem decapsFixed_eq_decapsTable (g : M × Hash → K × R) (j : Z × C → K) (T : C → K)
    (sk : SK) (pk : PK) (z : Z) (h : ∀ c, j (z, c) = T c) (c : C) :
    decapsFixed P hpk g j (sk, pk, z) c = decapsTable P hpk g T sk pk c := by
  unfold decapsFixed decapsTable
  cases P.dec sk c <;> simp [h]

/-- Decapsulation with the rejection key read from the table `T` on the
    ciphertext alone, the challenge excluded, as a function of the outer part. -/
def hopDecaps (o : HopOuter PK SK M K m₁ n) (T : C → Fin n) : Fin c → Fin a :=
  fun x => if eC.symm x = hopChal P hpk eG eKR o then eKa (Classical.arbitrary K)
    else eKa (decapsTable P hpk (fun y => eKR.symm (o.2.2.2 (eG y))) (fun c => (eKR.symm (T c)).1)
      o.1.2 o.1.1 (eC.symm x))

omit [Fintype PK] [Fintype SK] [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z]
  [Fintype K] [Nonempty R] [Fintype C] in
/-- The decapsulation function at `hopInput o z J` is `hopDecaps o (J(z, ·))`. -/
theorem kemDecaps_hopInput (o : HopOuter PK SK M K m₁ n) (z : Z) (J : Fin m₂ → Fin n) :
    kemDecaps P hpk eG eJ eKR eC eKa (hopInput o z J) = hopDecaps P hpk eG eKR eC eKa o
      (fun c => J (eJ (z, c))) := by
  unfold kemDecaps
  rw [kemChal_hopInput]
  funext x
  simp only [hopDecaps, decapsOracle]
  by_cases h : eC.symm x = hopChal P hpk eG eKR o
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, decapsFixed_eq_decapsTable P hpk (kemG eG eKR (hopInput o z J))
      (kemJ eJ eKR (hopInput o z J)) (fun c => (eKR.symm (J (eJ (z, c)))).1) o.1.2 o.1.1 z
      (fun c => rfl)]
    rfl

/-- The embedded adversary at the outer part and the table. -/
def hopAdv (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) (o : HopOuter PK SK M K m₁ n)
    (T : C → Fin n) [NeZero c] : QAdv (m₁ + m₂) n (ancW c k (2 * w)) (flatQ q k q) :=
  toQAdv (A.run o.1.1 (hopChal P hpk eG eKR o) (hopKey hpk eG eKR o b))
    (hopDecaps P hpk eG eKR eC eKa o T)

omit [Fintype PK] [Fintype SK] [Fintype M] [Nonempty M] [Fintype K] [Nonempty R] [Fintype C] in
/-- The embedded adversary has a pure initial state. -/
theorem hopAdv_pure (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (o : HopOuter PK SK M K m₁ n) (T : C → Fin n) [NeZero c] :
    ∃ ψ, (hopAdv P hpk eG eKR eC eKa A b o T).init.val = vecMulVec ψ (star ψ) := by
  obtain ⟨ψ, hψ⟩ := A.pure o.1.1 (hopChal P hpk eG eKR o) (hopKey hpk eG eKR o b)
  exact pure_toQAdv _ _ hψ

/-- A weighted sum over `α × β` whose inner sums over `β` are at most one, with
    weights that depend on `α` alone and sum to one over `α × β`, is at most
    `|β|⁻¹`. -/
theorem sum_prod_mul_le_inv_card {α β : Type} [Fintype α] [Fintype β] (wt : α → ℝ≥0∞)
    (g : α → β → ℝ≥0∞) (hg : ∀ x, ∑ y, g x y ≤ 1) (hwt : ∑ r : α × β, wt r.1 = 1) :
    ∑ r : α × β, wt r.1 * g r.1 r.2 ≤ (Fintype.card β : ℝ≥0∞)⁻¹ := by
  have hw : ∑ x, wt x = (Fintype.card β : ℝ≥0∞)⁻¹ := by
    rw [Fintype.sum_prod_type] at hwt
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] at hwt
    rw [ENNReal.eq_inv_of_mul_eq_one_left hwt, inv_inv]
  calc ∑ r : α × β, wt r.1 * g r.1 r.2 = ∑ x, wt x * ∑ y, g x y := by
        rw [Fintype.sum_prod_type]; simp only [Finset.mul_sum]
    _ ≤ ∑ x, wt x * 1 := Finset.sum_le_sum fun x _ => by gcongr; exact hg x
    _ = (Fintype.card β : ℝ≥0∞)⁻¹ := by rw [← hw]; simp only [mul_one]

variable [NeZero n] [NeZero c]

/-- The summand of the guessing sum at the reindexed input: the weight is that
    of the outer part, the adversary is `hopAdv o T`, the oracle is
    `mergeOracle G J`, and the punctured set is `hopSet eJ z`. -/
theorem hopJGame_summand (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (j : Fin (flatQ q k q))
    (r : (HopOuter PK SK M K m₁ n × ((Fin m₂ → Fin n) × (C → Fin n))) × Z) :
    (hopJGame P hpk eG eJ eKR eC eKa A b).sample ((hopReindex eJ).symm r) *
      guessProb ((hopJGame P hpk eG eJ eKR eC eKa A b).adv ((hopReindex eJ).symm r))
        ((hopJGame P hpk eG eJ eKR eC eKa A b).oracle' ((hopReindex eJ).symm r))
        ((hopJGame P hpk eG eJ eKR eC eKa A b).S ((hopReindex eJ).symm r)) j =
    tabWeight n C * hopWeight P Z m₂ r.1.1 *
      guessProb (hopAdv P hpk eG eKR eC eKa A b r.1.1 r.1.2.2) (mergeOracle r.1.1.2.2.2 r.1.2.1)
        (hopSet eJ r.2) j := by
  simp only [hopJGame, hopReindex, Equiv.coe_fn_symm_mk, hopAdv, kemOracle', kemJ',
    kemSample_hopInput, kemChal_hopInput, kemKey_hopInput, kemDecaps_hopInput,
    prefixUpdate_prefixUpdate, prefixUpdate_apply_prefix]

/-- The guessing sum at query `j` over the whole game is at most `|Z|⁻¹`. -/
theorem sum_guess_hopJ_le (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (j : Fin (flatQ q k q)) :
    ∑ p, (hopJGame P hpk eG eJ eKR eC eKa A b).sample p *
      guessProb ((hopJGame P hpk eG eJ eKR eC eKa A b).adv p)
        ((hopJGame P hpk eG eJ eKR eC eKa A b).oracle' p)
        ((hopJGame P hpk eG eJ eKR eC eKa A b).S p) j ≤ (Fintype.card Z : ℝ≥0∞)⁻¹ := by
  rw [← Fintype.sum_equiv (hopReindex eJ).symm _ _ (fun _ => rfl)]
  simp only [hopJGame_summand]
  refine sum_prod_mul_le_inv_card
    (α := HopOuter PK SK M K m₁ n × ((Fin m₂ → Fin n) × (C → Fin n))) (β := Z)
    (fun s => tabWeight n C * hopWeight P Z m₂ s.1)
    (fun s z => guessProb (hopAdv P hpk eG eKR eC eKa A b s.1 s.2.2)
      (mergeOracle s.1.2.2.2 s.2.1) (hopSet eJ z) j) (fun s => ?_) ?_
  · obtain ⟨ψ, hψ⟩ := hopAdv_pure P hpk eG eKR eC eKa A b s.1 s.2.2
    exact sum_guessProb_hopSet_le_one eJ _ _ j hψ
  · calc ∑ r : (HopOuter PK SK M K m₁ n × ((Fin m₂ → Fin n) × (C → Fin n))) × Z,
          tabWeight n C * hopWeight P Z m₂ r.1.1
        = ∑ r, (hopJGame P hpk eG eJ eKR eC eKa A b).sample ((hopReindex eJ).symm r) :=
          Finset.sum_congr rfl fun r _ => rfl
      _ = ∑ p, (hopJGame P hpk eG eJ eKR eC eKa A b).sample p :=
          Fintype.sum_equiv (hopReindex eJ).symm _ _ fun _ => rfl
      _ = 1 := (hopJGame P hpk eG eJ eKR eC eKa A b).sample_sum

/-- `prFindAvg (hopJGame A b) ≤ 4 q' / |Z|` with `q' = flatQ q k q`. -/
theorem prFindAvg_hopJ_le (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    prFindAvg (hopJGame P hpk eG eJ eKR eC eKa A b) ≤
      4 * (flatQ q k q : ℝ≥0∞) * (Fintype.card Z : ℝ≥0∞)⁻¹ := by
  set G := hopJGame P hpk eG eJ eKR eC eKa A b with hG
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
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ => by ring
    _ ≤ 4 * ∑ _j : Fin (flatQ q k q), (Fintype.card Z : ℝ≥0∞)⁻¹ := by
        gcongr with j
        exact sum_guess_hopJ_le P hpk eG eJ eKR eC eKa A b j
    _ = 4 * (flatQ q k q : ℝ≥0∞) * (Fintype.card Z : ℝ≥0∞)⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- The first hop of the U-step:
    `|prWinKEM − prWinKEM'| ≤ 4 √(q' · 4 q' / |Z|)` with `q' = flatQ q k q`. -/
theorem hopJ (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    absDiff (prWinKEM P hpk eG eJ eKR eC eKa A b) (prWinKEM' P hpk eG eJ eKR eC eKa A b) ≤
      4 * ((flatQ q k q : ℝ≥0∞) *
        (4 * (flatQ q k q : ℝ≥0∞) * (Fintype.card Z : ℝ≥0∞)⁻¹)) ^ (1 / 2 : ℝ) := by
  refine (hopJ_o2h P hpk eG eJ eKR eC eKa A b).trans ?_
  have := prFindAvg_hopJ_le P hpk eG eJ eKR eC eKa A b
  gcongr

/-- `√(x² · y) = x · √y` in `ℝ≥0∞`. -/
theorem rpow_half_sq_mul (x y : ℝ≥0∞) : (x ^ 2 * y) ^ (1 / 2 : ℝ) = x * y ^ (1 / 2 : ℝ) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- The first hop of the U-step in closed form:
    `|prWinKEM − prWinKEM'| ≤ 8 q' / √|Z|` with `q' = flatQ q k q`.

    References: Saito, Xagawa, Yamakawa, "Tightly-secure key encapsulation
    mechanism in the quantum random oracle model", EUROCRYPT 2018, ePrint
    2017/1005; Hövelmanns, Kiltz, Schäge, Unruh, "Generic authenticated key
    exchange in the quantum random oracle model", PKC 2020, ePrint 2018/928 (the
    pseudorandomness of the implicit-rejection key `J(z, ·)` to an adversary
    that cannot guess `z`). -/
theorem hopJ' (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    absDiff (prWinKEM P hpk eG eJ eKR eC eKa A b) (prWinKEM' P hpk eG eJ eKR eC eKa A b) ≤
      8 * (flatQ q k q : ℝ≥0∞) * ((Fintype.card Z : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) := by
  refine (hopJ P hpk eG eJ eKR eC eKa A b).trans (le_of_eq ?_)
  rw [show (flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) * (Fintype.card Z : ℝ≥0∞)⁻¹) =
    (2 * (flatQ q k q : ℝ≥0∞)) ^ 2 * (Fintype.card Z : ℝ≥0∞)⁻¹ by ring, rpow_half_sq_mul]
  ring

end Reindex

end CatCrypt.Quantum.QROM
