/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.PRFOracle
public import CatCryptCore.Crypto.MLKEM.FIPS203QROMQuantumMLWE

/-!
# The quantum IND-CCA bound averaged over a table that the scheme reads

When the K-PKE reads its noise from a random table `F` (`PRF_η` as a random
oracle), the scheme is a family `P F` and the quantum IND-CCA bound of the
Fujisaki–Okamoto KEM is applied at each `F` and averaged. This module carries
the bound of `qINDCCA_le_qOwcpaAux_numeric_coll` through the average: the
one-wayness terms enter under square roots, which are concave, and the
correctness and collision hypotheses are required only on a set of good
tables, whose complement enters the bound with its weight.

## Main definitions

* `chainBound q₁ q₂ Λ ε ζ x₁ x₀` — the bound of `qINDCCA_le_qOwcpaAux_numeric_coll`
  with every correctness term `Λ`, collision term `ε`, `ζ = |Z|⁻¹` and
  one-wayness terms `x₁`, `x₀`
* `ChainGoodColl P hpk eG eKR Λ ε` — the hypotheses of that theorem at the
  constant failure bound `Λ`: a correctly decrypting coin for every message, the
  bad-coin fraction at most `Λ` at every point, and the bound `collWeight P ≤ ε`
  on the coin-collision weight (`Quantum/QROM/CollisionWeight.lean`)
* `ChainGood P hpk eG eKR Λ ε` — the same with the collision bound replaced by
  `ε`-spreadness, which implies it

## Main results

* `qINDCCA_le_chainBound` — for one scheme, the advantage is at most `chainBound`
  at the one-wayness probabilities of `owRedQuery (nfKEM A) b`
* `avg_rpow_half_le` — `avg (f ^ (1/2)) ≤ (avg f) ^ (1/2)`
* `avg_chainBound_le`, `avg_chainBound_all_le` — the average of `chainBound` is
  at most `chainBound` at the averages, with every argument allowed to depend on
  the table in the second form
* `qINDCCA_le_chainBound_coll`, `avg_qINDCCA_le_coll` — the two bounds under
  `ChainGoodColl`
* `avg_qINDCCA_le` — for families `P F` and `A F`, the average advantage is at
  most the weight of the tables outside `ChainGood` plus `chainBound` at the
  average one-wayness probabilities
* `qOwcpaAux_le_qIndcpaAuxPr_true` — the one-wayness probability is at most the
  probability that `indRed B` outputs `1` at `b = true`, plus `corrErr P`
* `avg_qOwcpaAux_le_of_close` — when the averaged IND-CPA probabilities of
  `indRed (B F)` are within `δ` of two values `I₁`, `I₀`, the averaged
  one-wayness probability is at most `|I₁ - I₀| + |M|⁻¹ + 2 δ` plus the averaged
  decryption error

## Scope

The average is taken over the adversaries `A F` as a family: `avg_qINDCCA_le`
holds for every function `F ↦ A F`. The one-wayness to IND-CPA step is kept in
its signed form (`qOwcpaAux_le_qIndcpaAuxPr_true`,
`qIndcpaAuxPr_indRed_false_le`), because an average of absolute differences is
not bounded by the absolute difference of the averages that the PRF hop
`PRFOracle.absDiff_prfReal_prfIdeal` controls.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.QROM
open CatCrypt.Crypto.PKE.Games (Scheme)
open CatCrypt.Crypto.MLKEM.FIPS203QROMQuantumMLWE (qINDCCA_le_qOwcpaAux_numeric_coll)
open CatCrypt.Crypto.MLKEM.PRFOracle (avg avg_mono avg_const avg_add avg_mul_left
  avg_le_one absDiff_avg_le absDiff_le_one)

noncomputable section

namespace CatCrypt.Quantum.QROM.PRFChain

/-! ## The bound -/

section Bound

/-- The bound of `qINDCCA_le_qOwcpaAux_numeric_coll` with `q₁ = flatQ q k q`,
`q₂ = flatQ (q + 4) k q`, every correctness term `Λ`, collision term `ε`,
`ζ = |Z|⁻¹` and one-wayness terms `x₁` at `b = true` and `x₀` at `b = false`. -/
def chainBound (q₁ q₂ : ℕ) (Λ ε ζ x₁ x₀ : ℝ≥0∞) : ℝ≥0∞ :=
  (4 * ((q₁ : ℝ≥0∞) * (4 * (q₁ : ℝ≥0∞) * (x₁ + Λ))) ^ (1 / 2 : ℝ) +
      (8 * (q₁ : ℝ≥0∞) * Λ ^ (1 / 2 : ℝ) + (Λ + ε) + 8 * (q₁ : ℝ≥0∞) * Λ ^ (1 / 2 : ℝ)) +
      4 * ((q₁ : ℝ≥0∞) * (4 * (q₁ : ℝ≥0∞) * (x₀ + Λ))) ^ (1 / 2 : ℝ)) +
    2 * (8 * (q₁ : ℝ≥0∞) * ζ ^ (1 / 2 : ℝ) +
      (8 * (q₂ : ℝ≥0∞) * Λ ^ (1 / 2 : ℝ) + Λ + 8 * (q₁ : ℝ≥0∞) * Λ ^ (1 / 2 : ℝ)))

/-- `chainBound` is monotone in the one-wayness terms. -/
theorem chainBound_mono (q₁ q₂ : ℕ) (Λ ε ζ : ℝ≥0∞) {x₁ x₁' x₀ x₀' : ℝ≥0∞} (h₁ : x₁ ≤ x₁')
    (h₀ : x₀ ≤ x₀') : chainBound q₁ q₂ Λ ε ζ x₁ x₀ ≤ chainBound q₁ q₂ Λ ε ζ x₁' x₀' := by
  unfold chainBound
  gcongr

/-- `chainBound` is monotone in the failure bound, the collision bound and the
one-wayness terms. -/
theorem chainBound_mono_all (q₁ q₂ : ℕ) (ζ : ℝ≥0∞) {Λ Λ' ε ε' x₁ x₁' x₀ x₀' : ℝ≥0∞}
    (hΛ : Λ ≤ Λ') (hε : ε ≤ ε') (h₁ : x₁ ≤ x₁') (h₀ : x₀ ≤ x₀') :
    chainBound q₁ q₂ Λ ε ζ x₁ x₀ ≤ chainBound q₁ q₂ Λ' ε' ζ x₁' x₀' := by
  unfold chainBound
  gcongr

end Bound

/-! ## One scheme -/

section OneScheme

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

/-- The hypotheses of `qINDCCA_le_qOwcpaAux_numeric_coll` at the constant failure
bound `Λ`: every generated key pair has a correctly decrypting coin for every
message, the fraction of bad `G`-values at every point is at most `Λ`, and the
coin-collision weight `collWeight P` is at most `ε`. -/
def ChainGoodColl (P : Scheme PK SK M C R) (Λ ε : ℝ≥0∞) : Prop :=
  (∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ m, ∃ ρ, P.dec sk (P.enc pk m ρ) = some m) ∧
    (∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ Λ) ∧
    collWeight P ≤ ε

/-- `ChainGoodColl` with the collision bound replaced by `ε`-spreadness of the
scheme, which implies it (`collWeight_le_of_isSpread`). -/
def ChainGood [NeZero n] (P : Scheme PK SK M C R) (Λ ε : ℝ≥0∞) : Prop :=
  (∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ m, ∃ ρ, P.dec sk (P.enc pk m ρ) = some m) ∧
    (∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ Λ) ∧
    P.IsSpread ε

omit [Fintype PK] [Fintype SK] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K] [Nonempty K]
  [Fintype C] in
/-- `ChainGood` implies `ChainGoodColl` at the same parameters. -/
theorem chainGoodColl_of_chainGood [NeZero n] (P : Scheme PK SK M C R) (Λ ε : ℝ≥0∞)
    (h : ChainGood hpk eG eKR P Λ ε) : ChainGoodColl hpk eG eKR P Λ ε :=
  ⟨h.1, h.2.1, collWeight_le_of_isSpread P ε h.2.2⟩

variable [NeZero n] [NeZero c] [NeZero a] [NeZero (m₁ + m₂)] [NeZero (flatQ q k q)]

open scoped Classical in
/-- **The quantum IND-CCA bound of one scheme in the form `chainBound`.** Under
`ChainGoodColl P Λ ε`, the advantage of `A` is at most `chainBound` at the
one-wayness probabilities of `owRedQuery (nfKEM A) b` in `qOwcpaAux`. -/
theorem qINDCCA_le_chainBound_coll (P : Scheme PK SK M C R) (A : KEMQAdv m₁ m₂ n w q k c a PK C K)
    (Λ ε : ℝ≥0∞) (hgood : ChainGoodColl hpk eG eKR P Λ ε) :
    qINDCCAAdvantage P hpk eG eJ eKR eC eKa A ≤
      chainBound (flatQ q k q) (flatQ (q + 4) k q) Λ ε (Fintype.card Z : ℝ≥0∞)⁻¹
        (qOwcpaAux P hpk eG eJ eKR eC eKa (owRedQuery (nfKEM A) true))
        (qOwcpaAux P hpk eG eJ eKR eC eKa (owRedQuery (nfKEM A) false)) := by
  obtain ⟨hcoin, hlam, hcoll⟩ := hgood
  rw [← qINDCCAAdvantage_nfKEM]
  refine (qINDCCA_le_qOwcpaAux_numeric_coll P hpk eG eJ eKR eC eKa (nfKEM A) hcoin (fun _ => Λ)
    hlam ε hcoll (2 * (w * nfX c a k)) (nfKEM_hw w c a k (m₁ + m₂))
    (fun _ _ _ => nfAns (m₁ + m₂) n c a k w) (nfKEM_hseg A) (nfKEM_hrounds A)
    (nfKEM_hinit A)).trans ?_
  have hΛ := deltaStar_le_Lambda P hpk eG eKR (Z := Z) (m₂ := m₂) (fun _ => Λ) hlam
  have hsum : ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * Λ = Λ := by
    rw [← Finset.sum_mul, kemSample_sum (Z := Z) (K := K) P eKR, one_mul]
  rw [hsum] at hΛ ⊢
  unfold chainBound
  gcongr

open scoped Classical in
/-- `qINDCCA_le_chainBound_coll` under `ChainGood P Λ ε`. -/
theorem qINDCCA_le_chainBound (P : Scheme PK SK M C R) (A : KEMQAdv m₁ m₂ n w q k c a PK C K)
    (Λ ε : ℝ≥0∞) (hgood : ChainGood hpk eG eKR P Λ ε) :
    qINDCCAAdvantage P hpk eG eJ eKR eC eKa A ≤
      chainBound (flatQ q k q) (flatQ (q + 4) k q) Λ ε (Fintype.card Z : ℝ≥0∞)⁻¹
        (qOwcpaAux P hpk eG eJ eKR eC eKa (owRedQuery (nfKEM A) true))
        (qOwcpaAux P hpk eG eJ eKR eC eKa (owRedQuery (nfKEM A) false)) :=
  qINDCCA_le_chainBound_coll hpk eG eJ eKR eC eKa P A Λ ε
    (chainGoodColl_of_chainGood hpk eG eKR P Λ ε hgood)

end OneScheme

/-! ## Averages over the table -/

section Average

variable {T : Type} [Fintype T] [Nonempty T]

/-- The square root of an average is at least the average of the square roots. -/
theorem avg_rpow_half_le (f : T → ℝ≥0∞) :
    avg (fun F => f F ^ (1 / 2 : ℝ)) ≤ (avg f) ^ (1 / 2 : ℝ) :=
  sum_mul_rpow_half_le (fun _ => (Fintype.card T : ℝ≥0∞)⁻¹) f
    (by simpa using sum_inv_mul_const (α := T) (1 : ℝ≥0∞))

/-- The average of `4 √(q₁ (4 q₁ (x + Λ)))` is at most its value at the average
of `x`. -/
theorem avg_sqrtTerm_le (q₁ : ℕ) (Λ : ℝ≥0∞) (x : T → ℝ≥0∞) :
    avg (fun F => 4 * ((q₁ : ℝ≥0∞) * (4 * (q₁ : ℝ≥0∞) * (x F + Λ))) ^ (1 / 2 : ℝ)) ≤
      4 * ((q₁ : ℝ≥0∞) * (4 * (q₁ : ℝ≥0∞) * (avg x + Λ))) ^ (1 / 2 : ℝ) := by
  rw [avg_mul_left]
  gcongr
  refine (avg_rpow_half_le _).trans (le_of_eq ?_)
  rw [avg_mul_left, avg_mul_left, avg_add, avg_const]

/-- The average of `chainBound` is at most `chainBound` at the averages. -/
theorem avg_chainBound_le (q₁ q₂ : ℕ) (Λ ε ζ : ℝ≥0∞) (x₁ x₀ : T → ℝ≥0∞) :
    avg (fun F => chainBound q₁ q₂ Λ ε ζ (x₁ F) (x₀ F)) ≤
      chainBound q₁ q₂ Λ ε ζ (avg x₁) (avg x₀) := by
  unfold chainBound
  rw [avg_add, avg_add, avg_add, avg_const, avg_const]
  gcongr
  · exact avg_sqrtTerm_le q₁ Λ x₁
  · exact avg_sqrtTerm_le q₁ Λ x₀

/-- The average of `chainBound` over a table on which the failure bound, the
collision bound and the one-wayness terms all depend is at most `chainBound` at
the averages: every term is linear in `Λ` and `ε` or the square root of a
quantity linear in `Λ` and the one-wayness terms. -/
theorem avg_chainBound_all_le (q₁ q₂ : ℕ) (ζ : ℝ≥0∞) (Λ ε x₁ x₀ : T → ℝ≥0∞) :
    avg (fun F => chainBound q₁ q₂ (Λ F) (ε F) ζ (x₁ F) (x₀ F)) ≤
      chainBound q₁ q₂ (avg Λ) (avg ε) ζ (avg x₁) (avg x₀) := by
  unfold chainBound
  simp only [avg_add, avg_const, avg_mul_left]
  gcongr
  all_goals exact (avg_rpow_half_le _).trans (le_of_eq (by simp only [avg_mul_left, avg_add]))

omit [Nonempty T] in
/-- A quantity at most one, bounded by `B F` on the tables where `good` holds, has
average at most the weight of the tables where `good` fails plus the average
of `B`. -/
theorem avg_le_bad_add (good : T → Prop) [DecidablePred good] (v B : T → ℝ≥0∞)
    (hv : ∀ F, v F ≤ 1) (h : ∀ F, good F → v F ≤ B F) :
    avg v ≤ avg (fun F => if good F then 0 else 1) + avg B := by
  rw [← avg_add]
  refine avg_mono fun F => ?_
  by_cases hF : good F
  · rw [if_pos hF, zero_add]
    exact h F hF
  · rw [if_neg hF]
    exact (hv F).trans le_self_add

end Average

/-! ## Families of schemes and adversaries -/

section Family

variable {T : Type} [Fintype T] [Nonempty T]
  {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
  [NeZero n] [NeZero c] [NeZero a] [NeZero (m₁ + m₂)] [NeZero (flatQ q k q)]

omit [Nonempty T] [DecidableEq M] [Nonempty M] [Nonempty Z] [DecidableEq Z] [Fintype R]
  [Nonempty R] [Fintype C] [DecidableEq Hash] [NeZero c] [NeZero a] [NeZero (m₁ + m₂)]
  [NeZero (flatQ q k q)] in
/-- The advantage of the game whose table is drawn uniformly is at most the
average of the advantages at each table. -/
theorem absDiff_avg_prWinKEM_le (P : T → Scheme PK SK M C R)
    (A : T → KEMQAdv m₁ m₂ n w q k c a PK C K) :
    absDiff (avg fun F => prWinKEM (P F) hpk eG eJ eKR eC eKa (A F) true)
        (avg fun F => prWinKEM (P F) hpk eG eJ eKR eC eKa (A F) false) ≤
      avg fun F => qINDCCAAdvantage (P F) hpk eG eJ eKR eC eKa (A F) :=
  absDiff_avg_le _ _

open scoped Classical in
/-- **The quantum IND-CCA bound averaged over a table.** For a family of schemes
`P F` and adversaries `A F`, the average advantage is at most the weight of the
tables at which `ChainGood (P F) Λ ε` fails, plus `chainBound` at the averages
over `F` of the one-wayness probabilities of `owRedQuery (nfKEM (A F)) b`. -/
theorem avg_qINDCCA_le (P : T → Scheme PK SK M C R) (A : T → KEMQAdv m₁ m₂ n w q k c a PK C K)
    (Λ ε : ℝ≥0∞) :
    (avg fun F => qINDCCAAdvantage (P F) hpk eG eJ eKR eC eKa (A F)) ≤
      (avg fun F => if ChainGood hpk eG eKR (P F) Λ ε then 0 else 1) +
        chainBound (flatQ q k q) (flatQ (q + 4) k q) Λ ε (Fintype.card Z : ℝ≥0∞)⁻¹
          (avg fun F => qOwcpaAux (P F) hpk eG eJ eKR eC eKa (owRedQuery (nfKEM (A F)) true))
          (avg fun F => qOwcpaAux (P F) hpk eG eJ eKR eC eKa (owRedQuery (nfKEM (A F)) false)) :=
  (avg_le_bad_add (fun F => ChainGood hpk eG eKR (P F) Λ ε) _ _
    (fun F => absDiff_le_one (prWinKEM_le_one (P F) hpk eG eJ eKR eC eKa (A F) true)
      (prWinKEM_le_one (P F) hpk eG eJ eKR eC eKa (A F) false))
    (fun F hF => qINDCCA_le_chainBound hpk eG eJ eKR eC eKa (P F) (A F) Λ ε hF)).trans
    (add_le_add le_rfl (avg_chainBound_le _ _ _ _ _ _ _))

open scoped Classical in
/-- `avg_qINDCCA_le` with `ChainGood` replaced by `ChainGoodColl`. -/
theorem avg_qINDCCA_le_coll (P : T → Scheme PK SK M C R)
    (A : T → KEMQAdv m₁ m₂ n w q k c a PK C K) (Λ ε : ℝ≥0∞) :
    (avg fun F => qINDCCAAdvantage (P F) hpk eG eJ eKR eC eKa (A F)) ≤
      (avg fun F => if ChainGoodColl hpk eG eKR (P F) Λ ε then 0 else 1) +
        chainBound (flatQ q k q) (flatQ (q + 4) k q) Λ ε (Fintype.card Z : ℝ≥0∞)⁻¹
          (avg fun F => qOwcpaAux (P F) hpk eG eJ eKR eC eKa (owRedQuery (nfKEM (A F)) true))
          (avg fun F => qOwcpaAux (P F) hpk eG eJ eKR eC eKa (owRedQuery (nfKEM (A F)) false)) :=
  (avg_le_bad_add (fun F => ChainGoodColl hpk eG eKR (P F) Λ ε) _ _
    (fun F => absDiff_le_one (prWinKEM_le_one (P F) hpk eG eJ eKR eC eKa (A F) true)
      (prWinKEM_le_one (P F) hpk eG eJ eKR eC eKa (A F) false))
    (fun F hF => qINDCCA_le_chainBound_coll hpk eG eJ eKR eC eKa (P F) (A F) Λ ε hF)).trans
    (add_le_add le_rfl (avg_chainBound_le _ _ _ _ _ _ _))

end Family

/-! ## One-wayness from IND-CPA in signed form -/

section Signed

variable {m₁ m₂ n W q k c a : ℕ} {PK SK M C R K Hash Z ι : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Fintype C] [DecidableEq C] [DecidableEq Hash] [Fintype ι]
  [Nonempty Z] [Nonempty R] [Nonempty ι]
  (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a) [NeZero n] [NeZero c]

omit [Nonempty R] in
/-- The one-wayness probability of `B` is at most the probability that `indRed B`
outputs `1` at `b = true`, plus the decryption error. -/
theorem qOwcpaAux_le_qIndcpaAuxPr_true (P : Scheme PK SK M C R)
    (B : QOwAuxAdv ι (m₁ + m₂) n W q k c a PK C K) :
    qOwcpaAux P hpk eG eJ eKR eC eKa B ≤
      qIndcpaAuxPr P hpk eG eJ eKR eC eKa (indRed eG B) true + corrErr P := by
  rw [qOwcpaAux_eq_auxTabAvg, qIndcpaAuxPr_indRed_true]
  calc _ ≤ ∑ ks : PK × SK, P.keygen ks * ∑ m : M, (Fintype.card M : ℝ≥0∞)⁻¹ *
        auxTabAvg (fun r z G J Hq T => (∑ x : ι, (Fintype.card ι : ℝ≥0∞)⁻¹ *
          prOut (owPrefixAt eG eC eKa B ks.1 (P.enc ks.1 m r) Hq x m)
            (auxOracle P hpk eG eJ eKR ks.1 Hq G J T z)) +
          if P.dec ks.2 (P.enc ks.1 m r) = some m then 0 else 1) := by
        gcongr with ks _ m _
        exact auxTabAvg_mono fun r z G J Hq T =>
          qOwcpaAuxRun_le P hpk eG eJ eKR eC eKa B ks.1 ks.2 m r Hq G J T z
    _ = _ := by
        unfold corrErr
        simp only [auxTabAvg_add, auxTabAvg_of_coins, mul_add, Finset.sum_add_distrib]

variable {T : Type} [Fintype T] [Nonempty T]

/-- The averaged one-wayness probability from averaged IND-CPA probabilities: if
the averages over `F` of the probabilities that `indRed (B F)` outputs `1` are
within `δ` of `I₁` at `b = true` and of `I₀` at `b = false`, the averaged
one-wayness probability is at most `|I₁ - I₀| + |M|⁻¹ + 2 δ` plus the averaged
decryption error. -/
theorem avg_qOwcpaAux_le_of_close (P : T → Scheme PK SK M C R)
    (B : T → QOwAuxAdv ι (m₁ + m₂) n W q k c a PK C K) (I₁ I₀ δ : ℝ≥0∞)
    (h₁ : (avg fun F => qIndcpaAuxPr (P F) hpk eG eJ eKR eC eKa (indRed eG (B F)) true) ≤
      I₁ + δ)
    (h₀ : I₀ ≤ (avg fun F => qIndcpaAuxPr (P F) hpk eG eJ eKR eC eKa (indRed eG (B F)) false) +
      δ) :
    (avg fun F => qOwcpaAux (P F) hpk eG eJ eKR eC eKa (B F)) ≤
      absDiff I₁ I₀ + (Fintype.card M : ℝ≥0∞)⁻¹ + 2 * δ + avg fun F => corrErr (P F) := by
  have hfalse : (avg fun F => qIndcpaAuxPr (P F) hpk eG eJ eKR eC eKa (indRed eG (B F)) false) ≤
      (Fintype.card M : ℝ≥0∞)⁻¹ :=
    (avg_mono fun F => qIndcpaAuxPr_indRed_false_le (P F) hpk eG eJ eKR eC eKa (B F)).trans
      (avg_const _).le
  have hI₁ : I₁ ≤ absDiff I₁ I₀ + I₀ := le_tsub_add.trans (add_le_add (le_max_left _ _) le_rfl)
  calc (avg fun F => qOwcpaAux (P F) hpk eG eJ eKR eC eKa (B F))
      ≤ avg fun F => qIndcpaAuxPr (P F) hpk eG eJ eKR eC eKa (indRed eG (B F)) true +
          corrErr (P F) :=
        avg_mono fun F => qOwcpaAux_le_qIndcpaAuxPr_true hpk eG eJ eKR eC eKa (P F) (B F)
    _ = (avg fun F => qIndcpaAuxPr (P F) hpk eG eJ eKR eC eKa (indRed eG (B F)) true) +
          avg fun F => corrErr (P F) := avg_add _ _
    _ ≤ (absDiff I₁ I₀ + ((Fintype.card M : ℝ≥0∞)⁻¹ + δ) + δ) + avg fun F => corrErr (P F) := by
        gcongr
        exact h₁.trans (add_le_add (hI₁.trans (add_le_add le_rfl (h₀.trans
          (add_le_add hfalse le_rfl)))) le_rfl)
    _ = _ := by ring

end Signed

end CatCrypt.Quantum.QROM.PRFChain

end

end
