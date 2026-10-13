/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleSimulation
public import CatCryptCore.Crypto.PRPPRFSwitching

/-!
# Public-key encryption: schemes with explicit coins and their security games

A public-key encryption scheme `Scheme PK SK M C R` has probabilistic key
generation, encryption `enc pk m r` with explicit coins `r : R` drawn uniformly,
and decryption `dec sk c : Option M` (`none` is the rejection symbol). The games
follow Hofheinz–Hövelmanns–Kiltz (TCC 2017), Section 2.1: keys are sampled by the
challenger, the adversary receives the public key, and every oracle is
implemented by the challenger.

* **OW-CPA**: on `(pk, c*)` with `c* ← Enc(pk, m*)` for uniform `m*`, the adversary
  outputs `m'` and wins when `Dec(sk, c*) = m'`.
* **OW-PCA**: as OW-CPA with a plaintext-checking oracle `Pco(m, c) = [Dec(sk, c) = m]`.
* **OW-PCVA**: as OW-PCA with a ciphertext-validity oracle `Cvo(c) = [Dec(sk, c) ≠ ⊥]`
  that answers `false` on the challenge ciphertext.
* **IND-CPA**: the adversary chooses `(m₀, m₁)` on `pk` and guesses from
  `Enc(pk, m_b)`.
* **IND-CCA**: as IND-CPA with a decryption oracle in both stages; the challenger
  records the challenge ciphertext and the oracle answers `none` on it.

Query bounds are fields of the adversary structures. Advantages of the
indistinguishability games are distances between the game with `b = true` and
the game with `b = false`, which is twice `|Pr[b' = b] − 1/2|`.

The scheme parameters `corrWorst` (the δ of δ-correctness, an expectation over
keys of the worst-message decryption-failure probability), `corrErr` (the
failure probability for a uniform message) and `IsSpread ε` (every ciphertext has
probability at most `ε = 2^(−γ)` under fresh coins) are information-theoretic
quantities of the scheme.

## Main definitions

* `Scheme`, `Scheme.encDist`, `Scheme.pco`
* `Scheme.failProb`, `Scheme.corrWorst`, `Scheme.IsCorrect`, `Scheme.corrErr`,
  `Scheme.IsSpread`
* `owcpaGame`, `owcpaAdvantage`; `OWPCAAdversary`, `owpcaGame`, `owpcaAdvantage`;
  `OWPCVAAdversary`, `owpcvaGame`, `owpcvaAdvantage`
* `INDCPAAdversary`, `indcpaGame`, `indcpaAdvantage`
* `INDCCAAdversary`, `decOracle`, `indccaGame`, `indccaAdvantage`
* `ROMScheme`, `romPcaOracle`, `ROMOWPCAAdversary`, `romOWPCAGame`, `romOWPCAAdvantage` —
  schemes whose encryption and decryption query a lazily sampled random oracle, and
  their OW-PCA game, in which the challenger, the adversary and the
  plaintext-checking oracle share the table of the random oracle

## Main results

* `corrErr_le_corrWorst` — the uniform-message failure probability is at most δ
* `owcpa_le_indcpa` — for every OW-CPA adversary `A`,
  `owcpaAdvantage P A ≤ indcpaAdvantage P (owToIndcpa A) + 1/|M| + P.corrErr`

## References

* D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the
  Fujisaki–Okamoto Transformation*, TCC 2017, ePrint 2017/604, Section 2.1.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PKE.Games

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open scoped ENNReal

/-- A public-key encryption scheme with public keys `PK`, secret keys `SK`,
messages `M`, ciphertexts `C` and encryption coins `R`. -/
structure Scheme (PK SK M C R : Type) where
  /-- Key generation, returning `(pk, sk)`. -/
  keygen : PMF (PK × SK)
  /-- Encryption of a message with explicit coins. -/
  enc : PK → M → R → C
  /-- Decryption; `none` rejects the ciphertext. -/
  dec : SK → C → Option M

namespace Scheme

variable {PK SK M C R : Type} [Fintype R] [Nonempty R] (P : Scheme PK SK M C R)

/-- The ciphertext distribution of `m` under `pk` with uniform coins. -/
noncomputable def encDist (pk : PK) (m : M) : PMF C :=
  (PMF.uniformOfFintype R).map (P.enc pk m)

/-- The plaintext-checking predicate `[Dec(sk, c) = m]`. -/
def pco [DecidableEq M] (sk : SK) (m : M) (c : C) : Bool :=
  decide (P.dec sk c = some m)

/-- The probability over uniform coins that encrypting `m` under `pk` does not
decrypt to `m` under `sk`. -/
noncomputable def failProb (pk : PK) (sk : SK) (m : M) : ℝ≥0∞ :=
  (PMF.uniformOfFintype R).toOuterMeasure {r | P.dec sk (P.enc pk m r) ≠ some m}

/-- The correctness error δ: the expectation over key pairs of the largest
decryption-failure probability over messages. -/
noncomputable def corrWorst : ℝ≥0∞ :=
  ∑' ks, P.keygen ks * ⨆ m, P.failProb ks.1 ks.2 m

/-- δ-correctness: `corrWorst ≤ δ`. -/
def IsCorrect (δ : ℝ≥0∞) : Prop := P.corrWorst ≤ δ

/-- The decryption-failure probability for a uniform message and uniform coins,
averaged over key pairs. -/
noncomputable def corrErr [Fintype M] [Nonempty M] : ℝ≥0∞ :=
  ∑' ks, P.keygen ks * ∑' m, PMF.uniformOfFintype M m * P.failProb ks.1 ks.2 m

/-- `ε`-spreadness (`ε = 2^(−γ)` for γ-spread): for every generated key pair, every
message and every ciphertext, uniform coins hit the ciphertext with probability at
most `ε`. -/
def IsSpread (ε : ℝ≥0∞) : Prop :=
  ∀ ks ∈ P.keygen.support, ∀ (m : M) (c : C),
    (PMF.uniformOfFintype R).toOuterMeasure {r | P.enc ks.1 m r = c} ≤ ε

/-- The uniform-message failure probability is at most the correctness error. -/
theorem corrErr_le_corrWorst [Fintype M] [Nonempty M] : P.corrErr ≤ P.corrWorst := by
  refine ENNReal.tsum_le_tsum fun ks => mul_le_mul_right ?_ _
  calc ∑' m, PMF.uniformOfFintype M m * P.failProb ks.1 ks.2 m
      ≤ ∑' m, PMF.uniformOfFintype M m * ⨆ m', P.failProb ks.1 ks.2 m' :=
        ENNReal.tsum_le_tsum fun m => mul_le_mul_right (le_iSup (P.failProb ks.1 ks.2) m) _
    _ = ⨆ m', P.failProb ks.1 ks.2 m' := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Scheme

variable {PK SK M C R : Type} [Fintype R] [Nonempty R]

/-! ## One-wayness -/

section OW

variable [Fintype M] [Nonempty M] [DecidableEq M] (P : Scheme PK SK M C R)

/-- The OW-CPA experiment against the adversary `A` on `(pk, c*)`. -/
noncomputable def owcpaGame (A : PK → C → PMF M) : PMF Bool :=
  P.keygen.bind fun ks => (PMF.uniformOfFintype M).bind fun m =>
    (P.encDist ks.1 m).bind fun c => (A ks.1 c).map fun m' => P.pco ks.2 m' c

/-- The OW-CPA advantage. -/
noncomputable def owcpaAdvantage (A : PK → C → PMF M) : ℝ≥0∞ :=
  prTrue (pmfGame (owcpaGame P A)) Heap.empty

/-- The plaintext-checking oracle for the secret key `sk`, without state. -/
noncomputable def pcoOracle (sk : SK) (_ : Unit) (q : M × C) : PMF (Bool × Unit) :=
  PMF.pure (P.pco sk q.1 q.2, ())

variable (PK M C) in
/-- An OW-PCA adversary with at most `q` plaintext-checking queries. -/
structure OWPCAAdversary (q : ℕ) : Type 1 where
  /-- The adversary on the public key and the challenge ciphertext. -/
  run : PK → C → OracleAdv (M × C) Bool M
  /-- The query bound. -/
  isQueryBound : ∀ pk c, (run pk c).IsQueryBound q

/-- The OW-PCA experiment. -/
noncomputable def owpcaGame {q : ℕ} (A : OWPCAAdversary PK M C q) : PMF Bool :=
  P.keygen.bind fun ks => (PMF.uniformOfFintype M).bind fun m =>
    (P.encDist ks.1 m).bind fun c =>
      (OracleAdv.run (pcoOracle P ks.2) (A.run ks.1 c) ()).map fun x => P.pco ks.2 x.1 c

/-- The OW-PCA advantage. -/
noncomputable def owpcaAdvantage {q : ℕ} (A : OWPCAAdversary PK M C q) : ℝ≥0∞ :=
  prTrue (pmfGame (owpcaGame P A)) Heap.empty

/-- The plaintext-checking and ciphertext-validity oracles for `sk` and the
challenge ciphertext `c*`; the validity oracle answers `false` on `c*`. -/
noncomputable def pcvaOracle [DecidableEq C] (sk : SK) (cstar : C) (_ : Unit) :
    (M × C) ⊕ C → PMF (Bool × Unit)
  | .inl q => PMF.pure (P.pco sk q.1 q.2, ())
  | .inr c => PMF.pure (!decide (c = cstar) && (P.dec sk c).isSome, ())

variable (PK M C) in
/-- An OW-PCVA adversary with at most `qP` plaintext-checking and `qV` validity
queries. -/
structure OWPCVAAdversary (qP qV : ℕ) : Type 1 where
  /-- The adversary on the public key and the challenge ciphertext. -/
  run : PK → C → OracleAdv ((M × C) ⊕ C) Bool M
  /-- The plaintext-checking query bound. -/
  isQueryBoundP : ∀ pk c, (run pk c).IsQueryBoundBy (Sum.elim (fun _ => 1) fun _ => 0) qP
  /-- The validity query bound. -/
  isQueryBoundV : ∀ pk c, (run pk c).IsQueryBoundBy (Sum.elim (fun _ => 0) fun _ => 1) qV

/-- The OW-PCVA experiment. -/
noncomputable def owpcvaGame [DecidableEq C] {qP qV : ℕ} (A : OWPCVAAdversary PK M C qP qV) :
    PMF Bool :=
  P.keygen.bind fun ks => (PMF.uniformOfFintype M).bind fun m =>
    (P.encDist ks.1 m).bind fun c =>
      (OracleAdv.run (pcvaOracle P ks.2 c) (A.run ks.1 c) ()).map fun x => P.pco ks.2 x.1 c

/-- The OW-PCVA advantage. -/
noncomputable def owpcvaAdvantage [DecidableEq C] {qP qV : ℕ}
    (A : OWPCVAAdversary PK M C qP qV) : ℝ≥0∞ :=
  prTrue (pmfGame (owpcvaGame P A)) Heap.empty

end OW

/-! ## Indistinguishability -/

section IND

variable (P : Scheme PK SK M C R)

variable (PK M C) in
/-- A two-stage IND-CPA adversary: `choose` receives the public key and returns two
messages and a state; `guess` receives the state and the challenge ciphertext. -/
structure INDCPAAdversary : Type 1 where
  /-- The state passed from the first to the second stage. -/
  St : Type
  /-- The first stage. -/
  choose : PK → PMF (M × M × St)
  /-- The second stage. -/
  guess : St → C → PMF Bool

/-- The IND-CPA experiment with challenge bit `b`: the challenge encrypts `m₀` when
`b = true` and `m₁` when `b = false`; the result is the adversary's output. -/
noncomputable def indcpaGame (A : INDCPAAdversary PK M C) (b : Bool) : PMF Bool :=
  P.keygen.bind fun ks => (A.choose ks.1).bind fun x =>
    (P.encDist ks.1 (if b then x.1 else x.2.1)).bind fun c => A.guess x.2.2 c

/-- The IND-CPA advantage: the distance between the two challenge bits. -/
noncomputable def indcpaAdvantage (A : INDCPAAdversary PK M C) : ℝ≥0∞ :=
  Advantage (pmfGame (indcpaGame P A true)) (pmfGame (indcpaGame P A false))

/-- The decryption oracle for `sk`. The state is the challenge ciphertext recorded
by the challenger (`none` before the challenge); the oracle answers `none` on it. -/
noncomputable def decOracle [DecidableEq C] (sk : SK) (st : Option C) (c : C) :
    PMF (Option M × Option C) :=
  PMF.pure (if st = some c then none else P.dec sk c, st)

variable (PK M C) in
/-- A two-stage IND-CCA adversary with at most `q₁` decryption queries in the first
stage and `q₂` in the second. -/
structure INDCCAAdversary (q₁ q₂ : ℕ) : Type 1 where
  /-- The state passed from the first to the second stage. -/
  St : Type
  /-- The first stage, with decryption queries. -/
  choose : PK → OracleAdv C (Option M) (M × M × St)
  /-- The second stage, with decryption queries. -/
  guess : St → C → OracleAdv C (Option M) Bool
  /-- The first-stage query bound. -/
  isQueryBound₁ : ∀ pk, (choose pk).IsQueryBound q₁
  /-- The second-stage query bound. -/
  isQueryBound₂ : ∀ st c, (guess st c).IsQueryBound q₂

/-- The IND-CCA experiment with challenge bit `b`. -/
noncomputable def indccaGame [DecidableEq C] {q₁ q₂ : ℕ} (A : INDCCAAdversary PK M C q₁ q₂)
    (b : Bool) : PMF Bool :=
  P.keygen.bind fun ks =>
    (OracleAdv.run (decOracle P ks.2) (A.choose ks.1) none).bind fun x =>
      (P.encDist ks.1 (if b then x.1.1 else x.1.2.1)).bind fun c =>
        (OracleAdv.run (decOracle P ks.2) (A.guess x.1.2.2 c) (some c)).map Prod.fst

/-- The IND-CCA advantage. -/
noncomputable def indccaAdvantage [DecidableEq C] {q₁ q₂ : ℕ}
    (A : INDCCAAdversary PK M C q₁ q₂) : ℝ≥0∞ :=
  Advantage (pmfGame (indccaGame P A true)) (pmfGame (indccaGame P A false))

end IND

/-! ## One-wayness from indistinguishability -/

section OWfromIND

variable [Fintype M] [Nonempty M] [DecidableEq M] (P : Scheme PK SK M C R)

/-- The IND-CPA adversary built from an OW-CPA adversary `A`: it chooses two uniform
messages, runs `A` once on the challenge, and outputs whether `A` returned the first
message. -/
noncomputable def owToIndcpa (A : PK → C → PMF M) : INDCPAAdversary PK M C where
  St := PK × M
  choose pk := (PMF.uniformOfFintype M).bind fun m₀ =>
    (PMF.uniformOfFintype M).map fun m₁ => (m₀, m₁, (pk, m₀))
  guess st c := (A st.1 c).map fun m' => decide (m' = st.2)

/-- **One-wayness from indistinguishability** (Hofheinz–Hövelmanns–Kiltz, Lemma 2.3,
with the pco-based winning condition). For every OW-CPA adversary `A`,
`owcpaAdvantage P A ≤ indcpaAdvantage P (owToIndcpa A) + 1/|M| + P.corrErr`. -/
theorem owcpa_le_indcpa (A : PK → C → PMF M) :
    owcpaAdvantage P A ≤ indcpaAdvantage P (owToIndcpa A) + (Fintype.card M : ℝ≥0∞)⁻¹ +
      P.corrErr := by
  have hpr : ∀ p : PMF Bool, prTrue (pmfGame p) Heap.empty = p.toOuterMeasure {b | b = true} := by
    intro p
    have h := prTrue_pmfGame_map p id Heap.empty
    rwa [PMF.map_id] at h
  have hconst : ∀ (c : ℝ≥0∞), ∑' m : M, PMF.uniformOfFintype M m * c = c := fun c => by
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have h1 : (indcpaGame P (owToIndcpa A) true).toOuterMeasure {b | b = true} =
      ∑' ks, P.keygen ks * ∑' m, PMF.uniformOfFintype M m * ∑' r, PMF.uniformOfFintype R r *
        (A ks.1 (P.enc ks.1 m r)).toOuterMeasure {m' | m' = m} := by
    simp only [indcpaGame, owToIndcpa, Scheme.encDist, PMF.bind_bind, PMF.bind_map,
      Function.comp_def, if_true, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply,
      Set.preimage, Set.mem_ofPred_eq, decide_eq_true_eq, hconst]
  have h0 : (indcpaGame P (owToIndcpa A) false).toOuterMeasure {b | b = true} =
      ∑' ks, P.keygen ks * ∑' m₀, PMF.uniformOfFintype M m₀ * ∑' m₁, PMF.uniformOfFintype M m₁ *
        ∑' r, PMF.uniformOfFintype R r *
          (A ks.1 (P.enc ks.1 m₁ r)).toOuterMeasure {m' | m' = m₀} := by
    simp only [indcpaGame, owToIndcpa, Scheme.encDist, PMF.bind_bind, PMF.bind_map,
      Function.comp_def, Bool.false_eq_true, if_false, PMF.toOuterMeasure_bind_apply,
      PMF.toOuterMeasure_map_apply, Set.preimage, Set.mem_ofPred_eq, decide_eq_true_eq]
  have hN : (indcpaGame P (owToIndcpa A) false).toOuterMeasure {b | b = true} =
      (Fintype.card M : ℝ≥0∞)⁻¹ := by
    rw [h0]
    have hin : ∀ (q : PMF M), ∑' m₀, PMF.uniformOfFintype M m₀ * q.toOuterMeasure {m' | m' = m₀} =
        (Fintype.card M : ℝ≥0∞)⁻¹ := by
      intro q
      simp only [PMF.uniformOfFintype_apply, ENNReal.tsum_mul_left]
      rw [show (fun m₀ => q.toOuterMeasure {m' | m' = m₀}) = fun m₀ => q m₀ from
        funext fun m₀ => by
          rw [show {m' | m' = m₀} = ({m₀} : Set M) from rfl, PMF.toOuterMeasure_apply_singleton],
        PMF.tsum_coe, mul_one]
    calc _ = ∑' ks, P.keygen ks * ∑' m₁, PMF.uniformOfFintype M m₁ * ∑' r,
          PMF.uniformOfFintype R r * ∑' m₀, PMF.uniformOfFintype M m₀ *
            (A ks.1 (P.enc ks.1 m₁ r)).toOuterMeasure {m' | m' = m₀} := by
          refine tsum_congr fun ks => congrArg _ ?_
          simp only [← ENNReal.tsum_mul_left]
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun m₁ => ?_
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun r => ?_
          exact tsum_congr fun m₀ => by ring
      _ = _ := by
          simp only [hin, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hOW : (owcpaGame P A).toOuterMeasure {b | b = true} ≤
      (indcpaGame P (owToIndcpa A) true).toOuterMeasure {b | b = true} + P.corrErr := by
    have hOWeq : (owcpaGame P A).toOuterMeasure {b | b = true} =
        ∑' ks, P.keygen ks * ∑' m, PMF.uniformOfFintype M m * ∑' r, PMF.uniformOfFintype R r *
          (A ks.1 (P.enc ks.1 m r)).toOuterMeasure {m' | P.pco ks.2 m' (P.enc ks.1 m r) = true} := by
      simp only [owcpaGame, Scheme.encDist, PMF.bind_map, Function.comp_def,
        PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply]
      rfl
    have hinner : ∀ (ks : PK × SK) (m : M), ∑' r, PMF.uniformOfFintype R r *
        (A ks.1 (P.enc ks.1 m r)).toOuterMeasure {m' | P.pco ks.2 m' (P.enc ks.1 m r) = true} ≤
        ∑' r, PMF.uniformOfFintype R r * (A ks.1 (P.enc ks.1 m r)).toOuterMeasure {m' | m' = m} +
          P.failProb ks.1 ks.2 m := by
      intro ks m
      rw [Scheme.failProb, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun r => ?_
      by_cases hd : P.dec ks.2 (P.enc ks.1 m r) = some m
      · have hs : {m' | P.pco ks.2 m' (P.enc ks.1 m r) = true} = {m' | m' = m} := by
          ext m'; simp [Scheme.pco, hd, eq_comm]
        rw [hs, Set.indicator_of_notMem (by simpa using hd), add_zero]
      · rw [Set.indicator_of_mem (by simpa using hd)]
        calc _ ≤ PMF.uniformOfFintype R r * 1 :=
              mul_le_mul_of_nonneg_left ((MeasureTheory.measure_mono (Set.subset_univ _)).trans_eq
                ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _))) bot_le
          _ ≤ _ := by rw [mul_one]; exact le_add_self
    rw [hOWeq, h1, Scheme.corrErr, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun ks => ?_
    rw [← mul_add, ← ENNReal.tsum_add]
    refine mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum fun m => ?_) bot_le
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hinner ks m) bot_le
  rw [indcpaAdvantage, Advantage, hpr, hpr, owcpaAdvantage, hpr, hN]
  refine hOW.trans ?_
  gcongr
  calc (indcpaGame P (owToIndcpa A) true).toOuterMeasure {b | b = true}
      ≤ ((indcpaGame P (owToIndcpa A) true).toOuterMeasure {b | b = true} -
          (Fintype.card M : ℝ≥0∞)⁻¹) + (Fintype.card M : ℝ≥0∞)⁻¹ := le_tsub_add
    _ ≤ _ := by gcongr; exact le_sup_left

end OWfromIND

/-! ## Random-oracle model -/

section ROM

variable {D H : Type} [DecidableEq D] [Fintype H] [Nonempty H]

variable (PK SK M C D H) in
/-- A public-key encryption scheme in the random-oracle model with oracle `D → H`:
encryption and decryption are oracle programs. -/
structure ROMScheme where
  /-- Key generation, returning `(pk, sk)`. -/
  keygen : PMF (PK × SK)
  /-- Encryption. -/
  enc : PK → M → OracleAdv D H C
  /-- Decryption; `none` rejects. -/
  dec : SK → C → OracleAdv D H (Option M)

variable [Fintype M] [Nonempty M] [DecidableEq M]

/-- The oracle of the OW-PCA game in the random-oracle model for the secret key `sk`,
on the random-oracle table: `inl d` is a random-oracle query and `inr (m, c)` a
plaintext-checking query, answered by running decryption of `c` against the shared
table and comparing with `m`. -/
noncomputable def romPcaOracle (S : ROMScheme PK SK M C D H) (sk : SK) (T : D → Option H) :
    D ⊕ (M × C) → PMF ((H ⊕ Bool) × (D → Option H))
  | .inl d => (roOracle T d).map fun x => (.inl x.1, x.2)
  | .inr q => (OracleAdv.run roOracle (S.dec sk q.2) T).map fun x =>
      (.inr (decide (x.1 = some q.1)), x.2)

variable (PK M C D H) in
/-- An OW-PCA adversary in the random-oracle model with at most `qG` random-oracle
queries and `qP` plaintext-checking queries. -/
structure ROMOWPCAAdversary (qG qP : ℕ) : Type 1 where
  /-- The adversary on the public key and the challenge ciphertext. -/
  run : PK → C → OracleAdv (D ⊕ (M × C)) (H ⊕ Bool) M
  /-- The random-oracle query bound. -/
  isQueryBoundG : ∀ pk c, (run pk c).IsQueryBoundBy (Sum.elim (fun _ => 1) fun _ => 0) qG
  /-- The plaintext-checking query bound. -/
  isQueryBoundP : ∀ pk c, (run pk c).IsQueryBoundBy (Sum.elim (fun _ => 0) fun _ => 1) qP

/-- The OW-PCA experiment in the random-oracle model: the challenger encrypts a
uniform message against the empty table, runs the adversary against
`romPcaOracle` from the resulting table, and checks the output by decrypting the
challenge against the final table. -/
noncomputable def romOWPCAGame (S : ROMScheme PK SK M C D H) {qG qP : ℕ}
    (B : ROMOWPCAAdversary PK M C D H qG qP) : PMF Bool :=
  S.keygen.bind fun ks => (PMF.uniformOfFintype M).bind fun m =>
    (OracleAdv.run roOracle (S.enc ks.1 m) emptyTable).bind fun x =>
      (OracleAdv.run (romPcaOracle S ks.2) (B.run ks.1 x.1) x.2).bind fun y =>
        (OracleAdv.run roOracle (S.dec ks.2 x.1) y.2).map fun z => decide (z.1 = some y.1)

/-- The OW-PCA advantage in the random-oracle model. -/
noncomputable def romOWPCAAdvantage (S : ROMScheme PK SK M C D H) {qG qP : ℕ}
    (B : ROMOWPCAAdversary PK M C D H qG qP) : ℝ≥0∞ :=
  prTrue (pmfGame (romOWPCAGame S B)) Heap.empty

end ROM

end CatCrypt.Crypto.PKE.Games
