/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.DuplexSpongeNIZK
public import CatCryptCore.Tactics.AutoDispatchExt

/-!
# The duplex-sponge transform against the raw random oracle

The sponge of the duplex-sponge Fiat–Shamir transform is modelled as a random oracle
on absorbed byte strings with `L` uniform bytes as values. In this module the adversary
queries that oracle at arbitrary byte strings and receives the raw bytes.

* Knowledge soundness (`dsRawKsExtractProb_ge`). The reduction `dsRawRed` turns an
  adversary against the raw oracle into a knowledge-soundness adversary of
  `FiatShamirROM.NIZK` by simulating the raw oracle from the challenge oracle: a string
  that is not the absorbed string of a transcript is answered by fresh uniform bytes, the
  absorbed string of a transcript `k` by bytes sampled uniformly among those decoding to
  the challenge at `k` (`DSParams.condB`). Against challenges drawn from the decoding of
  uniform bytes the simulation is exact (`run_dsRawRed`); each of the `qH + 1` queries of
  the reduction moves the success probability by at most `β`.
* Zero knowledge (`dsRawZkReal_le_zkSim`). The game of `FiatShamirROM.Game` for the
  protocol `dsZkProtocol`, whose random-oracle points are byte strings and whose proving
  oracle programs the absorbed string of the transcript. The distinguisher queries the
  random oracle at arbitrary byte strings, and the bound is `qP·δ + qP·(qH + qP)·γ`.

## Main definitions

* `DSParams.unabsorb`, `DSParams.condB` — the transcript of an absorbed string, and the
  uniform bytes conditioned on their decoding
* `dsRawStep`, `dsRawKsAdvantage` — the knowledge-soundness game against the raw oracle
* `dsRawImpl`, `dsRawRed` — the simulation of the raw oracle and the reduction
* `dsZkProtocol`, `DSRawZKDistinguisher`, `dsRawZkReal`, `dsRawZkSim` — the
  zero-knowledge game against the raw oracle

## Main results

* `bind_condB_map` — the decoding of uniform bytes followed by conditional sampling is
  uniform sampling
* `run_dsRawRed` — the reduction against decoded challenges is the raw game
* `dsRawKsAdvantage_le` — `dsRawKsAdvantage A ≤ ksAdvantage (dsRawRed A) + (qH + 1)·β`
* `dsRawKsExtractProb_ge` — with `ε = dsRawKsAdvantage A − (qH + 1)·β`,
  `ε·(ε/(qH + 1) − 1/|Ch|) ≤ ksExtractProb (dsRawRed A)`
* `dsRawZkReal_le_zkSim` — `dsRawZkReal D ≤ dsRawZkSim D + qP·δ + qP·(qH + qP)·γ`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.OracleForking CatCrypt.Crypto.Constructions.ECBCPRF
open CatCrypt.Crypto.FiatShamirROM.DuplexSponge
open scoped ENNReal

variable {P : Sigma} (Dp : DSParams P)

namespace DSParams

/-- The transcript whose absorbed string is `s`, if there is one. -/
noncomputable def unabsorb (s : Bytes) : Option (P.NizkInput SessionId) :=
  Function.partialInv Dp.absorbed s

open Classical in
/-- `L` uniform bytes conditioned on decoding to `c`: uniform on the byte strings that
decode to `c`, and uniform on all byte strings when none does. -/
noncomputable def condB (c : P.Ch) : PMF (Fin Dp.L → UInt8) :=
  if h : ∃ b, Dp.decB b = c then
    PMF.uniformOfFinset (Finset.univ.filter fun b => Dp.decB b = c)
      (by obtain ⟨b, hb⟩ := h; exact ⟨b, by simp [hb]⟩)
  else PMF.uniformOfFintype _

end DSParams

/-! ## Conditional sampling -/

theorem unabsorb_absorbed (hX : PrefixFree Dp.encX) (hA : PrefixFree Dp.encA)
    (k : P.NizkInput SessionId) : Dp.unabsorb (Dp.absorbed k) = some k :=
  Function.partialInv_left (absorbedTranscript_injective Dp.R hX hA) k

theorem absorbed_of_unabsorb {s : Bytes} {k : P.NizkInput SessionId}
    (h : Dp.unabsorb s = some k) : Dp.absorbed k = s := by
  unfold DSParams.unabsorb Function.partialInv at h
  split_ifs at h with h'
  cases h
  exact Classical.choose_spec h'

/-- The decoding of uniform bytes paired with the conditional sample is uniform bytes
paired with their decoding. -/
theorem bind_condB_pair :
    ((PMF.uniformOfFintype (Fin Dp.L → UInt8)).map Dp.decB).bind
        (fun c => (Dp.condB c).map fun b => (c, b)) =
      (PMF.uniformOfFintype (Fin Dp.L → UInt8)).map fun b => (Dp.decB b, b) := by
  classical
  set U := PMF.uniformOfFintype (Fin Dp.L → UInt8) with hU
  have hpair : ∀ c' c b, ((Dp.condB c').map fun b => (c', b)) (c, b) =
      if c' = c then Dp.condB c b else 0 := by
    intro c' c b
    rw [PMF.map_apply, tsum_eq_single b]
    · by_cases h : c' = c
      · subst h; simp
      · simp [h, Ne.symm h]
    · intro b' hb'
      simp [Ne.symm hb']
  have hν : ∀ c, (U.map Dp.decB) c =
      ((Finset.univ.filter fun b => Dp.decB b = c).card : ℝ≥0∞) * (Fintype.card (Fin Dp.L → UInt8) : ℝ≥0∞)⁻¹ := by
    intro c
    rw [PMF.map_apply, tsum_fintype]
    simp [hU, PMF.uniformOfFintype_apply, Finset.sum_ite, eq_comm]
  have hR : ∀ c b, (U.map fun b => (Dp.decB b, b)) (c, b) =
      if Dp.decB b = c then U b else 0 := by
    intro c b
    rw [PMF.map_apply, tsum_eq_single b]
    · by_cases h : Dp.decB b = c
      · subst h; simp
      · simp [h, Ne.symm h]
    · intro b' hb'
      simp [Ne.symm hb']
  ext ⟨c, b⟩
  rw [PMF.bind_apply, tsum_eq_single c (fun c' hc' => by simp [hpair, hc']), hpair, if_pos rfl,
    hR, hν]
  by_cases h : Dp.decB b = c
  · subst h
    have hmem : b ∈ Finset.univ.filter fun b' => Dp.decB b' = Dp.decB b := by simp
    have hne : ((Finset.univ.filter fun b' => Dp.decB b' = Dp.decB b).card : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero_of_mem hmem
    rw [if_pos rfl, DSParams.condB, dif_pos ⟨b, rfl⟩, PMF.uniformOfFinset_apply, if_pos hmem,
      hU, PMF.uniformOfFintype_apply, mul_comm, ← mul_assoc,
      ENNReal.inv_mul_cancel hne (ENNReal.natCast_ne_top _), one_mul]
  · rw [if_neg h]
    by_cases he : ∃ b', Dp.decB b' = c
    · rw [DSParams.condB, dif_pos he, PMF.uniformOfFinset_apply, if_neg (by simp [h]), mul_zero]
    · have h0 : (Finset.univ.filter fun b' => Dp.decB b' = c) = ∅ := by
        simpa [Finset.filter_eq_empty_iff] using he
      rw [h0, Finset.card_empty, Nat.cast_zero, zero_mul, zero_mul]

/-- **Conditional sampling.** Drawing a challenge from the decoding of uniform bytes and
then bytes uniformly among those decoding to it is drawing uniform bytes. -/
theorem bind_condB_map {γ : Type} (F : P.Ch → (Fin Dp.L → UInt8) → γ) :
    ((PMF.uniformOfFintype (Fin Dp.L → UInt8)).map Dp.decB).bind
        (fun c => (Dp.condB c).map (F c)) =
      (PMF.uniformOfFintype (Fin Dp.L → UInt8)).map fun b => F (Dp.decB b) b := by
  have h := congrArg (PMF.map fun p : P.Ch × (Fin Dp.L → UInt8) => F p.1 p.2) (bind_condB_pair Dp)
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using h

/-! ## Knowledge soundness against the raw oracle -/

section Knowledge

variable [DecidableEq P.Stmt]

/-- The sponge as a random oracle on byte strings: the `L` bytes recorded at a string,
or `L` fresh uniform bytes recorded there. -/
noncomputable def dsRawStep (T : List (Bytes × (Fin Dp.L → UInt8))) (s : Bytes) :
    Step (Fin Dp.L → UInt8) (List (Bytes × (Fin Dp.L → UInt8))) (Fin Dp.L → UInt8) :=
  match lookupIn T s with
  | some b => .plain (PMF.pure (b, T))
  | none => .fresh fun b => (b, T ++ [(s, b)])

/-- The adversary against the raw oracle followed by the challenger's query at the
absorbed string of the transcript of its output. -/
def dsRawWithVerify
    (A : OracleAdv Bytes (Fin Dp.L → UInt8) (SessionId × P.Stmt × P.NizkProof)) :
    OracleAdv Bytes (Fin Dp.L → UInt8) (SessionId × P.Stmt × P.NizkProof) :=
  A.bind fun y => .query (Dp.absorbed (ksInput y)) fun _ => .ret y

/-- The probability that an adversary querying the raw oracle at byte strings outputs a
proof that verifies against the decoding of the bytes at the absorbed string of its
transcript. -/
noncomputable def dsRawKsAdvantage
    (A : OracleAdv Bytes (Fin Dp.L → UInt8) (SessionId × P.Stmt × P.NizkProof)) : ℝ≥0∞ :=
  (OracleAdv.run (toOracle (dsRawStep Dp)) (dsRawWithVerify Dp A) []).toOuterMeasure
    {y | dsKsAccepts Dp y = true}

/-- The simulation of the raw oracle from the challenge oracle, with its table of
answered strings: a recorded string is answered from the table; the absorbed string of a
transcript `k` by bytes sampled conditionally on decoding to the challenge at `k`; any
other string by fresh uniform bytes. -/
noncomputable def dsRawImpl (T : List (Bytes × (Fin Dp.L → UInt8))) (s : Bytes) :
    OracleAdv (P.NizkInput SessionId) P.Ch
      ((Fin Dp.L → UInt8) × List (Bytes × (Fin Dp.L → UInt8))) :=
  match lookupIn T s with
  | some b => .ret (b, T)
  | none =>
    match Dp.unabsorb s with
    | some k => .query k fun c => .rand (Dp.condB c) fun b => .ret (b, T ++ [(s, b)])
    | none => .rand (PMF.uniformOfFintype _) fun b => .ret (b, T ++ [(s, b)])

omit [DecidableEq P.Stmt] in
theorem isQueryBound_dsRawImpl (T : List (Bytes × (Fin Dp.L → UInt8))) (s : Bytes) :
    (dsRawImpl Dp T s).IsQueryBound 1 := by
  unfold dsRawImpl
  split <;> [trivial; split] <;> simp [OracleAdv.IsQueryBound]

/-- **The reduction to knowledge soundness.** The adversary `A` against the raw oracle,
with its queries answered by `dsRawImpl` from the empty table. -/
noncomputable def dsRawRed {qH : ℕ}
    (A : OracleAdv Bytes (Fin Dp.L → UInt8) (SessionId × P.Stmt × P.NizkProof))
    (hA : A.IsQueryBound qH) : KSAdversary P SessionId qH where
  run := (OracleAdv.simulate (dsRawImpl Dp) A []).bind fun x => .ret x.1
  isQueryBound := OracleAdv.isQueryBound_bind (m := qH) (n := 0)
    (OracleAdv.isQueryBound_simulate _ (fun _ => 1) (isQueryBound_dsRawImpl Dp)
      hA.isQueryBoundBy_one []) fun _ => trivial

/-- The challenge table of the transcripts among the entries of a raw table, with the
decoded values. -/
noncomputable def dsDecTable (T : List (Bytes × (Fin Dp.L → UInt8))) :
    List (P.NizkInput SessionId × P.Ch) :=
  T.filterMap fun p => (Dp.unabsorb p.1).map fun k => (k, Dp.decB p.2)

omit [DecidableEq P.Stmt] in
theorem dsDecTable_append (T : List (Bytes × (Fin Dp.L → UInt8))) (s : Bytes)
    (b : Fin Dp.L → UInt8) :
    dsDecTable Dp (T ++ [(s, b)]) =
      dsDecTable Dp T ++ ((Dp.unabsorb s).map fun k => (k, Dp.decB b)).toList := by
  cases h : Dp.unabsorb s <;> simp [dsDecTable, h]

theorem lookupIn_dsDecTable (hX : PrefixFree Dp.encX) (hA : PrefixFree Dp.encA)
    (T : List (Bytes × (Fin Dp.L → UInt8))) (k : P.NizkInput SessionId) :
    lookupIn (dsDecTable Dp T) k = (lookupIn T (Dp.absorbed k)).map Dp.decB := by
  have hinj : Function.Injective Dp.absorbed := absorbedTranscript_injective Dp.R hX hA
  induction T with
  | nil => simp [dsDecTable, lookupIn_nil]
  | cons p T ih =>
    rcases p with ⟨s, b⟩
    have hT : dsDecTable Dp ((s, b) :: T) =
        ((Dp.unabsorb s).map fun k => (k, Dp.decB b)).toList ++ dsDecTable Dp T := by
      cases h : Dp.unabsorb s <;> simp [dsDecTable, h]
    rw [hT, lookupIn_cons]
    rcases hk : Dp.unabsorb s with _ | k'
    · have hne : s ≠ Dp.absorbed k := by
        rintro rfl
        rw [unabsorb_absorbed Dp hX hA] at hk
        exact absurd hk (by simp)
      simp [hne, ih]
    · have hs := absorbed_of_unabsorb Dp hk
      subst hs
      rw [Option.map_some, Option.toList_some, List.singleton_append, lookupIn_cons]
      by_cases hkk : k' = k
      · subst hkk; simp
      · simp [hkk, hinj.ne hkk, ih]

/-- The simulation against the challenge oracle with decoded fresh values, from the
challenge table of the raw table, is the raw oracle. -/
theorem simOracle_dsRawImpl (hX : PrefixFree Dp.encX) (hA : PrefixFree Dp.encA)
    (T : List (Bytes × (Fin Dp.L → UInt8))) (s : Bytes) :
    (toOracle (dsRawStep Dp) T s).map (Prod.map id fun T => (T, dsDecTable Dp T)) =
      OracleAdv.simOracle (dsRawImpl Dp)
        (toOracleWith ((PMF.uniformOfFintype (Fin Dp.L → UInt8)).map Dp.decB) ksStep)
        (T, dsDecTable Dp T) s := by
  unfold OracleAdv.simOracle
  simp only [toOracle, dsRawStep, dsRawImpl]
  rcases hl : lookupIn T s with _ | b
  · rcases hk : Dp.unabsorb s with _ | k
    · simp only [Step.toPMF, OracleAdv.run_rand, OracleAdv.run_ret, PMF.map_comp, PMF.map_bind,
        PMF.pure_map, Function.comp_def, Prod.map, id, dsDecTable_append, hk, Option.map_none,
        Option.toList_none, List.append_nil]
      rfl
    · have hs := absorbed_of_unabsorb Dp hk
      have hlk : lookupIn (dsDecTable Dp T) k = none := by
        rw [lookupIn_dsDecTable Dp hX hA, hs, hl, Option.map_none]
      calc _ = (PMF.uniformOfFintype (Fin Dp.L → UInt8)).map
              (fun b => (b, (T ++ [(s, b)], dsDecTable Dp T ++ [(k, Dp.decB b)]))) := by
            simp [Step.toPMF, PMF.map_comp, Function.comp_def, dsDecTable_append, hk]
        _ = ((PMF.uniformOfFintype (Fin Dp.L → UInt8)).map Dp.decB).bind (fun e =>
              (Dp.condB e).map fun b => (b, (T ++ [(s, b)], dsDecTable Dp T ++ [(k, e)]))) :=
            (bind_condB_map Dp (fun e b => (b, (T ++ [(s, b)], dsDecTable Dp T ++ [(k, e)])))).symm
        _ = _ := by
            simp only [OracleAdv.run_rand, OracleAdv.run_ret, OracleAdv.run_query, toOracleWith,
              ksStep, hlk, Step.toPMFWith, PMF.map_bind, PMF.bind_map, PMF.pure_map,
              Function.comp_def]
            rfl
  · simp [Step.toPMF, PMF.pure_map]

/-- The challenge oracle with decoded fresh values at a transcript, from the challenge
table of a raw table, is the raw oracle at its absorbed string with decoded answers. -/
theorem toOracleWith_ksStep_dsDecTable (hX : PrefixFree Dp.encX) (hA : PrefixFree Dp.encA)
    (T : List (Bytes × (Fin Dp.L → UInt8))) (k : P.NizkInput SessionId) :
    (toOracle (dsRawStep Dp) T (Dp.absorbed k)).map (Prod.map Dp.decB (dsDecTable Dp)) =
      toOracleWith ((PMF.uniformOfFintype (Fin Dp.L → UInt8)).map Dp.decB) ksStep
        (dsDecTable Dp T) k := by
  simp only [toOracle, toOracleWith, dsRawStep, ksStep, lookupIn_dsDecTable Dp hX hA]
  rcases lookupIn T (Dp.absorbed k) with _ | b
  · simp [Step.toPMF, Step.toPMFWith, PMF.map_comp, Function.comp_def, dsDecTable_append,
      unabsorb_absorbed Dp hX hA]
  · simp [Step.toPMF, Step.toPMFWith, PMF.pure_map]

/-- **The simulation is exact against decoded challenges.** The reduction followed by the
challenger's query, against the challenge oracle whose fresh values are decodings of
uniform bytes, is the raw game with its table replaced by its challenge table. -/
theorem run_dsRawRed (hX : PrefixFree Dp.encX) (hA : PrefixFree Dp.encA) {qH : ℕ}
    (A : OracleAdv Bytes (Fin Dp.L → UInt8) (SessionId × P.Stmt × P.NizkProof))
    (hAq : A.IsQueryBound qH) :
    OracleAdv.run (toOracleWith ((PMF.uniformOfFintype (Fin Dp.L → UInt8)).map Dp.decB)
        ksStep) (ksWithVerify (dsRawRed Dp A hAq).run) [] =
      (OracleAdv.run (toOracle (dsRawStep Dp)) (dsRawWithVerify Dp A) []).map
        (Prod.map id (dsDecTable Dp)) := by
  set ν := (PMF.uniformOfFintype (Fin Dp.L → UInt8)).map Dp.decB with hν
  have hsim := OracleAdv.run_map_state _ _ (fun T => (T, dsDecTable Dp T))
    (simOracle_dsRawImpl Dp hX hA) A []
  have hfin : ∀ (y : SessionId × P.Stmt × P.NizkProof) (T : List (Bytes × (Fin Dp.L → UInt8))),
      OracleAdv.run (toOracleWith ν ksStep)
          (.query (ksInput y) fun _ => .ret y) (dsDecTable Dp T) =
        (OracleAdv.run (toOracle (dsRawStep Dp))
          (.query (Dp.absorbed (ksInput y)) fun _ => .ret y) T).map
            (Prod.map id (dsDecTable Dp)) := by
    intro y T
    rw [OracleAdv.run_query, OracleAdv.run_query, hν,
      ← toOracleWith_ksStep_dsDecTable Dp hX hA]
    simp [PMF.bind_map, PMF.map_bind, PMF.pure_map, Function.comp_def]
  rw [ksWithVerify, dsRawRed, OracleAdv.bind_assoc]
  simp only [OracleAdv.bind_ret]
  rw [OracleAdv.run_bind, OracleAdv.run_simulate, dsRawWithVerify, OracleAdv.run_bind,
    PMF.map_bind]
  change ((OracleAdv.run _ A ((fun T => (T, dsDecTable Dp T)) [])).map _).bind _ = _
  rw [← hsim, PMF.map_comp, PMF.bind_map]
  refine congrArg _ (funext fun x => ?_)
  exact hfin x.1 x.2

/-- **Knowledge soundness against the raw oracle, advantage.** For prefix-free encodings
and a decoding with the minorant `(1 − β)·uniform`, the advantage of an adversary with at
most `qH` raw-oracle queries is at most the knowledge-soundness advantage of the
reduction plus `(qH + 1)·β`. -/
theorem dsRawKsAdvantage_le (hX : PrefixFree Dp.encX) (hA : PrefixFree Dp.encA) {β : ℝ≥0∞}
    (hβ : ∀ c, (1 - β) * PMF.uniformOfFintype P.Ch c ≤
      (PMF.uniformOfFintype (Fin Dp.L → UInt8)).map Dp.decB c)
    {qH : ℕ} (A : OracleAdv Bytes (Fin Dp.L → UInt8) (SessionId × P.Stmt × P.NizkProof))
    (hAq : A.IsQueryBound qH) :
    dsRawKsAdvantage Dp A ≤ ksAdvantage (dsRawRed Dp A hAq) + (qH + 1 : ℕ) * β := by
  set ν := (PMF.uniformOfFintype (Fin Dp.L → UInt8)).map Dp.decB with hνdef
  have hpre : (Prod.map id (dsDecTable Dp)) ⁻¹' {y | ksAccepts y = true} =
      {y | dsKsAccepts Dp y = true} := by
    ext ⟨y, T⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Prod.map_fst, Prod.map_snd, id, ksAccepts,
      dsKsAccepts, lookupIn_dsDecTable Dp hX hA]
    rcases lookupIn T (Dp.absorbed (ksInput y)) with _ | b <;> rfl
  have e₁ : dsRawKsAdvantage Dp A = (OracleAdv.run (toOracleWith ν ksStep)
      (ksWithVerify (dsRawRed Dp A hAq).run) []).toOuterMeasure {y | ksAccepts y = true} := by
    rw [run_dsRawRed Dp hX hA A hAq, PMF.toOuterMeasure_map_apply, hpre, dsRawKsAdvantage]
  have hν : ∀ g : P.Ch → ℝ≥0∞, (∀ c, g c ≤ 1) →
      ∑' c, ν c * g c ≤ ∑' c, PMF.uniformOfFintype P.Ch c * g c + β := fun g hg =>
    (MLKEM.XOFMatrix.tsum_le_add_of_minorant ν _ β hβ g hg).1
  rw [e₁, ksAdvantage, toOuterMeasure_eq_tsum_ite, toOuterMeasure_eq_tsum_ite]
  exact run_toOracleWith_le ν hν ksStep (ksWithVerify (dsRawRed Dp A hAq).run) (qH + 1)
    (isQueryBound_ksWithVerify _ (dsRawRed Dp A hAq).isQueryBound) [] _
    fun y => by split_ifs <;> simp

/-- **Knowledge soundness of the duplex-sponge transform against the raw oracle.** For a
special-sound Σ-protocol, prefix-free encodings and a decoding with the minorant
`(1 − β)·uniform`, every adversary with at most `qH` queries to the raw oracle satisfies,
with `ε = dsRawKsAdvantage A − (qH + 1)·β`,
`ε·(ε/(qH + 1) − 1/|Ch|) ≤ ksExtractProb (dsRawRed A)`. -/
theorem dsRawKsExtractProb_ge (hSS : P.SpecialSound) (hX : PrefixFree Dp.encX)
    (hA : PrefixFree Dp.encA) {β : ℝ≥0∞}
    (hβ : ∀ c, (1 - β) * PMF.uniformOfFintype P.Ch c ≤
      (PMF.uniformOfFintype (Fin Dp.L → UInt8)).map Dp.decB c)
    {qH : ℕ} (A : OracleAdv Bytes (Fin Dp.L → UInt8) (SessionId × P.Stmt × P.NizkProof))
    (hAq : A.IsQueryBound qH) :
    (dsRawKsAdvantage Dp A - (qH + 1 : ℕ) * β) *
        ((dsRawKsAdvantage Dp A - (qH + 1 : ℕ) * β) / ((qH + 1 : ℕ) : ℝ≥0∞) -
          1 / Fintype.card P.Ch) ≤
      ksExtractProb (dsRawRed Dp A hAq) := by
  have hle : dsRawKsAdvantage Dp A - (qH + 1 : ℕ) * β ≤ ksAdvantage (dsRawRed Dp A hAq) :=
    tsub_le_iff_right.mpr (dsRawKsAdvantage_le Dp hX hA hβ A hAq)
  refine le_trans ?_ (ksExtractProb_ge hSS (dsRawRed Dp A hAq))
  gcongr

end Knowledge

/-! ## Zero knowledge against the raw oracle -/

section ZK

/-- The simulated proving answer in the session `sid` on the statement `x` for the
challenge bytes `b` and simulator randomness `s`: the simulated transcript `(a, z)` for
the decoded challenge and the entry `(absorbed (sid, x, a), b)` to program when `z` is
accepted, nothing otherwise. -/
def dsZkSimulate (sid : SessionId) (x : P.Stmt) (b : Fin Dp.L → UInt8) (s : P.SimRand) :
    List (Bytes × (Fin Dp.L → UInt8)) × Option P.NizkProof :=
  if P.accept (P.simulate x (Dp.decB b) s).2 then
    ([(Dp.absorbed (sid, x, (P.simulate x (Dp.decB b) s).1), b)],
      some (P.simulate x (Dp.decB b) s))
  else ([], none)

/-- The protocol of the proving oracle of the duplex-sponge transform with the sponge as
a random oracle on byte strings: the proving queries as messages, one entry at the
absorbed string of `(sid, x, P.commit x w r)` with `L` bytes as value, decoded before the
prover reads it, public when the response is accepted; the simulator programs the
absorbed string of the simulated transcript (`dsZkSimulate`). -/
@[reducible] noncomputable def dsZkProtocol : Protocol where
  Stmt := Unit
  Wit := Unit
  Msg := P.ProveQuery SessionId
  Key := Bytes
  Ch := Fin Dp.L → UInt8
  Sig := P.NizkProof
  Rand := P.Rand
  SimRand := P.SimRand
  decMsg := Classical.decEq _
  gen := PMF.pure ((), ())
  μ := 1
  key _ _ q r _ _ := Dp.absorbed (q.1, q.2.1.1, P.commit q.2.1.1 q.2.1.2 r)
  key_causal _ _ _ _ _ _ _ _ := rfl
  key_inj _ _ _ _ _ i j _ := Subsingleton.elim i j
  pub _ _ q r v _ := P.accept (P.respond q.2.1.1 q.2.1.2 r (Dp.decB (v 0)))
  sign _ _ q r v :=
    if P.accept (P.respond q.2.1.1 q.2.1.2 r (Dp.decB (v 0))) then
      some (P.commit q.2.1.1 q.2.1.2 r, P.respond q.2.1.1 q.2.1.2 r (Dp.decB (v 0)))
    else none
  simulate _ q v s := dsZkSimulate Dp q.1 q.2.1.1 (v 0) s
  V := 1
  vkey _ q σ _ := Dp.absorbed (q.1, q.2.1.1, σ.1)
  verify _ q σ vs := match vs with
    | [b] => P.verify q.2.1.1 σ.1 (Dp.decB b) σ.2
    | _ => false

/-- The view of a transcript `(a, z)` on the query `q` with challenge bytes `b`: the entry
`(absorbed (sid, x, a), b)` and the proof `(a, z)` when `z` is accepted, nothing
otherwise. -/
def dsZkView (q : P.ProveQuery SessionId) (b : Fin Dp.L → UInt8) (az : P.Com × P.Resp) :
    (dsZkProtocol Dp).View :=
  if P.accept az.2 then ([(Dp.absorbed (q.1, q.2.1.1, az.1), b)], some az) else ([], none)

theorem trace_dsZkProtocol (q : P.ProveQuery SessionId) (r : P.Rand)
    (e : Fin 1 → Fin Dp.L → UInt8) :
    (dsZkProtocol Dp).trace () () q r e =
      ([], dsZkView Dp q (e 0)
        (P.commit q.2.1.1 q.2.1.2 r, P.respond q.2.1.1 q.2.1.2 r (Dp.decB (e 0)))) := by
  rw [Protocol.trace, Protocol.evEntries_of_ev_false (fun _ => rfl)]
  unfold Protocol.view Protocol.pubEntries Protocol.entries dsZkView
  cases h : P.accept (P.respond q.2.1.1 q.2.1.2 r (Dp.decB (e 0))) <;>
    simp [dsZkProtocol, h, List.finRange_succ, Fin.fin_one_eq_zero]

theorem simTrace_dsZkProtocol (look : Bytes → Option (Fin Dp.L → UInt8))
    (q : P.ProveQuery SessionId) (e : Fin 1 → Fin Dp.L → UInt8) (s : P.SimRand) :
    (dsZkProtocol Dp).simTrace look () q e s =
      ([], dsZkView Dp q (e 0) (P.simulate q.2.1.1 (Dp.decB (e 0)) s)) := by
  rw [Protocol.simTrace_of_simKey_none (fun _ _ => rfl)]
  rfl

theorem vals_dsZkProtocol (look : Bytes → Option (Fin Dp.L → UInt8))
    (q : P.ProveQuery SessionId) (r : P.Rand) (e : Fin 1 → Fin Dp.L → UInt8) :
    (dsZkProtocol Dp).vals look () () q r e = e :=
  Protocol.vals_of_ev_false (G := dsZkProtocol Dp) (fun _ => rfl) look () () q r e

theorem guessView_dsZkProtocol (look : Bytes → Option (Fin Dp.L → UInt8))
    (q : P.ProveQuery SessionId) (r : P.Rand) (e : Fin 1 → Fin Dp.L → UInt8) (i : Fin 1) :
    (dsZkProtocol Dp).guessView look () () q r e i = ([], [], none) := by
  unfold Protocol.guessView
  split
  · rfl
  · next h =>
    rw [vals_dsZkProtocol, trace_dsZkProtocol]
    rw [vals_dsZkProtocol] at h
    have h' : P.accept (P.respond q.2.1.1 q.2.1.2 r (Dp.decB (e 0))) = false := by
      simp only [dsZkProtocol, Bool.or_eq_true, not_or, Bool.not_eq_true] at h
      exact h.1
    simp [dsZkView, h']

/-- Statistical HVZK of `P` with distance `δ` at every pair of the relation gives
statistical HVZK of the protocol of the proving oracle against the raw oracle. -/
theorem statHVZKAt_dsZkProtocol {δ : ℝ≥0∞} (h : ∀ x w, P.rel x w → P.StatHVZKAt x w δ) :
    (dsZkProtocol Dp).StatHVZKAt () () δ := by
  intro q look g hg
  simp only [vals_dsZkProtocol, trace_dsZkProtocol, simTrace_dsZkProtocol]
  have hstep : ∀ e : Fin 1 → Fin Dp.L → UInt8, ∑' r, PMF.uniformOfFintype P.Rand r *
      (if (dsZkProtocol Dp).hidFresh look () () q r e then
        g ([], dsZkView Dp q (e 0)
          (P.commit q.2.1.1 q.2.1.2 r, P.respond q.2.1.1 q.2.1.2 r (Dp.decB (e 0))))
        else 0) ≤
      ∑' s, PMF.uniformOfFintype P.SimRand s *
        g ([], dsZkView Dp q (e 0) (P.simulate q.2.1.1 (Dp.decB (e 0)) s)) + δ := fun e => by
    have hb : Dp.sigmaBytes.RejectBlind (fun az => g ([], dsZkView Dp q (e 0) az)) := by
      intro a a' z hz
      have hz' : P.accept z = false := hz
      simp [dsZkView, hz']
    refine (ENNReal.tsum_le_tsum fun r => mul_le_mul_right ?_ _).trans
      (statHVZKAt_sigmaBytes Dp (h q.2.1.1 q.2.1.2 q.2.2) (e 0)
        (fun az => g ([], dsZkView Dp q (e 0) az)) (fun _ => hg _) hb)
    split_ifs
    · exact le_rfl
    · exact zero_le
  calc _ ≤ ∑' e, PMF.uniformOfFintype (Fin 1 → Fin Dp.L → UInt8) e *
          (∑' s, PMF.uniformOfFintype P.SimRand s *
            g ([], dsZkView Dp q (e 0) (P.simulate q.2.1.1 (Dp.decB (e 0)) s)) + δ) :=
        ENNReal.tsum_le_tsum fun e => mul_le_mul_right (hstep e) _
    _ = _ := by
        simp only [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- For prefix-free encodings, the commitment bound `γ` of `P` at every pair of the
relation is a key bound of the protocol of the proving oracle against the raw oracle. -/
theorem keyBoundAt_dsZkProtocol (hX : PrefixFree Dp.encX) (hA : PrefixFree Dp.encA)
    {γ : ℝ≥0∞} (h : ∀ x w, P.rel x w → P.CommitBoundAt x w γ) :
    (dsZkProtocol Dp).KeyBoundAt () () γ := by
  intro q look Q
  simp only [guessView_dsZkProtocol, vals_dsZkProtocol, Fin.sum_univ_one]
  set Qv := Q ([], [], none)
  set f : P.Rand → Bytes := fun r => Dp.absorbed (q.1, q.2.1.1, P.commit q.2.1.1 q.2.1.2 r)
    with hf
  have hy : ∀ y, (PMF.uniformOfFintype P.Rand).toOuterMeasure (f ⁻¹' {y}) ≤ γ := by
    intro y
    rcases hk : Dp.unabsorb y with _ | k
    · have he : f ⁻¹' {y} = ∅ := by
        ext r
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false]
        intro hr
        rw [← hr, hf, unabsorb_absorbed Dp hX hA] at hk
        exact absurd hk (by simp)
      rw [he, MeasureTheory.measure_empty]
      exact zero_le
    · refine (MeasureTheory.measure_mono fun r hr => ?_).trans (h q.2.1.1 q.2.1.2 q.2.2 k.2.2)
      have hr' : f r = y := hr
      rw [← hr', hf, unabsorb_absorbed Dp hX hA] at hk
      cases hk
      rfl
  have hr : ∑' r, PMF.uniformOfFintype P.Rand r * Qv (f r) ≤ γ := by
    rw [← tsum_map_mul' (PMF.uniformOfFintype P.Rand) f Qv]
    calc ∑' y, ((PMF.uniformOfFintype P.Rand).map f) y * Qv y
        ≤ ∑' y, γ * Qv y := by
          refine ENNReal.tsum_le_tsum fun y => mul_le_mul_left ?_ _
          rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
          exact hy y
      _ = γ := by rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
  calc _ ≤ ∑' e, PMF.uniformOfFintype (Fin 1 → Fin Dp.L → UInt8) e *
        ∑' r, PMF.uniformOfFintype P.Rand r * Qv (f r) := by
        refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right
          (ENNReal.tsum_le_tsum fun r => mul_le_mul_right ?_ _) _
        split_ifs
        · exact le_rfl
        · exact zero_le
    _ ≤ ∑' e, PMF.uniformOfFintype (Fin 1 → Fin Dp.L → UInt8) e * γ :=
        ENNReal.tsum_le_tsum fun e => mul_le_mul_right hr _
    _ = γ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- A zero-knowledge distinguisher against the raw oracle: an oracle adversary with at
most `qH` random-oracle queries `inl s` at byte strings `s` and `qP` proving queries
`inr (sid, (x, w))` on every path that outputs a bit. -/
structure DSRawZKDistinguisher (qH qP : ℕ) : Type 1 where
  /-- The distinguisher. -/
  run : OracleAdv (dsZkProtocol Dp).Query (dsZkProtocol Dp).Answer Bool
  /-- The query bounds. -/
  isQueryBound : IsQueryBound₂ run qH qP

/-- The probability that the distinguisher outputs `true` against the raw oracle and the
honest duplex-sponge prover. -/
noncomputable def dsRawZkReal {qH qP : ℕ} (D : DSRawZKDistinguisher Dp qH qP) : ℝ≥0∞ :=
  (OracleAdv.run (toOracle (realStep (G := dsZkProtocol Dp) ((), ()))) D.run
    (Protocol.Tables.empty, false)).toOuterMeasure {y | y.1 = true}

/-- The probability that the distinguisher outputs `true` against the raw oracle
programmed at absorbed strings by the simulator. -/
noncomputable def dsRawZkSim {qH qP : ℕ} (D : DSRawZKDistinguisher Dp qH qP) : ℝ≥0∞ :=
  (OracleAdv.run (toOracle (simStep (G := dsZkProtocol Dp) ())) D.run
    (Protocol.Tables.empty, false)).toOuterMeasure {y | y.1 = true}

/-- **Zero knowledge of the duplex-sponge transform against the raw oracle.** For
prefix-free encodings, a Σ-protocol with statistical HVZK distance `δ` and commitment
bound `γ` at every pair of the relation, and every distinguisher with at most `qH`
queries to the raw oracle and `qP` proving queries,
`dsRawZkReal D ≤ dsRawZkSim D + qP·δ + qP·(qH + qP)·γ`. -/
theorem dsRawZkReal_le_zkSim (hX : PrefixFree Dp.encX) (hA : PrefixFree Dp.encA)
    {δ γ : ℝ≥0∞} (hZK : ∀ x w, P.rel x w → P.StatHVZKAt x w δ)
    (hγ : ∀ x w, P.rel x w → P.CommitBoundAt x w γ) {qH qP : ℕ}
    (D : DSRawZKDistinguisher Dp qH qP) :
    dsRawZkReal Dp D ≤ dsRawZkSim Dp D + (qP * δ + ((qP * (qH + qP) : ℕ) : ℝ≥0∞) * γ) := by
  set g : Bool × ((dsZkProtocol Dp).Tables × Bool) → ℝ≥0∞ :=
    fun y => if y.1 = true then 1 else 0 with hgdef
  have hg : ∀ y, g y ≤ 1 := fun y => by simp only [g]; split_ifs <;> simp
  have hgr : RejInsensitive g := fun _ _ => rfl
  have hE : ∀ p : PMF (Bool × ((dsZkProtocol Dp).Tables × Bool)),
      p.toOuterMeasure {y | y.1 = true} = ∑' y, p y * g y := fun p => by
    rw [PMF.toOuterMeasure_apply]
    refine tsum_congr fun y => ?_
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, g, mul_ite, mul_one, mul_zero]
  have hflag := run_real_flag_le ((), ()) (keyBoundAt_dsZkProtocol Dp hX hA hγ) D.run qH qP
    D.isQueryBound Protocol.Tables.empty rfl
  replace hflag := (toOuterMeasure_eq_tsum_ite _
    fun y : Bool × ((dsZkProtocol Dp).Tables × Bool) => y.2.2).symm.trans_le hflag
  have hflag' : ((qP * ((Protocol.Tables.empty : (dsZkProtocol Dp).Tables).hash.length +
      (Protocol.Tables.empty : (dsZkProtocol Dp).Tables).prog.length + qH +
      (dsZkProtocol Dp).μ * qP) : ℕ) : ℝ≥0∞) = ((qP * (qH + qP) : ℕ) : ℝ≥0∞) := by
    simp [Protocol.Tables.empty]
  rw [hflag'] at hflag
  have hsim := run_real_le_sim ((), ()) (statHVZKAt_dsZkProtocol Dp hZK) D.run qH qP
    D.isQueryBound (Protocol.Tables.empty, false) g hg hgr
  rw [dsRawZkReal, dsRawZkSim, hE, hE]
  calc _ ≤ ∑' y, OracleAdv.run (toOracle (realStep (G := dsZkProtocol Dp) ((), ()))) D.run
          (Protocol.Tables.empty, false) y * (offFlag g y + if y.2.2 = true then 1 else 0) := by
        refine ENNReal.tsum_le_tsum fun y => mul_le_mul_right ?_ _
        simp only [offFlag]
        split_ifs <;> simp [hg]
    _ = ∑' y, OracleAdv.run (toOracle (realStep (G := dsZkProtocol Dp) ((), ()))) D.run
          (Protocol.Tables.empty, false) y * offFlag g y +
        ∑' y, OracleAdv.run (toOracle (realStep (G := dsZkProtocol Dp) ((), ()))) D.run
          (Protocol.Tables.empty, false) y * (if y.2.2 = true then 1 else 0) := by
        simp only [mul_add]
        rw [ENNReal.tsum_add]
    _ ≤ _ := by
        rw [← add_assoc]
        exact add_le_add hsim hflag

end ZK

end CatCrypt.Crypto.FiatShamirROM
