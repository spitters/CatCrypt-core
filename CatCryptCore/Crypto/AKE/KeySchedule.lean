/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Assumptions.AEAD
public import CatCryptCore.Crypto.Assumptions.DualPRF
public import CatCryptCore.Crypto.KEM.Games
public import CatCryptCore.Tactics.DeriveTimed

/-!
# From a key exchange to a secure channel

A session of a KEM-based key exchange followed by a record layer. The responder's key pair
`(pk, sk)` comes from the KEM `S` (core `KEM.Games.Scheme`), the initiator encapsulates a
shared secret `ss` with encapsulation `c`, and an independent side computation `side` yields
a public part `t` of the transcript and a secret part `z`. The traffic key is
`F ss (ctx pk c t z)`: the key schedule `F` keyed by the shared secret, applied to a context
computed from the transcript and the secret side part. The records are protected by the AEAD
`D` (core `Assumptions.AEAD`) under the traffic key.

The channel adversary sees the transcript `(pk, c, t)` and then interacts with the record
layer: in the real game with the encryption and decryption oracles of `D` under the traffic
key, in the ideal game with the ideal oracles of the core authenticated-encryption game
(a lazily sampled random function and decryption from its log).

Instances:

* a single KEM with a transcript-bound salt: `side = PMF.pure ((), ())` and
  `ctx pk c _ _ = salt pk c`, so the traffic key is `F ss (salt pk c)`
  (`channelAdvantage_le_salt`);
* a hybrid secret from two KEMs through a dual PRF `G : SS₁ → SS₂ → W`, as in hybrid TLS 1.3
  (Bindel–Brendel–Fischlin–Goncalves–Stebila): the second KEM is the side computation, the
  context is its secret, and the schedule is `G` keyed by the first secret; or the roles of
  the two KEMs are exchanged and the schedule is `Function.swap G`. The hybrid channel is
  secure when either KEM is (`hybridAdvantage_le_left`, `hybridAdvantage_le_right`,
  `hybridAdvantage_le_min`).

The proof has three hops: the KEM secret becomes uniform (the KEM reduction `kemRed`, an
IND-CCA adversary with no decapsulation queries, that is an IND-CPA adversary), the traffic
key becomes uniform (the PRF reduction `prfRed`, one query on the context), and the record
layer becomes ideal (the AEAD reduction `aeadRed`, which samples the key exchange itself).
Each reduction answers the record-layer queries of the channel adversary with the real AEAD
oracle under a key it holds (`withKey`).

## Main definitions

* `aeadAnswer`, `withKey` — the answer of the real AEAD oracle, and an adversary with its
  record-layer queries answered by it
* `channelReal`, `channelIdeal`, `channelAdvantage` — the channel games and advantage
* `kemRedTree`, `kemRed`, `prfRed`, `aeadRed` — the three reductions
* `hybridReal`, `hybridIdeal`, `hybridAdvantage`, `kemSide` — the hybrid channel
* the costed forms `withKey.timed`, `kemRedTree.timed`, `prfRed.timed`, `aeadRed.timed`
  (`derive_timed`)

## Main results

* `channelAdvantage_le` — for every adversary, the channel advantage is at most the KEM
  IND-CCA advantage of `kemRed` plus the left dual-PRF advantage of `prfRed` plus the AEAD
  advantage of `aeadRed`
* `hybridAdvantage_le_left`, `hybridAdvantage_le_right`, `hybridAdvantage_le_min` — the
  either-or bounds of the hybrid channel
* `withKey.timeBound_timed`, `kemRedTree.timeBound_timed`, `prfRed.timeBound_timed`,
  `aeadRed.timeBound_timed` — the costed reductions run in the time of the adversary plus
  the AEAD calls of its queries plus a constant

## References

* F. Bindel, J. Brendel, M. Fischlin, B. Goncalves, D. Stebila, *Hybrid Key Encapsulation
  Mechanisms and Authenticated Key Exchange*, PQCrypto 2019
* B. Dowling, M. Fischlin, F. Günther, D. Stebila, *A Cryptographic Analysis of the TLS 1.3
  Handshake Protocol*, J. Cryptology 2021
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.KeySchedule

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.KEM.Games CatCrypt.Crypto.PRPPRF
open scoped ENNReal

/-! ## Answering record-layer queries under a key -/

section Answer

variable {W Ct : Type}

/-- The answer of the real AEAD oracle under `key`, for the encryption `enc` and the
decryption `dec`. -/
def aeadAnswer (enc : W → W → W → Ct) (dec : W → Ct → W → Option W) (key : W) :
    AEAD_CCA_Query W Ct → AEAD_CCA_Answer W Ct
  | .inl (pt, ad) => .inl (enc key pt ad)
  | .inr (ct, ad) => .inr (dec key ct ad)

/-- The record-layer adversary `B` with every query answered by the real AEAD oracle under
`key`; the result asks no queries. -/
def withKey {Q R : Type} (enc : W → W → W → Ct) (dec : W → Ct → W → Option W) (key : W)
    (B : AEAD_CCA_Adversary W Ct) : OracleAdv Q R Bool :=
  (OracleAdv.simulate (fun _ q => .ret (aeadAnswer enc dec key q, ())) B ()).bind
    fun x => .ret x.1

theorem withKey_isQueryBound {Q R : Type} (enc : W → W → W → Ct)
    (dec : W → Ct → W → Option W) (key : W) (B : AEAD_CCA_Adversary W Ct) :
    (withKey (Q := Q) (R := R) enc dec key B).IsQueryBound 0 := by
  unfold withKey
  induction B with
  | ret a => trivial
  | rand p k ih => exact ih
  | query q k ih => exact ih _

end Answer

section Games

variable {W Ct : Type} [SampleableType W] [SampleableType Ct]

/-- The output distribution of `B` against the real AEAD oracles under `key`. -/
noncomputable def aeadRealRun (D : AEADDef W Ct) (key : W) (B : AEAD_CCA_Adversary W Ct) :
    PMF Bool :=
  (OracleAdv.run (aeadRealOracle D key) B ()).map Prod.fst

/-- The output distribution of `B` against the ideal AEAD oracles. -/
noncomputable def aeadIdealRun (B : AEAD_CCA_Adversary W Ct) : PMF Bool :=
  (OracleAdv.run aeadIdealOracle B []).map Prod.fst

omit [SampleableType Ct] in
theorem aeadRealOracle_eq (D : AEADDef W Ct) (key : W) (s : Unit) (q : AEAD_CCA_Query W Ct) :
    aeadRealOracle D key s q = PMF.pure (aeadAnswer D.encrypt D.decrypt key q, ()) := by
  cases q <;> rfl

omit [SampleableType Ct] in
/-- Running `withKey` against any oracle gives the output distribution of `B` against the
real AEAD oracles. -/
theorem run_withKey {Q R S' : Type} (O : S' → Q → PMF (R × S')) (D : AEADDef W Ct) (key : W)
    (B : AEAD_CCA_Adversary W Ct) (s' : S') :
    (OracleAdv.run O (withKey D.encrypt D.decrypt key B) s').map Prod.fst =
      aeadRealRun D key B := by
  unfold withKey aeadRealRun
  induction B generalizing s' with
  | ret a => simp [OracleAdv.simulate, PMF.pure_map]
  | rand p k ih =>
    simp only [OracleAdv.simulate, OracleAdv.bind, OracleAdv.run_rand, PMF.map_bind]
    exact congrArg _ (funext fun b => ih b s')
  | query q k ih =>
    simp only [OracleAdv.simulate, OracleAdv.bind, OracleAdv.run_query, aeadRealOracle_eq,
      PMF.pure_bind]
    exact ih _ s'

/-! ## The channel -/

variable {PK SK SS C T Z X : Type}

/-- The real channel: key generation, encapsulation, the side computation, and the record
layer under the traffic key `F ss (ctx pk c t z)`. -/
noncomputable def channelReal (S : Scheme PK SK SS C) (side : PMF (T × Z))
    (ctx : PK → C → T → Z → X) (F : SS → X → W) (D : AEADDef W Ct)
    (A : PK → C → T → AEAD_CCA_Adversary W Ct) : PMF Bool :=
  S.keygen.bind fun ks => (S.encaps ks.1).bind fun x => side.bind fun tz =>
    aeadRealRun D (F x.1 (ctx ks.1 x.2 tz.1 tz.2)) (A ks.1 x.2 tz.1)

/-- The ideal channel: the same transcript, and the ideal record layer. -/
noncomputable def channelIdeal (S : Scheme PK SK SS C) (side : PMF (T × Z))
    (A : PK → C → T → AEAD_CCA_Adversary W Ct) : PMF Bool :=
  S.keygen.bind fun ks => (S.encaps ks.1).bind fun x => side.bind fun tz =>
    aeadIdealRun (A ks.1 x.2 tz.1)

/-- The channel advantage of `A`. -/
noncomputable def channelAdvantage (S : Scheme PK SK SS C) (side : PMF (T × Z))
    (ctx : PK → C → T → Z → X) (F : SS → X → W) (D : AEADDef W Ct)
    (A : PK → C → T → AEAD_CCA_Adversary W Ct) : ℝ≥0∞ :=
  Advantage (pmfGame (channelReal S side ctx F D A)) (pmfGame (channelIdeal S side A))

end Games

/-! ## Reductions -/

section Reductions

variable {W Ct PK SK SS C T Z X : Type}

/-- The KEM reduction on the public key `pk`, the challenge `c` and the challenge key `k`:
run the side computation and answer the record layer under `F k (ctx pk c t z)`. -/
noncomputable def kemRedTree (side : PMF (T × Z)) (ctx : PK → C → T → Z → X) (F : SS → X → W)
    (enc : W → W → W → Ct) (dec : W → Ct → W → Option W)
    (A : PK → C → T → AEAD_CCA_Adversary W Ct) (pk : PK) (c : C) (k : SS) :
    OracleAdv C (Option SS) Bool :=
  .rand side fun tz => withKey enc dec (F k (ctx pk c tz.1 tz.2)) (A pk c tz.1)

/-- The PRF reduction: run the key exchange and the side computation, query the context, and
answer the record layer under the answer. -/
noncomputable def prfRed (keygen : PMF (PK × SK)) (encaps : PK → PMF (SS × C))
    (side : PMF (T × Z)) (ctx : PK → C → T → Z → X) (enc : W → W → W → Ct)
    (dec : W → Ct → W → Option W) (A : PK → C → T → AEAD_CCA_Adversary W Ct) :
    OracleAdv X W Bool :=
  .rand keygen fun ks => .rand (encaps ks.1) fun x => .rand side fun tz =>
    .query (ctx ks.1 x.2 tz.1 tz.2) fun tk => withKey enc dec tk (A ks.1 x.2 tz.1)

/-- The AEAD reduction: run the key exchange and the side computation, then the channel
adversary on the transcript against the record-layer oracles of the AEAD game. -/
noncomputable def aeadRed (keygen : PMF (PK × SK)) (encaps : PK → PMF (SS × C))
    (side : PMF (T × Z)) (A : PK → C → T → AEAD_CCA_Adversary W Ct) :
    AEAD_CCA_Adversary W Ct :=
  .rand keygen fun ks => .rand (encaps ks.1) fun x => .rand side fun tz => A ks.1 x.2 tz.1

/-- The KEM reduction as an IND-CCA adversary with no decapsulation queries. -/
noncomputable def kemRed [SampleableType W] (side : PMF (T × Z)) (ctx : PK → C → T → Z → X)
    (F : SS → X → W) (D : AEADDef W Ct) (A : PK → C → T → AEAD_CCA_Adversary W Ct) :
    INDCCAAdversary PK SS C 0 where
  run := kemRedTree side ctx F D.encrypt D.decrypt A
  isQueryBound := fun _ _ _ _ => withKey_isQueryBound _ _ _ _

end Reductions

/-! ## Game hops -/

section Hops

variable {W Ct PK SK SS C T Z X : Type} [SampleableType W] [SampleableType Ct]
  [Fintype SS] [Nonempty SS] [DecidableEq C] [DecidableEq X]

/-- The channel with a uniform shared secret. -/
noncomputable def hybKey (S : Scheme PK SK SS C) (side : PMF (T × Z))
    (ctx : PK → C → T → Z → X) (F : SS → X → W) (D : AEADDef W Ct)
    (A : PK → C → T → AEAD_CCA_Adversary W Ct) : PMF Bool :=
  S.keygen.bind fun ks => (S.encaps ks.1).bind fun x => (PMF.uniformOfFintype SS).bind fun k =>
    side.bind fun tz => aeadRealRun D (F k (ctx ks.1 x.2 tz.1 tz.2)) (A ks.1 x.2 tz.1)

/-- The channel with a uniform traffic key. -/
noncomputable def hybTraffic (S : Scheme PK SK SS C) (side : PMF (T × Z)) (D : AEADDef W Ct)
    (A : PK → C → T → AEAD_CCA_Adversary W Ct) : PMF Bool :=
  S.keygen.bind fun ks => (S.encaps ks.1).bind fun x => side.bind fun tz =>
    (PMF.uniformOfFintype W).bind fun tk => aeadRealRun D tk (A ks.1 x.2 tz.1)

variable (S : Scheme PK SK SS C) (side : PMF (T × Z)) (ctx : PK → C → T → Z → X)
  (F : SS → X → W) (D : AEADDef W Ct) (A : PK → C → T → AEAD_CCA_Adversary W Ct)

omit [SampleableType Ct] [DecidableEq X] in
/-- The IND-CCA game of `kemRed` with the real key is the real channel. -/
theorem indccaGame_true_eq :
    indccaGame S (kemRed side ctx F D A) true = channelReal S side ctx F D A := by
  simp [indccaGame, channelReal, kemRed, kemRedTree, run_withKey, PMF.map_bind]

omit [SampleableType Ct] [DecidableEq X] in
/-- The IND-CCA game of `kemRed` with a uniform key is the channel with a uniform shared
secret. -/
theorem indccaGame_false_eq :
    indccaGame S (kemRed side ctx F D A) false = hybKey S side ctx F D A := by
  simp [indccaGame, hybKey, kemRed, kemRedTree, run_withKey, PMF.map_bind]

omit [SampleableType Ct] [DecidableEq C] [DecidableEq X] in
/-- The real PRF game of `prfRed` is the channel with a uniform shared secret. -/
theorem prfReal_eq :
    ((PMF.uniformOfFintype SS).bind fun k =>
      (OracleAdv.run (keyedOracle F k) (prfRed S.keygen S.encaps side ctx D.encrypt D.decrypt A)
        ()).map Prod.fst) = hybKey S side ctx F D A := by
  simp only [prfRed, hybKey, keyedOracle, OracleAdv.run_rand, OracleAdv.run_query,
    PMF.pure_bind, PMF.map_bind, run_withKey]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun ks => ?_)
  rw [PMF.bind_comm]

omit [SampleableType Ct] [Fintype SS] [Nonempty SS] [DecidableEq C] in
/-- The random-function game of `prfRed` is the channel with a uniform traffic key. -/
theorem prfIdeal_eq :
    (OracleAdv.run rfOracle (prfRed S.keygen S.encaps side ctx D.encrypt D.decrypt A) []).map
      Prod.fst = hybTraffic S side D A := by
  simp [prfRed, hybTraffic, rfOracle, PMF.map_bind, PMF.bind_map, run_withKey]

omit [SampleableType Ct] [Fintype SS] [Nonempty SS] [DecidableEq C] in
/-- The real AEAD game of `aeadRed` is the channel with a uniform traffic key. -/
theorem aeadReal_eq :
    ((PMF.uniformOfFintype W).bind fun key =>
      (OracleAdv.run (aeadRealOracle D key) (aeadRed S.keygen S.encaps side A) ()).map
        Prod.fst) = hybTraffic S side D A := by
  simp only [aeadRed, hybTraffic, aeadRealRun, OracleAdv.run_rand, PMF.map_bind]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun ks => ?_)
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun x => ?_)
  rw [PMF.bind_comm]

omit [Fintype SS] [Nonempty SS] [DecidableEq C] in
/-- The ideal AEAD game of `aeadRed` is the ideal channel. -/
theorem aeadIdeal_eq :
    (OracleAdv.run aeadIdealOracle (aeadRed S.keygen S.encaps side A) []).map Prod.fst =
      channelIdeal S side A := by
  simp only [aeadRed, channelIdeal, aeadIdealRun, OracleAdv.run_rand, PMF.map_bind]

/-! ## Security of the channel -/

/-- **Key exchange to channel.** For every channel adversary `A`, the channel advantage is
at most the KEM IND-CCA advantage of the reduction `kemRed` (which asks no decapsulation
queries), plus the dual-PRF advantage of `prfRed` against the key schedule `F` keyed by the
shared secret, plus the AEAD advantage of `aeadRed`. -/
theorem channelAdvantage_le :
    channelAdvantage S side ctx F D A ≤
      indccaAdvantage S (kemRed side ctx F D A) +
      DualPRF_Left_Advantage F (prfRed S.keygen S.encaps side ctx D.encrypt D.decrypt A) +
      AEAD_CCA_Advantage D (aeadRed S.keygen S.encaps side A) := by
  unfold channelAdvantage indccaAdvantage DualPRF_Left_Advantage PRF_q_Advantage
    AEAD_CCA_Advantage realGame rfGame AEAD_CCA_Game_Real AEAD_CCA_Game_Ideal
  rw [indccaGame_true_eq, indccaGame_false_eq, prfReal_eq, prfIdeal_eq, aeadReal_eq,
    aeadIdeal_eq]
  calc _ ≤ _ := advantage_triangle _ (pmfGame (hybKey S side ctx F D A)) _
    _ ≤ _ := add_le_add_right (advantage_triangle _ (pmfGame (hybTraffic S side D A)) _) _
    _ = _ := (add_assoc _ _ _).symm

omit [DecidableEq X] in
/-- **A single KEM with a transcript-bound salt.** The traffic key is `F ss (salt pk c)`. -/
theorem channelAdvantage_le_salt [DecidableEq X] (salt : PK → C → X)
    (A : PK → C → Unit → AEAD_CCA_Adversary W Ct) :
    channelAdvantage S (PMF.pure ((), ())) (fun pk c _ (_ : Unit) => salt pk c) F D A ≤
      indccaAdvantage S (kemRed (PMF.pure ((), ())) (fun pk c _ (_ : Unit) => salt pk c) F D A) +
      DualPRF_Left_Advantage F (prfRed S.keygen S.encaps (PMF.pure ((), ()))
        (fun pk c _ (_ : Unit) => salt pk c) D.encrypt D.decrypt A) +
      AEAD_CCA_Advantage D (aeadRed S.keygen S.encaps (PMF.pure ((), ())) A) :=
  channelAdvantage_le S _ _ F D A

end Hops

/-! ## The hybrid channel -/

section Hybrid

variable {W Ct PK₁ SK₁ SS₁ C₁ PK₂ SK₂ SS₂ C₂ : Type} [SampleableType W] [SampleableType Ct]

/-- Key generation and encapsulation of `S`, with the key pair and the encapsulation. -/
noncomputable def kemJoint {PK SK SS C : Type} (S : Scheme PK SK SS C) :
    PMF ((PK × SK) × (SS × C)) :=
  S.keygen.bind fun ks => (S.encaps ks.1).map fun x => (ks, x)

/-- A KEM run as the side computation of a channel: the public part is the public key and
the encapsulation, the secret part is the shared secret. -/
noncomputable def kemSide {PK SK SS C : Type} (S : Scheme PK SK SS C) : PMF ((PK × C) × SS) :=
  (kemJoint S).map fun r => ((r.1.1, r.2.2), r.2.1)

/-- The context that is the secret part of the side computation. -/
def ctxSecret {PK C T Z : Type} : PK → C → T → Z → Z := fun _ _ _ z => z

/-- The real hybrid channel: both KEMs run, and the traffic key is `G ss₁ ss₂`. -/
noncomputable def hybridReal (S₁ : Scheme PK₁ SK₁ SS₁ C₁) (S₂ : Scheme PK₂ SK₂ SS₂ C₂)
    (G : SS₁ → SS₂ → W) (D : AEADDef W Ct)
    (A : PK₁ × C₁ → PK₂ × C₂ → AEAD_CCA_Adversary W Ct) : PMF Bool :=
  S₁.keygen.bind fun ks₁ => (S₁.encaps ks₁.1).bind fun x₁ =>
    S₂.keygen.bind fun ks₂ => (S₂.encaps ks₂.1).bind fun x₂ =>
      aeadRealRun D (G x₁.1 x₂.1) (A (ks₁.1, x₁.2) (ks₂.1, x₂.2))

/-- The ideal hybrid channel: both KEMs run, and the record layer is ideal. -/
noncomputable def hybridIdeal (S₁ : Scheme PK₁ SK₁ SS₁ C₁) (S₂ : Scheme PK₂ SK₂ SS₂ C₂)
    (A : PK₁ × C₁ → PK₂ × C₂ → AEAD_CCA_Adversary W Ct) : PMF Bool :=
  S₁.keygen.bind fun ks₁ => (S₁.encaps ks₁.1).bind fun x₁ =>
    S₂.keygen.bind fun ks₂ => (S₂.encaps ks₂.1).bind fun x₂ =>
      aeadIdealRun (A (ks₁.1, x₁.2) (ks₂.1, x₂.2))

/-- The advantage of `A` against the hybrid channel. -/
noncomputable def hybridAdvantage (S₁ : Scheme PK₁ SK₁ SS₁ C₁) (S₂ : Scheme PK₂ SK₂ SS₂ C₂)
    (G : SS₁ → SS₂ → W) (D : AEADDef W Ct)
    (A : PK₁ × C₁ → PK₂ × C₂ → AEAD_CCA_Adversary W Ct) : ℝ≥0∞ :=
  Advantage (pmfGame (hybridReal S₁ S₂ G D A)) (pmfGame (hybridIdeal S₁ S₂ A))

/-- The hybrid adversary as a channel adversary against the first KEM. -/
def hybAdvLeft (A : PK₁ × C₁ → PK₂ × C₂ → AEAD_CCA_Adversary W Ct) :
    PK₁ → C₁ → PK₂ × C₂ → AEAD_CCA_Adversary W Ct :=
  fun pk c t => A (pk, c) t

/-- The hybrid adversary as a channel adversary against the second KEM. -/
def hybAdvRight (A : PK₁ × C₁ → PK₂ × C₂ → AEAD_CCA_Adversary W Ct) :
    PK₂ → C₂ → PK₁ × C₁ → AEAD_CCA_Adversary W Ct :=
  fun pk c t => A t (pk, c)

variable (S₁ : Scheme PK₁ SK₁ SS₁ C₁) (S₂ : Scheme PK₂ SK₂ SS₂ C₂) (G : SS₁ → SS₂ → W)
  (D : AEADDef W Ct) (A : PK₁ × C₁ → PK₂ × C₂ → AEAD_CCA_Adversary W Ct)

omit [SampleableType Ct] in
/-- The real channel of the first KEM with the second KEM as side computation is the real
hybrid channel. -/
theorem channelReal_left_eq :
    channelReal S₁ (kemSide S₂) ctxSecret G D (hybAdvLeft A) = hybridReal S₁ S₂ G D A := by
  simp [channelReal, hybridReal, kemSide, kemJoint, ctxSecret, hybAdvLeft, PMF.bind_bind,
    PMF.bind_map, PMF.map_bind, Function.comp_def]

/-- The ideal channel of the first KEM with the second KEM as side computation is the ideal
hybrid channel. -/
theorem channelIdeal_left_eq :
    channelIdeal S₁ (kemSide S₂) (hybAdvLeft A) = hybridIdeal S₁ S₂ A := by
  simp [channelIdeal, hybridIdeal, kemSide, kemJoint, hybAdvLeft, PMF.bind_bind,
    PMF.bind_map, PMF.map_bind, Function.comp_def]

omit [SampleableType Ct] in
/-- The real channel of the second KEM with the first KEM as side computation and the
schedule `Function.swap G` is the real hybrid channel. -/
theorem channelReal_right_eq :
    channelReal S₂ (kemSide S₁) ctxSecret (Function.swap G) D (hybAdvRight A) =
      hybridReal S₁ S₂ G D A := by
  have h₁ : hybridReal S₁ S₂ G D A = (kemJoint S₁).bind fun r₁ => (kemJoint S₂).bind fun r₂ =>
      aeadRealRun D (G r₁.2.1 r₂.2.1) (A (r₁.1.1, r₁.2.2) (r₂.1.1, r₂.2.2)) := by
    simp [hybridReal, kemJoint, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  have h₂ : channelReal S₂ (kemSide S₁) ctxSecret (Function.swap G) D (hybAdvRight A) =
      (kemJoint S₂).bind fun r₂ => (kemJoint S₁).bind fun r₁ =>
        aeadRealRun D (G r₁.2.1 r₂.2.1) (A (r₁.1.1, r₁.2.2) (r₂.1.1, r₂.2.2)) := by
    simp [channelReal, kemSide, kemJoint, ctxSecret, hybAdvRight, Function.swap, PMF.bind_bind,
      PMF.bind_map, PMF.map_bind, Function.comp_def]
  rw [h₁, h₂, PMF.bind_comm]

/-- The ideal channel of the second KEM with the first KEM as side computation is the ideal
hybrid channel. -/
theorem channelIdeal_right_eq :
    channelIdeal S₂ (kemSide S₁) (hybAdvRight A) = hybridIdeal S₁ S₂ A := by
  have h₁ : hybridIdeal S₁ S₂ A = (kemJoint S₁).bind fun r₁ => (kemJoint S₂).bind fun r₂ =>
      aeadIdealRun (A (r₁.1.1, r₁.2.2) (r₂.1.1, r₂.2.2)) := by
    simp [hybridIdeal, kemJoint, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  have h₂ : channelIdeal S₂ (kemSide S₁) (hybAdvRight A) =
      (kemJoint S₂).bind fun r₂ => (kemJoint S₁).bind fun r₁ =>
        aeadIdealRun (A (r₁.1.1, r₁.2.2) (r₂.1.1, r₂.2.2)) := by
    simp [channelIdeal, kemSide, kemJoint, hybAdvRight, PMF.bind_bind, PMF.bind_map,
      PMF.map_bind, Function.comp_def]
  rw [h₁, h₂, PMF.bind_comm]

variable [Fintype SS₁] [Nonempty SS₁] [Fintype SS₂] [Nonempty SS₂] [DecidableEq SS₁]
  [DecidableEq SS₂] [DecidableEq C₁] [DecidableEq C₂]

omit [Fintype SS₂] [Nonempty SS₂] [DecidableEq SS₁] [DecidableEq C₂] in
/-- **Hybrid channel, first KEM.** For every adversary, the hybrid channel advantage is at
most the IND-CCA advantage of a reduction against the first KEM, plus the dual-PRF advantage
of a reduction against `G` keyed by the first secret, plus the AEAD advantage of a
reduction; the second KEM may be broken. -/
theorem hybridAdvantage_le_left :
    hybridAdvantage S₁ S₂ G D A ≤
      indccaAdvantage S₁ (kemRed (kemSide S₂) ctxSecret G D (hybAdvLeft A)) +
      DualPRF_Left_Advantage G (prfRed S₁.keygen S₁.encaps (kemSide S₂) ctxSecret D.encrypt
        D.decrypt (hybAdvLeft A)) +
      AEAD_CCA_Advantage D (aeadRed S₁.keygen S₁.encaps (kemSide S₂) (hybAdvLeft A)) := by
  have h := channelAdvantage_le S₁ (kemSide S₂) ctxSecret G D (hybAdvLeft A)
  unfold channelAdvantage at h
  rwa [channelReal_left_eq, channelIdeal_left_eq] at h

omit [Fintype SS₁] [Nonempty SS₁] [DecidableEq SS₂] [DecidableEq C₁] in
/-- **Hybrid channel, second KEM.** For every adversary, the hybrid channel advantage is at
most the IND-CCA advantage of a reduction against the second KEM, plus the dual-PRF advantage
of a reduction against `G` keyed by the second secret, plus the AEAD advantage of a
reduction; the first KEM may be broken. -/
theorem hybridAdvantage_le_right :
    hybridAdvantage S₁ S₂ G D A ≤
      indccaAdvantage S₂ (kemRed (kemSide S₁) ctxSecret (Function.swap G) D (hybAdvRight A)) +
      DualPRF_Right_Advantage G (prfRed S₂.keygen S₂.encaps (kemSide S₁) ctxSecret D.encrypt
        D.decrypt (hybAdvRight A)) +
      AEAD_CCA_Advantage D (aeadRed S₂.keygen S₂.encaps (kemSide S₁) (hybAdvRight A)) := by
  have h := channelAdvantage_le S₂ (kemSide S₁) ctxSecret (Function.swap G) D (hybAdvRight A)
  unfold channelAdvantage at h
  rwa [channelReal_right_eq, channelIdeal_right_eq] at h

/-- **Hybrid channel, either-or.** The hybrid channel advantage is at most the smaller of the
two bounds: the channel is secure when either KEM is, provided `G` is a dual PRF and the AEAD
is secure. -/
theorem hybridAdvantage_le_min :
    hybridAdvantage S₁ S₂ G D A ≤
      min (indccaAdvantage S₁ (kemRed (kemSide S₂) ctxSecret G D (hybAdvLeft A)) +
        DualPRF_Left_Advantage G (prfRed S₁.keygen S₁.encaps (kemSide S₂) ctxSecret D.encrypt
          D.decrypt (hybAdvLeft A)) +
        AEAD_CCA_Advantage D (aeadRed S₁.keygen S₁.encaps (kemSide S₂) (hybAdvLeft A)))
      (indccaAdvantage S₂ (kemRed (kemSide S₁) ctxSecret (Function.swap G) D (hybAdvRight A)) +
        DualPRF_Right_Advantage G (prfRed S₂.keygen S₂.encaps (kemSide S₁) ctxSecret D.encrypt
          D.decrypt (hybAdvRight A)) +
        AEAD_CCA_Advantage D (aeadRed S₂.keygen S₂.encaps (kemSide S₁) (hybAdvRight A))) :=
  le_min (hybridAdvantage_le_left S₁ S₂ G D A) (hybridAdvantage_le_right S₁ S₂ G D A)

end Hybrid

/-! ## Costed reductions -/

derive_timed withKey

derive_timed kemRedTree

derive_timed prfRed

derive_timed aeadRed

section Time

open OracleAdv.Timed

variable {W Ct PK SK SS C T Z X : Type}

/-- **Time of `withKey`.** With the record-layer adversary `B` of time at most `T` and at most
`q` queries, and encryption and decryption of cost at most `te` and `td`, the costed `withKey`
has time at most `T + q * (3 + te + td)`: each query is answered by one call of the
encryption or the decryption and three steps. -/
theorem withKey.timeBound_timed {Q R : Type} (enc : W → W → W → Ct) (encCost : W → W → W → ℕ)
    (dec : W → Ct → W → Option W) (decCost : W → Ct → W → ℕ) {te td : ℕ}
    (he : ∀ k pt ad, encCost k pt ad ≤ te) (hd : ∀ k ct ad, decCost k ct ad ≤ td) (key : W)
    {B : OracleAdv.Timed (AEAD_CCA_Query W Ct) (AEAD_CCA_Answer W Ct) Bool} {T q : ℕ}
    (hB : B.TimeBound T) (hq : B.erase.IsQueryBound q) :
    StepTimeBound (withKey.timed (Q := Q) (R := R) enc encCost dec decCost key B)
      (T + q * (3 + te + td)) := by
  have hs := timeBound_simulate (t := 3 + te + td)
    (fun (_ : Unit) (d : AEAD_CCA_Query W Ct) => ((2 + match d with
      | .inl (pt, ad) => 1 + encCost key pt ad
      | .inr (ct, ad) => 1 + decCost key ct ad),
      (OracleAdv.Timed.ret (aeadAnswer enc dec key d, ()) : OracleAdv.Timed Q R _)))
    (fun _ d => ⟨by rcases d with ⟨pt, ad⟩ | ⟨ct, ad⟩ <;> simp only <;> grind, trivial⟩) hB hq ()
  unfold withKey.timed
  refine (stepTimeBound_delay (timeBound_bind (n := 0) (f := fun x => (0, OracleAdv.Timed.ret x.1))
    hs.2 fun _ => ⟨le_refl _, trivial⟩)).mono ?_
  have := hs.1
  omega

/-- **Time of the KEM reduction.** With the channel adversary of time at most `T`, at most `q`
record-layer queries and call cost at most `a`, the key schedule and the context of cost at
most `f` and `x`, and encryption and decryption of cost at most `te` and `td`, the costed KEM
reduction has time at most `5 + f + x + a + T + q * (3 + te + td)`. -/
theorem kemRedTree.timeBound_timed (side : PMF (T × Z)) (ctx : PK → C → T → Z → X)
    (ctxCost : PK → C → T → Z → ℕ) (F : SS → X → W) (FCost : SS → X → ℕ)
    (enc : W → W → W → Ct) (encCost : W → W → W → ℕ) (dec : W → Ct → W → Option W)
    (decCost : W → Ct → W → ℕ)
    (A : PK → C → T → OracleAdv.Timed (AEAD_CCA_Query W Ct) (AEAD_CCA_Answer W Ct) Bool)
    (ACost : PK → C → T → ℕ) {te td f x a Tm q : ℕ}
    (he : ∀ k pt ad, encCost k pt ad ≤ te) (hd : ∀ k ct ad, decCost k ct ad ≤ td)
    (hF : ∀ k y, FCost k y ≤ f) (hctx : ∀ pk c t z, ctxCost pk c t z ≤ x)
    (hAc : ∀ pk c t, ACost pk c t ≤ a) (hA : ∀ pk c t, (A pk c t).TimeBound Tm)
    (hq : ∀ pk c t, (A pk c t).erase.IsQueryBound q) (pk : PK) (c : C) (k : SS) :
    StepTimeBound (kemRedTree.timed side ctx ctxCost F FCost enc encCost dec decCost A ACost
      pk c k) (5 + f + x + a + (Tm + q * (3 + te + td))) := by
  unfold kemRedTree.timed
  refine stepTimeBound_zero.2 ⟨by omega, fun tz => ?_⟩
  have w := withKey.timeBound_timed (Q := C) (R := Option SS) enc encCost dec decCost he hd
    (F k (ctx pk c tz.1 tz.2)) (hA pk c tz.1) (hq pk c tz.1)
  have := hF k (ctx pk c tz.1 tz.2)
  have := hctx pk c tz.1 tz.2
  have := hAc pk c tz.1
  exact (stepTimeBound_delay w).mono (by omega)

/-- **Time of the PRF reduction.** Under the bounds of `kemRedTree.timeBound_timed` and
encapsulation of cost at most `e`, the costed PRF reduction has time at most
`8 + e + x + a + T + q * (3 + te + td)`: three samples, one query, the encapsulation, the
context, the adversary call and the answered record-layer queries. -/
theorem prfRed.timeBound_timed (keygen : PMF (PK × SK)) (encaps : PK → PMF (SS × C))
    (encapsCost : PK → ℕ) (side : PMF (T × Z)) (ctx : PK → C → T → Z → X)
    (ctxCost : PK → C → T → Z → ℕ)
    (enc : W → W → W → Ct) (encCost : W → W → W → ℕ) (dec : W → Ct → W → Option W)
    (decCost : W → Ct → W → ℕ)
    (A : PK → C → T → OracleAdv.Timed (AEAD_CCA_Query W Ct) (AEAD_CCA_Answer W Ct) Bool)
    (ACost : PK → C → T → ℕ) {te td e x a Tm q : ℕ}
    (he : ∀ k pt ad, encCost k pt ad ≤ te) (hd : ∀ k ct ad, decCost k ct ad ≤ td)
    (hE : ∀ pk, encapsCost pk ≤ e) (hctx : ∀ pk c t z, ctxCost pk c t z ≤ x)
    (hAc : ∀ pk c t, ACost pk c t ≤ a) (hA : ∀ pk c t, (A pk c t).TimeBound Tm)
    (hq : ∀ pk c t, (A pk c t).erase.IsQueryBound q) :
    StepTimeBound (prfRed.timed keygen encaps encapsCost side ctx ctxCost enc encCost dec
      decCost A ACost) (8 + e + x + a + (Tm + q * (3 + te + td))) := by
  unfold prfRed.timed
  refine stepTimeBound_zero.2 ⟨by omega, fun ks => ?_⟩
  have := hE ks.1
  refine ⟨by beta_reduce; omega, by beta_reduce; omega, fun xx =>
    ⟨by beta_reduce; omega, by beta_reduce; omega, fun tz => ?_⟩⟩
  have := hctx ks.1 xx.2 tz.1 tz.2
  refine ⟨by beta_reduce; omega, by beta_reduce; omega, fun tk => ?_⟩
  have w := withKey.timeBound_timed (Q := X) (R := W) enc encCost dec decCost he hd tk
    (hA ks.1 xx.2 tz.1) (hq ks.1 xx.2 tz.1)
  have := hAc ks.1 xx.2 tz.1
  have := w.1
  exact ⟨by beta_reduce; omega, w.2.mono (by beta_reduce; omega)⟩

/-- **Time of the AEAD reduction.** With the channel adversary of time at most `T` and call
cost at most `a`, and encapsulation of cost at most `e`, the costed AEAD reduction has time at
most `5 + e + a + T`: three samples, the encapsulation and the adversary call. -/
theorem aeadRed.timeBound_timed (keygen : PMF (PK × SK)) (encaps : PK → PMF (SS × C))
    (encapsCost : PK → ℕ) (side : PMF (T × Z))
    (A : PK → C → T → OracleAdv.Timed (AEAD_CCA_Query W Ct) (AEAD_CCA_Answer W Ct) Bool)
    (ACost : PK → C → T → ℕ) {e a Tm : ℕ} (hE : ∀ pk, encapsCost pk ≤ e)
    (hAc : ∀ pk c t, ACost pk c t ≤ a) (hA : ∀ pk c t, (A pk c t).TimeBound Tm) :
    StepTimeBound (aeadRed.timed keygen encaps encapsCost side A ACost) (5 + e + a + Tm) := by
  unfold aeadRed.timed
  refine stepTimeBound_zero.2 ⟨by omega, fun ks => ?_⟩
  have := hE ks.1
  refine ⟨by beta_reduce; omega, by beta_reduce; omega, fun xx =>
    ⟨by beta_reduce; omega, by beta_reduce; omega, fun tz => ?_⟩⟩
  have := hAc ks.1 xx.2 tz.1
  exact ⟨by beta_reduce; omega, (hA ks.1 xx.2 tz.1).mono (by beta_reduce; omega)⟩

end Time

end CatCrypt.Crypto.AKE.KeySchedule
