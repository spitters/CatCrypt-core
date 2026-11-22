/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMIDAuth
import CatCryptCore.Tactics.AutoDispatchExt
import CatCryptCore.Tactics.AutoOracleRun

/-!
# The FS-AEAD integrity hop of the ACD construction with headers

The hop games `acdIDHopGame … k root A` of `CatCryptCore.Crypto.Messaging.SMIDAuth` at any root
step `root` keep the bookkeeping invariant `ACDIDInv` of `acdIDSM`. A step of a hop game at a
root output `y` is a step of the hop game at the real root step of the constant root KDF
`constPRG y`, whose states satisfy the invariant `ACDInv` of the base whenever the hop states
do (`acdIDHopOracle_support_real`). Hence the invariant `ACDIDHopInv` (the invariant `ACDInv`
at some root KDF and `ACDIDInv` of the joined state) holds along every run of a hop game
(`acdIDHopOracle_hopInv`).

## The FS-AEAD integrity hop

At the uniform root output of the epoch `k`, the chain of the epoch `k` starts from a uniform
state. The reduction `acdIDFSRed` embeds the challenger of the FS-AEAD integrity game of `G` and
`aeadComapAD D dec` as that chain: its simulator `acdIDFSImpl` answers the queries of the
corruption game by the simulator `smAuthFSImplAt` of the base, keeps the bookkeeping of
`acdIDSM` with a value in place of the chain of the epoch `k`, and asks each delivery into the
epoch `k` with a successful key lookup to the `dec` oracle, at the associated data `enc h ad`.
The abstraction `acdIDFSAbs` puts the chain of the integrity game back and replaces the stored
keys of the epoch `k` by the keys of that chain (`acdIDFixSt`); the hop oracle does not read the
base states of the bookkeeping (`acdIDHopOracle_normHop`). With `dec` a left inverse of `enc`,
the real integrity game of the reduction is the hop game at a uniform root output
(`acdIDFS_real_eq`) and the ideal one never raises the flag (`acdIDFS_ideal_eq_zero`). Hence
(`acdIDSM_intAdvantage_le`)

  `Adv_int(A) ≤ ∑_{k < N} (Adv_CKA(acdIDCKARed k A) + Adv_PRF-PRNG(acdIDRootRed k A) +
    Adv_FS-INT(acdIDFSRed k A))`.

## Main definitions

* `constPRG` — the root KDF with a constant output
* `ACDIDHopInv` — the invariant of the hop states
* `acdIDFixEl`, `acdIDFixSt`, `acdIDFixX`, `acdIDNormSt`, `acdIDNormX`, `acdIDNormHop` — the
  bookkeeping with the keys of the epoch `k` from a given chain and with trivial base states
* `acdIDDlvHit` — a delivery into the epoch `k` with a successful key lookup
* `ACDIDFSSt`, `fsSimRcv`, `acdIDFSSmF`, `acdIDFSDlvOf`, `acdIDFSImpl`, `acdIDFSInit` — the
  simulator of the integrity hop
* `acdIDFSTree`, `acdIDFSRed` — the FS-AEAD integrity reduction
* `acdIDFSAbs`, `smAuxOfID`, `ACDIDFSInv` — the abstraction and the invariant of the simulation

## Main results

* `ACDInv.of_canSend` — the invariant `ACDInv` does not read the root KDF at a state where a
  party may send
* `acdIDHopOracle_support_real` — a step of a hop game is a step at the real root step of a
  root KDF
* `acdIDHopOracle_hopInv`, `acdIDHopInv_init` — the invariant of the hop states
* `ACDIDInv.store_epoch_of_storeClear`, `ACDIDInv.store_ne_of_allowCorr` — a corruption
  admitted by the restricted gate that leaves the epoch `k` safe finds no key of the epoch `k`
  in the store
* `ACDIDInv.undelivered_of_rkey` — a successful key lookup is at an undelivered position
* `acdIDHop_run_eager_unif` — eager sampling of the uniform root output at the epoch `k`
* `acdIDRKey_fix`, `acdIDDeliver_fix`, `acdIDDeliver_fix_flag`, `acdIDXUpd_fixX` — the key
  lookup, the delivery and the bookkeeping update with the chain of the epoch `k` held elsewhere
* `acdIDHopOracle_normHop` — the hop oracle does not read the base states of the bookkeeping
* `acdIDFS_step_sm`, `acdIDFS_step_dlv`, `acdIDFS_step` — the simulator is the hop oracle at the
  abstraction
* `acdIDFS_inv`, `acdIDFSInv_init`, `ACDIDFSInv.logDec_eq`, `acdIDFS_ideal_flag` — the invariant
  of the simulation
* `acdIDFS_real_eq`, `acdIDFS_ideal_eq_zero`, `acdIDHopGame_le_fsint` — the FS-AEAD integrity
  hop
* `acdIDSM_intAdvantage_le` — the integrity bound above
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open scoped ENNReal

section HopInv

variable {Sc Msg Key Rand RK Sa W Ct Kt : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [SampleableType Kt] [Fintype RK] [Nonempty RK] [Inhabited Msg]
  [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct]

/-- The root KDF with the constant output `y`. -/
def constPRG (y : RK × Sa) : PRGDef (RK × Key) (RK × Sa) := ⟨fun _ => y⟩

omit [Fintype RK] [Nonempty RK] [Inhabited Msg] [DecidableEq Msg] [SampleableType W]
  [SampleableType Ct] [DecidableEq W] [DecidableEq Ct] in
/-- At a state where party `p` may send, no party may receive, so the invariant `ACDInv` holds
at every root KDF. -/
theorem ACDInv.of_canSend {C : CKADef Sc Msg Key} {R : PRGDef (RK × Key) (RK × Sa)}
    {J : Sc → Sc → Prop} {σ : SMSt Sc Msg RK Sa} (h : ACDInv C R J σ) {p : CKAParty}
    (hp : σ.ck.canSend p = true) (R' : PRGDef (RK × Key) (RK × Sa)) : ACDInv C R' J σ := by
  refine ⟨h.reach, h.send, fun q hq => ?_⟩
  exfalso
  cases q <;> cases p <;> simp_all [CKAGameSt.canSend, CKAGameSt.canRecv]

omit [Fintype RK] [Nonempty RK] [Inhabited Msg] [DecidableEq Msg] [DecidableEq W]
  [DecidableEq Ct] in
omit [SampleableType Kt] in
/-- **A step of the secure-messaging oracle at any root step is a step at the real root step of
some root KDF** keeping the invariant `ACDInv`. -/
theorem smOracleOfAt_support_real (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R R₀ : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct W Kt)
    {J : Sc → Sc → Prop} (ΔFS ΔPCS t k : ℕ) (root : RK → Key → PMF (RK × Sa))
    (σ : SMSt Sc Msg RK Sa) (hσ : ACDInv C R₀ J σ) (q : SMQuery W)
    (w : SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa)
    (hw : w ∈ (smOracleOfAt C R G D ΔFS ΔPCS t k false root σ q).support) :
    ∃ R' : PRGDef (RK × Key) (RK × Sa), ACDInv C R' J σ ∧
      w ∈ (smOracleOfAt C R' G D ΔFS ΔPCS t k false (realRoot R') σ q).support := by
  cases q with
  | ratchet p =>
    by_cases hc : σ.ck.canSend p = true
    · simp only [smOracleOfAt, smOracleOf, hc, ite_true, PMF.support_bind, Set.mem_iUnion,
        PMF.support_uniformFintype] at hw
      obtain ⟨r, -, y, hy, hw⟩ := hw
      refine ⟨constPRG y, hσ.of_canSend hc _, ?_⟩
      simp only [smOracleOfAt, smOracleOf, hc, ite_true, PMF.support_bind, Set.mem_iUnion,
        PMF.support_uniformFintype, realRoot, ite_self]
      exact ⟨r, Set.mem_univ _, y, by simp [constPRG], hw⟩
    · refine ⟨R₀, hσ, ?_⟩
      simpa [smOracleOfAt, smOracleOf, hc] using hw
  | recv p => exact ⟨R₀, hσ, by simpa [smOracleOfAt, smOracleOf] using hw⟩
  | send p m => exact ⟨R₀, hσ, by simpa [smOracleOfAt, smOracleOf] using hw⟩
  | chall p m => exact ⟨R₀, hσ, by simpa [smOracleOfAt, smOracleOf] using hw⟩
  | corrupt p => exact ⟨R₀, hσ, by simpa [smOracleOfAt, smOracleOf] using hw⟩

omit [Fintype RK] [Nonempty RK] [Inhabited Msg] in
omit [SampleableType Kt] in
/-- **A step of a hop game at any root step is a step of the hop game at the real root step of
some root KDF** keeping the invariant `ACDInv` of the base state. -/
theorem acdIDHopOracle_support_real (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R R₀ : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg) Kt) (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W)
    (maxSkip maxStored : ℕ) {J : Sc → Sc → Prop} (ΔFS ΔPCS t k : ℕ)
    (root : RK → Key → PMF (RK × Sa)) (s : ACDIDHopSt Sc Msg RK Sa W Ct Kt)
    (hσ : ACDInv C R₀ J s.1.1.1) (d : SMIDQuery W (ACDHdr Msg) Ct)
    (z : ACDIDAns Sc Msg RK Sa W Ct Kt × ACDIDHopSt Sc Msg RK Sa W Ct Kt)
    (hz : z ∈ (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k root s d).support) :
    ∃ R' : PRGDef (RK × Key) (RK × Sa), ACDInv C R' J s.1.1.1 ∧
      z ∈ (acdIDHopOracle C R' G D dec enc maxSkip maxStored ΔFS ΔPCS t k (realRoot R') s
        d).support := by
  simp only [acdIDHopOracle, PMF.support_map, Set.mem_image] at hz ⊢
  obtain ⟨w, hw, rfl⟩ := hz
  by_cases hs : s.1.2.epochSafe ΔFS ΔPCS k = true
  · simp only [hs, ite_true] at hw ⊢
    cases d with
    | sm q =>
      by_cases hg : smIDGate s.1.2 (ckaShadow s.1.1.1.ck) q = true
      · simp only [acdIDHopStep, hg, ite_true, PMF.support_map, Set.mem_image] at hw ⊢
        obtain ⟨v, hv, rfl⟩ := hw
        obtain ⟨R', hR', hv'⟩ := smOracleOfAt_support_real C R R₀ G (aeadComapAD D dec)
          ΔFS ΔPCS t k root s.1.1.1 hσ _ v hv
        exact ⟨R', hR', _, ⟨v, hv', rfl⟩, rfl⟩
      · exact ⟨R₀, hσ, w, by simpa [acdIDHopStep, hg] using hw, rfl⟩
    | deliver p h ad c => exact ⟨R₀, hσ, w, by simpa [acdIDHopStep] using hw, rfl⟩
  · exact ⟨R₀, hσ, w, by simpa [hs] using hw, rfl⟩

/-- The invariant of the states of the hop games: the invariant `ACDInv` of the base state at
some root KDF, and the invariant `ACDIDInv` of the joined state. -/
structure ACDIDHopInv (C : CKADef Sc Msg Key) (J : Sc → Sc → Prop) (G : PRGDef Sa (Kt × Sa))
    (s : ACDIDHopSt Sc Msg RK Sa W Ct Kt) : Prop where
  /-- The invariant of the base state at some root KDF. -/
  base : ∃ R : PRGDef (RK × Key) (RK × Sa), ACDInv C R J s.1.1.1
  /-- The invariant of the joined state. -/
  book : ACDIDInv G (acdIDEmb s).1

omit [SampleableType Kt] in
/-- The truncated oracle with decryption from the log over `acdIDSM` keeps the invariant
`ACDIDInv`. -/
theorem acdID_inv_trunc (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg) Kt) (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W)
    (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    (s : (SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) ×
      SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) × Bool) (hs : ACDIDInv G s.1)
    (d : SMIDQuery W (ACDHdr Msg) Ct) (w)
    (hw : w ∈ (smIDTruncOracle (acdIDSM C R G D dec enc maxSkip maxStored) ΔFS ΔPCS t false
      (fun _ => true) k s d).support) : ACDIDInv G w.2.1 := by
  simp only [smIDTruncOracle] at hw
  split at hw
  · simp only [smIDFlagOracle, PMF.support_map, Set.mem_image] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    exact acdID_inv_step C R G D dec enc maxSkip maxStored ΔFS ΔPCS t false s.1 d hs y hy
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact hs

set_option linter.unusedFintypeInType false in
omit [SampleableType Kt] in
/-- **The hop oracle at any root step keeps the invariant of the hop states**, when the CKA is
correct along `J`. -/
theorem acdIDHopOracle_hopInv (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg) Kt) (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W)
    (maxSkip maxStored : ℕ) {J : Sc → Sc → Prop} (hJ : CKACorrect C J) (ΔFS ΔPCS t k : ℕ)
    (root : RK → Key → PMF (RK × Sa)) (s : ACDIDHopSt Sc Msg RK Sa W Ct Kt)
    (hs : ACDIDHopInv C J G s) (d : SMIDQuery W (ACDHdr Msg) Ct) :
    ∀ z ∈ (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k root s d).support,
      ACDIDHopInv C J G z.2 := by
  intro z hz
  obtain ⟨R₀, h₀⟩ := hs.base
  obtain ⟨R', hR', hz'⟩ := acdIDHopOracle_support_real C R R₀ G D dec enc maxSkip maxStored
    ΔFS ΔPCS t k root s h₀ d z hz
  refine ⟨⟨R', acdIDHop_acdInv C R' G D dec enc maxSkip maxStored hJ ΔFS ΔPCS t k s hR' d z
    hz'⟩, ?_⟩
  have hm : Prod.map id acdIDEmb z ∈ ((smIDTruncOracle (acdIDSM C R' G D dec enc maxSkip
      maxStored) ΔFS ΔPCS t false (fun _ => true) k (acdIDEmb s) d).map
        (acdIDCut ΔFS ΔPCS k)).support := by
    rw [← acdIDHop_step C R' G D dec enc maxSkip maxStored J ΔFS ΔPCS t k s hR' d,
      PMF.support_map]
    exact ⟨z, hz', rfl⟩
  rw [PMF.support_map] at hm
  obtain ⟨w, hw, hwz⟩ := hm
  have h2 : (acdIDCut ΔFS ΔPCS k w).2 = w.2 := by
    unfold acdIDCut
    split <;> rfl
  have he : acdIDEmb z.2 = w.2 := by
    rw [← h2, hwz]
    rfl
  rw [he]
  exact acdID_inv_trunc C R' G D dec enc maxSkip maxStored ΔFS ΔPCS t k _ hs.book d w hw

omit [Fintype RK] [Nonempty RK] [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct]
  [SampleableType W] [SampleableType Ct] in
omit [SampleableType Kt] in
/-- The invariant of the hop states holds at the initial state, for initial CKA states related
by `J`. -/
theorem acdIDHopInv_init (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (Kt × Sa)) {J : Sc → Sc → Prop} (i : Msg × Sc × Sc) (hi : J i.2.1 i.2.2)
    (rk : RK) :
    ACDIDHopInv C J G ((((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)), false) :
      ACDIDHopSt Sc Msg RK Sa W Ct Kt) := by
  refine ⟨⟨R, acdInv_smInit C R i hi rk⟩, ?_⟩
  have he : (acdIDEmb ((((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)), false) :
      ACDIDHopSt Sc Msg RK Sa W Ct Kt)).1 =
      (SMSchemeSt.init ((i.1, 0), (ACDIDSt.embed ⟨i.2.1, rk, none, none⟩ : ACDIDSt Sc RK Sa Msg Kt),
        (ACDIDSt.embed ⟨i.2.2, rk, none, none⟩ : ACDIDSt Sc RK Sa Msg Kt)),
        SMIDAux.init (i.1, 0)) := by
    simp only [acdIDEmb, Prod.mk.injEq, and_true]
    refine SMSchemeSt.ext_of (funext fun q => ?_) rfl rfl rfl
    cases q <;> rfl
  rw [he]
  exact acdID_inv_init G (i.1, ⟨i.2.1, rk, none, none⟩, ⟨i.2.2, rk, none, none⟩)

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] in
omit [SampleableType Kt] in
/-- **Under the restricted corruption gate the store holds keys of the receiving epoch only.**
On a state of the invariant `ACDIDInv` where `SMIDAux.storeClear` admits a corruption of `p`,
every key stored by `p` has the receiving epoch of `p`. -/
theorem ACDIDInv.store_epoch_of_storeClear {G : PRGDef Sa (Kt × Sa)}
    {s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct}
    (hs : ACDIDInv G s) (p : CKAParty)
    (hc : s.2.storeClear (ckaShadow s.1.ck) p = true) :
    ∀ el ∈ (s.1.ck.st p).store, el.1 = smRecvEpoch (ckaShadow s.1.ck) p := by
  intro el hel
  obtain ⟨l, hl, hq, ht⟩ := ((hs.party p).sound el hel).1
  have hc' := List.all_eq_true.1 hc l hl
  have her := (hs.party p).er
  simp only [acdQual, acdTag, ACDIDSt.tag, Prod.mk.injEq] at hq ht
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hc'
  rw [her] at hq
  grind

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] in
omit [SampleableType Kt] in
/-- **An answered corruption with the epoch `k` outside its window finds no key of the epoch
`k` in the store.** With `2 ≤ ΔFS` and `1 ≤ ΔPCS`, on a state of the invariant `ACDIDInv` where
`SMIDAux.storeClear` admits a corruption of `p` that leaves the epoch `k` safe, party `p` stores
no key of the epoch `k`. -/
theorem ACDIDInv.store_ne_of_allowCorr {G : PRGDef Sa (Kt × Sa)} {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS)
    (hPCS : 1 ≤ ΔPCS) (k : ℕ)
    {s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct}
    (hs : ACDIDInv G s) (p : CKAParty)
    (hc : s.2.storeClear (ckaShadow s.1.ck) p = true)
    (hk : ckaAllowCorr ΔFS ΔPCS k (ckaShadow s.1.ck) p = true) :
    ∀ el ∈ (s.1.ck.st p).store, el.1 ≠ k := by
  intro el hel hek
  have he := hs.store_epoch_of_storeClear p hc el hel
  have hw : ckaAllowCorr ΔFS ΔPCS k (ckaShadow s.1.ck) p = false := by
    refine not_allowCorr_of_window hFS hPCS ?_ ?_ <;>
      simp only [smRecvEpoch] at he <;> split at he <;> omega
  rw [hw] at hk
  exact absurd hk (by decide)

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] [DecidableEq W] [DecidableEq Ct] in
omit [SampleableType Kt] in
/-- **A successful key lookup is at an undelivered position.** On a state of the invariant
`ACDIDInv`, when the key lookup of party `p` at the header `h` succeeds, the public value of
`h` resolves to an epoch `e` of the game, and every logged message at the epoch `e` and the
position of `h` is undelivered. -/
theorem ACDIDInv.undelivered_of_rkey {G : PRGDef Sa (Kt × Sa)} (maxSkip maxStored : ℕ)
    {s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct}
    (hs : ACDIDInv G s) (p : CKAParty) (h : ACDHdr Msg)
    (y : ACDIDSt Sc RK Sa Msg Kt × Kt)
    (hy : acdIDRKey G maxSkip maxStored (s.1.ck.st p) h = some y) :
    ∃ e, s.2.epochOf (ckaShadow s.1.ck) p h.1 = some e ∧
      ∀ l ∈ s.2.log, acdTag l = (e, h.2) → l.delivered = false := by
  have hp := hs.party p
  unfold acdIDRKey at hy
  split at hy
  · simp at hy
  · rename_i q hq
    rw [hp.rpubs] at hq
    obtain ⟨he, -⟩ := acdRPubs_find_epochOf s.2 (ckaShadow s.1.ck) p h.1 hs.pubs_sorted q hq
    refine ⟨q.1, he, fun l hl ht => ?_⟩
    simp only [acdTag, Prod.mk.injEq] at ht
    split_ifs at hy with h1 h2
    · by_contra hd
      have := acdNr_gt s.2.log _ l hl (by simpa using hd) (ht.1.trans h1.1)
      rw [← hp.nr] at this
      omega
    · obtain ⟨el, hel, -⟩ := Option.map_eq_some_iff.1 hy
      have hmem := List.mem_of_find?_eq_some hel
      have htag : ACDIDSt.tag el = (q.1, h.2) := by
        simpa using List.find?_some hel
      obtain ⟨l', hl', hq', ht'⟩ := (hp.sound el hmem).1
      have hll : l = l' :=
        List.inj_on_of_nodup_map hs.log_nodup hl hl' (by rw [ht', htag]; simp [acdTag, ht])
      subst hll
      simp only [acdQual, Bool.and_eq_true, Bool.not_eq_true'] at hq'
      exact hq'.1.1.1

variable [Fintype Sa] [Nonempty Sa]

omit [Fintype RK] [Nonempty RK] [Inhabited Msg] in
omit [SampleableType Kt] in
/-- **Eager sampling of the root output at the epoch `k`** in the hop oracle: the run with a
uniform root output at the epoch `k` is the run with the root output drawn in advance. -/
theorem acdIDHop_run_eager_unif (C : CKADef Sc Msg Key) [CKACoins C Rand] [Fintype RK]
    [Nonempty RK] (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg) Kt) (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W)
    (maxSkip maxStored ΔFS ΔPCS t k : ℕ) {α : Type}
    (A : OracleAdv (SMIDQuery W (ACDHdr Msg) Ct) (ACDIDAns Sc Msg RK Sa W Ct Kt) α)
    (s : ACDIDHopSt Sc Msg RK Sa W Ct Kt) :
    OracleAdv.run (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k unifRoot) A s =
      (PMF.uniformFintype (RK × Sa)).bind fun y =>
        OracleAdv.run (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k
          (constRoot (Key := Key) y)) A s := by
  refine OracleAdv.run_eq_bind_eager _ _ (PMF.uniformFintype (RK × Sa)) (acdIDRootCrit ΔFS ΔPCS k)
    ?_ ?_ (fun s => smOpened k s.1.1.1) ?_ ?_ ?_ A s
  · intro s d hc
    cases d with
    | sm q =>
      simp only [acdIDRootCrit, Bool.and_eq_true] at hc
      obtain ⟨⟨hs, hg⟩, hq⟩ := hc
      cases q with
      | ratchet p =>
        have hroot : ∀ rk I, (unifRoot rk I : PMF (RK × Sa)) =
            (PMF.uniformFintype (RK × Sa)).bind fun v => constRoot (Key := Key) v rk I :=
          fun _ _ => (PMF.bind_pure _).symm
        simp only [smCrit, Bool.and_eq_true] at hq
        have h : smOracleOfAt C R G (aeadComapAD D dec) ΔFS ΔPCS t k false unifRoot
            s.1.1.1 (acdIDBaseQuery enc s.1.1.2 (.ratchet p)) =
            (PMF.uniformFintype (RK × Sa)).bind fun v =>
              smOracleOfAt C R G (aeadComapAD D dec) ΔFS ΔPCS t k false (constRoot v)
                s.1.1.1 (acdIDBaseQuery enc s.1.1.2 (.ratchet p)) := by
          simp only [acdIDBaseQuery, SMQuery.mapMsg, smOracleOfAt, smOracleOf, hq.1, hq.2,
            ite_true, hroot, PMF.bind_bind]
          exact PMF.bind_comm _ _ _
        simp only [acdIDHopOracle, hs, ite_true,
          acdIDHopStep_sm C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k _ s _ hg, h, PMF.map_bind]
      | _ => simp [smCrit] at hq
    | deliver p h ad c => simp [acdIDRootCrit] at hc
  · intro v s d hc
    exact acdIDHopOracle_root_congr C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k _ _ s d hc
  · intro v s d hc x hx
    exact acdIDHopOracle_opened_of_crit C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k _ s d hc
      x hx
  · intro s d hs x hx
    exact acdIDHopOracle_opened C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k _ s d hs x hx
  · intro s d hs
    cases d with
    | sm q => simp [acdIDRootCrit, smCrit_of_opened k s.1.1.1 hs q]
    | deliver p h ad c => rfl

end HopInv

/-! ## The bookkeeping with the chain of the epoch `k` held elsewhere -/

section FixKeys

variable {Msg Sa W Kt : Type}

/-- A stored key of the epoch `k` replaced by the key of the chain `sa` at its position. -/
def acdIDFixEl (G : PRGDef Sa (Kt × Sa)) (k : ℕ) (sa : Sa) (el : ℕ × ℕ × Kt) : ℕ × ℕ × Kt :=
  if el.1 = k then (el.1, el.2.1, chainKey G sa el.2.1) else el

/-- The bookkeeping of a party with the trivial base state. -/
def acdIDNormSt (x : ACDIDSt Unit Unit Sa Msg Kt) : ACDIDSt Unit Unit Sa Msg Kt :=
  ⟨⟨(), (), none, none⟩, x.pubS, x.ns, x.ep, x.er, x.nr, x.rpubs, x.store⟩

/-- The bookkeeping of a party with the trivial base state and with the stored keys of the epoch
`k` those of the chain `sa`. -/
def acdIDFixSt (G : PRGDef Sa (Kt × Sa)) (k : ℕ) (sa : Sa) (x : ACDIDSt Unit Unit Sa Msg Kt) :
    ACDIDSt Unit Unit Sa Msg Kt :=
  ⟨⟨(), (), none, none⟩, x.pubS, x.ns, x.ep, x.er, x.nr, x.rpubs,
    x.store.map (acdIDFixEl G k sa)⟩

/-- `acdIDNormSt` at every party. -/
def acdIDNormX (X : ACDIDX Sa Msg Kt) : ACDIDX Sa Msg Kt := (fun p => acdIDNormSt (X.1 p), X.2)

/-- `acdIDFixSt` at every party. -/
def acdIDFixX (G : PRGDef Sa (Kt × Sa)) (k : ℕ) (sa : Sa) (X : ACDIDX Sa Msg Kt) :
    ACDIDX Sa Msg Kt :=
  (fun p => acdIDFixSt G k sa (X.1 p), X.2)

/-- `acdIDFixEl` keeps the epoch and the position. -/
theorem acdIDFixEl_tag (G : PRGDef Sa (Kt × Sa)) (k : ℕ) (sa : Sa) (el : ℕ × ℕ × Kt) :
    (acdIDFixEl G k sa el).1 = el.1 ∧ ACDIDSt.tag (acdIDFixEl G k sa el) = ACDIDSt.tag el := by
  unfold acdIDFixEl ACDIDSt.tag
  split <;> simp

/-- `acdIDFixEl` on the skipped keys of a chain. -/
theorem acdIDFixEl_skipKeys (G : PRGDef Sa (Kt × Sa)) (k : ℕ) (sa sa' : Sa) (e a n : ℕ) :
    (ACDIDSt.skipKeys G e sa' a n).map (acdIDFixEl G k sa) =
      if e = k then ACDIDSt.skipKeys G e sa a n else ACDIDSt.skipKeys G e sa' a n := by
  unfold ACDIDSt.skipKeys
  split_ifs with h <;> simp [List.map_map, Function.comp_def, acdIDFixEl, h]

/-- `acdIDFixEl` keeps a store without keys of the epoch `k`. -/
theorem acdIDFixEl_map_of_ne (G : PRGDef Sa (Kt × Sa)) (k : ℕ) (sa : Sa) (L : List (ℕ × ℕ × Kt))
    (h : ∀ el ∈ L, el.1 ≠ k) : L.map (acdIDFixEl G k sa) = L :=
  (List.map_congr_left fun el hel => by simp [acdIDFixEl, h el hel]).trans (List.map_id L)

/-- The answer of a party whose store holds no key of the epoch `k` does not see `acdIDFixSt`. -/
theorem acdIDAns_fixSt {Sc RK Ct : Type} (G : PRGDef Sa (Kt × Sa)) (k : ℕ) (sa : Sa)
    (x : ACDIDSt Unit Unit Sa Msg Kt) (hx : ∀ el ∈ x.store, el.1 ≠ k)
    (a : SMAns Sc Msg RK Sa Ct) : acdIDAns (acdIDFixSt G k sa x) a = acdIDAns x a := by
  have hs : x.store.map (acdIDFixEl G k sa) = x.store := acdIDFixEl_map_of_ne G k sa _ hx
  cases a with
  | state γ rk snd rcv =>
    simp only [acdIDAns, acdIDFixSt, hs]
    rfl
  | _ => rfl

/-- The answer of a party other than a corruption answer does not see `acdIDFixSt`. -/
theorem acdIDAns_fixSt_of_ne {Sc RK Ct : Type} (G : PRGDef Sa (Kt × Sa)) (k : ℕ) (sa : Sa)
    (x : ACDIDSt Unit Unit Sa Msg Kt) (a : SMAns Sc Msg RK Sa Ct)
    (ha : ∀ γ rk snd rcv, a ≠ .state γ rk snd rcv) :
    acdIDAns (acdIDFixSt G k sa x) a = acdIDAns x a := by
  cases a with
  | state γ rk snd rcv => exact absurd rfl (ha γ rk snd rcv)
  | _ => rfl

/-- The answer of a party does not see `acdIDNormSt`. -/
theorem acdIDAns_normSt {Sc RK Ct : Type} (x : ACDIDSt Unit Unit Sa Msg Kt)
    (a : SMAns Sc Msg RK Sa Ct) : acdIDAns (acdIDNormSt x) a = acdIDAns x a := by
  cases a <;> rfl

/-- The receive of a party with the chain `sa` of the epoch `k` in the bookkeeping. -/
theorem acdIDFixSt_recvX (G : PRGDef Sa (Kt × Sa)) (k : ℕ) (sa : Sa)
    (x : ACDIDSt Unit Unit Sa Msg Kt) (rS rR : Option Sa)
    (hR : 1 ≤ x.er → (x.er = k → rR = some sa ∧ rS.isSome) ∧ (x.er ≠ k → rS = rR))
    (T : Msg × ℕ) :
    acdIDFixSt G k sa (x.recvX G rS T) = acdIDNormSt ((acdIDFixSt G k sa x).recvX G rR T) := by
  simp only [ACDIDSt.recvX, acdIDFixSt, acdIDNormSt, List.map_append, ACDIDSt.mk.injEq,
    true_and]
  by_cases h0 : x.er = 0
  · simp [h0]
  · obtain ⟨h1, h2⟩ := hR (by omega)
    by_cases hk : x.er = k
    · obtain ⟨hr, hs⟩ := h1 hk
      obtain ⟨sa', hsa'⟩ := Option.isSome_iff_exists.1 hs
      subst hk
      simp [h0, hr, hsa', acdIDFixEl_skipKeys]
    · rw [h2 hk]
      cases rR <;> simp [h0, acdIDFixEl_skipKeys, hk]

/-- **The bookkeeping update with the chain of the epoch `k` held elsewhere.** With receiving
chains `rS` that agree with `rR` outside the receiving epoch `k`, and `rR` the chain `sa` at the
receiving epoch `k`, the update of the bookkeeping commutes with `acdIDFixX`. -/
theorem acdIDXUpd_fixX {Sc RK Ct : Type} (G : PRGDef Sa (Kt × Sa)) (k : ℕ) (sa : Sa)
    (rS rR : CKAParty → Option Sa) (sh : CKAGameSt Unit Unit) (T₀ : Msg) (X : ACDIDX Sa Msg Kt)
    (hR : ∀ p, 1 ≤ (X.1 p).er → ((X.1 p).er = k → rR p = some sa ∧ (rS p).isSome) ∧
      ((X.1 p).er ≠ k → rS p = rR p))
    (q : SMQuery W) (a : SMAns Sc Msg RK Sa Ct) :
    acdIDFixX G k sa (acdIDXUpd G rS sh T₀ X q a) =
      acdIDNormX (acdIDXUpd G rR sh T₀ (acdIDFixX G k sa X) q a) := by
  cases q with
  | ratchet p =>
    cases a <;> simp only [acdIDXUpd, acdIDFixX, acdIDNormX] <;>
      refine Prod.ext (funext fun p' => ?_) rfl <;>
      by_cases hp : p' = p <;> simp [hp, acdIDFixSt, acdIDNormSt]
  | recv p =>
    simp only [acdIDXUpd]
    split_ifs
    · refine Prod.ext (funext fun p' => ?_) rfl
      by_cases hp : p' = p
      · subst hp
        simpa [acdIDFixX, acdIDNormX] using acdIDFixSt_recvX G k sa (X.1 p') (rS p') (rR p')
          (hR p') (T₀, X.2)
      · simp [acdIDFixX, acdIDNormX, hp, acdIDFixSt, acdIDNormSt]
    · refine Prod.ext (funext fun p' => ?_) rfl
      simp [acdIDFixX, acdIDNormX, acdIDFixSt, acdIDNormSt]
  | send p m =>
    cases a <;> simp only [acdIDXUpd, acdIDFixX, acdIDNormX] <;>
      refine Prod.ext (funext fun p' => ?_) rfl <;>
      by_cases hp : p' = p <;> simp [hp, acdIDFixSt, acdIDNormSt]
  | chall p m =>
    cases a <;> simp only [acdIDXUpd, acdIDFixX, acdIDNormX] <;>
      refine Prod.ext (funext fun p' => ?_) rfl <;>
      by_cases hp : p' = p <;> simp [hp, acdIDFixSt, acdIDNormSt]
  | corrupt p =>
    simp only [acdIDXUpd, acdIDFixX, acdIDNormX]
    refine Prod.ext (funext fun p' => ?_) rfl
    simp [acdIDFixSt, acdIDNormSt]

end FixKeys

/-! ## Deliveries with the chain of the epoch `k` held elsewhere -/

section FixDeliver

variable {Msg Sa W Ct Kt : Type} [SampleableType W] [SampleableType Kt]
  [DecidableEq Msg] [DecidableEq W]
  [DecidableEq Ct]

omit [SampleableType W] [DecidableEq W] [DecidableEq Ct] in
omit [SampleableType Kt] in
/-- **The key lookup with the chain of the epoch `k` held elsewhere.** The lookup at the state
`acdIDFixSt` with the receiving chain `rR` and at the state with the receiving chain `rS` agree
up to `acdIDNormSt` and `acdIDFixSt`; a lookup of the epoch `k` returns the key of the chain
`sa`. -/
theorem acdIDRKey_fix (G : PRGDef Sa (Kt × Sa)) (maxSkip maxStored k : ℕ) (sa : Sa)
    (x : ACDIDSt Unit Unit Sa Msg Kt) (rS rR : Option Sa)
    (hR : 1 ≤ x.er → (x.er = k → rR = some sa ∧ rS.isSome) ∧ (x.er ≠ k → rS = rR))
    (hpub : ∀ q ∈ x.rpubs, 1 ≤ q.1) (h : ACDHdr Msg) :
    (acdIDRKey G maxSkip maxStored ((acdIDFixSt G k sa x).withBase ⟨(), (), none, rR⟩) h).map
        (fun y => acdIDNormSt y.1) =
      (acdIDRKey G maxSkip maxStored (x.withBase ⟨(), (), none, rS⟩) h).map
        (fun y => acdIDFixSt G k sa y.1) ∧
    ∀ y, acdIDRKey G maxSkip maxStored ((acdIDFixSt G k sa x).withBase ⟨(), (), none, rR⟩) h =
        some y → ∀ q, x.rpubs.find? (fun q => decide (q.2 = h.1)) = some q → q.1 = k →
          y.2 = chainKey G sa h.2 := by
  have htag : ∀ el, ACDIDSt.tag (acdIDFixEl G k sa el) = ACDIDSt.tag el :=
    fun el => (acdIDFixEl_tag G k sa el).2
  constructor
  · simp only [acdIDRKey, ACDIDSt.withBase, acdIDFixSt]
    cases hf : x.rpubs.find? (fun q => decide (q.2 = h.1)) with
    | none => rfl
    | some q =>
      have hq1 := hpub q (List.mem_of_find?_eq_some hf)
      by_cases hc : q.1 = x.er ∧ x.nr ≤ h.2
      · simp only [hc, and_self, ite_true, List.length_map]
        by_cases hc2 : h.2 - x.nr ≤ maxSkip ∧ x.store.length + (h.2 - x.nr) ≤ maxStored
        · have hc3 : h.2 ≤ maxSkip + x.nr := by omega
          obtain ⟨h1, h2⟩ := hR (hc.1 ▸ hq1)
          by_cases hk : x.er = k
          · obtain ⟨hr, hs⟩ := h1 hk
            obtain ⟨sa', hsa'⟩ := Option.isSome_iff_exists.1 hs
            subst hk
            simp [hr, hsa', acdIDNormSt, acdIDFixEl_skipKeys, hc2]
          · rw [h2 hk]
            cases rR <;> simp [acdIDNormSt, acdIDFixEl_skipKeys, hk, hc2]
        · have hc3 : ¬(h.2 ≤ maxSkip + x.nr ∧ x.store.length + (h.2 - x.nr) ≤ maxStored) := by
            omega
          simp [hc3]
      · simp only [hc, ite_false, List.find?_map, Option.map_map]
        simp [Function.comp_def, htag, List.filter_map, acdIDNormSt]
  · intro y hy q hq hqk
    unfold acdIDRKey at hy
    split at hy
    · simp at hy
    · rename_i q' hq'
      obtain rfl : q = q' := (Option.some.inj (hq'.symm.trans hq)).symm
      have hq1 := hpub q (List.mem_of_find?_eq_some hq)
      split_ifs at hy with hc hc2
      · simp only [ACDIDSt.withBase, acdIDFixSt] at hc
        obtain ⟨h1, -⟩ := hR (hc.1 ▸ hq1)
        have hr := (h1 (hc.1 ▸ hqk)).1
        simp only [ACDIDSt.withBase, hr, Option.map_some, Option.some.injEq] at hy
        rw [← hy]
      obtain ⟨el, hel, rfl⟩ := Option.map_eq_some_iff.1 hy
      have hmem := List.find?_some hel
      obtain ⟨el0, -, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hel)
      simp only [beq_iff_eq, ACDIDSt.tag, Prod.mk.injEq] at hmem
      grind [acdIDFixEl, hmem.1, hmem.2]

/-- The delivery to party `p` at the header `h` reaches the epoch `k` with a successful key
lookup. -/
def acdIDDlvHit (G : PRGDef Sa (Kt × Sa)) (maxSkip maxStored ΔFS ΔPCS k : ℕ)
    (rcv : CKAParty → Option Sa) (sh : CKAGameSt Unit Unit)
    (X : CKAParty → ACDIDSt Unit Unit Sa Msg Kt) (x : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (p : CKAParty) (h : ACDHdr Msg) : Bool :=
  match x.epochOf sh p h.1 with
  | none => false
  | some e => decide (e = k) && x.safe ΔFS ΔPCS p e h.2 &&
      (acdIDRKey G maxSkip maxStored (acdIDRcvSt rcv X p) h).isSome

omit [SampleableType Kt] in
/-- **The delivery with the chain of the epoch `k` held elsewhere.** With the hypotheses of
`acdIDRKey_fix` at party `p`, the delivery at the bookkeeping `acdIDFixSt` with the receiving
chains `rR` and at the bookkeeping with the receiving chains `rS` have the same answer, the same
bookkeeping of the game, the same success at the epoch `k`, and party states that agree up to
`acdIDNormSt` and `acdIDFixSt`. -/
theorem acdIDDeliver_fix (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg) Kt)
    (maxSkip maxStored ΔFS ΔPCS k : ℕ) (sa : Sa) (rS rR : CKAParty → Option Sa)
    (sh : CKAGameSt Unit Unit) (X : CKAParty → ACDIDSt Unit Unit Sa Msg Kt)
    (x : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) (p : CKAParty) (h : ACDHdr Msg) (ad : W) (c : Ct)
    (hR : 1 ≤ (X p).er → ((X p).er = k → rR p = some sa ∧ (rS p).isSome) ∧
      ((X p).er ≠ k → rS p = rR p))
    (hpub : ∀ q ∈ (X p).rpubs, 1 ≤ q.1) :
    (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k rR sh (fun q => acdIDFixSt G k sa (X q)) x p
        h ad c).1 = (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k rS sh X x p h ad c).1 ∧
    (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k rR sh (fun q => acdIDFixSt G k sa (X q)) x p
        h ad c).2.1.2 = (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k rS sh X x p h ad c).2.1.2 ∧
    (fun q => acdIDNormSt ((acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k rR sh
        (fun q => acdIDFixSt G k sa (X q)) x p h ad c).2.1.1 q)) =
      (fun q => acdIDFixSt G k sa
        ((acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k rS sh X x p h ad c).2.1.1 q)) ∧
    acdIDDlvHit G maxSkip maxStored ΔFS ΔPCS k rR sh (fun q => acdIDFixSt G k sa (X q)) x p h =
      acdIDDlvHit G maxSkip maxStored ΔFS ΔPCS k rS sh X x p h := by
  have hk := (acdIDRKey_fix G maxSkip maxStored k sa (X p) (rS p) (rR p) hR hpub h).1
  have hrs : acdIDRcvSt rR (fun q => acdIDFixSt G k sa (X q)) p =
      (acdIDFixSt G k sa (X p)).withBase ⟨(), (), none, rR p⟩ := rfl
  have hss : acdIDRcvSt rS X p = (X p).withBase ⟨(), (), none, rS p⟩ := rfl
  have hfix : ∀ q, acdIDNormSt (acdIDFixSt G k sa (X q)) = acdIDFixSt G k sa (X q) := fun _ => rfl
  simp only [acdIDDeliver, acdIDDlvHit, hrs, hss]
  cases he : x.epochOf sh p h.1 with
  | none => simp [hfix]
  | some e =>
    simp only
    by_cases hsafe : x.safe ΔFS ΔPCS p e h.2 = true
    · simp only [hsafe, ite_true, Bool.and_true]
      cases hR' : acdIDRKey G maxSkip maxStored ((acdIDFixSt G k sa (X p)).withBase
          ⟨(), (), none, rR p⟩) h with
      | none =>
        rw [hR'] at hk
        cases hS' : acdIDRKey G maxSkip maxStored ((X p).withBase ⟨(), (), none, rS p⟩) h with
        | none => simp [hfix]
        | some y => rw [hS'] at hk; simp at hk
      | some y =>
        rw [hR'] at hk
        cases hS' : acdIDRKey G maxSkip maxStored ((X p).withBase ⟨(), (), none, rS p⟩) h with
        | none => rw [hS'] at hk; simp at hk
        | some y' =>
          rw [hS'] at hk
          simp only [Option.map_some, Option.some.injEq] at hk
          refine ⟨rfl, ?_, ?_, rfl⟩
          · cases x.findEntry e h ad c <;> rfl
          · cases x.findEntry e h ad c
            · simp [hfix]
            · funext q
              by_cases hq : q = p
              · subst hq
                simp [hk]
              · simp [hq, hfix]
    · simp [hsafe, hfix]

omit [SampleableType Kt] in
/-- **The flag of a forgery with the chain of the epoch `k` held elsewhere.** With the
hypotheses of `acdIDDeliver_fix`, and when the public values of party `p` resolve to the epochs
of the game, the flag of the delivery at the bookkeeping `acdIDFixSt` with the receiving chains
`rR` is raised exactly at a successful delivery into the epoch `k` whose decryption under the key
of the chain `sa` differs from the answer from the log. -/
theorem acdIDDeliver_fix_flag (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg) Kt)
    (maxSkip maxStored ΔFS ΔPCS k : ℕ) (sa : Sa) (rS rR : CKAParty → Option Sa)
    (sh : CKAGameSt Unit Unit) (X : CKAParty → ACDIDSt Unit Unit Sa Msg Kt)
    (x : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) (p : CKAParty) (h : ACDHdr Msg) (ad : W) (c : Ct)
    (hR : 1 ≤ (X p).er → ((X p).er = k → rR p = some sa ∧ (rS p).isSome) ∧
      ((X p).er ≠ k → rS p = rR p))
    (hpub : ∀ q ∈ (X p).rpubs, 1 ≤ q.1)
    (hep : ∀ q, (X p).rpubs.find? (fun q => decide (q.2 = h.1)) = some q →
      x.epochOf sh p h.1 = some q.1) :
    (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k rR sh (fun q => acdIDFixSt G k sa (X q)) x p
        h ad c).2.2 =
      (acdIDDlvHit G maxSkip maxStored ΔFS ΔPCS k rS sh X x p h &&
        (D.decrypt (chainKey G sa h.2) c (ad, h) !=
          (x.findEntry k h ad c).map SMIDLogEntry.pt)) := by
  rw [← (acdIDDeliver_fix G D maxSkip maxStored ΔFS ΔPCS k sa rS rR sh X x p h ad c hR
    hpub).2.2.2]
  have hkey := (acdIDRKey_fix G maxSkip maxStored k sa (X p) (rS p) (rR p) hR hpub h).2
  have hrs : acdIDRcvSt rR (fun q => acdIDFixSt G k sa (X q)) p =
      (acdIDFixSt G k sa (X p)).withBase ⟨(), (), none, rR p⟩ := rfl
  simp only [acdIDDeliver, acdIDDlvHit, hrs]
  cases he : x.epochOf sh p h.1 with
  | none => rfl
  | some e =>
    simp only
    by_cases hsafe : x.safe ΔFS ΔPCS p e h.2 = true
    · simp only [hsafe, ite_true, Bool.and_true]
      cases hR' : acdIDRKey G maxSkip maxStored ((acdIDFixSt G k sa (X p)).withBase
          ⟨(), (), none, rR p⟩) h with
      | none => simp
      | some y =>
        by_cases hek : e = k
        · subst hek
          cases hf : (X p).rpubs.find? (fun q => decide (q.2 = h.1)) with
          | none =>
            exfalso
            simp [acdIDRKey, ACDIDSt.withBase, acdIDFixSt, hf] at hR'
          | some q =>
            have hq : q.1 = e := Option.some.inj ((hep q hf).symm.trans he)
            simp [hkey y hR' q hf hq]
        · simp [hek]
    · simp [hsafe]

end FixDeliver

/-! ## The bookkeeping with the trivial base states -/

section NormHop

variable {Sc Msg Key Rand RK Sa W Ct Kt : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [SampleableType Kt] [Fintype RK] [Nonempty RK] [Inhabited Msg]
  [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct]

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] [Inhabited Msg] [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] in
omit [SampleableType Kt] in
/-- The update of the bookkeeping does not see the base states. -/
theorem acdIDXUpd_normX (G : PRGDef Sa (Kt × Sa)) (rcv : CKAParty → Option Sa)
    (sh : CKAGameSt Unit Unit) (T₀ : Msg) (X : ACDIDX Sa Msg Kt) (q : SMQuery W)
    (a : SMAns Sc Msg RK Sa Ct) :
    acdIDNormX (acdIDXUpd G rcv sh T₀ (acdIDNormX X) q a) =
      acdIDNormX (acdIDXUpd G rcv sh T₀ X q a) := by
  cases q with
  | recv p =>
    simp only [acdIDXUpd]
    split_ifs
    · refine Prod.ext (funext fun p' => ?_) rfl
      by_cases hp : p' = p
      · subst hp
        simp only [acdIDNormX, Function.update_self]
        rfl
      · simp [acdIDNormX, hp, acdIDNormSt]
    · rfl
  | ratchet p =>
    cases a <;> simp only [acdIDXUpd, acdIDNormX] <;>
      refine Prod.ext (funext fun p' => ?_) rfl <;>
      by_cases hp : p' = p <;> simp [hp, acdIDNormSt]
  | send p m =>
    cases a <;> simp only [acdIDXUpd, acdIDNormX] <;>
      refine Prod.ext (funext fun p' => ?_) rfl <;>
      by_cases hp : p' = p <;> simp [hp, acdIDNormSt]
  | chall p m =>
    cases a <;> simp only [acdIDXUpd, acdIDNormX] <;>
      refine Prod.ext (funext fun p' => ?_) rfl <;>
      by_cases hp : p' = p <;> simp [hp, acdIDNormSt]
  | corrupt p => rfl

omit [Fintype Rand] [Nonempty Rand] [SampleableType Ct] [Fintype RK] [Nonempty RK]
  [Inhabited Msg] in
omit [SampleableType Kt] in
/-- The delivery does not see the base states of the bookkeeping. -/
theorem acdIDDeliver_normX (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg) Kt)
    (maxSkip maxStored ΔFS ΔPCS k : ℕ) (rcv : CKAParty → Option Sa) (sh : CKAGameSt Unit Unit)
    (X : CKAParty → ACDIDSt Unit Unit Sa Msg Kt) (x : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (p : CKAParty) (h : ACDHdr Msg) (ad : W) (c : Ct) :
    (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k rcv sh (fun q => acdIDNormSt (X q)) x p h ad
        c).1 = (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k rcv sh X x p h ad c).1 ∧
    (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k rcv sh (fun q => acdIDNormSt (X q)) x p h ad
        c).2.1.2 = (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k rcv sh X x p h ad c).2.1.2 ∧
    (fun q => acdIDNormSt ((acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k rcv sh
        (fun q => acdIDNormSt (X q)) x p h ad c).2.1.1 q)) =
      (fun q => acdIDNormSt
        ((acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k rcv sh X x p h ad c).2.1.1 q)) ∧
    (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k rcv sh (fun q => acdIDNormSt (X q)) x p h ad
        c).2.2 = (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k rcv sh X x p h ad c).2.2 := by
  have hr : acdIDRcvSt rcv (fun q => acdIDNormSt (X q)) p = acdIDRcvSt rcv X p := rfl
  simp only [acdIDDeliver, hr]
  cases x.epochOf sh p h.1 with
  | none => exact ⟨rfl, rfl, rfl, rfl⟩
  | some e =>
    simp only
    split_ifs
    · cases acdIDRKey G maxSkip maxStored (acdIDRcvSt rcv X p) h with
      | none => exact ⟨rfl, rfl, rfl, rfl⟩
      | some y =>
        cases x.findEntry e h ad c with
        | none => exact ⟨rfl, rfl, rfl, rfl⟩
        | some l =>
          refine ⟨rfl, rfl, funext fun q => ?_, rfl⟩
          by_cases hq : q = p <;> simp [hq, acdIDNormSt]
    · exact ⟨rfl, rfl, rfl, rfl⟩

/-- The hop states with the trivial base states in the bookkeeping. -/
def acdIDNormHop (s : ACDIDHopSt Sc Msg RK Sa W Ct Kt) : ACDIDHopSt Sc Msg RK Sa W Ct Kt :=
  (((s.1.1.1, acdIDNormX s.1.1.2), s.1.2), s.2)

omit [Fintype RK] [Nonempty RK] [Inhabited Msg] in
omit [SampleableType Kt] in
/-- **The hop oracle does not see the base states of the bookkeeping**: its calls at a state and
at the state with the trivial base states agree up to `acdIDNormHop`. -/
theorem acdIDHopOracle_normHop (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg) Kt) (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W)
    (maxSkip maxStored ΔFS ΔPCS t k : ℕ) (root : RK → Key → PMF (RK × Sa))
    (s : ACDIDHopSt Sc Msg RK Sa W Ct Kt) (d : SMIDQuery W (ACDHdr Msg) Ct) :
    (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k root s d).map
        (Prod.map id acdIDNormHop) =
      (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k root (acdIDNormHop s)
        d).map (Prod.map id acdIDNormHop) := by
  have hcut : (Prod.map id acdIDNormHop ∘ acdIDCut ΔFS ΔPCS k :
      ACDIDAns Sc Msg RK Sa W Ct Kt × ACDIDHopSt Sc Msg RK Sa W Ct Kt → _) =
      acdIDCut ΔFS ΔPCS k ∘ Prod.map id acdIDNormHop := by
    funext y
    by_cases hy : y.2.1.2.epochSafe ΔFS ΔPCS k = false <;>
      simp [acdIDCut, hy, acdIDNormHop]
  simp only [acdIDHopOracle, PMF.map_comp, hcut]
  rw [← PMF.map_comp, ← PMF.map_comp]
  congr 1
  obtain ⟨⟨⟨σ, X⟩, x⟩, b⟩ := s
  have hN : acdIDNormHop ((((σ, X), x), b) : ACDIDHopSt Sc Msg RK Sa W Ct Kt) =
      (((σ, acdIDNormX X), x), b) := rfl
  rw [hN]
  by_cases hs : x.epochSafe ΔFS ΔPCS k = true
  · simp only [hs, ite_true]
    cases d with
    | sm q =>
      by_cases hg : smIDGate x (ckaShadow σ.ck) q = true
      · simp only [acdIDHopStep, hg, ite_true, PMF.map_comp]
        congr 1
        funext y
        have hX : ∀ p, (acdIDNormX X).1 p = acdIDNormSt (X.1 p) := fun _ => rfl
        simp only [Function.comp_def, Prod.map, id, acdIDNormHop, hX, acdIDAns_normSt,
          acdIDXUpd_normX]
        rfl
      · simp [acdIDHopStep, hg, PMF.pure_map, acdIDNormHop, acdIDNormX, acdIDNormSt]
    | deliver p h ad c =>
      obtain ⟨h1, h2, h3, h4⟩ := acdIDDeliver_normX G D maxSkip maxStored ΔFS ΔPCS k σ.loc.rcv
        (ckaShadow σ.ck) X.1 x p h ad c
      simp only [acdIDHopStep, PMF.pure_map, Prod.map, id, acdIDNormHop, acdIDNormX]
      simp only [h1, h2, h4]
      rw [h3]
  · simp [hs, PMF.pure_map, acdIDNormHop, acdIDNormX, acdIDNormSt]

end NormHop

/-! ## The FS-AEAD integrity reduction -/

section IntRed

variable {Sc Msg Key Rand RK Sa W Ct Kt : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [SampleableType Kt] [Fintype RK] [Nonempty RK] [Inhabited Msg]
  [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct]

/-- The states of the simulator of the integrity hop: the state of the simulator of the
FS-AEAD hop of the base, the bookkeeping beside it, the bookkeeping of the game with immediate
decryption and the flag of a forgery. -/
abbrev ACDIDFSSt (Sc Msg RK Sa W Ct Kt : Type) :=
  ((FSSim Sc Msg RK Sa × ACDIDX Sa Msg Kt) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) × Bool

/-- The receiving chains of a state of the simulator of the FS-AEAD hop, with `sa₀` in place of
the chain held by the FS-AEAD game. -/
def fsSimRcv (sa₀ : Sa) (x : FSSim Sc Msg RK Sa) (p : CKAParty) : Option Sa :=
  if x.rcvX p then some sa₀ else x.s.loc.rcv p

/-- The answer and the state of the simulator of the integrity hop after the query `q` of the
corruption game, answered by `y` by the simulator of the base. -/
def acdIDFSSmF (G : PRGDef Sa (Kt × Sa)) (sa₀ : Sa) (s : ACDIDFSSt Sc Msg RK Sa W Ct Kt)
    (q : SMQuery W) (y : SMAns Sc Msg RK Sa Ct × FSSim Sc Msg RK Sa) :
    ACDIDAns Sc Msg RK Sa W Ct Kt × ACDIDFSSt Sc Msg RK Sa W Ct Kt :=
  (.sm ((acdIDAns (s.1.1.2.1 q.party) y.1).withHdr (acdIDHdr s.1.1.2 q.party)),
    (((y.2, acdIDXUpd G (fsSimRcv sa₀ s.1.1.1) (ckaShadow s.1.1.1.s.ck) s.1.1.1.s.ck.msg
        s.1.1.2 q y.1),
      s.1.2.upd Prod.snd (ckaShadow s.1.1.1.s.ck) q
        ((acdIDAns (s.1.1.2.1 q.party) y.1).withHdr (acdIDHdr s.1.1.2 q.party))), s.2))

/-- The answer and the state of the simulator of the integrity hop after a delivery with the
outcome `r` of `acdIDDeliver` and the flag `b` of a forgery. -/
def acdIDFSDlvOf (s : ACDIDFSSt Sc Msg RK Sa W Ct Kt)
    (r : Option W × ((CKAParty → ACDIDSt Unit Unit Sa Msg Kt) ×
      SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) × Bool) (b : Bool) :
    ACDIDAns Sc Msg RK Sa W Ct Kt × ACDIDFSSt Sc Msg RK Sa W Ct Kt :=
  (.dec r.1, (((s.1.1.1, (r.2.1.1, s.1.1.2.2)), r.2.1.2), s.2 || b))

/-- **The simulator of the FS-AEAD integrity hop of the forgery event at the epoch `k`** over
`acdIDSM`, with the challenge epoch `t`, the root key `rkS` of the epoch `k` and a value `sa₀`
in place of the chain of the epoch `k`. A query of the corruption game through the gate is answered
by the simulator `smAuthFSImplAt` of the base, against the FS-AEAD integrity game of `G` and
`aeadComapAD D dec`, which holds the chain of the epoch `k`; a delivery into the epoch `k` with a
successful key lookup asks its decryption, with the associated data `enc h ad`, to the `dec`
oracle and raises the flag of a forgery when the answer differs from the answer from the log. -/
noncomputable def acdIDFSImpl (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg) Kt)
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    (rkS : RK) (sa₀ : Sa) (s : ACDIDFSSt Sc Msg RK Sa W Ct Kt) (d : SMIDQuery W (ACDHdr Msg) Ct) :
    OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W)
      (ACDIDAns Sc Msg RK Sa W Ct Kt × ACDIDFSSt Sc Msg RK Sa W Ct Kt) :=
  if s.1.2.epochSafe ΔFS ΔPCS k then
    match d with
    | .sm q =>
      if smIDGate s.1.2 (ckaShadow s.1.1.1.s.ck) q then
        (smAuthFSImplAt C R G (aeadComapAD D dec) ΔFS ΔPCS t k rkS s.1.1.1
          (acdIDBaseQuery enc s.1.1.2 q)).bind fun y =>
            .ret (acdIDCut ΔFS ΔPCS k (acdIDFSSmF G sa₀ s q y))
      else .ret (.sm .none, s)
    | .deliver p h ad c =>
      if acdIDDlvHit G maxSkip maxStored ΔFS ΔPCS k (fsSimRcv sa₀ s.1.1.1)
          (ckaShadow s.1.1.1.s.ck) s.1.1.2.1 s.1.2 p h then
        .query (.dec h.2 (enc h ad) c) fun a =>
          .ret (acdIDCut ΔFS ΔPCS k (acdIDFSDlvOf s (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k
            (fsSimRcv sa₀ s.1.1.1) (ckaShadow s.1.1.1.s.ck) s.1.1.2.1 s.1.2 p h ad c)
            (fsIntDecOf a != (s.1.2.findEntry k h ad c).map SMIDLogEntry.pt)))
      else
        .ret (acdIDCut ΔFS ΔPCS k (acdIDFSDlvOf s (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k
          (fsSimRcv sa₀ s.1.1.1) (ckaShadow s.1.1.1.s.ck) s.1.1.2.1 s.1.2 p h ad c) false))
  else .ret (.dec none, s)

/-- The initial state of the simulator of the integrity hop. -/
def acdIDFSInit (i : Msg × Sc × Sc) (rk : RK) : ACDIDFSSt Sc Msg RK Sa W Ct Kt :=
  (((⟨smInit i rk, fun _ => false, fun _ => false, false⟩, acdIDXInit), SMIDAux.init (i.1, 0)),
    false)

/-- The FS-AEAD integrity reduction of the forgery event at the epoch `k` over `acdIDSM` as an
oracle tree: it draws the challenge epoch `t` from `tStar`, the CKA initialisation from `initP`,
a uniform root key and a uniform root key `rkS` of the epoch `k`, runs the adversary against the
simulator `acdIDFSImpl` and outputs the flag of a forgery. -/
noncomputable def acdIDFSTree (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg) Kt)
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS k : ℕ)
    (sa₀ : Sa) (initP : PMF (Msg × Sc × Sc)) (tStar : PMF ℕ)
    (play : ℕ → Msg × ℕ → OracleAdv (SMIDQuery W (ACDHdr Msg) Ct) (ACDIDAns Sc Msg RK Sa W Ct Kt)
      Bool) : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool :=
  .rand tStar fun t => .rand initP fun i => .rand (PMF.uniformFintype RK) fun rk =>
    .rand (PMF.uniformFintype RK) fun rkS =>
      (OracleAdv.simulate
        (acdIDFSImpl C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k rkS sa₀) (play t (i.1, 0))
        (acdIDFSInit i rk)).bind fun r => .ret r.2.2

/-- **The FS-AEAD integrity reduction of the forgery event at the epoch `k`** over `acdIDSM`:
the tree `acdIDFSTree` at the challenge-epoch distribution and the interaction of `A`. -/
noncomputable def acdIDFSRed [Nonempty Sa] (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg) Kt)
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS k : ℕ)
    (initP : PMF (Msg × Sc × Sc))
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg Kt)) :
    OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool :=
  acdIDFSTree C R G D dec enc maxSkip maxStored ΔFS ΔPCS k (Classical.arbitrary Sa) initP
    A.tStar A.play

/-- The state of the hop games that a state of the simulator of the integrity hop and a state of
the integrity game stand for, with the chain `sa` of the epoch `k`. -/
def acdIDFSAbs (G : PRGDef Sa (Kt × Sa)) (k : ℕ) (rkS : RK) (sa : Sa)
    (z : ACDIDFSSt Sc Msg RK Sa W Ct Kt × FSIntSt Sa W Ct) : ACDIDHopSt Sc Msg RK Sa W Ct Kt :=
  (((fsIntAbs rkS z.1.1.1.1 z.2, acdIDFixX G k sa z.1.1.1.2), z.1.1.2), z.1.2)

/-- The log of the game with immediate decryption as the log of the authenticity game, with the
associated data `enc h ad` of the base. -/
def smAuxOfID (enc : ACDHdr Msg → W → W) (x : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) :
    SMAuthAux W Ct :=
  ⟨x.log.map fun l => ⟨l.e, l.j, l.pt, enc l.hdr l.ad, l.ct⟩, []⟩

/-- The invariant of the simulation of the integrity hop at the epoch `k` with the root key
`rkS` and the chain `sa` of the epoch `k`: the invariant `AuthFSInv` of the simulation of the
base with the log of `smAuxOfID`, a receiver of the epoch `k` one epoch ahead holds the chain of
the integrity game, and the invariant of the hop states at the abstraction. -/
structure ACDIDFSInv (C : CKADef Sc Msg Key) (J : Sc → Sc → Prop) (G : PRGDef Sa (Kt × Sa))
    (enc : ACDHdr Msg → W → W) (k : ℕ) (rkS : RK) (sa : Sa)
    (z : ACDIDFSSt Sc Msg RK Sa W Ct Kt × FSIntSt Sa W Ct) : Prop where
  /-- The invariant of the simulation of the base. -/
  auth : AuthFSInv k sa (((z.1.1.1.1, smAuxOfID enc z.1.1.2), z.1.2), z.2)
  /-- A receiver of the epoch `k` one epoch ahead holds the chain of the integrity game. -/
  rcvk1 : ∀ p, p ≠ ckaSender k → z.1.1.1.1.s.ck.t p = k + 1 → 1 ≤ k → z.1.1.1.1.rcvX p = true
  /-- The invariant of the hop states. -/
  hop : ACDIDHopInv C J G (acdIDFSAbs G k rkS sa z)

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] [DecidableEq Msg] in
omit [SampleableType Kt] in
/-- **The receiving chains of the simulator.** On the states of the invariant, the receiving
chains of the simulator with `sa₀` and those of the abstraction agree outside the receiving epoch
`k`, and at the receiving epoch `k` from `1` the abstraction holds the chain `sa`. -/
theorem ACDIDFSInv.rcv_rel {C : CKADef Sc Msg Key} {J : Sc → Sc → Prop} {G : PRGDef Sa (Kt × Sa)}
    {enc : ACDHdr Msg → W → W} {k : ℕ} {rkS : RK} {sa : Sa}
    {z : ACDIDFSSt Sc Msg RK Sa W Ct Kt × FSIntSt Sa W Ct} (hz : ACDIDFSInv C J G enc k rkS sa z)
    (sa₀ : Sa) (p : CKAParty) :
    1 ≤ (z.1.1.1.2.1 p).er →
      ((z.1.1.1.2.1 p).er = k → fsSimRcv z.2.init z.1.1.1.1 p = some sa ∧
        (fsSimRcv sa₀ z.1.1.1.1 p).isSome) ∧
      ((z.1.1.1.2.1 p).er ≠ k → fsSimRcv sa₀ z.1.1.1.1 p = fsSimRcv z.2.init z.1.1.1.1 p) := by
  obtain ⟨⟨⟨⟨x, X⟩, xid⟩, f⟩, u⟩ := z
  have her : (X.1 p).er =
      if ckaSender (x.s.ck.t p) = p then x.s.ck.t p - 1 else x.s.ck.t p :=
    (hz.hop.book.party p).er
  have hinit : u.init = sa := hz.auth.fs.init
  have hrk : x.rcvX p = true → (X.1 p).er = k := fun hr => by
    obtain ⟨h1, h2, h3⟩ := hz.auth.fs.rcv p hr
    have h2' : k ≤ x.s.ck.t p := h2
    have h3' : x.s.ck.t p ≤ k + 1 := h3
    rcases (by omega : x.s.ck.t p = k ∨ x.s.ck.t p = k + 1) with ht | ht
    · grind
    · have hs : ckaSender (k + 1) = p :=
        CKAParty.eq_of_ne_ne (ckaSender k) _ _ (ckaSender_succ_ne k).symm (Ne.symm h1)
      grind
  intro h1
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · have hr : x.rcvX p = true := by
      by_cases hs : ckaSender (x.s.ck.t p) = p
      · simp only [hs, ite_true] at her
        have ht : x.s.ck.t p = k + 1 := by grind
        rw [ht] at hs
        exact hz.rcvk1 p (fun h => ckaSender_succ_ne k (hs.trans h)) ht (by omega)
      · simp only [hs, ite_false] at her
        have ht : x.s.ck.t p = k := by grind
        rcases hz.auth.rcvk p (fun h => hs (ht ▸ h.symm)) ht with h | ⟨h0, -⟩
        · exact h
        · omega
    simp [fsSimRcv, hr, hinit]
  · have hr : x.rcvX p = false := by
      by_contra h
      exact hk (hrk (by simpa using h))
    simp [fsSimRcv, hr]

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] in
omit [SampleableType Kt] in
/-- **The received epochs of the simulator.** On the states of the invariant, the received
epochs of a party are from `1`, and the epoch a party resolves a public value to is the epoch of
the game. -/
theorem ACDIDFSInv.rpubs {C : CKADef Sc Msg Key} {J : Sc → Sc → Prop} {G : PRGDef Sa (Kt × Sa)}
    {enc : ACDHdr Msg → W → W} {k : ℕ} {rkS : RK} {sa : Sa}
    {z : ACDIDFSSt Sc Msg RK Sa W Ct Kt × FSIntSt Sa W Ct} (hz : ACDIDFSInv C J G enc k rkS sa z)
    (p : CKAParty) :
    (∀ q ∈ (z.1.1.1.2.1 p).rpubs, 1 ≤ q.1) ∧
      ∀ T q, (z.1.1.1.2.1 p).rpubs.find? (fun q => decide (q.2 = T)) = some q →
        z.1.1.2.epochOf (ckaShadow z.1.1.1.1.s.ck) p T = some q.1 := by
  obtain ⟨⟨⟨⟨x, X⟩, xid⟩, f⟩, u⟩ := z
  have hr : (X.1 p).rpubs = acdRPubs xid.pubs (x.s.ck.t p) p := (hz.hop.book.party p).rpubs
  refine ⟨fun q hq => ?_, fun T q hq => ?_⟩
  · rw [hr] at hq
    simp only [acdRPubs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.2.1.1
  · rw [hr] at hq
    exact (acdRPubs_find_epochOf xid (ckaShadow x.s.ck) p T hz.hop.book.pubs_sorted q hq).1

omit [Fintype RK] [Nonempty RK] [Inhabited Msg] [DecidableEq Msg] [DecidableEq W]
  [DecidableEq Ct] in
omit [SampleableType Kt] in
/-- A corruption answer of the secure-messaging oracle answers a corruption query. -/
theorem smOracleOfAt_state (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct W Kt)
    (ΔFS ΔPCS t k : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa))
    (σ : SMSt Sc Msg RK Sa) (q : SMQuery W) :
    ∀ y ∈ (smOracleOfAt C R G D ΔFS ΔPCS t k ideal root σ q).support,
      ∀ γ rk snd rcv, y.1 = .state γ rk snd rcv → ∃ p, q = .corrupt p := by
  intro y hy γ rk snd rcv h
  cases q with
  | corrupt p => exact ⟨p, rfl⟩
  | ratchet p =>
    simp only [smOracleOfAt, smOracleOf] at hy
    split at hy
    · simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff]
        at hy
      obtain ⟨r, -, z, -, rfl⟩ := hy
      cases h
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
      subst hy
      cases h
  | recv p =>
    simp only [smOracleOfAt, smOracleOf] at hy
    split at hy <;> simp only [PMF.support_pure, Set.mem_singleton_iff] at hy <;> subst hy <;>
      cases h
  | send p m =>
    simp only [smOracleOfAt, smOracleOf] at hy
    split at hy
    · split at hy <;> simp only [PMF.support_pure, Set.mem_singleton_iff] at hy <;> subst hy <;>
        cases h
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
      subst hy
      cases h
  | chall p m =>
    simp only [smOracleOfAt, smOracleOf] at hy
    split at hy
    · split at hy
      · simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff]
          at hy
        obtain ⟨c, -, rfl⟩ := hy
        cases h
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
        subst hy
        cases h
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
      subst hy
      cases h

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] [Inhabited Msg] [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] in
omit [SampleableType Kt] in
/-- The bookkeeping of the game does not see `acdIDFixSt` in the answer. -/
theorem SMIDAux.upd_acdIDAns_fixSt (G : PRGDef Sa (Kt × Sa)) (k : ℕ) (sa : Sa)
    (xid : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) (sh : CKAGameSt Unit Unit) (q : SMQuery W)
    (x : ACDIDSt Unit Unit Sa Msg Kt) (a : SMAns Sc Msg RK Sa Ct) (h : ACDHdr Msg) :
    xid.upd Prod.snd sh q ((acdIDAns (acdIDFixSt G k sa x) a).withHdr h) =
      xid.upd Prod.snd sh q ((acdIDAns x a).withHdr h) := by
  cases a with
  | state γ rk snd rcv => cases q <;> rfl
  | _ => rfl

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] [Inhabited Msg] [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] in
omit [SampleableType Kt] in
/-- **The answer of the simulator of the base, completed, is the completed answer of the hop
oracle at the abstraction**, up to `acdIDNormHop`, when the receiving chains are related as in
`ACDIDFSInv.rcv_rel` and the store of an answered corruption with the epoch `k` in no window holds
no key of the epoch `k`. -/
theorem acdIDFSSmF_abs (G : PRGDef Sa (Kt × Sa)) (ΔFS ΔPCS k : ℕ) (rkS : RK) (sa sa₀ : Sa)
    (x : FSSim Sc Msg RK Sa) (X : ACDIDX Sa Msg Kt) (xid : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (f : Bool) (u u' : FSIntSt Sa W Ct) (q : SMQuery W)
    (y : SMAns Sc Msg RK Sa Ct × FSSim Sc Msg RK Sa)
    (hR : ∀ p, 1 ≤ (X.1 p).er → ((X.1 p).er = k → fsSimRcv u.init x p = some sa ∧
      (fsSimRcv sa₀ x p).isSome) ∧ ((X.1 p).er ≠ k → fsSimRcv sa₀ x p = fsSimRcv u.init x p))
    (hA : ∀ γ rk snd rcv, y.1 = .state γ rk snd rcv → ∃ p, q = .corrupt p ∧
      (ckaAllowCorr ΔFS ΔPCS k (ckaShadow x.s.ck) p = true → ∀ el ∈ (X.1 p).store, el.1 ≠ k)) :
    ((acdIDCut ΔFS ΔPCS k (acdIDFSSmF G sa₀ (((x, X), xid), f) q y)).1,
        acdIDFSAbs G k rkS sa ((acdIDCut ΔFS ΔPCS k (acdIDFSSmF G sa₀ (((x, X), xid), f) q y)).2,
          u')) =
      Prod.map id acdIDNormHop (acdIDCut ΔFS ΔPCS k (acdIDSmF G
        (acdIDFSAbs G k rkS sa ((((x, X), xid), f), u)) q (y.1, fsIntAbs rkS y.2 u'))) := by
  have hX := acdIDXUpd_fixX G k sa (fsSimRcv sa₀ x) (fsSimRcv u.init x) (ckaShadow x.s.ck)
    x.s.ck.msg X hR q y.1
  have hrcv : (fsIntAbs rkS x u).loc.rcv = fsSimRcv u.init x := by
    funext p
    simp [fsIntAbs, fsAbs, fsSimRcv, fsStOfInt]
  have hU := SMIDAux.upd_acdIDAns_fixSt G k sa xid (ckaShadow x.s.ck) q (X.1 q.party) y.1
    (acdIDHdr X q.party)
  have hans : (xid.upd Prod.snd (ckaShadow x.s.ck) q
      ((acdIDAns (X.1 q.party) y.1).withHdr (acdIDHdr X q.party))).epochSafe ΔFS ΔPCS k = true →
      acdIDAns (acdIDFixSt G k sa (X.1 q.party)) y.1 = acdIDAns (X.1 q.party) y.1 := by
    intro hsafe
    cases hy : y.1 with
    | state γ rk snd rcv =>
      obtain ⟨p, rfl, hst⟩ := hA γ rk snd rcv hy
      rw [hy] at hsafe
      simp only [acdIDAns, SMSchemeAns.withHdr, SMIDAux.upd, SMIDAux.epochSafe, List.all_cons,
        Bool.and_eq_true] at hsafe
      exact acdIDAns_fixSt G k sa _ (hst hsafe.1) _
    | _ => rfl
  have hck : (fsIntAbs rkS x u).ck = x.s.ck := rfl
  simp only [acdIDFSSmF, acdIDSmF, acdIDFSAbs, acdIDCut, hrcv, hck]
  by_cases hsafe : (xid.upd Prod.snd (ckaShadow x.s.ck) q
      ((acdIDAns (X.1 q.party) y.1).withHdr (acdIDHdr X q.party))).epochSafe ΔFS ΔPCS k = true
  · have h1 : ∀ p, (acdIDFixX G k sa X).1 p = acdIDFixSt G k sa (X.1 p) := fun _ => rfl
    have h2 : ∀ p, acdIDHdr (acdIDFixX G k sa X) p = acdIDHdr X p := fun _ => rfl
    simp only [h1, h2, hans hsafe, hsafe, hX, Bool.true_eq_false, ite_false, Prod.map, id]
    rfl
  · have h1 : ∀ p, (acdIDFixX G k sa X).1 p = acdIDFixSt G k sa (X.1 p) := fun _ => rfl
    have h2 : ∀ p, acdIDHdr (acdIDFixX G k sa X) p = acdIDHdr X p := fun _ => rfl
    simp only [Bool.not_eq_true] at hsafe
    simp only [h1, h2, hU, hsafe, hX, ite_true, Prod.map, id]
    rfl

omit [Fintype RK] [Nonempty RK] [SampleableType Ct] [Inhabited Msg] in
omit [SampleableType Kt] in
/-- A query of the corruption game through the gate in the simulator of the integrity hop, from
a safe state, is the query of `smAuthFSImplAt` on the query of the base, completed and cut. -/
theorem acdIDFSImpl_simOracle (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg) Kt)
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    (rkS : RK) (sa₀ : Sa) {U : Type} (O' : U → FSIntQuery W Ct → PMF (FSIntAns Sa Ct W × U))
    (s : ACDIDFSSt Sc Msg RK Sa W Ct Kt) (u : U) (q : SMQuery W)
    (hs : s.1.2.epochSafe ΔFS ΔPCS k = true)
    (hg : smIDGate s.1.2 (ckaShadow s.1.1.1.s.ck) q = true) :
    OracleAdv.simOracle (acdIDFSImpl C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k rkS sa₀) O'
        (s, u) (.sm q) =
      (OracleAdv.simOracle (smAuthFSImplAt C R G (aeadComapAD D dec) ΔFS ΔPCS t k rkS) O'
        (s.1.1.1, u) (acdIDBaseQuery enc s.1.1.2 q)).map fun y =>
          ((acdIDCut ΔFS ΔPCS k (acdIDFSSmF G sa₀ s q (y.1, y.2.1))).1,
            ((acdIDCut ΔFS ΔPCS k (acdIDFSSmF G sa₀ s q (y.1, y.2.1))).2, y.2.2)) := by
  simp only [OracleAdv.simOracle, acdIDFSImpl, hs, hg, ite_true, OracleAdv.run_bind,
    OracleAdv.run_ret, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]

omit [Fintype RK] [Nonempty RK] in
omit [SampleableType Kt] in
/-- **The simulator of the integrity hop is the hop oracle at the queries of the corruption
game.** With `2 ≤ ΔFS` and `1 ≤ ΔPCS`, on the states of the invariant, a query of the
corruption game to the simulator against the integrity game, real or ideal, carried by the
abstraction, is the query of the hop oracle with the root output `(rkS, sa)` at the epoch `k`, up
to `acdIDNormHop`. -/
theorem acdIDFS_step_sm (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg) Kt)
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored : ℕ)
    {J : Sc → Sc → Prop} {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS) (t k : ℕ) (rkS : RK)
    (sa sa₀ : Sa) (b : Bool) (z : ACDIDFSSt Sc Msg RK Sa W Ct Kt × FSIntSt Sa W Ct)
    (hz : ACDIDFSInv C J G enc k rkS sa z) (q : SMQuery W) :
    (OracleAdv.simOracle (acdIDFSImpl C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k rkS sa₀)
        (fsIntOracle G (aeadComapAD D dec) b) z (.sm q)).map
        (Prod.map id (acdIDFSAbs G k rkS sa)) =
      (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k
        (constRoot (Key := Key) (rkS, sa)) (acdIDFSAbs G k rkS sa z) (.sm q)).map
        (Prod.map id acdIDNormHop) := by
  obtain ⟨⟨⟨⟨x, X⟩, xid⟩, f⟩, u⟩ := z
  have hN : acdIDNormHop (acdIDFSAbs G k rkS sa ((((x, X), xid), f), u)) =
      acdIDFSAbs G k rkS sa ((((x, X), xid), f), u) := rfl
  have hck : (fsIntAbs rkS x u).ck = x.s.ck := rfl
  by_cases hs : xid.epochSafe ΔFS ΔPCS k = true
  · by_cases hg : smIDGate xid (ckaShadow x.s.ck) q = true
    · rw [acdIDFSImpl_simOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k rkS sa₀ _ _ u q hs
        hg]
      have hstep : acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k
          (constRoot (Key := Key) (rkS, sa)) (acdIDFSAbs G k rkS sa ((((x, X), xid), f), u))
          (.sm q) =
          (smOracleOfAt C R G (aeadComapAD D dec) ΔFS ΔPCS t k false
            (constRoot (Key := Key) (rkS, sa)) (fsIntAbs rkS x u) (acdIDBaseQuery enc X q)).map
            (fun y => acdIDCut ΔFS ΔPCS k
              (acdIDSmF G (acdIDFSAbs G k rkS sa ((((x, X), xid), f), u)) q y)) := by
        simp only [acdIDHopOracle, acdIDFSAbs, hs, ite_true]
        rw [acdIDHopStep_sm C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k _ _ q hg, PMF.map_comp]
        rfl
      rw [hstep]
      by_cases hbad : ∃ p, q = .corrupt p ∧ ckaAllowCorr ΔFS ΔPCS t x.s.ck p = true ∧
          ckaAllowCorr ΔFS ΔPCS k x.s.ck p = false
      · obtain ⟨p, rfl, h1, h2⟩ := hbad
        have h2' : ckaAllowCorr ΔFS ΔPCS k (ckaShadow x.s.ck) p = false := h2
        have hNF : acdIDNormX (acdIDFixX G k sa X) = acdIDFixX G k sa X := rfl
        simp [hNF,OracleAdv.simOracle, smAuthFSImplAt, OracleAdv.run_mapQueryAnswer, smFSCorr, h1,
          OracleAdv.run_ret, PMF.pure_map, acdIDBaseQuery, SMQuery.mapMsg, smOracleOfAt,
          smOracleOf, hck, acdIDCut, acdIDFSSmF, acdIDSmF, SMIDAux.upd, SMIDAux.epochSafe, h2',
          acdIDFSAbs, acdIDNormHop, acdIDXUpd, acdIDAns, SMSchemeAns.withHdr]
      · have hq : ∀ p, acdIDBaseQuery enc X q = .corrupt p →
            ckaAllowCorr ΔFS ΔPCS t x.s.ck p = true → ckaAllowCorr ΔFS ΔPCS k x.s.ck p = true := by
          intro p hp h1
          have hp' : q = .corrupt p := by
            cases q <;> simp_all [acdIDBaseQuery, SMQuery.mapMsg]
          by_contra h2
          exact hbad ⟨p, hp', h1, by simpa using h2⟩
        have hst := smAuthFSImplAt_step C R G (aeadComapAD D dec) hFS hPCS t k rkS sa b x u
          hz.auth.fs _ hq
        rw [← hst, PMF.map_comp, PMF.map_comp, PMF.map_comp]
        simp only [PMF.map]
        refine PMF.bind_congr_support _ _ _ fun y hy => ?_
        simp only [Function.comp_apply, Prod.map_apply, id_eq]
        congr 1
        refine acdIDFSSmF_abs G ΔFS ΔPCS k rkS sa sa₀ x X xid f u y.2.2 q (y.1, y.2.1)
          (fun p => hz.rcv_rel sa₀ p) ?_
        intro γ rk snd rcv hy1
        have hy' : (y.1, fsIntAbs rkS y.2.1 y.2.2) ∈ (smOracleOfAt C R G (aeadComapAD D dec) ΔFS
            ΔPCS t k false (constRoot (Key := Key) (rkS, sa)) (fsIntAbs rkS x u)
            (acdIDBaseQuery enc X q)).support := by
          rw [← hst, PMF.support_map]
          exact ⟨y, hy, rfl⟩
        obtain ⟨p, hp⟩ := smOracleOfAt_state C R G _ ΔFS ΔPCS t k false _ _ _ _ hy' γ rk snd rcv
          hy1
        have hp' : q = .corrupt p := by
          cases q <;> simp_all [acdIDBaseQuery, SMQuery.mapMsg]
        refine ⟨p, hp', fun hk el hel => ?_⟩
        subst hp'
        have hc : xid.storeClear (ckaShadow x.s.ck) p = true := hg
        have := ACDIDInv.store_ne_of_allowCorr hFS hPCS k hz.hop.book p hc hk
          (acdIDFixEl G k sa el) (List.mem_map_of_mem hel)
        rwa [(acdIDFixEl_tag G k sa el).1] at this
    · simp [OracleAdv.simOracle, acdIDFSImpl, hs, hg, PMF.pure_map, acdIDHopOracle,
        acdIDFSAbs, acdIDHopStep, acdIDCut, hck, acdIDNormHop, acdIDFixX, acdIDNormX,
        acdIDNormSt, acdIDFixSt]
  · simp [OracleAdv.simOracle, acdIDFSImpl, hs, PMF.pure_map, acdIDHopOracle, acdIDFSAbs,
      acdIDCut, acdIDNormHop, acdIDFixX, acdIDNormX, acdIDNormSt, acdIDFixSt]

omit [Fintype RK] [Nonempty RK] in
omit [SampleableType Kt] in
/-- **The simulator of the integrity hop against the real integrity game is the hop oracle at
the deliveries.** When `dec` is a left inverse of `enc`, on the states of the invariant, a
delivery to the simulator against the real integrity game, carried by the abstraction, is the
delivery of the hop oracle with the root output `(rkS, sa)` at the epoch `k`, up to
`acdIDNormHop`. -/
theorem acdIDFS_step_dlv (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg) Kt)
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W)
    (hdec : ∀ h a, dec (enc h a) = (a, h)) (maxSkip maxStored : ℕ)
    {J : Sc → Sc → Prop} (ΔFS ΔPCS t k : ℕ) (rkS : RK)
    (sa sa₀ : Sa) (z : ACDIDFSSt Sc Msg RK Sa W Ct Kt × FSIntSt Sa W Ct)
    (hz : ACDIDFSInv C J G enc k rkS sa z) (p : CKAParty) (h : ACDHdr Msg) (ad : W) (c : Ct) :
    (OracleAdv.simOracle (acdIDFSImpl C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k rkS sa₀)
        (fsIntOracle G (aeadComapAD D dec) false) z (.deliver p h ad c)).map
        (Prod.map id (acdIDFSAbs G k rkS sa)) =
      (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k
        (constRoot (Key := Key) (rkS, sa)) (acdIDFSAbs G k rkS sa z) (.deliver p h ad c)).map
        (Prod.map id acdIDNormHop) := by
  have hR := hz.rcv_rel sa₀ p
  have hpub := (hz.rpubs p).1
  have hep := (hz.rpubs p).2 h.1
  obtain ⟨⟨⟨⟨x, X⟩, xid⟩, f⟩, u⟩ := z
  have hcorr : u.corr = false := hz.auth.fs.corr
  have hinit : u.init = sa := hz.auth.fs.init
  have hrcv : (fsIntAbs rkS x u).loc.rcv = fsSimRcv sa x := by
    funext p
    simp [fsIntAbs, fsAbs, fsSimRcv, fsStOfInt, hinit]
  have hR' : 1 ≤ (X.1 p).er → ((X.1 p).er = k → fsSimRcv sa x p = some sa ∧
      (fsSimRcv sa₀ x p).isSome) ∧ ((X.1 p).er ≠ k → fsSimRcv sa₀ x p = fsSimRcv sa x p) := by
    grind
  have hck : (fsIntAbs rkS x u).ck = x.s.ck := rfl
  have hfX : (acdIDFixX G k sa X).1 = fun q => acdIDFixSt G k sa (X.1 q) := rfl
  obtain ⟨h1, h2, h3, h4⟩ := acdIDDeliver_fix G D maxSkip maxStored ΔFS ΔPCS k sa
    (fsSimRcv sa₀ x) (fsSimRcv sa x) (ckaShadow x.s.ck) X.1 xid p h ad c hR' hpub
  have hfl := acdIDDeliver_fix_flag G D maxSkip maxStored ΔFS ΔPCS k sa
    (fsSimRcv sa₀ x) (fsSimRcv sa x) (ckaShadow x.s.ck) X.1 xid p h ad c hR' hpub hep
  by_cases hs : xid.epochSafe ΔFS ΔPCS k = true
  · simp only [acdIDHopOracle, acdIDFSAbs, hs, ite_true, acdIDHopStep, hrcv, hck, hfX,
      PMF.pure_map]
    by_cases hhit : acdIDDlvHit G maxSkip maxStored ΔFS ΔPCS k (fsSimRcv sa₀ x) (ckaShadow x.s.ck)
        X.1 xid p h = true
    · simp only [OracleAdv.simOracle, acdIDFSImpl, hs, hhit, ite_true, OracleAdv.run_query,
        fsIntOracle, PMF.pure_bind, OracleAdv.run_ret, PMF.pure_map, hcorr, Bool.false_eq_true,
        ite_false, fsIntDecOf, aeadComapAD, hdec, hinit]
      rw [hfl, hhit, Bool.true_and, h1, h2]
      simp only [acdIDCut, acdIDFSDlvOf]
      split_ifs with hc <;> simp [hc, Prod.map, acdIDFSAbs, acdIDNormHop, acdIDNormX, acdIDFixX, h3]
    · simp only [Bool.not_eq_true] at hhit
      simp only [OracleAdv.simOracle, acdIDFSImpl, hs, hhit, ite_true, Bool.false_eq_true,
        ite_false, OracleAdv.run_ret, PMF.pure_map]
      rw [hfl, hhit, Bool.false_and, h1, h2]
      simp only [acdIDCut, acdIDFSDlvOf]
      split_ifs with hc <;> simp [hc, Prod.map, acdIDFSAbs, acdIDNormHop, acdIDNormX, acdIDFixX, h3]
  · simp [OracleAdv.simOracle, acdIDFSImpl, hs, PMF.pure_map, acdIDHopOracle, acdIDFSAbs,
      acdIDCut, acdIDNormHop, acdIDFixX, acdIDNormX, acdIDNormSt, acdIDFixSt]

end IntRed

/-! ## The invariant of the simulation of the integrity hop -/

section IntInv

variable {Sc Msg Key Rand RK Sa W Ct Kt : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [SampleableType Kt] [DecidableEq W] [DecidableEq Ct]

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] in
/-- The invariant `AuthFSInv` reads the bookkeeping only through its log, and not the flag. -/
theorem AuthFSInv.congr_log {k : ℕ} {sa : Sa} {x : FSSim Sc Msg RK Sa} {aux aux' : SMAuthAux W Ct}
    {f f' : Bool} {u : FSIntSt Sa W Ct} (h : AuthFSInv k sa (((x, aux), f), u))
    (hl : aux'.log = aux.log) : AuthFSInv k sa (((x, aux'), f'), u) := by
  refine ⟨h.fs, ?_, fun j ad c => ?_, h.outk, h.rcvk, h.zero⟩
  · have := h.len
    simp only [SMAuthAux.nextIdx] at this ⊢
    rw [hl]
    exact this
  · have := h.dec j ad c
    simp only [SMAuthAux.logDec] at this ⊢
    rw [hl]
    exact this

omit [SampleableType Ct] in
omit [SampleableType Kt] in
/-- **A receiver of the epoch `k` one epoch ahead keeps the chain of the integrity game** along
the calls of the simulator of the base. -/
theorem smAuthFSImplAt_rcvk1 (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct W Kt)
    (ΔFS ΔPCS t k : ℕ) (rkS : RK) (sa : Sa) (b : Bool) (x : FSSim Sc Msg RK Sa)
    (aux : SMAuthAux W Ct) (f : Bool) (u : FSIntSt Sa W Ct)
    (hx : AuthFSInv k sa (((x, aux), f), u))
    (h1 : ∀ p, p ≠ ckaSender k → x.s.ck.t p = k + 1 → 1 ≤ k → x.rcvX p = true) (q : SMQuery W)
    (y) (hy : y ∈ (OracleAdv.simOracle (smAuthFSImplAt C R G D ΔFS ΔPCS t k rkS)
      (fsIntOracle G D b) (x, u) q).support) :
    ∀ p, p ≠ ckaSender k → y.2.1.s.ck.t p = k + 1 → 1 ≤ k → y.2.1.rcvX p = true := by
  intro p hp ht hk
  have hstep : ∀ n, (n = x.s.ck.t p ∨ n = x.s.ck.t p + 1) → n = k + 1 → x.rcvX p = true := by
    intro n hn hnk
    rcases hn with rfl | rfl
    · exact h1 p hp hnk hk
    · rcases hx.rcvk p hp (show x.s.ck.t p = k by omega) with h | ⟨h0, -⟩
      · exact h
      · omega
  have hreach : ckaReach x.s.ck := hx.fs.reach
  cases q with
  | ratchet p' =>
    simp only [OracleAdv.simOracle, smAuthFSImplAt, OracleAdv.run_mapQueryAnswer, smFSRatchet,
      PMF.support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    split at hz
    · simp only [OracleAdv.run_rand, PMF.support_bind, Set.mem_iUnion] at hz
      obtain ⟨r, -, hz⟩ := hz
      split at hz <;>
        simp only [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hz <;>
        subst hz <;> simp only [CKAGameSt.sent_t] at ht ⊢ <;>
        exact hstep _ (by split_ifs <;> simp_all) ht
    · simp only [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hstep _ (Or.inl rfl) ht
  | recv p' =>
    simp only [OracleAdv.simOracle, smAuthFSImplAt, OracleAdv.run_mapQueryAnswer, smFSRecv,
      PMF.support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    by_cases hc : x.s.ck.canRecv p' = true
    · obtain ⟨hto, hso⟩ := ckaReach_recv hreach hc
      have hzs : z.1.2.s.ck = x.s.ck.recvd p' (C.recv (x.s.ck.st p') x.s.ck.msg).1 ∧
          (p ≠ p' → z.1.2.rcvX p = x.rcvX p) := by
        by_cases ho : x.outX = true
        · simp only [hc, ho, ite_true, OracleAdv.run_ret, PMF.support_pure,
            Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨rfl, fun h => by simp [Function.update_of_ne h]⟩
        · have ho' : x.outX = false := by simpa using ho
          cases hl : x.s.loc.out with
          | none =>
            simp only [hc, ho', hl, Bool.false_eq_true, ite_true, ite_false, OracleAdv.run_ret,
              PMF.support_pure, Set.mem_singleton_iff] at hz
            subst hz
            exact ⟨rfl, fun _ => rfl⟩
          | some yy =>
            simp only [hc, ho', hl, Bool.false_eq_true, ite_true, ite_false, OracleAdv.run_ret,
              PMF.support_pure, Set.mem_singleton_iff] at hz
            subst hz
            exact ⟨rfl, fun h => by simp [Function.update_of_ne h]⟩
      by_cases hpp : p = p'
      · subst hpp
        exfalso
        have hz' : z.1.2.s.ck.t p = x.s.ck.t p + 1 := by
          rw [hzs.1]
          simp
        have htk : x.s.ck.t p = k := by
          change z.1.2.s.ck.t p = k + 1 at ht
          omega
        rw [htk] at hto
        rw [hto] at hso
        rcases CKAParty.eq_or_eq_other p (ckaSender k) with h | h
        · exact hp h
        · exact ckaSender_succ_ne k (hso.trans (by rw [h, CKAParty.other_other]))
      · have hz' : z.1.2.s.ck.t p = x.s.ck.t p ∧ z.1.2.rcvX p = x.rcvX p := by
          refine ⟨?_, hzs.2 hpp⟩
          rw [hzs.1]
          simp [hpp]
        change z.1.2.s.ck.t p = k + 1 at ht
        change z.1.2.rcvX p = true
        rw [hz'.2]
        exact hstep _ (Or.inl hz'.1) ht
    · simp only [hc, Bool.false_eq_true, ite_false, OracleAdv.run_ret, PMF.support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact hstep _ (Or.inl rfl) ht
  | send p' m =>
    simp only [OracleAdv.simOracle, smAuthFSImplAt, OracleAdv.run_mapQueryAnswer, smFSSend,
      PMF.support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hz' : z.1.2.s.ck = x.s.ck ∧ z.1.2.rcvX = x.rcvX := by
      split at hz <;> (try split at hz) <;> (try split at hz) <;>
        simp_all [OracleAdv.run_ret, OracleAdv.run_query, fsIntOracle, fsIntQ, fsIntA]
    change z.1.2.s.ck.t p = k + 1 at ht
    change z.1.2.rcvX p = true
    rw [hz'.2]
    rw [hz'.1] at ht
    exact hstep _ (Or.inl rfl) ht
  | chall p' m =>
    simp only [OracleAdv.simOracle, smAuthFSImplAt, smAuthFSChall, PMF.support_map,
      Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hz' : z.1.2.s.ck = x.s.ck ∧ z.1.2.rcvX = x.rcvX := by
      by_cases hs : x.sndX p' = true
      · by_cases hok : challOk x.s.loc t (x.s.ck.t p') p' = true
        · simp only [hs, hok, ite_true, OracleAdv.run_mapQueryAnswer, smFSChall,
            OracleAdv.run_query, fsIntQ, fsIntOracle, PMF.pure_map, PMF.pure_bind, fsIntA,
            OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨rfl, rfl⟩
        · have hok' : challOk x.s.loc t (x.s.ck.t p') p' = false := by simpa using hok
          simp only [hs, hok', ite_true, Bool.false_eq_true, ite_false,
            OracleAdv.run_mapQueryAnswer, smFSChall, OracleAdv.run_ret,
            PMF.support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨rfl, rfl⟩
      · have hs' : x.sndX p' = false := by simpa using hs
        cases hl : x.s.loc.snd p' with
        | none =>
          simp only [hs', hl, Bool.false_eq_true, ite_false, OracleAdv.run_ret,
            PMF.support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨rfl, rfl⟩
        | some sa' =>
          by_cases hok : challOk x.s.loc t (x.s.ck.t p') p' = true
          · simp only [hs', hl, hok, Bool.false_eq_true, ite_true, ite_false, OracleAdv.run_ret,
              PMF.support_pure, Set.mem_singleton_iff] at hz
            subst hz
            exact ⟨rfl, rfl⟩
          · have hok' : challOk x.s.loc t (x.s.ck.t p') p' = false := by simpa using hok
            simp only [hs', hl, hok', Bool.false_eq_true, ite_false, OracleAdv.run_ret,
              PMF.support_pure, Set.mem_singleton_iff] at hz
            subst hz
            exact ⟨rfl, rfl⟩
    change z.1.2.s.ck.t p = k + 1 at ht
    change z.1.2.rcvX p = true
    rw [hz'.2]
    rw [hz'.1] at ht
    exact hstep _ (Or.inl rfl) ht
  | corrupt p' =>
    simp only [OracleAdv.simOracle, smAuthFSImplAt, OracleAdv.run_mapQueryAnswer, smFSCorr,
      PMF.support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    split at hz <;> simp only [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hz <;>
      subst hz <;> exact hstep _ (Or.inl rfl) ht

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [DecidableEq W]
  [DecidableEq Ct] in
/-- The position of a logged message whose tag is new in an initial segment of the positions of
its epoch is the number of the messages of its epoch logged before. -/
theorem acd_j_eq_cnt {Hdr : Type} (l : SMIDLogEntry W Hdr Ct) (log : List (SMIDLogEntry W Hdr Ct))
    (hnew : ∀ e j, (e, j) ∈ (l :: log).map acdTag ↔ j < acdCnt (l :: log) e)
    (hold : ∀ e j, (e, j) ∈ log.map acdTag ↔ j < acdCnt log e)
    (hnd : ((l :: log).map acdTag).Nodup) : l.j = acdCnt log l.e := by
  have h1 := (hnew l.e l.j).1 (by simp [acdTag])
  rw [acdCnt_cons] at h1
  simp only [ite_true] at h1
  have h2 : ¬ l.j < acdCnt log l.e := fun h => by
    have hm := (hold l.e l.j).2 h
    rw [List.map_cons, List.nodup_cons] at hnd
    exact hnd.1 (by simpa [acdTag] using hm)
  omega

end IntInv

/-! ## The invariant along the simulation -/

section IntInvRun

variable {Sc Msg Key Rand RK Sa W Ct Kt : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [SampleableType Kt] [Fintype RK] [Nonempty RK] [Inhabited Msg]
  [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct]

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] in
omit [SampleableType Kt] in
/-- The invariant of the hop states does not read the flag nor the base states of the
bookkeeping. -/
theorem ACDIDHopInv.normHop {C : CKADef Sc Msg Key} {J : Sc → Sc → Prop} {G : PRGDef Sa (Kt × Sa)}
    {s : ACDIDHopSt Sc Msg RK Sa W Ct Kt} (h : ACDIDHopInv C J G s) (f : Bool) :
    ACDIDHopInv C J G ((acdIDNormHop s).1, f) :=
  ⟨h.base, h.book⟩

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] [Inhabited Msg] [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] in
/-- The positions of the log of `smAuxOfID` are those of `acdCnt`. -/
theorem smAuxOfID_nextIdx (enc : ACDHdr Msg → W → W) (xid : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (e : ℕ) : (smAuxOfID enc xid).nextIdx e = acdCnt xid.log e := by
  simp [SMAuthAux.nextIdx, smAuxOfID, acdCnt, List.countP_map, acdTag, Function.comp_def]

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] [Inhabited Msg] [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] in
/-- Unfolding lemma of the log of `smAuxOfID`. -/
theorem smAuxOfID_log (enc : ACDHdr Msg → W → W) (xid : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) :
    (smAuxOfID enc xid).log = xid.log.map fun l => ⟨l.e, l.j, l.pt, enc l.hdr l.ad, l.ct⟩ :=
  rfl

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] [Inhabited Msg] [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] in
omit [SampleableType Kt] in
/-- **The log of `smAuxOfID` after a query of the corruption game** is the log of the
authenticity game after the query of the base, when a logged ciphertext has the next position of
its epoch. -/
theorem smAuxOfID_upd (enc : ACDHdr Msg → W → W) (xid : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (sh : CKAGameSt Unit Unit) (X : ACDIDX Sa Msg Kt) (q : SMQuery W) (a : SMAns Sc Msg RK Sa Ct)
    (hpos : ∀ c p m, (q = .send p m ∨ q = .chall p m) → a = .ct c →
      (acdIDHdr X p).2 = acdCnt xid.log (sh.t p)) :
    (smAuxOfID enc (xid.upd Prod.snd sh q
        ((acdIDAns (X.1 q.party) a).withHdr (acdIDHdr X q.party)))).log =
      ((smAuxOfID enc xid).upd sh (acdIDBaseQuery enc X q) a.toScheme).log := by
  cases q <;> cases a <;>
    simp_all [SMIDAux.upd, SMAuthAux.upd, acdIDAns, SMSchemeAns.withHdr, SMAns.toScheme,
      acdIDBaseQuery, SMQuery.mapMsg, SMIDAux.record, SMAuthAux.record, SMQuery.party,
      smAuxOfID_log, smAuxOfID_nextIdx]

omit [Fintype Rand] [Nonempty Rand] [SampleableType Ct] [Fintype RK] [Nonempty RK]
  [Inhabited Msg] in
omit [SampleableType Kt] in
/-- A delivery keeps the log of `smAuxOfID`. -/
theorem smAuxOfID_deliver (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg) Kt)
    (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS k : ℕ) (rcv : CKAParty → Option Sa)
    (sh : CKAGameSt Unit Unit) (X : CKAParty → ACDIDSt Unit Unit Sa Msg Kt)
    (xid : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) (p : CKAParty) (h : ACDHdr Msg) (ad : W) (c : Ct) :
    (smAuxOfID enc
        (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k rcv sh X xid p h ad c).2.1.2).log =
      (smAuxOfID enc xid).log := by
  have hm : ∀ e, (smAuxOfID enc (xid.mark e h ad c)).log = (smAuxOfID enc xid).log := by
    intro e
    simp only [smAuxOfID, SMIDAux.mark, List.map_map]
    refine List.map_congr_left fun l _ => ?_
    simp only [Function.comp_apply]
    split <;> rfl
  unfold acdIDDeliver
  split
  · rfl
  · split
    · split
      · rfl
      · split <;> simp [hm]
    · rfl

omit [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK] [DecidableEq Msg]
  [DecidableEq W] [DecidableEq Ct] in
/-- The rejection of the transitions into an unsafe state keeps the state. -/
theorem acdIDCut_snd {S' Pub Hdr Leak : Type} (ΔFS ΔPCS k : ℕ)
    (v : SMIDAns Pub Hdr Ct Leak W × ((S' × SMIDAux W Pub Hdr Ct) × Bool)) :
    (acdIDCut ΔFS ΔPCS k v).2 = v.2 := by
  unfold acdIDCut
  split <;> rfl

omit [Fintype RK] [Nonempty RK] [SampleableType Ct] [Inhabited Msg] in
omit [SampleableType Kt] in
/-- The states after a delivery to the simulator of the integrity hop, real or ideal: the state
of the integrity game is kept, and the state of the simulator, up to the flag, is that of
`acdIDDeliver` with the receiving chains `fsSimRcv`. -/
theorem acdIDFSImpl_dlv_support (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg) Kt)
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    (rkS : RK) (sa₀ : Sa) (b : Bool) (s : ACDIDFSSt Sc Msg RK Sa W Ct Kt) (u : FSIntSt Sa W Ct)
    (p : CKAParty) (h : ACDHdr Msg) (ad : W) (c : Ct) (y)
    (hy : y ∈ (OracleAdv.simOracle
      (acdIDFSImpl C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k rkS sa₀)
      (fsIntOracle G (aeadComapAD D dec) b) (s, u) (.deliver p h ad c)).support) :
    y.2.2 = u ∧ y.2.1.1 = if s.1.2.epochSafe ΔFS ΔPCS k then
      ((s.1.1.1, ((acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k (fsSimRcv sa₀ s.1.1.1)
        (ckaShadow s.1.1.1.s.ck) s.1.1.2.1 s.1.2 p h ad c).2.1.1, s.1.1.2.2)),
        (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k (fsSimRcv sa₀ s.1.1.1)
          (ckaShadow s.1.1.1.s.ck) s.1.1.2.1 s.1.2 p h ad c).2.1.2)
      else s.1 := by
  simp only [OracleAdv.simOracle, acdIDFSImpl, PMF.support_map, Set.mem_image] at hy
  obtain ⟨w, hw, rfl⟩ := hy
  split_ifs at hw with hs hhit <;>
    simp only [OracleAdv.run_query, fsIntOracle, PMF.pure_bind, OracleAdv.run_ret,
      PMF.support_pure, Set.mem_singleton_iff] at hw <;>
    subst hw <;> simp [hs, acdIDCut_snd, acdIDFSDlvOf]

set_option linter.unusedFintypeInType false in
omit [SampleableType Kt] in
/-- **The invariant of the simulation of the integrity hop is kept** by every call of the
simulator against the real and the ideal integrity game, when `dec` is a left inverse of `enc`,
the CKA is correct along `J`, `2 ≤ ΔFS` and `1 ≤ ΔPCS`. -/
theorem acdIDFS_inv (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg) Kt)
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W)
    (hdec : ∀ h a, dec (enc h a) = (a, h)) (maxSkip maxStored : ℕ)
    {J : Sc → Sc → Prop} (hJ : CKACorrect C J) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS)
    (t k : ℕ) (rkS : RK) (sa sa₀ : Sa) (b : Bool)
    (z : ACDIDFSSt Sc Msg RK Sa W Ct Kt × FSIntSt Sa W Ct) (hz : ACDIDFSInv C J G enc k rkS sa z)
    (d : SMIDQuery W (ACDHdr Msg) Ct) (y)
    (hy : y ∈ (OracleAdv.simOracle
      (acdIDFSImpl C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k rkS sa₀)
      (fsIntOracle G (aeadComapAD D dec) b) z d).support) :
    ACDIDFSInv C J G enc k rkS sa y.2 := by
  cases d with
  | sm q =>
    have hhop : ACDIDHopInv C J G (acdIDFSAbs G k rkS sa y.2) := by
      have hm : (y.1, acdIDFSAbs G k rkS sa y.2) ∈ ((acdIDHopOracle C R G D dec enc maxSkip
          maxStored ΔFS ΔPCS t k (constRoot (Key := Key) (rkS, sa)) (acdIDFSAbs G k rkS sa z)
          (.sm q)).map (Prod.map id acdIDNormHop)).support := by
        rw [← acdIDFS_step_sm C R G D dec enc maxSkip maxStored hFS hPCS t k rkS sa sa₀ b z hz q,
          PMF.support_map]
        exact ⟨y, hy, rfl⟩
      rw [PMF.support_map] at hm
      obtain ⟨w, hw, hwe⟩ := hm
      have hw' := acdIDHopOracle_hopInv C R G D dec enc maxSkip maxStored hJ ΔFS ΔPCS t k _ _
        hz.hop _ w hw
      have he : acdIDFSAbs G k rkS sa y.2 = ((acdIDNormHop w.2).1, (acdIDNormHop w.2).2) :=
        (congrArg Prod.snd hwe).symm
      rw [he]
      exact hw'.normHop _
    obtain ⟨⟨⟨⟨x, X⟩, xid⟩, f⟩, u⟩ := z
    by_cases hs : xid.epochSafe ΔFS ΔPCS k = true
    · by_cases hg : smIDGate xid (ckaShadow x.s.ck) q = true
      · rw [acdIDFSImpl_simOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k rkS sa₀ _ _ u q hs
          hg, PMF.support_map] at hy
        obtain ⟨w, hw, rfl⟩ := hy
        simp only [acdIDCut_snd] at hhop ⊢
        have hA := smAuthFSImplAt_inv C R G (aeadComapAD D dec) ΔFS ΔPCS t k rkS sa b x
          (smAuxOfID enc xid) f u hz.auth (acdIDBaseQuery enc X q) w hw f
        have hrk := smAuthFSImplAt_rcvk1 C R G (aeadComapAD D dec) ΔFS ΔPCS t k rkS sa b x
          (smAuxOfID enc xid) f u hz.auth hz.rcvk1 _ w hw
        refine ⟨hA.congr_log ?_, hrk, hhop⟩
        apply smAuxOfID_upd
        intro c p' m hq hc
        have hn := hhop.book.log_pos
        have hnd := hhop.book.log_nodup
        have hold : ∀ e j, (e, j) ∈ xid.log.map acdTag ↔ j < acdCnt xid.log e :=
          hz.hop.book.log_pos
        have hc' : w.1 = .ct c := hc
        rcases hq with rfl | rfl <;>
        · simp only [acdIDEmb, acdIDFSAbs, acdIDFSSmF, hc', acdIDAns, SMSchemeAns.withHdr,
            SMIDAux.upd, SMIDAux.record, SMQuery.party] at hn hnd
          exact acd_j_eq_cnt _ _ hn hold hnd
      · simp only [OracleAdv.simOracle, acdIDFSImpl, hs, hg, ite_true, Bool.false_eq_true,
          ite_false, OracleAdv.run_ret, PMF.pure_map, PMF.support_pure,
          Set.mem_singleton_iff] at hy
        subst hy
        exact hz
    · simp only [OracleAdv.simOracle, acdIDFSImpl, hs, Bool.false_eq_true, ite_false,
        OracleAdv.run_ret, PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact hz
  | deliver p h ad c =>
    obtain ⟨y0, hy0⟩ := (OracleAdv.simOracle
      (acdIDFSImpl C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k rkS sa₀)
      (fsIntOracle G (aeadComapAD D dec) false) z (.deliver p h ad c)).support_nonempty
    obtain ⟨hu, hs1⟩ := acdIDFSImpl_dlv_support C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k
      rkS sa₀ b z.1 z.2 p h ad c y hy
    obtain ⟨hu0, hs0⟩ := acdIDFSImpl_dlv_support C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k
      rkS sa₀ false z.1 z.2 p h ad c y0 hy0
    have hhop : ACDIDHopInv C J G (acdIDFSAbs G k rkS sa y.2) := by
      have hm : (y0.1, acdIDFSAbs G k rkS sa y0.2) ∈ ((acdIDHopOracle C R G D dec enc maxSkip
          maxStored ΔFS ΔPCS t k (constRoot (Key := Key) (rkS, sa)) (acdIDFSAbs G k rkS sa z)
          (.deliver p h ad c)).map (Prod.map id acdIDNormHop)).support := by
        rw [← acdIDFS_step_dlv C R G D dec enc hdec maxSkip maxStored ΔFS ΔPCS t k rkS sa sa₀ z
          hz p h ad c, PMF.support_map]
        exact ⟨y0, hy0, rfl⟩
      rw [PMF.support_map] at hm
      obtain ⟨w, hw, hwe⟩ := hm
      have hw' := acdIDHopOracle_hopInv C R G D dec enc maxSkip maxStored hJ ΔFS ΔPCS t k _ _
        hz.hop _ w hw
      have he0 : acdIDFSAbs G k rkS sa y0.2 = ((acdIDNormHop w.2).1, (acdIDNormHop w.2).2) :=
        (congrArg Prod.snd hwe).symm
      have he : acdIDFSAbs G k rkS sa y.2 = ((acdIDNormHop w.2).1, y.2.1.2) := by
        rw [← congrArg Prod.fst he0]
        simp only [acdIDFSAbs, hu, hu0, hs1, hs0]
      rw [he]
      exact hw'.normHop _
    obtain ⟨⟨⟨⟨x, X⟩, xid⟩, f⟩, u⟩ := z
    by_cases hs : xid.epochSafe ΔFS ΔPCS k = true
    · simp only [hs, ite_true] at hs1
      refine ⟨?_, ?_, hhop⟩
      · rw [hs1, hu]
        exact hz.auth.congr_log (smAuxOfID_deliver G D enc maxSkip maxStored ΔFS ΔPCS k _ _ _ xid
          p h ad c)
      · rw [hs1]
        exact hz.rcvk1
    · simp only [hs, Bool.false_eq_true, ite_false] at hs1
      refine ⟨?_, ?_, hhop⟩
      · rw [hs1, hu]
        exact hz.auth.congr_log rfl
      · rw [hs1]
        exact hz.rcvk1

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [DecidableEq Msg]
  [Fintype RK] [Nonempty RK] in
omit [SampleableType Kt] in
/-- The invariant holds at the initial state of the simulation, for initial CKA states related
by `J`. -/
theorem acdIDFSInv_init (C : CKADef Sc Msg Key) {J : Sc → Sc → Prop} (G : PRGDef Sa (Kt × Sa))
    (enc : ACDHdr Msg → W → W) (k : ℕ) (rkS rk : RK) (i : Msg × Sc × Sc) (hi : J i.2.1 i.2.2)
    (sa : Sa) :
    ACDIDFSInv C J G enc k rkS sa ((acdIDFSInit i rk : ACDIDFSSt Sc Msg RK Sa W Ct Kt),
      (⟨sa, sa, [], false⟩ : FSIntSt Sa W Ct)) := by
  have hR : PRGDef (RK × Key) (RK × Sa) := ⟨fun _ => (rk, sa)⟩
  refine ⟨(authFSInv_init k rk i sa).congr_log rfl, ?_, ?_⟩
  · intro p _ ht _
    simp [acdIDFSInit, smInit, CKAGameSt.init] at ht
  · have he : acdIDFSAbs G k rkS sa ((acdIDFSInit i rk : ACDIDFSSt Sc Msg RK Sa W Ct Kt),
        (⟨sa, sa, [], false⟩ : FSIntSt Sa W Ct)) =
        (((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)), false) := by
      simp only [acdIDFSAbs, acdIDFSInit, fsIntAbs, fsStOfInt]
      rw [fsAbs_init]
      rfl
    rw [he]
    exact acdIDHopInv_init C hR G i hi rk

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] in
omit [SampleableType Kt] in
/-- **Decryption from the log of the integrity game at a delivery into the epoch `k`.** On the
states of the invariant, when `dec` is a left inverse of `enc`, at a delivery into the epoch `k`
with a successful key lookup, decryption from the log of the integrity game at the associated
data `enc h ad` is the answer from the log of the game. -/
theorem ACDIDFSInv.logDec_eq {C : CKADef Sc Msg Key} {J : Sc → Sc → Prop}
    {G : PRGDef Sa (Kt × Sa)} {dec : W → W × ACDHdr Msg} {enc : ACDHdr Msg → W → W}
    (hdec : ∀ h a, dec (enc h a) = (a, h)) (maxSkip maxStored ΔFS ΔPCS : ℕ) {k : ℕ} {rkS : RK}
    {sa : Sa} (sa₀ : Sa) {z : ACDIDFSSt Sc Msg RK Sa W Ct Kt × FSIntSt Sa W Ct}
    (hz : ACDIDFSInv C J G enc k rkS sa z) (p : CKAParty) (h : ACDHdr Msg) (ad : W) (c : Ct)
    (hhit : acdIDDlvHit G maxSkip maxStored ΔFS ΔPCS k (fsSimRcv sa₀ z.1.1.1.1)
      (ckaShadow z.1.1.1.1.s.ck) z.1.1.1.2.1 z.1.1.2 p h = true) :
    z.2.logDec h.2 (enc h ad) c = (z.1.1.2.findEntry k h ad c).map SMIDLogEntry.pt := by
  have hR := hz.rcv_rel sa₀ p
  have hpub := (hz.rpubs p).1
  obtain ⟨⟨⟨⟨x, X⟩, xid⟩, f⟩, u⟩ := z
  have hinit : u.init = sa := hz.auth.fs.init
  have hR' : 1 ≤ (X.1 p).er → ((X.1 p).er = k → fsSimRcv sa x p = some sa ∧
      (fsSimRcv sa₀ x p).isSome) ∧ ((X.1 p).er ≠ k → fsSimRcv sa₀ x p = fsSimRcv sa x p) := by
    grind
  have hrcv : (fsIntAbs rkS x u).loc.rcv = fsSimRcv sa x := by
    funext p
    simp [fsIntAbs, fsAbs, fsSimRcv, fsStOfInt, hinit]
  simp only [acdIDDlvHit] at hhit
  cases he : xid.epochOf (ckaShadow x.s.ck) p h.1 with
  | none => simp [he] at hhit
  | some e =>
    simp only [he, Bool.and_eq_true, decide_eq_true_eq] at hhit
    obtain ⟨⟨rfl, -⟩, hk⟩ := hhit
    have hk' := (acdIDRKey_fix G maxSkip maxStored e sa (X.1 p) (fsSimRcv sa₀ x p)
      (fsSimRcv sa x p) hR' hpub h).1
    have hsome : (acdIDRKey G maxSkip maxStored
        ((acdIDFixSt G e sa (X.1 p)).withBase ⟨(), (), none, fsSimRcv sa x p⟩) h).isSome := by
      have := congrArg Option.isSome hk'
      simp only [Option.isSome_map] at this
      rw [this]
      exact hk
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hsome
    have hb := acdIDRKey_base_congr G maxSkip maxStored
      ((acdIDFixSt G e sa (X.1 p)).withBase ⟨(), (), none, fsSimRcv sa x p⟩)
      ((fsIntAbs rkS x u).toScheme.ck.st p) (by simp [SMSt.toScheme, hrcv, ACDIDSt.withBase]) h
    have hy' : acdIDRKey G maxSkip maxStored
        ((acdIDJoin (fsIntAbs rkS x u) (acdIDFixX G e sa X)).ck.st p) h =
        some (y.1.withBase ((fsIntAbs rkS x u).toScheme.ck.st p), y.2) := by
      have : (acdIDJoin (fsIntAbs rkS x u) (acdIDFixX G e sa X)).ck.st p =
          ((acdIDFixSt G e sa (X.1 p)).withBase ⟨(), (), none, fsSimRcv sa x p⟩).withBase
            ((fsIntAbs rkS x u).toScheme.ck.st p) := rfl
      rw [this, hb, hy]
      rfl
    obtain ⟨e', he', hund⟩ := ACDIDInv.undelivered_of_rkey maxSkip maxStored hz.hop.book p h _ hy'
    have hee : e' = e := Option.some.inj (he'.symm.trans he)
    subst hee
    have hlogj : ∀ l ∈ xid.log, l.j = l.hdr.2 := hz.hop.book.log_j
    have hdecl := hz.auth.dec h.2 (enc h ad) c
    simp only at hdecl
    rw [hdecl]
    simp only [SMAuthAux.logDec, smAuxOfID, SMIDAux.findEntry, List.find?_map, Option.map_map]
    rw [List.find?_congr (l := xid.log) (p₂ := SMIDLogEntry.isMatch e' h ad c) fun l hl => ?_]
    · rfl
    · simp only [Function.comp_apply, SMIDLogEntry.isMatch]
      by_cases hm : l.e = e' ∧ l.j = h.2 ∧ enc l.hdr l.ad = enc h ad ∧ l.ct = c
      · obtain ⟨h1, h2, h3, h4⟩ := hm
        have h3' := congrArg dec h3
        rw [hdec, hdec, Prod.mk.injEq] at h3'
        have hd := hund l hl (by simp [acdTag, h1, h2])
        simp [h1, h2, h3'.1, h3'.2, h4, hd]
      · have : ¬ (l.delivered = false ∧ l.e = e' ∧ l.hdr = h ∧ l.ad = ad ∧ l.ct = c) := by
          rintro ⟨-, h1, h2, h3, h4⟩
          exact hm ⟨h1, by rw [hlogj l hl, h2], by rw [h2, h3], h4⟩
        simp only [decide_eq_false hm]
        grind

omit [Fintype RK] [Nonempty RK] [SampleableType Ct] in
omit [SampleableType Kt] in
/-- **The reduction raises no flag against the ideal integrity game.** On the states of the
invariant, when `dec` is a left inverse of `enc`, from a state with the flag cleared, every call
of the simulator against the integrity game with decryption from its log leaves the flag
cleared. -/
theorem acdIDFS_ideal_flag (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg) Kt)
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W)
    (hdec : ∀ h a, dec (enc h a) = (a, h)) (maxSkip maxStored : ℕ) {J : Sc → Sc → Prop}
    (ΔFS ΔPCS t k : ℕ) (rkS : RK) (sa sa₀ : Sa)
    (z : ACDIDFSSt Sc Msg RK Sa W Ct Kt × FSIntSt Sa W Ct) (hz : ACDIDFSInv C J G enc k rkS sa z)
    (hf : z.1.2 = false) (d : SMIDQuery W (ACDHdr Msg) Ct) (y)
    (hy : y ∈ (OracleAdv.simOracle
      (acdIDFSImpl C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k rkS sa₀)
      (fsIntOracle G (aeadComapAD D dec) true) z d).support) :
    y.2.1.2 = false := by
  have hlog := fun p h ad c hhit =>
    hz.logDec_eq hdec maxSkip maxStored ΔFS ΔPCS sa₀ p h ad c hhit
  obtain ⟨⟨⟨⟨x, X⟩, xid⟩, f⟩, u⟩ := z
  simp only at hf
  subst hf
  have hcorr : u.corr = false := hz.auth.fs.corr
  by_cases hs : xid.epochSafe ΔFS ΔPCS k = true
  · cases d with
    | sm q =>
      by_cases hg : smIDGate xid (ckaShadow x.s.ck) q = true
      · rw [acdIDFSImpl_simOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k rkS sa₀ _ _ u q hs
          hg, PMF.support_map] at hy
        obtain ⟨w, hw, rfl⟩ := hy
        simp [acdIDCut_snd, acdIDFSSmF]
      · simp only [OracleAdv.simOracle, acdIDFSImpl, hs, hg, ite_true, Bool.false_eq_true,
          ite_false, OracleAdv.run_ret, PMF.pure_map, PMF.support_pure,
          Set.mem_singleton_iff] at hy
        subst hy
        rfl
    | deliver p h ad c =>
      by_cases hhit : acdIDDlvHit G maxSkip maxStored ΔFS ΔPCS k (fsSimRcv sa₀ x)
          (ckaShadow x.s.ck) X.1 xid p h = true
      · have hl := hlog p h ad c hhit
        simp only [OracleAdv.simOracle, acdIDFSImpl, hs, hhit, ite_true, OracleAdv.run_query,
          fsIntOracle, PMF.pure_bind, OracleAdv.run_ret, PMF.pure_map, PMF.support_pure,
          Set.mem_singleton_iff, hcorr, Bool.false_eq_true, ite_false] at hy
        subst hy
        simp only at hl
        simp [acdIDCut_snd, acdIDFSDlvOf, fsIntDecOf, hl]
      · simp only [Bool.not_eq_true] at hhit
        simp only [OracleAdv.simOracle, acdIDFSImpl, hs, hhit, ite_true, Bool.false_eq_true,
          ite_false, OracleAdv.run_ret, PMF.pure_map, PMF.support_pure,
          Set.mem_singleton_iff] at hy
        subst hy
        simp [acdIDCut_snd, acdIDFSDlvOf]
  · simp only [OracleAdv.simOracle, acdIDFSImpl, hs, Bool.false_eq_true, ite_false,
      OracleAdv.run_ret, PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    rfl

end IntInvRun

/-! ## The FS-AEAD integrity hop and the integrity bound -/

section IntGame

variable {Sc Msg Key Rand RK Sa W Ct Kt : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [SampleableType Kt] [Fintype RK] [Nonempty RK] [Inhabited Msg]
  [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct]

omit [SampleableType Ct] in
omit [SampleableType Kt] in
/-- Running the FS-AEAD integrity reduction tree against an oracle is running the adversary
against the composed oracle from the drawn initial state, with the flag of a forgery as
output. -/
theorem acdIDFSTree_run (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg) Kt)
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS k : ℕ)
    (sa₀ : Sa) (initP : PMF (Msg × Sc × Sc)) (tStar : PMF ℕ)
    (play : ℕ → Msg × ℕ → OracleAdv (SMIDQuery W (ACDHdr Msg) Ct) (ACDIDAns Sc Msg RK Sa W Ct Kt)
      Bool) {U : Type} (O' : U → FSIntQuery W Ct → PMF (FSIntAns Sa Ct W × U)) (u : U) :
    (OracleAdv.run O' (acdIDFSTree C R G D dec enc maxSkip maxStored ΔFS ΔPCS k sa₀ initP tStar
        play) u).map Prod.fst =
      tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (PMF.uniformFintype RK).bind fun rkS =>
          (OracleAdv.run (OracleAdv.simOracle
            (acdIDFSImpl C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k rkS sa₀) O')
            (play t (i.1, 0)) (acdIDFSInit i rk, u)).map fun x => x.2.1.2 := by
  simp only [acdIDFSTree, OracleAdv.run_rand, PMF.map_bind]
  refine congrArg _ (funext fun t => congrArg _ (funext fun i =>
    congrArg _ (funext fun rk => congrArg _ (funext fun rkS => ?_))))
  rw [OracleAdv.run_bind, OracleAdv.run_simulate]
  simp [PMF.map_bind, PMF.bind_map, Function.comp_def, PMF.pure_map]
  rfl

omit [Fintype RK] [Nonempty RK] in
omit [SampleableType Kt] in
/-- **The simulator of the integrity hop against the real integrity game is the hop oracle**,
carried by the abstraction, up to `acdIDNormHop`, on the states of the invariant. -/
theorem acdIDFS_step (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg) Kt)
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W)
    (hdec : ∀ h a, dec (enc h a) = (a, h)) (maxSkip maxStored : ℕ)
    {J : Sc → Sc → Prop} {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS) (t k : ℕ) (rkS : RK)
    (sa sa₀ : Sa) (z : ACDIDFSSt Sc Msg RK Sa W Ct Kt × FSIntSt Sa W Ct)
    (hz : ACDIDFSInv C J G enc k rkS sa z) (d : SMIDQuery W (ACDHdr Msg) Ct) :
    (OracleAdv.simOracle (acdIDFSImpl C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k rkS sa₀)
        (fsIntOracle G (aeadComapAD D dec) false) z d).map
        (Prod.map id (acdIDFSAbs G k rkS sa)) =
      (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k
        (constRoot (Key := Key) (rkS, sa)) (acdIDFSAbs G k rkS sa z) d).map
        (Prod.map id acdIDNormHop) := by
  cases d with
  | sm q =>
    exact acdIDFS_step_sm C R G D dec enc maxSkip maxStored hFS hPCS t k rkS sa sa₀ false z hz q
  | deliver p h ad c =>
    exact acdIDFS_step_dlv C R G D dec enc hdec maxSkip maxStored ΔFS ΔPCS t k rkS sa sa₀ z hz
      p h ad c

variable [Fintype Sa] [Nonempty Sa]

omit [SampleableType Kt] in
/-- **The real side of the FS-AEAD integrity hop.** For a CKA correct along `J`, an
initialisation that is the lift of `initP` with initial states related by `J`, `dec` a left
inverse of `enc`, `2 ≤ ΔFS` and `1 ≤ ΔPCS`, the real FS-AEAD integrity game of `G` and
`aeadComapAD D dec` at the reduction `acdIDFSRed` is the hop game with a uniform root output at
the epoch `k`. -/
theorem acdIDFS_real_eq (C : CKADef Sc Msg Key) [CKACoins C Rand] {J : Sc → Sc → Prop}
    (hJ : CKACorrect C J) (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg) Kt) (dec : W → W × ACDHdr Msg)
    (enc : ACDHdr Msg → W → W) (hdec : ∀ h a, dec (enc h a) = (a, h)) (maxSkip maxStored : ℕ)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS) (k : ℕ)
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg Kt)) :
    fsaead_int_game G (aeadComapAD D dec) false
        (acdIDFSRed C R G D dec enc maxSkip maxStored ΔFS ΔPCS k initP A) =
      acdIDHopGame C R G D dec enc maxSkip maxStored ΔFS ΔPCS k unifRoot A := by
  rw [acdIDHopGame_eq_liftPMF C initP hinit]
  unfold fsaead_int_game
  congr 1
  have h1 : ∀ sa : Sa,
      (OracleAdv.run (fsIntOracle G (aeadComapAD D dec) false)
        (acdIDFSRed C R G D dec enc maxSkip maxStored ΔFS ΔPCS k initP A)
        ⟨sa, sa, [], false⟩).map Prod.fst =
      A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (PMF.uniformFintype RK).bind fun rkS =>
          (OracleAdv.run (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k
            (constRoot (Key := Key) (rkS, sa))) (A.play t (i.1, 0))
            (((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)), false)).map fun x => x.2.2 := by
    intro sa
    rw [acdIDFSRed, acdIDFSTree_run]
    refine congrArg _ (funext fun t => ?_)
    refine PMF.bind_congr_support _ _ _ fun i hi => congrArg _ (funext fun rk =>
      congrArg _ (funext fun rkS => ?_))
    have hsim := OracleAdv.run_map_state_of_inv _
      (fun s d => (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k
        (constRoot (Key := Key) (rkS, sa)) s d).map (Prod.map id acdIDNormHop))
      (acdIDFSAbs G k rkS sa) (ACDIDFSInv C J G enc k rkS sa)
      (fun z d hz y hy => acdIDFS_inv C R G D dec enc hdec maxSkip maxStored hJ hFS hPCS t k rkS
        sa (Classical.arbitrary Sa) false z hz d y hy)
      (fun z d hz => acdIDFS_step C R G D dec enc hdec maxSkip maxStored hFS hPCS t k rkS sa
        (Classical.arbitrary Sa) z
        hz d)
      (A.play t (i.1, 0)) (acdIDFSInit i rk, ⟨sa, sa, [], false⟩)
      (acdIDFSInv_init C G enc k rkS rk i (hJi i hi) sa)
    have hreal := OracleAdv.run_map_state
      (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k
        (constRoot (Key := Key) (rkS, sa)))
      (fun s d => (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k
        (constRoot (Key := Key) (rkS, sa)) s d).map (Prod.map id acdIDNormHop))
      acdIDNormHop (fun s d => acdIDHopOracle_normHop C R G D dec enc maxSkip maxStored ΔFS ΔPCS
        t k _ s d) (A.play t (i.1, 0)) (((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)), false)
    have he : acdIDFSAbs G k rkS sa ((acdIDFSInit i rk : ACDIDFSSt Sc Msg RK Sa W Ct Kt),
        (⟨sa, sa, [], false⟩ : FSIntSt Sa W Ct)) =
        (((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)), false) := by
      simp only [acdIDFSAbs, acdIDFSInit, fsIntAbs, fsStOfInt]
      rw [fsAbs_init]
      rfl
    have hN : acdIDNormHop ((((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)), false) :
        ACDIDHopSt Sc Msg RK Sa W Ct Kt) = (((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)),
          false) := rfl
    rw [he] at hsim
    rw [hN] at hreal
    have hs := congrArg (PMF.map fun x => x.2.2) hsim
    have hr := congrArg (PMF.map fun x => x.2.2) hreal
    rw [PMF.map_comp] at hs hr
    exact hs.trans hr.symm
  simp only [h1]
  have h2 : ∀ (t : ℕ) (i : Msg × Sc × Sc) (rk : RK),
      (OracleAdv.run (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k unifRoot)
        (A.play t (i.1, 0)) (((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)), false)).map
          (fun x => x.2.2) =
      (PMF.uniformFintype RK).bind fun rkS => (PMF.uniformFintype Sa).bind fun sa =>
        (OracleAdv.run (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k
          (constRoot (Key := Key) (rkS, sa))) (A.play t (i.1, 0))
          (((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)), false)).map fun x => x.2.2 := by
    intro t i rk
    rw [acdIDHop_run_eager_unif, PMF.map_bind, PMF.uniform_prod_eq_bind, PMF.bind_bind]
    refine congrArg _ (funext fun rkS => ?_)
    rw [PMF.bind_map]
    rfl
  simp only [h2, PMF.bind_comm (PMF.uniformFintype Sa)]

omit [SampleableType Kt] in
/-- **The ideal side of the FS-AEAD integrity hop.** Against the integrity game with
decryption from its log, the reduction `acdIDFSRed` never outputs `true`. -/
theorem acdIDFS_ideal_eq_zero (C : CKADef Sc Msg Key) [CKACoins C Rand] {J : Sc → Sc → Prop}
    (hJ : CKACorrect C J) (initP : PMF (Msg × Sc × Sc))
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg) Kt) (dec : W → W × ACDHdr Msg)
    (enc : ACDHdr Msg → W → W) (hdec : ∀ h a, dec (enc h a) = (a, h)) (maxSkip maxStored : ℕ)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS) (k : ℕ)
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg Kt)) :
    prTrue (fsaead_int_game G (aeadComapAD D dec) true
      (acdIDFSRed C R G D dec enc maxSkip maxStored ΔFS ΔPCS k initP A)) Heap.empty = 0 := by
  unfold fsaead_int_game
  rw [prTrue_liftPMF, PMF.apply_eq_zero_iff]
  simp only [PMF.support_bind, Set.mem_iUnion, not_exists]
  intro sa _
  rw [acdIDFSRed, acdIDFSTree_run]
  simp only [PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image, not_exists,
    not_and]
  intro t _ i hi rk _ rkS _ x hx
  have h := OracleAdv.run_support_inv _
    (fun z => ACDIDFSInv C J G enc k rkS sa z ∧ z.1.2 = false)
    (fun z d y hz hy => ⟨acdIDFS_inv C R G D dec enc hdec maxSkip maxStored hJ hFS hPCS t k rkS
      sa (Classical.arbitrary Sa) true z hz.1 d y hy, acdIDFS_ideal_flag C R G D dec enc hdec
      maxSkip maxStored ΔFS ΔPCS t k rkS sa (Classical.arbitrary Sa) z hz.1 hz.2 d y hy⟩)
    (A.play t (i.1, 0)) _
    ⟨acdIDFSInv_init C G enc k rkS rk i (hJi i hi) sa, rfl⟩ x hx
  simp [h.2]

omit [SampleableType Kt] in
/-- **The FS-AEAD integrity hop of the forgery event at the epoch `k`** over `acdIDSM`: the
probability of a forgery at the epoch `k` in the hop game with a uniform root output at the epoch
`k` is at most the FS-AEAD integrity advantage of `G` and `aeadComapAD D dec` at the reduction
`acdIDFSRed … k initP A`. -/
theorem acdIDHopGame_le_fsint (C : CKADef Sc Msg Key) [CKACoins C Rand] {J : Sc → Sc → Prop}
    (hJ : CKACorrect C J) (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg) Kt) (dec : W → W × ACDHdr Msg)
    (enc : ACDHdr Msg → W → W) (hdec : ∀ h a, dec (enc h a) = (a, h)) (maxSkip maxStored : ℕ)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS) (k : ℕ)
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg Kt)) :
    prTrue (acdIDHopGame C R G D dec enc maxSkip maxStored ΔFS ΔPCS k unifRoot A) Heap.empty ≤
      FSAEAD_Int_Advantage G (aeadComapAD D dec)
        (acdIDFSRed C R G D dec enc maxSkip maxStored ΔFS ΔPCS k initP A) := by
  rw [← acdIDFS_real_eq C hJ initP hinit hJi R G D dec enc hdec maxSkip maxStored hFS hPCS k A]
  have h0 := acdIDFS_ideal_eq_zero C hJ initP hJi R G D dec enc hdec maxSkip maxStored hFS hPCS k A
  unfold FSAEAD_Int_Advantage Advantage
  simp [h0]

variable [DecidableEq RK] [DecidableEq Key] [Fintype Key] [Nonempty Key]

omit [SampleableType Kt] in
/-- **Integrity of the ACD construction with headers.** For a CKA correct along `J` with a sound
explicit-randomness sending algorithm, an initialisation that is the lift of `initP` with initial
states related by `J`, `dec` a left inverse of `enc`, `2 ≤ ΔFS`, `1 ≤ ΔPCS`, and an adversary `A`
whose interactions ask at most `N` queries, the integrity advantage of `A` against
`acdIDSM C R G D dec enc maxSkip maxStored` is at most the sum over the epochs `k < N` of the
CKA corruption advantage of `acdIDCKARed … k A`, the PRF-PRNG advantage of `R` at
`acdIDRootRed … k initP A`, and the FS-AEAD integrity advantage of `G` and `aeadComapAD D dec` at
`acdIDFSRed … k initP A`. -/
theorem acdIDSM_intAdvantage_le (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hS : CKACoins.Sound C) {J : Sc → Sc → Prop} (hJ : CKACorrect C J)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg) Kt) (dec : W → W × ACDHdr Msg)
    (enc : ACDHdr Msg → W → W) (hdec : ∀ h a, dec (enc h a) = (a, h)) (maxSkip maxStored : ℕ)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS) (N : ℕ)
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg Kt))
    (hA : ∀ t pub, (A.play t pub).IsQueryBound N) :
    (acdIDSM C R G D dec enc maxSkip maxStored).intAdvantage ΔFS ΔPCS A ≤
      ∑ k ∈ Finset.range N,
        (CKA_Corrupt_Advantage C ΔFS ΔPCS
            (acdIDCKARed R G D dec enc maxSkip maxStored ΔFS ΔPCS k A) +
          PRFPRNG_Advantage R
            (acdIDRootRed C R G D dec enc maxSkip maxStored ΔFS ΔPCS k initP A) +
          FSAEAD_Int_Advantage G (aeadComapAD D dec)
            (acdIDFSRed C R G D dec enc maxSkip maxStored ΔFS ΔPCS k initP A)) :=
  (acdIDSM_intAdvantage_le_unifRoot C hS hJ initP hinit hJi R G D dec enc maxSkip maxStored ΔFS
    ΔPCS N A hA).trans (Finset.sum_le_sum fun k _ => add_le_add le_rfl
      (acdIDHopGame_le_fsint C hJ initP hinit hJi R G D dec enc hdec maxSkip maxStored hFS hPCS k
        A))

end IntGame

end CatCrypt.Crypto.Messaging
