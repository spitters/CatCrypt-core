/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMCorrupt
public import CatCryptCore.Crypto.Messaging.CKAPrekey

/-!
# Secure messaging with state corruption at a given initial key pair

The secure-messaging game of the CKA `C.atInit i` starts the CKA at the fixed pair `i`. For the
Diffie–Hellman CKA at the signed-prekey pair `dhPairInit decE x₀` the CKA bound holds for
challenge epochs at least `2` only (`dhCKAOf_atInit_corrupt_advantage_le`); the secrecy of the
challenge epoch `1` rests on the initial root key.

* Challenge epoch `1`. With `2 ≤ ΔPCS` no corruption is answered to a party at counter `0`, so
  the initial root key is used only by the root step of epoch `1`. The PRF-PRNG reduction
  `smcRootRedFirst` asks that step as the `prng` query of the PRF-PRNG game, whose hidden root
  state is the initial root key (`sm_corrupt_advantage_le_first`).
* Split of the challenge epoch. The adversary `A.first` has the challenge epoch `1`, the
  adversary `A.later` the distribution of the challenge epoch of `A` conditioned on `t ≥ 2`. A
  challenge epoch `0` admits no challenge. The advantage of `A` is at most the sum of the
  advantages of `A.first` and `A.later` (`SM_Corrupt_Advantage_le_split`).
* The Diffie–Hellman double ratchet at the signed-prekey pair: the first-epoch terms of
  `A.first`, and the terms of `sm_corrupt_advantage_le` with the DDH bound at the pair for
  `A.later` (`sm_dh_corrupt_advantage_le_pair`).

## Main results

* `smRootRatchetFirst`, `smRootImplFirst`, `smRootTreeFirst`, `smcRootRedFirst` — the
  PRF-PRNG reduction of the first epoch
* `sm_corrupt_advantage_le_first` — the bound at challenge epoch `1`
* `SMCorruptAdv.first`, `SMCorruptAdv.later`, `SM_Corrupt_Advantage_le_split` — the split
* `sm_dh_corrupt_advantage_le_pair` — the Diffie–Hellman double ratchet at the prekey pair
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
  CatCryptCore.Examples.CyclicGroupDDH
open scoped ENNReal

/-! ## The PRF-PRNG reduction of the first epoch -/

section RootFirst

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct]

/-- The opening of an epoch by party `p` in the simulator of the first-epoch root hop: at the
challenge epoch `t`, the root step is the `prng` query of the PRF-PRNG game at the CKA key; every
other opening is that of `smRootRatchet`. -/
noncomputable def smRootRatchetFirst (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (t : ℕ) (s : SMSt Sc Msg RK Sa) (p : CKAParty) :
    OracleAdv (PPQuery RK Key) (RK × Sa) (SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa) :=
  if s.ck.canSend p && (s.ck.t p + 1 == t) then
    .rand (PMF.uniformFintype Rand) fun r =>
      .query (.prng (CKACoins.sendR (C := C) (s.ck.st p) r).2.2) fun y =>
        .ret (.msg (CKACoins.sendR (C := C) (s.ck.st p) r).2.1,
          ⟨s.ck.sent p (CKACoins.sendR (C := C) (s.ck.st p) r).1
            (CKACoins.sendR (C := C) (s.ck.st p) r).2.1, s.loc.opened p y⟩)
  else smRootRatchet C R t s p

/-- The simulator of the first-epoch root hop with the challenge epoch `t`: the simulator
`smRootImplOf` with the root step at the challenge epoch asked to the `prng` oracle. -/
noncomputable def smRootImplFirst (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (s : SMSt Sc Msg RK Sa) (q : SMQuery W) :
    OracleAdv (PPQuery RK Key) (RK × Sa) (SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa) :=
  match q with
  | .ratchet p => smRootRatchetFirst C R t s p
  | .recv p => smRootRecv C s p
  | .send p m => smFullSend G D s p m
  | .chall p m => smFullChall G D t ideal s p m
  | .corrupt p => smFullCorr ΔFS ΔPCS t s p

/-- **The PRF-PRNG reduction tree of the first epoch** at the initial pair `i`: it draws the
challenge epoch of the adversary and a root key, and runs the adversary against the simulator
`smRootImplFirst` from the pair `i`. The drawn root key is never read at challenge epoch `1`;
the initial root key of the game is the hidden root state of the PRF-PRNG game. -/
noncomputable def smRootTreeFirst (C : CKADef Sc Msg Key) [CKACoins C Rand] [Fintype RK]
    [Nonempty RK] (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (i : Msg × Sc × Sc) (tStar : PMF ℕ)
    (play : ℕ → Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool) :
    OracleAdv (PPQuery RK Key) (RK × Sa) Bool :=
  .rand tStar fun t =>
    .rand (PMF.uniformFintype RK) fun rk =>
      (OracleAdv.simulate (smRootImplFirst C R G D ΔFS ΔPCS t ideal) (play t i.1)
        (smInit i rk)).bind fun r => .ret r.1

/-- **The PRF-PRNG reduction of the first epoch** `smcRootRedFirst C R G D ΔFS ΔPCS ideal i A`:
the tree `smRootTreeFirst` at the pair `i` and the interaction of `A`. -/
noncomputable def smcRootRedFirst (C : CKADef Sc Msg Key) [CKACoins C Rand] [Fintype RK]
    [Nonempty RK] (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (i : Msg × Sc × Sc) (A : SMCorruptAdv Sc Msg RK Sa W Ct) :
    OracleAdv (PPQuery RK Key) (RK × Sa) Bool :=
  smRootTreeFirst C R G D ΔFS ΔPCS ideal i A.tStar A.play

/-- The game state seen from the simulator state `s` with the hidden root key `rk`: the parties
at counter `0` hold `rk`. -/
def smFirstAbs (rk : RK) (s : SMSt Sc Msg RK Sa) : SMSt Sc Msg RK Sa :=
  ⟨s.ck, { s.loc with rk := fun p => if s.ck.t p = 0 then rk else s.loc.rk p }⟩

/-- No root output is in transit only while both counters are `0`. -/
def smOutInv (s : SMSt Sc Msg RK Sa) : Prop := s.loc.out = none → ∀ p, s.ck.t p = 0

/-- Unfolding lemma of `smFirstAbs`: the CKA part is unchanged. -/
@[simp] theorem smFirstAbs_ck (rk : RK) (s : SMSt Sc Msg RK Sa) : (smFirstAbs rk s).ck = s.ck :=
  rfl

/-- A party past counter `0` keeps its root key under `smFirstAbs`. -/
theorem smFirstAbs_rk_of_ne (rk : RK) (s : SMSt Sc Msg RK Sa) {p : CKAParty}
    (h : s.ck.t p ≠ 0) : (smFirstAbs rk s).loc.rk p = s.loc.rk p := by
  simp [smFirstAbs, h]

/-- A party at counter `0` holds the hidden root key under `smFirstAbs`. -/
theorem smFirstAbs_rk_of_eq (rk : RK) (s : SMSt Sc Msg RK Sa) {p : CKAParty}
    (h : s.ck.t p = 0) : (smFirstAbs rk s).loc.rk p = rk := by
  simp [smFirstAbs, h]

/-- Unfolding lemma of `smFirstAbs`: the chains, the output in transit and the flag. -/
@[simp] theorem smFirstAbs_loc (rk : RK) (s : SMSt Sc Msg RK Sa) :
    (smFirstAbs rk s).loc.snd = s.loc.snd ∧ (smFirstAbs rk s).loc.rcv = s.loc.rcv ∧
      (smFirstAbs rk s).loc.out = s.loc.out ∧ (smFirstAbs rk s).loc.done = s.loc.done :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Unfolding lemma of `smFirstAbs` at an advanced sending chain. -/
theorem smFirstAbs_advanced (rk : RK) (s : SMSt Sc Msg RK Sa) (p : CKAParty) (sa : Sa) :
    smFirstAbs rk ⟨s.ck, s.loc.advanced p sa⟩ = ⟨s.ck, (smFirstAbs rk s).loc.advanced p sa⟩ :=
  rfl

/-- Unfolding lemma of `smFirstAbs` at an advanced sending chain after the challenge. -/
theorem smFirstAbs_advanced_done (rk : RK) (s : SMSt Sc Msg RK Sa) (p : CKAParty) (sa : Sa) :
    smFirstAbs rk ⟨s.ck, { s.loc.advanced p sa with done := true }⟩ =
      ⟨s.ck, { (smFirstAbs rk s).loc.advanced p sa with done := true }⟩ :=
  rfl

/-- The initial state seen with the hidden root key `rk` is the initial state with root key
`rk`. -/
theorem smFirstAbs_init (rk rk' : RK) (i : Msg × Sc × Sc) :
    smFirstAbs rk (smInit (Sa := Sa) i rk') = smInit i rk := by
  simp [smFirstAbs, smInit, SMLoc.init, CKAGameSt.init]

/-- `smFirstAbs` commutes with the opening of an epoch. -/
theorem smFirstAbs_sent_opened (rk : RK) (s : SMSt Sc Msg RK Sa) (p : CKAParty) (x : Sc)
    (T : Msg) (y : RK × Sa) :
    smFirstAbs rk ⟨s.ck.sent p x T, s.loc.opened p y⟩ =
      ⟨s.ck.sent p x T, (smFirstAbs rk s).loc.opened p y⟩ := by
  simp only [smFirstAbs, SMLoc.opened, CKAGameSt.sent, SMSt.mk.injEq, true_and]
  congr 1
  funext q
  by_cases h : q = p
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- `smFirstAbs` commutes with the receipt of a root output. -/
theorem smFirstAbs_recvd_recvY (rk : RK) (s : SMSt Sc Msg RK Sa) (p : CKAParty) (x : Sc)
    (y : RK × Sa) :
    smFirstAbs rk ⟨s.ck.recvd p x, s.loc.recvY p y⟩ =
      ⟨s.ck.recvd p x, (smFirstAbs rk s).loc.recvY p y⟩ := by
  simp only [smFirstAbs, SMLoc.recvY, CKAGameSt.recvd, SMSt.mk.injEq, true_and]
  congr 1
  funext q
  by_cases h : q = p
  · subst h; simp
  · simp [Function.update_of_ne h]

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] in
/-- A corruption answered at challenge epoch `1` with `2 ≤ ΔPCS` is of a party past counter
`0`. -/
theorem ne_zero_of_allowCorr_one {St M : Type} {ΔFS ΔPCS : ℕ} (hPCS : 2 ≤ ΔPCS)
    {s : CKAGameSt St M} {p : CKAParty} (h : ckaAllowCorr ΔFS ΔPCS 1 s p = true) :
    s.t p ≠ 0 := by
  simp only [ckaAllowCorr, Bool.or_eq_true, decide_eq_true_eq] at h
  omega

/-- Every call of the secure-messaging oracle keeps `smOutInv`. -/
theorem smOracleOf_outInv (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa)) (s : SMSt Sc Msg RK Sa)
    (hs : smOutInv s) (q : SMQuery W) (x)
    (hx : x ∈ (smOracleOf C R G D ΔFS ΔPCS t ideal root s q).support) : smOutInv x.2 := by
  cases q with
  | ratchet p =>
    simp only [smOracleOf] at hx
    split at hx
    · simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff]
        at hx
      obtain ⟨r, -, y, -, rfl⟩ := hx
      intro h
      simp [SMLoc.opened] at h
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]; exact hs
  | recv p =>
    simp only [smOracleOf] at hx
    split at hx
    · rename_i hr
      simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]
      intro h
      have hn : s.loc.out = none := by
        cases ho : s.loc.out <;> simp_all [SMLoc.received, SMLoc.recvY]
      have h0 := hs hn
      simp only [CKAGameSt.canRecv, beq_iff_eq] at hr
      have := h0 p.other
      omega
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]; exact hs
  | send p m =>
    simp only [smOracleOf] at hx
    split at hx
    · split at hx <;> simp only [PMF.support_pure, Set.mem_singleton_iff] at hx <;> rw [hx] <;>
        exact hs
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]; exact hs
  | chall p m =>
    simp only [smOracleOf] at hx
    split at hx
    · split at hx
      · simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff]
          at hx
        obtain ⟨c, -, rfl⟩ := hx
        exact hs
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
        rw [hx]; exact hs
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]; exact hs
  | corrupt p =>
    simp only [smOracleOf, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]; exact hs

/-- Away from the opening of the challenge epoch `1`, the simulator of the first-epoch root hop
asks no query and answers, through `smFirstAbs`, as the secure-messaging oracle with any root
step at the challenge epoch. -/
theorem smRootFirst_step_noncrit (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    {ΔFS ΔPCS : ℕ} (hPCS : 2 ≤ ΔPCS) (ideal : Bool) (root : RK → Key → PMF (RK × Sa))
    (O' : PPSt RK Key (RK × Sa) → PPQuery RK Key → PMF ((RK × Sa) × PPSt RK Key (RK × Sa)))
    (s : SMSt Sc Msg RK Sa) (u : PPSt RK Key (RK × Sa)) (hs : smOutInv s) (q : SMQuery W)
    (hc : smCrit 1 s q = false) :
    (OracleAdv.simOracle (smRootImplFirst C R G D ΔFS ΔPCS 1 ideal) O' (s, u) q).map
        (Prod.map id fun x => smFirstAbs x.2.rk x.1) =
      smOracleOf C R G D ΔFS ΔPCS 1 ideal root (smFirstAbs u.rk s) q := by
  cases q with
  | ratchet p =>
    simp only [smCrit] at hc
    simp only [OracleAdv.simOracle, smRootImplFirst, smRootRatchetFirst, hc, smRootRatchet,
      smOracleOf]
    simp only [Bool.and_eq_false_iff] at hc
    by_cases hs' : s.ck.canSend p = true
    · have h0 : s.ck.t p ≠ 0 := by
        rcases hc with h | h
        · simp [hs'] at h
        · simpa using h
      have h1 : (s.ck.t p + 1 == 1) = false := by simpa using h0
      simp only [hs', h1, ite_true, Bool.false_eq_true, ite_false, smFirstAbs_ck,
        smFirstAbs_rk_of_ne u.rk s h0, OracleAdv.run_rand, OracleAdv.run_ret, PMF.map_bind,
        PMF.pure_bind, PMF.pure_map, Prod.map, id, smFirstAbs_sent_opened]
    · grind only [smFirstAbs_ck, OracleAdv.run_ret, PMF.pure_map, = Prod.map_fst, = Prod.map_snd,
        = id.eq_1]
  | recv p =>
    simp only [OracleAdv.simOracle, smRootImplFirst, smRootRecv, smOracleOf, smFirstAbs_ck]
    by_cases h : s.ck.canRecv p = true
    · cases ho : s.loc.out with
      | none =>
        exfalso
        have h0 := hs ho
        simp only [CKAGameSt.canRecv, beq_iff_eq] at h
        have := h0 p.other
        omega
      | some y =>
        simp [h, ho, SMLoc.received, OracleAdv.run_ret, PMF.pure_map, smFirstAbs_recvd_recvY]
    · simp [h, OracleAdv.run_ret, PMF.pure_map]
  | send p m =>
    simp only [OracleAdv.simOracle, smRootImplFirst, smFullSend, smOracleOf, smFirstAbs_ck,
      smFirstAbs_loc]
    cases h : s.loc.snd p
    · simp [OracleAdv.run_ret, PMF.pure_map]
    · by_cases hc : ckaSender (s.ck.t p) = p <;>
        simp [hc, OracleAdv.run_ret, PMF.pure_map, smFirstAbs_advanced]
  | chall p m =>
    simp only [OracleAdv.simOracle, smRootImplFirst, smFullChall, smOracleOf, smFirstAbs_ck,
      smFirstAbs_loc, challOk]
    cases h : s.loc.snd p
    · simp [OracleAdv.run_ret, PMF.pure_map]
    · by_cases hc : (!s.loc.done && (ckaSender (s.ck.t p) == p) && (s.ck.t p == 1)) = true <;>
        simp [hc, OracleAdv.run_ret, OracleAdv.run_rand, PMF.pure_map, PMF.map_bind,
          smFirstAbs_advanced_done]
  | corrupt p =>
    simp only [OracleAdv.simOracle, smRootImplFirst, smFullCorr, smOracleOf, smFirstAbs_ck,
      smFirstAbs_loc]
    by_cases h : ckaAllowCorr ΔFS ΔPCS 1 s.ck p = true
    · simp [h, OracleAdv.run_ret, PMF.pure_map,
        smFirstAbs_rk_of_ne u.rk s (ne_zero_of_allowCorr_one hPCS h)]
    · simp [h, OracleAdv.run_ret, PMF.pure_map]

/-- Away from the opening of the challenge epoch, the simulator of the first-epoch root hop is
the simulator of the root hop. -/
theorem smRootImplFirst_noncrit (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (s : SMSt Sc Msg RK Sa) (q : SMQuery W)
    (hc : smCrit t s q = false) :
    smRootImplFirst C R G D ΔFS ΔPCS t ideal s q = smRootImplOf C R G D ΔFS ΔPCS t ideal s q := by
  cases q with
  | ratchet p =>
    simp only [smCrit] at hc
    simp only [smRootImplFirst, smRootRatchetFirst, hc, smRootImplOf, Bool.false_eq_true,
      ite_false]
  | _ => rfl

/-- A state map step of the first-epoch root hop keeps `smOutInv`. -/
theorem smRootFirst_outInv_of_step (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa))
    (O' : PPSt RK Key (RK × Sa) → PPQuery RK Key → PMF ((RK × Sa) × PPSt RK Key (RK × Sa)))
    (x : SMSt Sc Msg RK Sa × PPSt RK Key (RK × Sa)) (q : SMQuery W) (hx : smOutInv x.1)
    (hO : (OracleAdv.simOracle (smRootImplFirst C R G D ΔFS ΔPCS 1 ideal) O' x q).map
        (Prod.map id fun x => smFirstAbs x.2.rk x.1) =
      smOracleOf C R G D ΔFS ΔPCS 1 ideal root (smFirstAbs x.2.rk x.1) q) :
    ∀ y ∈ (OracleAdv.simOracle (smRootImplFirst C R G D ΔFS ΔPCS 1 ideal) O' x q).support,
      smOutInv y.2.1 := by
  intro y hy
  have hm : (y.1, smFirstAbs y.2.2.rk y.2.1) ∈
      (smOracleOf C R G D ΔFS ΔPCS 1 ideal root (smFirstAbs x.2.rk x.1) q).support := by
    rw [← hO, PMF.support_map]
    exact ⟨y, hy, rfl⟩
  have hx' : smOutInv (smFirstAbs x.2.rk x.1) := by simpa [smOutInv] using hx
  have h := smOracleOf_outInv C R G D ΔFS ΔPCS 1 ideal root _ hx' q _ hm
  simpa [smOutInv] using h

variable [Fintype RK] [Nonempty RK] [Fintype Sa] [Nonempty Sa] [DecidableEq RK]
  [DecidableEq Key]

/-- **The simulator against the real PRF-PRNG game.** With the hidden root state `u.rk`, each
call of the simulator of the first-epoch root hop against the real PRF-PRNG oracle is, through
`smFirstAbs`, the call of the real game. -/
theorem smRootFirst_step_real (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    {ΔFS ΔPCS : ℕ} (hPCS : 2 ≤ ΔPCS) (ideal : Bool) (s : SMSt Sc Msg RK Sa)
    (u : PPSt RK Key (RK × Sa)) (hs : smOutInv s) (q : SMQuery W) :
    (OracleAdv.simOracle (smRootImplFirst C R G D ΔFS ΔPCS 1 ideal)
        (ppOracle (rootFn R) false false) (s, u) q).map
        (Prod.map id fun x => smFirstAbs x.2.rk x.1) =
      smOracleOf C R G D ΔFS ΔPCS 1 ideal (realRoot R) (smFirstAbs u.rk s) q := by
  cases hc : smCrit 1 s q
  · exact smRootFirst_step_noncrit C R G D hPCS ideal _ _ s u hs q hc
  · cases q with
    | ratchet p =>
      have hc' := hc
      simp only [smCrit, Bool.and_eq_true, beq_iff_eq] at hc'
      have h0 : s.ck.t p = 0 := by omega
      simp only [OracleAdv.simOracle, smRootImplFirst, smRootRatchetFirst, smOracleOf,
        smFirstAbs_ck, hc'.1, h0, smFirstAbs_rk_of_eq u.rk s h0]
      simp [OracleAdv.run_rand, OracleAdv.run_query, OracleAdv.run_ret, ppOracle, rootFn,
        realRoot, PMF.map_bind, PMF.pure_bind, PMF.pure_map, smFirstAbs_sent_opened]
    | _ => simp [smCrit] at hc

/-- **The simulator against the ideal PRF-PRNG game.** From a state whose table of the `prng`
oracle is empty, each call of the simulator of the first-epoch root hop against the ideal
PRF-PRNG oracle is, through `smFirstAbs`, the call of the game with a uniform root output at the
challenge epoch `1`. -/
theorem smRootFirst_step_ideal (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    {ΔFS ΔPCS : ℕ} (hPCS : 2 ≤ ΔPCS) (ideal : Bool) (s : SMSt Sc Msg RK Sa)
    (u : PPSt RK Key (RK × Sa)) (hs : smOutInv s) (hu : u.tL = [] ∨ smOpened 1 s)
    (q : SMQuery W) :
    (OracleAdv.simOracle (smRootImplFirst C R G D ΔFS ΔPCS 1 ideal)
        (ppOracle (rootFn R) true true) (s, u) q).map
        (Prod.map id fun x => smFirstAbs x.2.rk x.1) =
      smOracleOf C R G D ΔFS ΔPCS 1 ideal unifRoot (smFirstAbs u.rk s) q := by
  cases hc : smCrit 1 s q
  · exact smRootFirst_step_noncrit C R G D hPCS ideal _ _ s u hs q hc
  · have hu' : u.tL = [] := by
      rcases hu with h | h
      · exact h
      · rw [smCrit_of_opened 1 s h q] at hc; exact absurd hc (by decide)
    cases q with
    | ratchet p =>
      have hc' := hc
      simp only [smCrit, Bool.and_eq_true, beq_iff_eq] at hc'
      have h0 : s.ck.t p = 0 := by omega
      simp only [OracleAdv.simOracle, smRootImplFirst, smRootRatchetFirst, smOracleOf,
        smFirstAbs_ck, hc'.1, h0, smFirstAbs_rk_of_eq u.rk s h0]
      simp [OracleAdv.run_rand, OracleAdv.run_query, OracleAdv.run_ret, ppOracle,
        PRPPRF.rfOracle, hu', unifRoot, PMF.map_bind, PMF.bind_map, PMF.pure_map,
        Function.comp_def, smFirstAbs_sent_opened]
    | _ => simp [smCrit] at hc

variable [Fintype Key] [Nonempty Key]

omit [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [DecidableEq Key] in
/-- The game of `C.atInit i` with the root step `root` at the challenge epoch, as a lifted
distribution. -/
theorem sm_corrupt_gameOf_atInit_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (i : Msg × Sc × Sc) (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (ΔFS ΔPCS : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa))
    (A : SMCorruptAdv Sc Msg RK Sa W Ct) :
    sm_corrupt_gameOf (C.atInit i) R G D ΔFS ΔPCS ideal root A =
      liftPMF (A.tStar.bind fun t => (PMF.uniformFintype RK).bind fun rk =>
        (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal root) (A.play t i.1)
          (smInit i rk)).map Prod.fst) := by
  rw [sm_corrupt_gameOf_eq_liftPMF (C.atInit i) (PMF.pure i) (liftPMF_pure i)]
  simp only [PMF.pure_bind]
  rfl

/-- **The real side of the first-epoch root hop.** At challenge epoch `1`, the real PRF-PRNG
game of `smcRootRedFirst` is the real game of `C.atInit i`. -/
theorem smRootFirst_real_eq (C : CKADef Sc Msg Key) [CKACoins C Rand] (i : Msg × Sc × Sc)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    {ΔFS ΔPCS : ℕ} (hPCS : 2 ≤ ΔPCS) (ideal : Bool) (A : SMCorruptAdv Sc Msg RK Sa W Ct)
    (hA : A.tStar = PMF.pure 1) :
    pp_game (rootFn R) false false (smcRootRedFirst C R G D ΔFS ΔPCS ideal i A) =
      sm_corrupt_gameOf (C.atInit i) R G D ΔFS ΔPCS ideal (realRoot R) A := by
  rw [sm_corrupt_gameOf_atInit_eq]
  unfold pp_game
  congr 1
  have h1 : ∀ (rk' : RK) (k : Key),
      (OracleAdv.run (ppOracle (rootFn R) false false)
        (smcRootRedFirst C R G D ΔFS ΔPCS ideal i A) ⟨rk', k, [], []⟩).map Prod.fst =
      (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS 1 ideal (realRoot R)) (A.play 1 i.1)
        (smInit i rk')).map Prod.fst := by
    intro rk' k
    simp only [smcRootRedFirst, smRootTreeFirst, hA, OracleAdv.run_rand, PMF.pure_bind,
      PMF.map_bind, OracleAdv.run_simulate_fst]
    have h2 : ∀ rk : RK,
        (OracleAdv.run (OracleAdv.simOracle (smRootImplFirst C R G D ΔFS ΔPCS 1 ideal)
          (ppOracle (rootFn R) false false)) (A.play 1 i.1)
          (smInit i rk, (⟨rk', k, [], []⟩ : PPSt RK Key (RK × Sa)))).map Prod.fst =
        (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS 1 ideal (realRoot R)) (A.play 1 i.1)
          (smInit i rk')).map Prod.fst := by
      intro rk
      rw [OracleAdv.run_map_fst_of_map_state_inv _ _ (fun x => smFirstAbs x.2.rk x.1)
        (fun x => smOutInv x.1)
        (fun x q hx => smRootFirst_outInv_of_step C R G D ΔFS ΔPCS ideal (realRoot R) _ x q hx
          (smRootFirst_step_real C R G D hPCS ideal x.1 x.2 hx q))
        (fun x q hx => smRootFirst_step_real C R G D hPCS ideal x.1 x.2 hx q) _ _
        (fun _ _ => rfl), smFirstAbs_init]
    simp only [h2, PMF.bind_const]
  simp only [h1, PMF.bind_const, hA, PMF.pure_bind]

/-- **The ideal side of the first-epoch root hop.** At challenge epoch `1`, the ideal PRF-PRNG
game of `smcRootRedFirst` is the game of `C.atInit i` with a uniform root output at the
challenge epoch. -/
theorem smRootFirst_ideal_eq (C : CKADef Sc Msg Key) [CKACoins C Rand] (i : Msg × Sc × Sc)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    {ΔFS ΔPCS : ℕ} (hPCS : 2 ≤ ΔPCS) (ideal : Bool) (A : SMCorruptAdv Sc Msg RK Sa W Ct)
    (hA : A.tStar = PMF.pure 1) :
    pp_game (rootFn R) true true (smcRootRedFirst C R G D ΔFS ΔPCS ideal i A) =
      sm_corrupt_gameOf (C.atInit i) R G D ΔFS ΔPCS ideal unifRoot A := by
  rw [sm_corrupt_gameOf_atInit_eq]
  unfold pp_game
  congr 1
  have h1 : ∀ (rk' : RK) (k : Key),
      (OracleAdv.run (ppOracle (rootFn R) true true)
        (smcRootRedFirst C R G D ΔFS ΔPCS ideal i A) ⟨rk', k, [], []⟩).map Prod.fst =
      (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS 1 ideal unifRoot) (A.play 1 i.1)
        (smInit i rk')).map Prod.fst := by
    intro rk' k
    simp only [smcRootRedFirst, smRootTreeFirst, hA, OracleAdv.run_rand, PMF.pure_bind,
      PMF.map_bind, OracleAdv.run_simulate_fst]
    have h2 : ∀ rk : RK,
        (OracleAdv.run (OracleAdv.simOracle (smRootImplFirst C R G D ΔFS ΔPCS 1 ideal)
          (ppOracle (rootFn R) true true)) (A.play 1 i.1)
          (smInit i rk, (⟨rk', k, [], []⟩ : PPSt RK Key (RK × Sa)))).map Prod.fst =
        (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS 1 ideal unifRoot) (A.play 1 i.1)
          (smInit i rk')).map Prod.fst := by
      intro rk
      rw [OracleAdv.run_map_fst_of_map_state_inv _ _ (fun x => smFirstAbs x.2.rk x.1)
        (fun x => smOutInv x.1 ∧ (x.2.tL = [] ∨ smOpened 1 x.1)) ?_
        (fun x q hx => smRootFirst_step_ideal C R G D hPCS ideal x.1 x.2 hx.1 hx.2 q) _ _
        ⟨fun _ _ => rfl, Or.inl rfl⟩, smFirstAbs_init]
      intro x q hx y hy
      refine ⟨smRootFirst_outInv_of_step C R G D ΔFS ΔPCS ideal unifRoot _ x q hx.1
        (smRootFirst_step_ideal C R G D hPCS ideal x.1 x.2 hx.1 hx.2 q) y hy, ?_⟩
      obtain ⟨s, u⟩ := x
      cases hc : smCrit 1 s q
      · have e : OracleAdv.simOracle (smRootImplFirst C R G D ΔFS ΔPCS 1 ideal)
            (ppOracle (rootFn R) true true) (s, u) q =
            OracleAdv.simOracle (smRootImplOf C R G D ΔFS ΔPCS 1 ideal)
              (ppOracle (rootFn R) true true) (s, u) q := by
          simp only [OracleAdv.simOracle, smRootImplFirst_noncrit C R G D ΔFS ΔPCS 1 ideal s q hc]
        rw [e, smRoot_step_noncrit C R G D ΔFS ΔPCS 1 ideal unifRoot _ s u q hc,
          PMF.support_map] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        rcases hx.2 with h | h
        · exact Or.inl h
        · exact Or.inr (smOracleOf_opened C R G D ΔFS ΔPCS 1 ideal _ s q h z hz)
      · have hm : (y.1, smFirstAbs y.2.2.rk y.2.1) ∈
            (smOracleOf C R G D ΔFS ΔPCS 1 ideal unifRoot (smFirstAbs u.rk s) q).support := by
          rw [← smRootFirst_step_ideal C R G D hPCS ideal s u hx.1 hx.2 q, PMF.support_map]
          exact ⟨y, hy, rfl⟩
        have hc' : smCrit 1 (smFirstAbs u.rk s) q = true := by
          cases q with
          | ratchet p => simpa [smCrit] using hc
          | _ => simp [smCrit] at hc
        have h := smOracleOf_opened_of_crit C R G D ΔFS ΔPCS 1 ideal _ _ q hc' _ hm
        exact Or.inr (by simpa [smOpened] using h)
    simp only [h2, PMF.bind_const]
  simp only [h1, PMF.bind_const, hA, PMF.pure_bind]

/-- **Secure messaging at a given pair, challenge epoch `1`.** Let `2 ≤ ΔFS`, `2 ≤ ΔPCS`, and
let the challenge epoch of `A` be `1`. The advantage of `A` against the double ratchet of
`C.atInit i` is at most the PRF-PRNG advantages of `R` at the reductions
`smcRootRedFirst C R G D ΔFS ΔPCS b i A`, which ask the root step of epoch `1` on the hidden
initial root key as a `prng` query, plus the FS-AEAD advantage with corruption of `G` and `D` at
`smcFSRed C R G D ΔFS ΔPCS (PMF.pure i) A`. No CKA term occurs. -/
theorem sm_corrupt_advantage_le_first (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (i : Msg × Sc × Sc) (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS)
    (A : SMCorruptAdv Sc Msg RK Sa W Ct) (hA : A.tStar = PMF.pure 1) :
    SM_Corrupt_Advantage (C.atInit i) R G D ΔFS ΔPCS A ≤
      ∑ b : Bool, PRFPRNG_Advantage R (smcRootRedFirst C R G D ΔFS ΔPCS b i A) +
        FSAEAD_Corrupt_Advantage G D (smcFSRed C R G D ΔFS ΔPCS (PMF.pure i) A) := by
  have e2 : ∀ b, pp_game (rootFn R) true true (smcRootRedFirst C R G D ΔFS ΔPCS b i A) =
      fsaead_corrupt_game G D b (smcFSRed C R G D ΔFS ΔPCS (PMF.pure i) A) := fun b =>
    (smRootFirst_ideal_eq C i R G D hPCS b A hA).trans
      (smFS_game_eq (C.atInit i) (PMF.pure i) (liftPMF_pure i) R G D hFS (by omega) b A).symm
  have hP : ∀ b, Advantage (sm_corrupt_game (C.atInit i) R G D ΔFS ΔPCS b A)
      (fsaead_corrupt_game G D b (smcFSRed C R G D ΔFS ΔPCS (PMF.pure i) A)) =
      PRFPRNG_Advantage R (smcRootRedFirst C R G D ΔFS ΔPCS b i A) := fun b => by
    rw [← e2, PRFPRNG_Advantage, smRootFirst_real_eq C i R G D hPCS b A hA]
    rfl
  unfold SM_Corrupt_Advantage
  simp only [Fintype.sum_bool]
  clear e2
  hop_chain [hP false, hP true,
    (show Advantage (fsaead_corrupt_game G D false _) _ = FSAEAD_Corrupt_Advantage G D _ from rfl)]

end RootFirst

/-! ## The split of the challenge epoch -/

section Split

/-- The distribution `τ` conditioned on `t ≥ 2`; the point `2` if `τ` gives no mass there. -/
noncomputable def tStarLater (τ : PMF ℕ) : PMF ℕ :=
  open Classical in
  if h : ∃ t ∈ {t : ℕ | 2 ≤ t}, t ∈ τ.support then τ.filter {t | 2 ≤ t} h else PMF.pure 2

/-- The support of `tStarLater τ` lies in `t ≥ 2`. -/
theorem tStarLater_support (τ : PMF ℕ) : ∀ t ∈ (tStarLater τ).support, 2 ≤ t := by
  intro t ht
  unfold tStarLater at ht
  split at ht
  · rw [PMF.support_filter] at ht
    exact ht.1
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at ht
    omega

/-- The absolute difference of two sums with a common summand is at most the sum of the
absolute differences. -/
theorem absDiff_add_add_le (c x₀ x₁ y₀ y₁ : ℝ≥0∞) :
    (c + (x₀ + y₀) - (c + (x₁ + y₁))) ⊔ (c + (x₁ + y₁) - (c + (x₀ + y₀))) ≤
      ((x₀ - x₁) ⊔ (x₁ - x₀)) + ((y₀ - y₁) ⊔ (y₁ - y₀)) := by
  have key : ∀ a₀ a₁ b₀ b₁ : ℝ≥0∞, c + (a₀ + b₀) - (c + (a₁ + b₁)) ≤ (a₀ - a₁) + (b₀ - b₁) := by
    intro a₀ a₁ b₀ b₁
    refine (add_tsub_add_le_tsub_add_tsub).trans ?_
    rw [tsub_self, zero_add]
    exact add_tsub_add_le_tsub_add_tsub
  refine max_le ((key _ _ _ _).trans (add_le_add le_sup_left le_sup_left))
    ((key _ _ _ _).trans (add_le_add le_sup_right le_sup_right))

/-- Scaling by a weight at most `1` does not increase the absolute difference. -/
theorem absDiff_mul_le (w a b : ℝ≥0∞) (hw : w ≤ 1) :
    (w * a - w * b) ⊔ (w * b - w * a) ≤ (a - b) ⊔ (b - a) := by
  have key : ∀ x y : ℝ≥0∞, w * x - w * y ≤ x - y := by
    intro x y
    rw [tsub_le_iff_right]
    calc w * x ≤ w * ((x - y) + y) := by gcongr; exact le_tsub_add
      _ = w * (x - y) + w * y := mul_add _ _ _
      _ ≤ (x - y) + w * y := by gcongr; exact mul_le_of_le_one_left bot_le hw
  exact max_le_max (key a b) (key b a)

/-- **Split of a mixture over `ℕ`.** If the two families agree at `0`, the advantage between the
mixtures over `w` is at most the advantage at `1` plus the advantage between the mixtures over
`w` conditioned on `t ≥ 2`. -/
theorem advantage_bind_split (w : PMF ℕ) (g₀ g₁ : ℕ → PMF Bool) (h0 : g₀ 0 = g₁ 0) :
    Advantage (liftPMF (w.bind g₀)) (liftPMF (w.bind g₁)) ≤
      Advantage (liftPMF (g₀ 1)) (liftPMF (g₁ 1)) +
        Advantage (liftPMF ((tStarLater w).bind g₀)) (liftPMF ((tStarLater w).bind g₁)) := by
  classical
  set L : ℕ → ℝ≥0∞ := Set.indicator {t | 2 ≤ t} w with hL
  set S : ℝ≥0∞ := ∑' t, L t with hS
  have hdec : ∀ g : ℕ → PMF Bool, (w.bind g) true =
      w 0 * g 0 true + (w 1 * g 1 true + ∑' t, L t * g t true) := by
    intro g
    have hpt : ∀ t, w t * g t true = (if t = 0 then w 0 * g 0 true else 0) +
        ((if t = 1 then w 1 * g 1 true else 0) + L t * g t true) := by
      intro t
      rcases t with _ | _ | t <;> simp [hL]
    rw [PMF.bind_apply, tsum_congr hpt, ENNReal.tsum_add, ENNReal.tsum_add, tsum_ite_eq,
      tsum_ite_eq]
  have hlater : ∀ g : ℕ → PMF Bool, ∑' t, L t * g t true = S * ((tStarLater w).bind g) true := by
    intro g
    by_cases h : ∃ t ∈ {t : ℕ | 2 ≤ t}, t ∈ w.support
    · have hS0 : S ≠ 0 := by
        obtain ⟨t, ht, hts⟩ := h
        intro hz
        rw [hS, ENNReal.tsum_eq_zero] at hz
        have := hz t
        simp only [hL, Set.indicator_of_mem ht] at this
        exact (PMF.mem_support_iff _ _).1 hts this
      have hST : S ≠ ⊤ := by
        refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
        rw [hS, ← w.tsum_coe]
        exact ENNReal.tsum_le_tsum fun t => Set.indicator_le_self _ _ t
      simp only [tStarLater, h, dite_true, PMF.bind_apply, PMF.filter_apply]
      rw [← hL, ← hS]
      simp_rw [mul_right_comm _ S⁻¹, ENNReal.tsum_mul_right, mul_comm S, mul_assoc,
        ENNReal.inv_mul_cancel hS0 hST, mul_one]
    · have hz : ∀ t, L t = 0 := by
        intro t
        by_cases ht : 2 ≤ t
        · simp only [hL, Set.indicator_of_mem (show t ∈ {t : ℕ | 2 ≤ t} from ht)]
          exact (PMF.apply_eq_zero_iff _ _).2 fun hts => h ⟨t, ht, hts⟩
        · exact Set.indicator_of_notMem (show t ∉ {t : ℕ | 2 ≤ t} from ht) _
      have hS0 : S = 0 := by simp [hS, hz]
      simp [hz, hS0]
  have hw1 : w 1 ≤ 1 := PMF.coe_le_one w 1
  have hS1 : S ≤ 1 := by
    rw [hS, ← w.tsum_coe]
    exact ENNReal.tsum_le_tsum fun t => Set.indicator_le_self _ _ t
  simp only [Advantage, prTrue_liftPMF]
  rw [hdec g₀, hdec g₁, hlater g₀, hlater g₁, h0]
  exact (absDiff_add_add_le _ _ _ _ _).trans
    (add_le_add (absDiff_mul_le _ _ _ hw1) (absDiff_mul_le _ _ _ hS1))

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct]

/-- A party with a sending chain has opened an epoch. -/
def smSndInv (s : SMSt Sc Msg RK Sa) : Prop := ∀ p, s.loc.snd p ≠ none → 1 ≤ s.ck.t p

/-- Every call of the secure-messaging oracle keeps `smSndInv`. -/
theorem smOracleOf_sndInv (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa)) (s : SMSt Sc Msg RK Sa)
    (hs : smSndInv s) (q : SMQuery W) (x)
    (hx : x ∈ (smOracleOf C R G D ΔFS ΔPCS t ideal root s q).support) : smSndInv x.2 := by
  have hmono := smOracleOf_t_mono C R G D ΔFS ΔPCS t ideal root s q x hx
  intro p' hp'
  cases q with
  | ratchet p =>
    simp only [smOracleOf] at hx
    split at hx
    · simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff]
        at hx
      obtain ⟨r, -, y, -, rfl⟩ := hx
      by_cases h : p' = p
      · subst h
        simp [CKAGameSt.sent]
      · exact (hs p' (by simpa [SMLoc.opened, Function.update_of_ne h] using hp')).trans
          (hmono p')
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hs p' hp'
  | recv p =>
    simp only [smOracleOf] at hx
    split at hx <;> simp only [PMF.support_pure, Set.mem_singleton_iff] at hx <;> subst hx
    · refine (hs p' ?_).trans (hmono p')
      simp_all
    · exact hs p' hp'
  | send p m =>
    simp only [smOracleOf] at hx
    split at hx
    · rename_i sa hsa
      split at hx <;> simp only [PMF.support_pure, Set.mem_singleton_iff] at hx <;> subst hx
      · by_cases h : p' = p
        · subst h; exact hs p' (by simp [hsa])
        · exact hs p' (by simpa [SMLoc.advanced, Function.update_of_ne h] using hp')
      · exact hs p' hp'
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hs p' hp'
  | chall p m =>
    simp only [smOracleOf] at hx
    split at hx
    · rename_i sa hsa
      split at hx
      · simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff]
          at hx
        obtain ⟨c, -, rfl⟩ := hx
        by_cases h : p' = p
        · subst h; exact hs p' (by simp [hsa])
        · exact hs p' (by simpa [SMLoc.advanced, Function.update_of_ne h] using hp')
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
        subst hx; exact hs p' hp'
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hs p' hp'
  | corrupt p =>
    simp only [smOracleOf, PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact hs p' hp'

/-- **No challenge at epoch `0`.** Under `smSndInv`, the oracle with the challenge epoch `0` does
not depend on the challenge mode. -/
theorem smOracleOf_zero_ideal (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (root : RK → Key → PMF (RK × Sa)) (s : SMSt Sc Msg RK Sa)
    (hs : smSndInv s) (q : SMQuery W) :
    smOracleOf C R G D ΔFS ΔPCS 0 true root s q = smOracleOf C R G D ΔFS ΔPCS 0 false root s q := by
  cases q with
  | chall p m =>
    simp only [smOracleOf]
    cases h : s.loc.snd p with
    | none => rfl
    | some sa =>
      have h1 := hs p (by simp [h])
      have hc : challOk s.loc 0 (s.ck.t p) p = false := by
        simp only [challOk, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
        right; omega
      simp only [hc, Bool.false_eq_true, ite_false]
  | _ => rfl

variable [Fintype RK] [Nonempty RK]

/-- The adversary `A` with the challenge epoch `1`. -/
noncomputable def SMCorruptAdv.first (A : SMCorruptAdv Sc Msg RK Sa W Ct) :
    SMCorruptAdv Sc Msg RK Sa W Ct :=
  ⟨PMF.pure 1, A.play⟩

/-- The adversary `A` with its challenge epoch conditioned on `t ≥ 2` (`tStarLater`). -/
noncomputable def SMCorruptAdv.later (A : SMCorruptAdv Sc Msg RK Sa W Ct) :
    SMCorruptAdv Sc Msg RK Sa W Ct :=
  ⟨tStarLater A.tStar, A.play⟩

/-- **Split of the challenge epoch.** If the CKA initialisation of `C` is the lift of `initP`,
the advantage of `A` is at most the advantage of `A.first` (challenge epoch `1`) plus the
advantage of `A.later` (challenge epoch conditioned on `t ≥ 2`); the challenge epoch `0` admits no
challenge. -/
theorem SM_Corrupt_Advantage_le_split (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (A : SMCorruptAdv Sc Msg RK Sa W Ct) :
    SM_Corrupt_Advantage C R G D ΔFS ΔPCS A ≤
      SM_Corrupt_Advantage C R G D ΔFS ΔPCS A.first +
        SM_Corrupt_Advantage C R G D ΔFS ΔPCS A.later := by
  have h0 : ∀ i rk, (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS 0 false (realRoot R))
      (A.play 0 i.1) (smInit (Sa := Sa) i rk)).map Prod.fst =
      (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS 0 true (realRoot R))
        (A.play 0 i.1) (smInit i rk)).map Prod.fst := by
    intro i rk
    rw [OracleAdv.run_eq_run_of_inv (smOracleOf C R G D ΔFS ΔPCS 0 false (realRoot R)) _ smSndInv
      (fun s q hs x hx => smOracleOf_sndInv C R G D ΔFS ΔPCS 0 false _ s hs q x hx)
      (fun s q hs => smOracleOf_zero_ideal C R G D ΔFS ΔPCS _ s hs q) _ _
      (fun _ h => absurd rfl h)]
  have h := advantage_bind_split A.tStar
    (fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
      (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t false (realRoot R)) (A.play t i.1)
        (smInit i rk)).map Prod.fst)
    (fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
      (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t true (realRoot R)) (A.play t i.1)
        (smInit i rk)).map Prod.fst)
    (by simp only [h0])
  simp only [SM_Corrupt_Advantage, sm_corrupt_game, sm_corrupt_gameOf_eq_liftPMF C initP hinit]
  simpa only [SMCorruptAdv.first, SMCorruptAdv.later, PMF.pure_bind] using h

end Split

/-! ## The Diffie–Hellman double ratchet at the signed-prekey pair -/

section DHPair

variable {RK Sa W Ct : Type} [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK]
  [Fintype Sa] [Nonempty Sa] [DecidableEq RK]
  {G : Type} [CG : CyclicGroup G] [DecidableEq G] {Sk : Type} [Fintype Sk] [Nonempty Sk]
  [Inhabited Sk]

/-- **Secure messaging with state corruption for the Diffie–Hellman double ratchet at the
signed-prekey pair.** Let `c` be a sampler certificate of the image of the uniform key of `Sk`
under `decE` against the uniform exponent, and let `2 ≤ ΔFS`, `2 ≤ ΔPCS`. For every adversary
`A`, the advantage of `A` against the double ratchet of `(dhCKAOf G decE).atInit
(dhPairInit decE x₀)` is at most

* the first-epoch terms of `A.first` (`sm_corrupt_advantage_le_first`): the PRF-PRNG advantages
  at `smcRootRedFirst` and the FS-AEAD advantage at `smcFSRed`,
* the terms of `sm_corrupt_advantage_le` for `A.later`, with each CKA term bounded by the DDH
  advantage of `ckaCorruptDDHRedAt decE x₀ ΔFS ΔPCS (smcCKARed R F D b A.later)` plus `4 c.δ`
  (`dhCKAOf_atInit_corrupt_advantage_le`). -/
theorem sm_dh_corrupt_advantage_le_pair (decE : Sk → CG.Exp) (c : SamplerCert CG.Exp)
    (hμ : c.μ = (SDistr.uniform Sk).bind fun x => SDistr.pure (decE x))
    (hν : c.ν = SDistr.uniform CG.Exp) (R : PRGDef (RK × G) (RK × Sa)) (F : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS) (x₀ : Sk)
    (A : SMCorruptAdv (G × Sk) G RK Sa W Ct) :
    SM_Corrupt_Advantage ((dhCKAOf G decE).atInit (dhPairInit decE x₀)) R F D ΔFS ΔPCS A ≤
      (∑ b : Bool, PRFPRNG_Advantage R
          (smcRootRedFirst (dhCKAOf G decE) R F D ΔFS ΔPCS b (dhPairInit decE x₀) A.first) +
        FSAEAD_Corrupt_Advantage F D
          (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS (PMF.pure (dhPairInit decE x₀)) A.first)) +
      (∑ b : Bool, DDH_Advantage G
          (ckaCorruptDDHRedAt decE x₀ ΔFS ΔPCS (smcCKARed (Rand := Sk) R F D b A.later)) +
        8 * c.δ +
        ∑ b : Bool, PRFPRNG_Advantage R
          (smcRootRed (dhCKAOf G decE) R F D ΔFS ΔPCS b (PMF.pure (dhPairInit decE x₀)) A.later) +
        FSAEAD_Corrupt_Advantage F D
          (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS (PMF.pure (dhPairInit decE x₀)) A.later)) := by
  have hinit : ((dhCKAOf G decE).atInit (dhPairInit decE x₀)).init =
      liftPMF (PMF.pure (dhPairInit decE x₀)) := liftPMF_pure _
  refine (SM_Corrupt_Advantage_le_split _ _ hinit R F D ΔFS ΔPCS A).trans
    (add_le_add (sm_corrupt_advantage_le_first (dhCKAOf G decE) (dhPairInit decE x₀) R F D hFS
      hPCS A.first rfl) ?_)
  refine (sm_corrupt_advantage_le ((dhCKAOf G decE).atInit (dhPairInit decE x₀))
    ((dhCKAOfCoins_sound G decE).atInit _) _ hinit R F D hFS (by omega) A.later).trans ?_
  have hC : ∀ b : Bool, CKA_Corrupt_Advantage ((dhCKAOf G decE).atInit (dhPairInit decE x₀))
      ΔFS ΔPCS (smcCKARed (Rand := Sk) R F D b A.later) ≤
      DDH_Advantage G (ckaCorruptDDHRedAt decE x₀ ΔFS ΔPCS (smcCKARed (Rand := Sk) R F D b A.later))
        + 4 * c.δ := fun b =>
    dhCKAOf_atInit_corrupt_advantage_le decE c hμ hν hFS hPCS x₀ _ (tStarLater_support _)
  have hsum : ∑ b : Bool, CKA_Corrupt_Advantage ((dhCKAOf G decE).atInit (dhPairInit decE x₀))
      ΔFS ΔPCS (smcCKARed (Rand := Sk) R F D b A.later) ≤
      ∑ b : Bool, DDH_Advantage G
        (ckaCorruptDDHRedAt decE x₀ ΔFS ΔPCS (smcCKARed (Rand := Sk) R F D b A.later)) +
        8 * c.δ := by
    simp only [Fintype.sum_bool]
    calc _ ≤ _ := add_le_add (hC true) (hC false)
      _ = _ := by ring
  exact add_le_add (add_le_add hsum le_rfl) le_rfl

end DHPair

end CatCrypt.Crypto.Messaging
