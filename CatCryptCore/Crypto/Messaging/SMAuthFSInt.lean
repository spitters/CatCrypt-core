/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMAuthRoot
import CatCryptCore.Tactics.AutoDispatchExt

/-!
# The FS-AEAD integrity hop of the forgery event at an epoch

The third hop of the forgery event at the epoch `k` of the authenticity game over the ACD
construction `acdAuthSM C R G D`. After the root hop (`acdAuthSM_truncGame_le_root`) the root
output at the opening of the epoch `k` is uniform, so the chain of the epoch `k` starts from a
uniform state. The reduction `smAuthFSRed` embeds the challenger of the FS-AEAD integrity game
(`fsaead_int_game`) as that chain: it runs the adversary against the simulator `smAuthFSImpl`,
which keeps the state of the truncated hybrid with the chain of the epoch `k` left out, sends the
encryptions of the epoch `k` to the `enc` oracle, asks the decryption of each delivery into the
epoch `k` to the `dec` oracle and raises the flag of a forgery when the answer differs from the
decryption from its log. With the real decryption the reduction outputs the flag of a forgery of
the hybrid; with the decryption from the log of the integrity game it never raises the flag.

The simulator of the secure-messaging queries is the simulator `smFSImplOf` of the FS-AEAD hop
of the confidentiality proof, with the queries and answers relabelled to those of the integrity
game, except for the challenge, whose epoch is the challenge epoch `t` of the adversary.

## Main definitions

* `smAuthFSImplAt`, `smAuthFSStep`, `smAuthFSImpl` — the simulator
* `smAuthFSTree`, `smAuthFSRed` — the FS-AEAD integrity reduction
* `AuthFSInv` — the invariant of the simulation

## Main results

* `smAuthFS_real_eq` — the real FS-AEAD integrity game of `smAuthFSRed` is the game
  `smAuthRootIdealGame`
* `smAuthFS_ideal_eq_zero` — the reduction never wins the ideal integrity game
* `smAuthRootIdealGame_le_fsint`, `acdAuthSM_truncGame_le_fsint` — the FS-AEAD integrity hop,
  and the CKA, root and FS-AEAD integrity hops composed
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open scoped ENNReal

section FSIntRed

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [DecidableEq W] [DecidableEq Ct]

/-- The queries of the FS-AEAD game with corruption as queries of the integrity game: the
challenge is an encryption. -/
def fsIntQ : FSQuery W → FSIntQuery W Ct
  | .enc m => .enc m
  | .chall m => .enc m
  | .corrupt => .corrupt

/-- The answers of the integrity game as answers of the FS-AEAD game with corruption. -/
def fsIntA : FSIntAns Sa Ct W → FSAns Sa Ct
  | .ct c => .ct c
  | .dec _ => .none
  | .state s => .state s

/-- The plaintext of an answer of the integrity game to a decryption. -/
def fsIntDecOf : FSIntAns Sa Ct W → Option W
  | .dec m => m
  | _ => none

/-- The state of the FS-AEAD game with corruption with the chain of a state of the integrity
game and the challenge flag `d`. -/
def fsStOfInt (d : Bool) (u : FSIntSt Sa W Ct) : FSSt Sa := ⟨u.cur, u.init, d, u.corr⟩

/-- The challenge of party `p` at the challenge epoch `t` in the simulator of the integrity hop:
on the chain of the epoch `k`, held by the integrity game, an encryption of the integrity game;
on a chain of the simulator, the real encryption. -/
noncomputable def smAuthFSChall (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (t : ℕ)
    (x : FSSim Sc Msg RK Sa) (p : CKAParty) (m : W × W) :
    OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) (SMAns Sc Msg RK Sa Ct × FSSim Sc Msg RK Sa) :=
  if x.sndX p then (smFSChall (W := W) (Ct := Ct) t x p m).mapQueryAnswer fsIntQ fsIntA
  else
    match x.s.loc.snd p with
    | some sa =>
      if challOk x.s.loc t (x.s.ck.t p) p then
        .ret (.ct (D.encrypt (G.stretch sa).1 m.1 m.2),
          { x with s := ⟨x.s.ck, { x.s.loc.advanced p (G.stretch sa).2 with done := true }⟩ })
      else .ret (.none, x)
    | none => .ret (.none, x)

/-- The simulator of the secure-messaging queries in the integrity hop at the epoch `k` with the
challenge epoch `t`: the simulator `smFSImplOf` of the FS-AEAD hop at the epoch `k`, relabelled
to the integrity game, with the challenge at the epoch `t` and the corruption gate of `t`. -/
noncomputable def smAuthFSImplAt (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (rkS : RK) (x : FSSim Sc Msg RK Sa) (q : SMQuery W) :
    OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) (SMAns Sc Msg RK Sa Ct × FSSim Sc Msg RK Sa) :=
  match q with
  | .ratchet p => (smFSRatchet (W := W) (Ct := Ct) C R k rkS x p).mapQueryAnswer fsIntQ fsIntA
  | .recv p => (smFSRecv (W := W) (Ct := Ct) C rkS x p).mapQueryAnswer fsIntQ fsIntA
  | .send p m => (smFSSend G D x p m).mapQueryAnswer fsIntQ fsIntA
  | .chall p m => smAuthFSChall G D t x p m
  | .corrupt p => (smFSCorr (W := W) (Ct := Ct) ΔFS ΔPCS t x p).mapQueryAnswer fsIntQ fsIntA

/-- A query of the truncated hybrid in the simulator of the integrity hop: a query of the
corruption game is answered by `smAuthFSImplAt` and logged, and by a rejection when the epoch `k`
leaves the safe epochs; a delivery is answered from the log and by a decryption under a key of
the receiving chain, and the flag of a forgery is raised, from the `dec` oracle of the integrity
game for a delivery into the epoch `k` on the chain it holds. -/
noncomputable def smAuthFSStep (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (rkS : RK) (σ : (FSSim Sc Msg RK Sa × SMAuthAux W Ct) × Bool) :
    SMAuthQuery W Ct → OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W)
      (SMAuthAns Msg Ct (SMPartySt Sc RK Sa) W × ((FSSim Sc Msg RK Sa × SMAuthAux W Ct) × Bool))
  | .sm q => (smAuthFSImplAt C R G D ΔFS ΔPCS t k rkS σ.1.1 q).bind fun y =>
      if (σ.1.2.upd (ckaShadow σ.1.1.s.ck) q y.1.toScheme).safe ΔFS ΔPCS k then
        .ret (.sm y.1.toScheme, ((y.2, σ.1.2.upd (ckaShadow σ.1.1.s.ck) q y.1.toScheme), σ.2))
      else .ret (.dec none, ((y.2, σ.1.2.upd (ckaShadow σ.1.1.s.ck) q y.1.toScheme), σ.2))
  | .deliver p j ad c =>
    if decide ((ckaShadow σ.1.1.s.ck).t p = k) &&
        σ.1.2.canDeliver ΔFS ΔPCS (ckaShadow σ.1.1.s.ck) p && σ.1.1.rcvX p then
      .query (.dec j ad c) fun a => .ret
        (.dec (acdDeliverAns G D ΔFS ΔPCS k (ckaShadow σ.1.1.s.ck) σ.1.1.s.loc σ.1.2 p j ad c),
          (σ.1, σ.2 || (fsIntDecOf a != σ.1.2.logDec k j ad c)))
    else .ret
      (.dec (acdDeliverAns G D ΔFS ΔPCS k (ckaShadow σ.1.1.s.ck) σ.1.1.s.loc σ.1.2 p j ad c),
        (σ.1, σ.2 ||
          acdDeliverBad G D ΔFS ΔPCS k (ckaShadow σ.1.1.s.ck) σ.1.1.s.loc σ.1.2 p j ad c))

/-- **The simulator of the integrity hop of the forgery event at the epoch `k`**:
`smAuthFSStep` while the epoch `k` is safe, a rejection otherwise. -/
noncomputable def smAuthFSImpl (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (rkS : RK) (σ : (FSSim Sc Msg RK Sa × SMAuthAux W Ct) × Bool)
    (d : SMAuthQuery W Ct) :
    OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W)
      (SMAuthAns Msg Ct (SMPartySt Sc RK Sa) W × ((FSSim Sc Msg RK Sa × SMAuthAux W Ct) × Bool)) :=
  if σ.1.2.safe ΔFS ΔPCS k then smAuthFSStep C R G D ΔFS ΔPCS t k rkS σ d
  else .ret (.dec none, σ)

/-- The FS-AEAD integrity reduction of the forgery event at the epoch `k` as an oracle tree: it
draws the challenge epoch `t` from `tStar`, the CKA initialisation from `initP`, a uniform root
key and a uniform root key `rkS` of the epoch `k`, runs the adversary against the simulator
`smAuthFSImpl` and outputs the flag of a forgery. -/
noncomputable def smAuthFSTree (C : CKADef Sc Msg Key) [CKACoins C Rand] [Fintype RK]
    [Nonempty RK] (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS k : ℕ) (initP : PMF (Msg × Sc × Sc)) (tStar : PMF ℕ)
    (play : ℕ → Msg → OracleAdv (SMAuthQuery W Ct) (SMAuthAns Msg Ct (SMPartySt Sc RK Sa) W) Bool) :
    OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool :=
  .rand tStar fun t => .rand initP fun i => .rand (PMF.uniformFintype RK) fun rk =>
    .rand (PMF.uniformFintype RK) fun rkS =>
      (OracleAdv.simulate (smAuthFSImpl C R G D ΔFS ΔPCS t k rkS) (play t i.1)
        ((⟨smInit i rk, fun _ => false, fun _ => false, false⟩, SMAuthAux.init), false)).bind
        fun r => .ret r.2.2

/-- **The FS-AEAD integrity reduction of the forgery event at the epoch `k`**: the tree
`smAuthFSTree` at the challenge-epoch distribution and the interaction of `A`. -/
noncomputable def smAuthFSRed (C : CKADef Sc Msg Key) [CKACoins C Rand] [Fintype RK]
    [Nonempty RK] (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS k : ℕ) (initP : PMF (Msg × Sc × Sc)) (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa)) :
    OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool :=
  smAuthFSTree C R G D ΔFS ΔPCS k initP A.tStar A.play

end FSIntRed

/-! ## The simulator of the secure-messaging queries -/

section FSIntSim

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [DecidableEq W] [DecidableEq Ct]

/-- At an opening, a receive and a send, the simulator of the integrity hop against the
integrity game, with the integrity state read as a state of the FS-AEAD game with corruption, is
the simulator `smFSImplOf` of the FS-AEAD hop at the epoch `k` against the real FS-AEAD game. -/
theorem smAuthFSImplAt_rel (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (rkS : RK) (b d : Bool) (x : FSSim Sc Msg RK Sa) (u : FSIntSt Sa W Ct)
    (q : SMQuery W) (hq : ∀ p m, q ≠ .chall p m) (hq' : ∀ p, q ≠ .corrupt p) :
    (OracleAdv.simOracle (smAuthFSImplAt C R G D ΔFS ΔPCS t k rkS) (fsIntOracle G D b)
        (x, u) q).map (fun y => (y.1, (y.2.1, fsStOfInt d y.2.2))) =
      OracleAdv.simOracle (smFSImplOf C R G D ΔFS ΔPCS k rkS) (fsOracle G D false)
        (x, fsStOfInt d u) q := by
  cases q with
  | ratchet p =>
    simp only [OracleAdv.simOracle, smAuthFSImplAt, smFSImplOf, OracleAdv.run_mapQueryAnswer,
      PMF.map_comp, smFSRatchet]
    split_ifs <;> simp [OracleAdv.run_rand, OracleAdv.run_ret, PMF.map_bind, PMF.pure_map]
  | recv p =>
    simp only [OracleAdv.simOracle, smAuthFSImplAt, smFSImplOf, OracleAdv.run_mapQueryAnswer,
      PMF.map_comp, smFSRecv]
    split <;> (try split) <;> (try split) <;> simp [OracleAdv.run_ret, PMF.pure_map]
  | send p m =>
    simp only [OracleAdv.simOracle, smAuthFSImplAt, smFSImplOf, OracleAdv.run_mapQueryAnswer,
      PMF.map_comp, smFSSend]
    split <;> (try split) <;> (try split) <;>
      simp [OracleAdv.run_ret, OracleAdv.run_query, PMF.pure_map, fsIntOracle, fsOracle, fsIntQ,
        fsIntA, fsStOfInt]
  | chall p m => exact absurd rfl (hq p m)
  | corrupt p => exact absurd rfl (hq' p)

/-- The secure-messaging state that a state of the simulator of the integrity hop and a state
of the integrity game stand for: `fsAbs` at the chain of the integrity game. -/
def fsIntAbs (rkS : RK) (x : FSSim Sc Msg RK Sa) (u : FSIntSt Sa W Ct) : SMSt Sc Msg RK Sa :=
  fsAbs rkS (x, fsStOfInt false u)

/-- **The simulator of the secure-messaging queries is the oracle of the truncated hybrid.**
Under the invariant of the FS-AEAD simulation at the epoch `k`, each call of `smAuthFSImplAt`
against the integrity game, mapped by `fsIntAbs`, is the call of `smOracleOfAt` with the root
output `(rkS, sa)` at the epoch `k`, at every query other than a corruption allowed at the
challenge epoch `t` with the epoch `k` in its window. -/
theorem smAuthFSImplAt_step (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS) (t k : ℕ) (rkS : RK) (sa : Sa) (b : Bool)
    (x : FSSim Sc Msg RK Sa) (u : FSIntSt Sa W Ct)
    (hx : FSInv k sa (x, fsStOfInt x.s.loc.done u)) (q : SMQuery W)
    (hq : ∀ p, q = .corrupt p → ckaAllowCorr ΔFS ΔPCS t x.s.ck p = true →
      ckaAllowCorr ΔFS ΔPCS k x.s.ck p = true) :
    (OracleAdv.simOracle (smAuthFSImplAt C R G D ΔFS ΔPCS t k rkS) (fsIntOracle G D b)
        (x, u) q).map (Prod.map id fun z => fsIntAbs rkS z.1 z.2) =
      smOracleOfAt C R G D ΔFS ΔPCS t k false (constRoot (Key := Key) (rkS, sa))
        (fsIntAbs rkS x u) q := by
  have key : ∀ q : SMQuery W, (∀ p m, q ≠ .chall p m) → (∀ p, q ≠ .corrupt p) →
      (OracleAdv.simOracle (smAuthFSImplAt C R G D ΔFS ΔPCS t k rkS) (fsIntOracle G D b)
        (x, u) q).map (Prod.map id fun z => fsIntAbs rkS z.1 z.2) =
      smOracleOf C R G D ΔFS ΔPCS k false (constRoot (Key := Key) (rkS, sa))
        (fsIntAbs rkS x u) q := by
    intro q h1 h2
    refine Eq.trans ?_ (smFS_step C R G D hFS hPCS k false rkS sa _ hx q)
    rw [← smAuthFSImplAt_rel C R G D ΔFS ΔPCS t k rkS b x.s.loc.done x u q h1 h2, PMF.map_comp]
    rfl
  cases q with
  | ratchet p => exact key _ (fun _ _ h => nomatch h) (fun _ h => nomatch h)
  | recv p => exact key _ (fun _ _ h => nomatch h) (fun _ h => nomatch h)
  | send p m => exact key _ (fun _ _ h => nomatch h) (fun _ h => nomatch h)
  | chall p m =>
    obtain ⟨⟨ck, l⟩, sX, rX, oX⟩ := x
    have hA : ∀ e, challOk (fsIntAbs rkS ⟨⟨ck, l⟩, sX, rX, oX⟩ u).loc t e p =
        challOk l t e p := fun _ => rfl
    simp only [OracleAdv.simOracle, smAuthFSImplAt, smAuthFSChall, smOracleOfAt, smOracleOf, hA]
    by_cases hs : sX p = true
    · have huniq : ∀ q, q ≠ p → sX q = false := fun q hq => by
        by_contra h
        exact hq ((hx.snd q (by simpa using h)).1.trans (hx.snd p hs).1.symm)
      by_cases hok : challOk l t (ck.t p) p = true
      · simp only [hs, hok, ite_true, OracleAdv.run_mapQueryAnswer, smFSChall, fsIntAbs, fsAbs,
          OracleAdv.run_query, fsIntQ, fsIntOracle, fsIntA, challCt, fsStOfInt, PMF.pure_map,
          PMF.pure_bind, OracleAdv.run_ret, Bool.false_eq_true, ite_false,
          Prod.map_apply, id_eq, SMLoc.advanced]
        congr 4
        funext q
        by_cases hq : q = p
        · subst hq; simp [hs]
        · simp [hq, huniq q hq]
      · have hok' : challOk l t (ck.t p) p = false := by simpa using hok
        simp [hs, hok', OracleAdv.run_mapQueryAnswer, smFSChall, fsIntAbs, fsAbs,
          OracleAdv.run_ret, PMF.pure_map, fsStOfInt]
    · have hs' : sX p = false := by simpa using hs
      cases hl : l.snd p with
      | none => simp [hs', hl, fsIntAbs, fsAbs, PMF.pure_map, OracleAdv.run_ret]
      | some sa' =>
        by_cases hok : challOk l t (ck.t p) p = true
        · simp only [hs', hl, hok, Bool.false_eq_true, ite_true, ite_false, fsIntAbs, fsAbs,
            OracleAdv.run_ret, PMF.pure_map, Prod.map_apply, id_eq, SMLoc.advanced, challCt,
            PMF.pure_bind]
          congr 4
          funext q
          by_cases hq : q = p
          · subst hq; simp [hs']
          · simp [hq]
        · have hok' : challOk l t (ck.t p) p = false := by simpa using hok
          simp [hs', hl, hok', fsIntAbs, fsAbs, PMF.pure_map, OracleAdv.run_ret]
  | corrupt p =>
    obtain ⟨⟨ck, l⟩, sX, rX, oX⟩ := x
    simp only [OracleAdv.simOracle, smAuthFSImplAt, OracleAdv.run_mapQueryAnswer, smFSCorr,
      smOracleOfAt, smOracleOf]
    by_cases hc : ckaAllowCorr ΔFS ΔPCS t ck p = true
    · have hk := hq p rfl hc
      have hs : sX p = false := by
        by_contra h
        have hw := (hx.snd p (by simpa using h)).2
        rw [not_allowCorr_of_window hFS hPCS hw.1 hw.2] at hk
        exact absurd hk (by decide)
      have hr : rX p = false := by
        by_contra h
        have hw := (hx.rcv p (by simpa using h)).2
        rw [not_allowCorr_of_window hFS hPCS hw.1 hw.2] at hk
        exact absurd hk (by decide)
      simp [hc, hs, hr, fsIntAbs, fsAbs, PMF.pure_map]
    · simp [hc, fsIntAbs, fsAbs, PMF.pure_map]

end FSIntSim

/-! ## The invariant of the simulation -/

section FSIntInv

variable {Sc Msg RK Sa W Ct : Type} [DecidableEq W] [DecidableEq Ct]

/-- The invariant of the simulation of the integrity hop at the epoch `k` with the initial state
`sa` of the integrity game: the invariant `FSInv` of the FS-AEAD simulation at the epoch `k`; the
log of the integrity game is the log of the honest ciphertexts of the epoch `k` (its length and
its decryption); the root output in transit to a party that receives the epoch `k` is held by
the integrity game; a party that receives in the epoch `k` holds the chain of the integrity
game, unless `k = 0`, where it holds no chain; and at `k = 0` the integrity game is not used. -/
structure AuthFSInv (k : ℕ) (sa : Sa)
    (z : ((FSSim Sc Msg RK Sa × SMAuthAux W Ct) × Bool) × FSIntSt Sa W Ct) : Prop where
  fs : FSInv k sa (z.1.1.1, fsStOfInt z.1.1.1.s.loc.done z.2)
  len : z.2.log.length = z.1.1.2.nextIdx k
  dec : ∀ j ad c, z.2.logDec j ad c = z.1.1.2.logDec k j ad c
  outk : ∀ p, z.1.1.1.s.ck.canRecv p = true → z.1.1.1.s.ck.t p + 1 = k → z.1.1.1.outX = true
  rcvk : ∀ p, p ≠ ckaSender k → z.1.1.1.s.ck.t p = k →
    z.1.1.1.rcvX p = true ∨ (k = 0 ∧ z.1.1.1.s.loc.rcv p = none)
  zero : k = 0 → (∀ p, z.1.1.1.sndX p = false) ∧ z.2.log = []

/-- The invariant does not depend on the flag of a forgery. -/
theorem AuthFSInv.flag {k : ℕ} {sa : Sa} {x : FSSim Sc Msg RK Sa} {a : SMAuthAux W Ct} {f : Bool}
    {u : FSIntSt Sa W Ct} (h : AuthFSInv k sa (((x, a), f), u)) (f' : Bool) :
    AuthFSInv k sa (((x, a), f'), u) :=
  ⟨h.fs, h.len, h.dec, h.outk, h.rcvk, h.zero⟩

/-- A ciphertext logged in an epoch other than `k` leaves the log of the epoch `k`. -/
theorem SMAuthAux.record_ne (x : SMAuthAux W Ct) {e k : ℕ} (h : e ≠ k) (m : W × W) (c : Ct) :
    (x.record e m c).nextIdx k = x.nextIdx k ∧
      ∀ j ad c', (x.record e m c).logDec k j ad c' = x.logDec k j ad c' := by
  refine ⟨?_, fun j ad c' => ?_⟩
  · simp [SMAuthAux.record, SMAuthAux.nextIdx, h]
  · simp [SMAuthAux.record, SMAuthAux.logDec, h]

/-- An encryption of the integrity game and the logging of its ciphertext in the epoch `k` keep
the log of the integrity game the log of the epoch `k`. -/
theorem fsIntSt_record (u : FSIntSt Sa W Ct) (x : SMAuthAux W Ct) (k : ℕ)
    (hl : u.log.length = x.nextIdx k) (hd : ∀ j ad c, u.logDec j ad c = x.logDec k j ad c)
    (cur : Sa) (m : W × W) (c : Ct) :
    ((u.log.length, m.1, m.2, c) :: u.log).length = (x.record k m c).nextIdx k ∧
      ∀ j ad c', ({ u with cur := cur, log := (u.log.length, m.1, m.2, c) :: u.log } :
        FSIntSt Sa W Ct).logDec j ad c' = (x.record k m c).logDec k j ad c' := by
  refine ⟨?_, fun j ad c' => ?_⟩
  · simp [SMAuthAux.record, SMAuthAux.nextIdx, hl]
  · have := hd j ad c'
    simp only [FSIntSt.logDec, SMAuthAux.logDec, SMAuthAux.record, List.find?_cons] at this ⊢
    rw [hl]
    by_cases h : x.nextIdx k = j ∧ m.2 = ad ∧ c = c'
    · obtain ⟨rfl, rfl, rfl⟩ := h
      simp
    · simp only [true_and, decide_eq_false h]
      exact this

end FSIntInv

section FSIntInvStep

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [DecidableEq W] [DecidableEq Ct]

/-- **The invariant of the simulation is kept by the secure-messaging queries**, with the log
of the honest ciphertexts updated by the answer, against the real and the ideal integrity
game. -/
theorem smAuthFSImplAt_inv (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (rkS : RK) (sa : Sa) (b : Bool) (x : FSSim Sc Msg RK Sa)
    (aux : SMAuthAux W Ct) (f : Bool) (u : FSIntSt Sa W Ct)
    (hx : AuthFSInv k sa (((x, aux), f), u)) (q : SMQuery W) (y)
    (hy : y ∈ (OracleAdv.simOracle (smAuthFSImplAt C R G D ΔFS ΔPCS t k rkS)
      (fsIntOracle G D b) (x, u) q).support) (f' : Bool) :
    AuthFSInv k sa (((y.2.1, aux.upd (ckaShadow x.s.ck) q y.1.toScheme), f'), y.2.2) := by
  have hfsR : ∀ q : SMQuery W, (∀ p m, q ≠ .chall p m) → (∀ p, q ≠ .corrupt p) →
      ∀ y ∈ (OracleAdv.simOracle (smAuthFSImplAt C R G D ΔFS ΔPCS t k rkS)
        (fsIntOracle G D b) (x, u) q).support,
        FSInv k sa (y.2.1, fsStOfInt y.2.1.s.loc.done y.2.2) := by
    intro q h1 h2 y hy
    have hy' : (y.1, (y.2.1, fsStOfInt x.s.loc.done y.2.2)) ∈
        (OracleAdv.simOracle (smFSImplOf C R G D ΔFS ΔPCS k rkS) (fsOracle G D false)
          (x, fsStOfInt x.s.loc.done u) q).support := by
      rw [← smAuthFSImplAt_rel C R G D ΔFS ΔPCS t k rkS b x.s.loc.done x u q h1 h2,
        PMF.support_map]
      exact ⟨y, hy, rfl⟩
    have h := smFS_inv C R G D ΔFS ΔPCS k false rkS sa _ hx.fs q _ hy'
    have hd : x.s.loc.done = y.2.1.s.loc.done := h.done
    rw [hd] at h
    exact h
  obtain ⟨⟨ck, l⟩, sX, rX, oX⟩ := x
  have hreach : ckaReach ck := hx.fs.reach
  cases q with
  | ratchet p =>
    have hF := hfsR (.ratchet p) (fun _ _ h => nomatch h) (fun _ h => nomatch h) y hy
    simp only [OracleAdv.simOracle, smAuthFSImplAt, OracleAdv.run_mapQueryAnswer, smFSRatchet,
      PMF.support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    by_cases hc : ck.canSend p = true
    · obtain ⟨hso, hsp⟩ := ckaSend_spec hc
      simp only [hc, ite_true, OracleAdv.run_rand, PMF.support_bind, Set.mem_iUnion] at hz
      obtain ⟨r, -, hz⟩ := hz
      by_cases ht : ck.t p + 1 = k
      · simp only [ht, beq_self_eq_true, ite_true, OracleAdv.run_ret, PMF.support_pure,
          Set.mem_singleton_iff] at hz
        subst hz
        have hsk : ckaSender k = p := ht ▸ hsp
        refine ⟨hF, by simpa [SMAuthAux.upd, SMAns.toScheme] using hx.len,
          fun j ad c => by simpa [SMAuthAux.upd, SMAns.toScheme] using hx.dec j ad c,
          fun _ _ _ => rfl, ?_, fun h0 => by omega⟩
        intro q hq hqt
        rcases CKAParty.eq_or_eq_other q p with rfl | rfl
        · exact absurd hsk.symm hq
        · simp [CKAGameSt.sent_t] at hqt
          omega
      · have ht' : (ck.t p + 1 == k) = false := by simpa using ht
        simp only [ht', Bool.false_eq_true, ite_false, OracleAdv.run_ret, PMF.support_pure,
          Set.mem_singleton_iff] at hz
        subst hz
        refine ⟨hF, by simpa [SMAuthAux.upd, SMAns.toScheme] using hx.len,
          fun j ad c => by simpa [SMAuthAux.upd, SMAns.toScheme] using hx.dec j ad c, ?_, ?_, ?_⟩
        · intro q hcr hqt
          simp only [CKAGameSt.canRecv, beq_iff_eq, CKAGameSt.sent_t] at hcr hqt
          rcases CKAParty.eq_or_eq_other q p with rfl | rfl
          · simp [CKAParty.other_ne] at hcr; omega
          · simp at hcr hqt; omega
        · intro q hq hqt
          rcases CKAParty.eq_or_eq_other q p with rfl | rfl
          · simp at hqt; omega
          · simp at hqt
            simpa [SMLoc.opened] using hx.rcvk p.other hq hqt
        · intro h0
          refine ⟨fun q => ?_, (hx.zero h0).2⟩
          by_cases hqp : q = p
          · subst hqp; simp
          · simpa [Function.update_apply, hqp] using (hx.zero h0).1 q
    · simp only [hc, Bool.false_eq_true, ite_false, OracleAdv.run_ret, PMF.support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      simpa [SMAuthAux.upd, SMAns.toScheme] using hx.flag f'
  | recv p =>
    have hF := hfsR (.recv p) (fun _ _ h => nomatch h) (fun _ h => nomatch h) y hy
    simp only [OracleAdv.simOracle, smAuthFSImplAt, OracleAdv.run_mapQueryAnswer, smFSRecv,
      PMF.support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    by_cases hc : ck.canRecv p = true
    · obtain ⟨hto, -⟩ := ckaReach_recv hreach hc
      have hnr : ∀ (xx : Sc) q, (ck.recvd p xx).canRecv q = true → False := by
        intro xx q h
        simp only [CKAGameSt.canRecv, beq_iff_eq, CKAGameSt.recvd_t] at h
        rcases CKAParty.eq_or_eq_other q p with rfl | rfl
        · simp [CKAParty.other_ne] at h; omega
        · simp at h; omega
      have hk : ∀ q, q ≠ ckaSender k → ck.t p + 1 = k → q = p → oX = true :=
        fun q _ h hq => hx.outk p hc h
      by_cases ho : oX = true
      · simp only [hc, ho, ite_true, OracleAdv.run_ret, PMF.support_pure,
          Set.mem_singleton_iff] at hz
        subst hz
        refine ⟨hF, by simpa [SMAuthAux.upd, SMAns.toScheme] using hx.len,
          fun j ad c => by simpa [SMAuthAux.upd, SMAns.toScheme] using hx.dec j ad c,
          fun q h _ => (hnr _ q h).elim, ?_, fun h0 => (hx.zero h0)⟩
        intro q hq hqt
        by_cases hqp : q = p
        · subst hqp; left; simp
        · simp only [CKAGameSt.recvd_t, hqp, ite_false] at hqt
          simpa [SMLoc.recvX, Function.update_apply, hqp] using hx.rcvk q hq hqt
      · have ho' : oX = false := by simpa using ho
        have hrc : ∀ (xx : Sc) (l' : SMLoc RK Sa) (rX' : CKAParty → Bool),
            (∀ q, q ≠ p → rX' q = rX q ∧ l'.rcv q = l.rcv q) →
            ∀ q, q ≠ ckaSender k → (ck.recvd p xx).t q = k →
              rX' q = true ∨ (k = 0 ∧ l'.rcv q = none) := by
          intro xx l' rX' hre q hq hqt
          by_cases hqp : q = p
          · subst hqp
            simp only [CKAGameSt.recvd_t, ite_true] at hqt
            rw [hk q hq hqt rfl] at ho'
            exact absurd ho' (by decide)
          · simp only [CKAGameSt.recvd_t, hqp, ite_false] at hqt
            rw [(hre q hqp).1, (hre q hqp).2]
            exact hx.rcvk q hq hqt
        cases hl : l.out with
        | none =>
          simp only [hc, ho', Bool.false_eq_true, ite_true, ite_false, hl, OracleAdv.run_ret,
            PMF.support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨hF, by simpa [SMAuthAux.upd, SMAns.toScheme] using hx.len,
            fun j ad c => by simpa [SMAuthAux.upd, SMAns.toScheme] using hx.dec j ad c,
            fun q h _ => (hnr _ q h).elim, hrc _ _ _ fun _ _ => ⟨rfl, rfl⟩,
            fun h0 => (hx.zero h0)⟩
        | some yy =>
          simp only [hc, ho', Bool.false_eq_true, ite_true, ite_false, hl, OracleAdv.run_ret,
            PMF.support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨hF, by simpa [SMAuthAux.upd, SMAns.toScheme] using hx.len,
            fun j ad c => by simpa [SMAuthAux.upd, SMAns.toScheme] using hx.dec j ad c,
            fun q h _ => (hnr _ q h).elim,
            hrc _ _ _ fun q hq => ⟨by simp [hq], by simp [SMLoc.recvY, hq]⟩,
            fun h0 => (hx.zero h0)⟩
    · simp only [hc, Bool.false_eq_true, ite_false, OracleAdv.run_ret, PMF.support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      simpa [SMAuthAux.upd, SMAns.toScheme] using hx.flag f'
  | send p m =>
    have hF := hfsR (.send p m) (fun _ _ h => nomatch h) (fun _ h => nomatch h) y hy
    simp only [OracleAdv.simOracle, smAuthFSImplAt, OracleAdv.run_mapQueryAnswer, smFSSend,
      PMF.support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    by_cases hs : sX p = true
    · by_cases hsd : ckaSender (ck.t p) = p
      · simp only [hs, hsd, beq_self_eq_true, ite_true, OracleAdv.run_query, fsIntQ, fsIntOracle,
          PMF.pure_map, PMF.pure_bind, fsIntA, OracleAdv.run_ret, PMF.support_pure,
          Set.mem_singleton_iff] at hz
        subst hz
        obtain ⟨hp1, hp2, hp3⟩ := hx.fs.snd p hs
        have hp2' : k ≤ ck.t p := hp2
        have hp3' : ck.t p ≤ k + 1 := hp3
        have hpk : ck.t p = k := by
          by_contra hne
          have he : ck.t p = k + 1 := by omega
          rw [he] at hsd
          exact ckaSender_ne_succ k (hsd.trans hp1)
        obtain ⟨h1, h2⟩ := fsIntSt_record u aux k hx.len hx.dec (G.stretch u.cur).2 m
          (D.encrypt (G.stretch u.cur).1 m.1 m.2)
        refine ⟨hF, ?_, ?_, hx.outk, hx.rcvk,
          fun h0 => absurd ((hx.zero h0).1 p) (by simp [hs])⟩
        · simpa [SMAuthAux.upd, SMAns.toScheme, ckaShadow, hpk] using h1
        · simpa [SMAuthAux.upd, SMAns.toScheme, ckaShadow, hpk] using h2
      · have hsd' : (ckaSender (ck.t p) == p) = false := by simpa using hsd
        simp only [hs, hsd', Bool.false_eq_true, ite_true, ite_false, OracleAdv.run_ret,
          PMF.support_pure, Set.mem_singleton_iff] at hz
        subst hz
        simpa [SMAuthAux.upd, SMAns.toScheme] using hx.flag f'
    · have hs' : sX p = false := by simpa using hs
      cases hl : l.snd p with
      | none =>
        simp only [hs', hl, Bool.false_eq_true, ite_false, OracleAdv.run_ret, PMF.support_pure,
          Set.mem_singleton_iff] at hz
        subst hz
        simpa [SMAuthAux.upd, SMAns.toScheme] using hx.flag f'
      | some sa' =>
        by_cases hsd : ckaSender (ck.t p) = p
        · simp only [hs', hl, hsd, beq_self_eq_true, Bool.false_eq_true, ite_true, ite_false,
            OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hz
          subst hz
          have hpk : ck.t p ≠ k := fun h => by
            have := hx.fs.chal p hsd h
            simp [hl] at this
          obtain ⟨h1, h2⟩ := SMAuthAux.record_ne aux hpk m (D.encrypt (G.stretch sa').1 m.1 m.2)
          refine ⟨hF, ?_, ?_, hx.outk, ?_, hx.zero⟩
          · simpa [SMAuthAux.upd, SMAns.toScheme, ckaShadow, h1] using hx.len
          · intro j ad c
            simpa [SMAuthAux.upd, SMAns.toScheme, ckaShadow, h2] using hx.dec j ad c
          · simpa [SMLoc.advanced] using hx.rcvk
        · have hsd' : (ckaSender (ck.t p) == p) = false := by simpa using hsd
          simp only [hs', hl, hsd', Bool.false_eq_true, ite_false, OracleAdv.run_ret,
            PMF.support_pure, Set.mem_singleton_iff] at hz
          subst hz
          simpa [SMAuthAux.upd, SMAns.toScheme] using hx.flag f'
  | chall p m =>
    simp only [OracleAdv.simOracle, smAuthFSImplAt, smAuthFSChall, PMF.support_map,
      Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    by_cases hs : sX p = true
    · by_cases hok : challOk l t (ck.t p) p = true
      · simp only [hs, hok, ite_true, OracleAdv.run_mapQueryAnswer, smFSChall,
          OracleAdv.run_query, fsIntQ, fsIntOracle, PMF.pure_map, PMF.pure_bind, fsIntA,
          OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hz
        subst hz
        obtain ⟨hp1, hp2, hp3⟩ := hx.fs.snd p hs
        have hp2' : k ≤ ck.t p := hp2
        have hp3' : ck.t p ≤ k + 1 := hp3
        have hsd : ckaSender (ck.t p) = p := by
          simp only [challOk, Bool.and_eq_true, beq_iff_eq] at hok
          exact hok.1.2
        have hpk : ck.t p = k := by
          by_contra hne
          have he : ck.t p = k + 1 := by omega
          rw [he] at hsd
          exact ckaSender_ne_succ k (hsd.trans hp1)
        obtain ⟨h1, h2⟩ := fsIntSt_record u aux k hx.len hx.dec (G.stretch u.cur).2 m
          (D.encrypt (G.stretch u.cur).1 m.1 m.2)
        refine ⟨⟨hx.fs.corr, rfl, hx.fs.init, fun h => absurd (smOpened_of_le hp2') h,
            hx.fs.reach, hx.fs.snd, hx.fs.rcv, hx.fs.out, hx.fs.empty, hx.fs.chal⟩, ?_, ?_,
          hx.outk, hx.rcvk, fun h0 => absurd ((hx.zero h0).1 p) (by simp [hs])⟩
        · simpa [SMAuthAux.upd, SMAns.toScheme, ckaShadow, hpk] using h1
        · simpa [SMAuthAux.upd, SMAns.toScheme, ckaShadow, hpk] using h2
      · have hok' : challOk l t (ck.t p) p = false := by simpa using hok
        simp only [hs, hok', ite_true, Bool.false_eq_true, ite_false,
          OracleAdv.run_mapQueryAnswer, smFSChall, OracleAdv.run_ret, PMF.support_pure,
          Set.mem_singleton_iff] at hz
        subst hz
        simpa [SMAuthAux.upd, SMAns.toScheme] using hx.flag f'
    · have hs' : sX p = false := by simpa using hs
      cases hl : l.snd p with
      | none =>
        simp only [hs', hl, Bool.false_eq_true, ite_false, OracleAdv.run_ret, PMF.support_pure,
          Set.mem_singleton_iff] at hz
        subst hz
        simpa [SMAuthAux.upd, SMAns.toScheme] using hx.flag f'
      | some sa' =>
        by_cases hok : challOk l t (ck.t p) p = true
        · simp only [hs', hl, hok, Bool.false_eq_true, ite_true, ite_false, OracleAdv.run_ret,
            PMF.support_pure, Set.mem_singleton_iff] at hz
          subst hz
          have hsd : ckaSender (ck.t p) = p := by
            simp only [challOk, Bool.and_eq_true, beq_iff_eq] at hok
            exact hok.1.2
          have hpk : ck.t p ≠ k := fun h => by
            have := hx.fs.chal p hsd h
            simp [hl] at this
          obtain ⟨h1, h2⟩ := SMAuthAux.record_ne aux hpk m (D.encrypt (G.stretch sa').1 m.1 m.2)
          refine ⟨⟨hx.fs.corr, rfl, hx.fs.init, hx.fs.fresh, hx.fs.reach, hx.fs.snd, hx.fs.rcv,
              hx.fs.out, hx.fs.empty, ?_⟩, ?_, ?_, hx.outk, ?_, hx.zero⟩
          · intro q hq1 hq2
            by_cases hqp : q = p
            · subst hqp; exact absurd hq2 hpk
            · simpa [SMLoc.advanced, Function.update_apply, hqp] using hx.fs.chal q hq1 hq2
          · simpa [SMAuthAux.upd, SMAns.toScheme, ckaShadow, h1] using hx.len
          · intro j ad c
            simpa [SMAuthAux.upd, SMAns.toScheme, ckaShadow, h2] using hx.dec j ad c
          · simpa [SMLoc.advanced] using hx.rcvk
        · have hok' : challOk l t (ck.t p) p = false := by simpa using hok
          simp only [hs', hl, hok', Bool.false_eq_true, ite_false, OracleAdv.run_ret,
            PMF.support_pure, Set.mem_singleton_iff] at hz
          subst hz
          simpa [SMAuthAux.upd, SMAns.toScheme] using hx.flag f'
  | corrupt p =>
    simp only [OracleAdv.simOracle, smAuthFSImplAt, OracleAdv.run_mapQueryAnswer, smFSCorr,
      PMF.support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    split at hz <;> simp only [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hz <;>
      subst hz <;> exact ⟨hx.fs, hx.len, hx.dec, hx.outk, hx.rcvk, hx.zero⟩

end FSIntInvStep

/-! ## The simulator of the truncated hybrid -/

section FSIntHop

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [DecidableEq W] [DecidableEq Ct]

/-- The state of the truncated hybrid that a state of the simulator of the integrity hop and a
state of the integrity game stand for. -/
def fsIntAbsA (rkS : RK) (z : ((FSSim Sc Msg RK Sa × SMAuthAux W Ct) × Bool) × FSIntSt Sa W Ct) :
    (SMSt Sc Msg RK Sa × SMAuthAux W Ct) × Bool :=
  ((fsIntAbs rkS z.1.1.1 z.2, z.1.1.2), z.1.2)

omit [SampleableType Ct] in
/-- A query of the corruption game in the simulator of the integrity hop, from a safe state, is
the query of `smAuthFSImplAt`, logged, with the rejection of the transitions into an unsafe
state. -/
theorem smAuthFSImpl_simOracle (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (rkS : RK) {U : Type} (O' : U → FSIntQuery W Ct → PMF (FSIntAns Sa Ct W × U))
    (σ : (FSSim Sc Msg RK Sa × SMAuthAux W Ct) × Bool) (u : U) (q : SMQuery W)
    (hs : σ.1.2.safe ΔFS ΔPCS k = true) :
    OracleAdv.simOracle (smAuthFSImpl C R G D ΔFS ΔPCS t k rkS) O' (σ, u) (.sm q) =
      (OracleAdv.simOracle (smAuthFSImplAt C R G D ΔFS ΔPCS t k rkS) O' (σ.1.1, u) q).map
        fun y =>
          ((smAuthCut ΔFS ΔPCS k (.sm y.1.toScheme,
              ((y.2.1, σ.1.2.upd (ckaShadow σ.1.1.s.ck) q y.1.toScheme), σ.2))).1,
            ((smAuthCut ΔFS ΔPCS k (.sm y.1.toScheme,
              ((y.2.1, σ.1.2.upd (ckaShadow σ.1.1.s.ck) q y.1.toScheme), σ.2))).2, y.2.2)) := by
  simp only [OracleAdv.simOracle, smAuthFSImpl, hs, ite_true, smAuthFSStep,
    OracleAdv.run_bind, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  refine congrArg _ (funext fun a => ?_)
  by_cases h : (σ.1.2.upd (ckaShadow σ.1.1.s.ck) q a.1.1.toScheme).safe ΔFS ΔPCS k = true
  · simp [h, smAuthCut, PMF.pure_bind]
  · simp [h, smAuthCut, PMF.pure_bind]

/-- **The simulator of the integrity hop against the real integrity game is the truncated
hybrid.** Under the invariant `AuthFSInv`, each call of `smAuthFSImpl` against the real
integrity game, mapped by `fsIntAbsA`, is the call of the truncated hybrid with the root output
`(rkS, sa)` at the epoch `k`. -/
theorem smAuthFS_step (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS) (t k : ℕ) (rkS : RK) (sa : Sa)
    (z : ((FSSim Sc Msg RK Sa × SMAuthAux W Ct) × Bool) × FSIntSt Sa W Ct)
    (hz : AuthFSInv k sa z) (d : SMAuthQuery W Ct) :
    (OracleAdv.simOracle (smAuthFSImpl C R G D ΔFS ΔPCS t k rkS) (fsIntOracle G D false) z
        d).map (Prod.map id (fsIntAbsA rkS)) =
      smAuthHopOracle C R G D ΔFS ΔPCS t k (constRoot (Key := Key) (rkS, sa))
        (fsIntAbsA rkS z) d := by
  obtain ⟨⟨⟨x, aux⟩, f⟩, u⟩ := z
  have hck : (fsIntAbs rkS x u).ck = x.s.ck := rfl
  by_cases hs : aux.safe ΔFS ΔPCS k = true
  · cases d with
    | sm q =>
      rw [smAuthFSImpl_simOracle C R G D ΔFS ΔPCS t k rkS _ ((x, aux), f) u q hs]
      by_cases hbad : ∃ p, q = .corrupt p ∧ ckaAllowCorr ΔFS ΔPCS t x.s.ck p = true ∧
          ckaAllowCorr ΔFS ΔPCS k x.s.ck p = false
      · obtain ⟨p, rfl, h1, h2⟩ := hbad
        have h2' : ckaAllowCorr ΔFS ΔPCS k
            ({ st := fun _ => (), t := x.s.ck.t, msg := () } : CKAGameSt Unit Unit) p = false := h2
        have hs' : (aux.corrs.all fun c => ckaAllowCorr ΔFS ΔPCS k c.2 c.1) = true := hs
        simp [OracleAdv.simOracle, smAuthFSImplAt, OracleAdv.run_mapQueryAnswer, smFSCorr, h1,
          OracleAdv.run_ret, PMF.pure_map, smAuthHopOracle, fsIntAbsA, smAuthHopStep,
          smOracleOfAt, smOracleOf, hck, smAuthCut, SMAuthAux.upd, SMAns.toScheme,
          SMAuthAux.safe, ckaShadow, h2', hs']
      · have hq : ∀ p, q = .corrupt p → ckaAllowCorr ΔFS ΔPCS t x.s.ck p = true →
            ckaAllowCorr ΔFS ΔPCS k x.s.ck p = true := fun p hp h1 => by
          by_contra h2
          exact hbad ⟨p, hp, h1, by simpa using h2⟩
        simp only [smAuthHopOracle, fsIntAbsA, hs, ite_true, smAuthHopStep, hck]
        rw [← smAuthFSImplAt_step C R G D hFS hPCS t k rkS sa false x u hz.fs q hq,
          PMF.map_comp, PMF.map_comp, PMF.map_comp]
        congr 1
        funext y
        by_cases h : (aux.upd (ckaShadow x.s.ck) q y.1.toScheme).safe ΔFS ΔPCS k = false <;>
          simp [smAuthCut, h, fsIntAbsA]
    | deliver p j ad c =>
      have hcorr : u.corr = false := hz.fs.corr
      have hrd : x.rcvX p = false → acdRecvDec G D (fsIntAbs rkS x u).loc p j ad c =
          acdRecvDec G D x.s.loc p j ad c := fun h => by
        simp [acdRecvDec, fsIntAbs, fsAbs, h]
      have hans : acdDeliverAns G D ΔFS ΔPCS k (ckaShadow x.s.ck) (fsIntAbs rkS x u).loc aux p j
          ad c = acdDeliverAns G D ΔFS ΔPCS k (ckaShadow x.s.ck) x.s.loc aux p j ad c := by
        by_cases hr : x.rcvX p = true
        · obtain ⟨hp1, hp2, hp3⟩ := hz.fs.rcv p hr
          have hp2' : k ≤ x.s.ck.t p := hp2
          have hp3' : x.s.ck.t p ≤ k + 1 := hp3
          simp only [acdDeliverAns]
          split_ifs with h1 h2
          · rfl
          · exfalso
            have he : x.s.ck.t p = k + 1 := by simp [ckaShadow] at h1; omega
            simp only [SMAuthAux.canDeliver, Bool.and_eq_true, bne_iff_ne, ne_eq, ckaShadow,
              he] at h2
            rw [ckaSender_succ] at h2
            rcases CKAParty.eq_or_eq_other p (ckaSender k) with h | h
            · exact hp1 h
            · exact h2.1 h.symm
          · rfl
        · simp only [acdDeliverAns, hrd (by simpa using hr)]
      by_cases hc : (decide ((ckaShadow x.s.ck).t p = k) &&
          aux.canDeliver ΔFS ΔPCS (ckaShadow x.s.ck) p && x.rcvX p) = true
      · have hc' := hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
        have hb : acdDeliverBad G D ΔFS ΔPCS k (ckaShadow x.s.ck) (fsIntAbs rkS x u).loc aux p j
            ad c = (D.decrypt (chainKey G u.init j) c ad != aux.logDec k j ad c) := by
          simp [acdDeliverBad, acdRecvDec, fsIntAbs, fsAbs, fsStOfInt, hc'.1.1, hc'.1.2, hc'.2]
        simp only [OracleAdv.simOracle, smAuthFSImpl, hs, ite_true, smAuthFSStep, hc,
          OracleAdv.run_query, fsIntOracle, PMF.pure_bind, OracleAdv.run_ret, PMF.pure_map,
          fsIntDecOf, hcorr, Bool.false_eq_true, ite_false, smAuthHopOracle, fsIntAbsA,
          smAuthHopStep, hck, hans, hb, Prod.map_apply, id_eq]
        simp [smAuthCut, hs]
      · have hb : acdDeliverBad G D ΔFS ΔPCS k (ckaShadow x.s.ck) (fsIntAbs rkS x u).loc aux p j
            ad c = acdDeliverBad G D ΔFS ΔPCS k (ckaShadow x.s.ck) x.s.loc aux p j ad c := by
          by_cases hr : x.rcvX p = true
          · have hab : (decide ((ckaShadow x.s.ck).t p = k) &&
                aux.canDeliver ΔFS ΔPCS (ckaShadow x.s.ck) p) = false := by
              revert hc
              cases (decide ((ckaShadow x.s.ck).t p = k) &&
                aux.canDeliver ΔFS ΔPCS (ckaShadow x.s.ck) p) <;> simp [hr]
            unfold acdDeliverBad
            rw [hab]
            rfl
          · unfold acdDeliverBad
            rw [hrd (by simpa using hr)]
        have hc2 : (decide ((ckaShadow x.s.ck).t p = k) &&
            aux.canDeliver ΔFS ΔPCS (ckaShadow x.s.ck) p && x.rcvX p) = false := by simpa using hc
        simp only [OracleAdv.simOracle, smAuthFSImpl, hs, ite_true, smAuthFSStep, hc2,
          Bool.false_eq_true, ite_false, OracleAdv.run_ret, PMF.pure_map, smAuthHopOracle,
          fsIntAbsA, smAuthHopStep, hck, hans, hb, Prod.map_apply, id_eq]
        simp [smAuthCut, hs]
  · simp [OracleAdv.simOracle, smAuthFSImpl, smAuthHopOracle, fsIntAbsA, hs, PMF.pure_map,
      smAuthCut]

omit [SampleableType W] [SampleableType Ct] [DecidableEq W] [DecidableEq Ct] in
/-- The rejection of the transitions into an unsafe state keeps the state. -/
theorem smAuthCut_snd {Pub Leak S' : Type} (ΔFS ΔPCS k : ℕ)
    (x : SMAuthAns Pub Ct Leak W × ((S' × SMAuthAux W Ct) × Bool)) :
    (smAuthCut ΔFS ΔPCS k x).2 = x.2 := by
  unfold smAuthCut
  split <;> rfl

/-- **The invariant of the simulation is kept** by every call of `smAuthFSImpl` against the
real and the ideal integrity game. -/
theorem smAuthFS_inv (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (rkS : RK) (sa : Sa) (b : Bool)
    (z : ((FSSim Sc Msg RK Sa × SMAuthAux W Ct) × Bool) × FSIntSt Sa W Ct)
    (hz : AuthFSInv k sa z) (d : SMAuthQuery W Ct) (y)
    (hy : y ∈ (OracleAdv.simOracle (smAuthFSImpl C R G D ΔFS ΔPCS t k rkS) (fsIntOracle G D b)
      z d).support) : AuthFSInv k sa y.2 := by
  obtain ⟨⟨⟨x, aux⟩, f⟩, u⟩ := z
  by_cases hs : aux.safe ΔFS ΔPCS k = true
  · cases d with
    | sm q =>
      rw [smAuthFSImpl_simOracle C R G D ΔFS ΔPCS t k rkS _ ((x, aux), f) u q hs,
        PMF.support_map] at hy
      obtain ⟨w, hw, rfl⟩ := hy
      simp only [smAuthCut_snd]
      exact smAuthFSImplAt_inv C R G D ΔFS ΔPCS t k rkS sa b x aux f u hz q w hw f
    | deliver p j ad c =>
      simp only [OracleAdv.simOracle, smAuthFSImpl, hs, ite_true, smAuthFSStep,
        PMF.support_map, Set.mem_image] at hy
      obtain ⟨w, hw, rfl⟩ := hy
      split at hw
      · simp only [OracleAdv.run_query, fsIntOracle, PMF.pure_bind, OracleAdv.run_ret,
          PMF.support_pure, Set.mem_singleton_iff] at hw
        subst hw
        exact hz.flag _
      · simp only [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hw
        subst hw
        exact hz.flag _
  · simp only [OracleAdv.simOracle, smAuthFSImpl, hs, Bool.false_eq_true, ite_false,
      OracleAdv.run_ret, PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact hz

omit [SampleableType Ct] in
/-- **The reduction raises no flag against the ideal integrity game.** Under the invariant, from
a state with the flag cleared, every call of `smAuthFSImpl` against the ideal integrity game
leaves the flag cleared. -/
theorem smAuthFS_ideal_flag (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (rkS : RK) (sa : Sa)
    (z : ((FSSim Sc Msg RK Sa × SMAuthAux W Ct) × Bool) × FSIntSt Sa W Ct)
    (hz : AuthFSInv k sa z) (hf : z.1.2 = false) (d : SMAuthQuery W Ct) (y)
    (hy : y ∈ (OracleAdv.simOracle (smAuthFSImpl C R G D ΔFS ΔPCS t k rkS) (fsIntOracle G D true)
      z d).support) : y.2.1.2 = false := by
  obtain ⟨⟨⟨x, aux⟩, f⟩, u⟩ := z
  simp only at hf
  subst hf
  by_cases hs : aux.safe ΔFS ΔPCS k = true
  · cases d with
    | sm q =>
      rw [smAuthFSImpl_simOracle C R G D ΔFS ΔPCS t k rkS _ ((x, aux), false) u q hs,
        PMF.support_map] at hy
      obtain ⟨w, hw, rfl⟩ := hy
      simp only [smAuthCut_snd]
    | deliver p j ad c =>
      have hcorr : u.corr = false := hz.fs.corr
      simp only [OracleAdv.simOracle, smAuthFSImpl, hs, ite_true, smAuthFSStep,
        PMF.support_map, Set.mem_image] at hy
      obtain ⟨w, hw, rfl⟩ := hy
      split at hw
      · simp only [OracleAdv.run_query, fsIntOracle, PMF.pure_bind, OracleAdv.run_ret,
          PMF.support_pure, Set.mem_singleton_iff] at hw
        subst hw
        simp [fsIntDecOf, hcorr, hz.dec]
      · rename_i hc
        simp only [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hw
        subst hw
        simp only [Bool.false_or]
        by_cases hr : x.rcvX p = true
        · have hab : (decide ((ckaShadow x.s.ck).t p = k) &&
              aux.canDeliver ΔFS ΔPCS (ckaShadow x.s.ck) p) = false := by
            revert hc
            cases (decide ((ckaShadow x.s.ck).t p = k) &&
              aux.canDeliver ΔFS ΔPCS (ckaShadow x.s.ck) p) <;> simp [hr]
          unfold acdDeliverBad
          rw [hab]
          rfl
        · unfold acdDeliverBad
          by_cases hab : (decide ((ckaShadow x.s.ck).t p = k) &&
              aux.canDeliver ΔFS ΔPCS (ckaShadow x.s.ck) p) = true
          · simp only [Bool.and_eq_true, decide_eq_true_eq] at hab
            have hpk : x.s.ck.t p = k := hab.1
            have hrec : p ≠ ckaSender k := by
              have := hab.2
              simp only [SMAuthAux.canDeliver, Bool.and_eq_true, bne_iff_ne, ne_eq,
                ckaShadow, hpk] at this
              exact fun h => this.1 h.symm
            rcases hz.rcvk p hrec hpk with h | ⟨h0, hrn⟩
            · exact absurd h hr
            · have hlog : u.logDec j ad c = aux.logDec k j ad c := hz.dec j ad c
              have hu : u.log = [] := (hz.zero h0).2
              have hrn' : x.s.loc.rcv p = none := hrn
              simp [acdRecvDec, hrn', ckaShadow, hpk, ← hlog, FSIntSt.logDec, hu]
          · simp only [Bool.not_eq_true] at hab
            rw [hab]
            rfl
  · simp only [OracleAdv.simOracle, smAuthFSImpl, hs, Bool.false_eq_true, ite_false,
      OracleAdv.run_ret, PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    rfl

end FSIntHop

/-! ## The FS-AEAD integrity hop of the forgery event -/

section FSIntGame

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [DecidableEq W] [DecidableEq Ct] [Fintype RK] [Nonempty RK] [Fintype Sa]
  [Nonempty Sa]

/-- **Eager sampling of the root output at the epoch `k`.** The run of the truncated hybrid with
a uniform root output at the epoch `k` is the run with the root output drawn in advance. -/
theorem smAuthHop_run_eager_unif (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) {α : Type}
    (A : OracleAdv (SMAuthQuery W Ct) (SMAuthAns Msg Ct (SMPartySt Sc RK Sa) W) α)
    (s : (SMSt Sc Msg RK Sa × SMAuthAux W Ct) × Bool) :
    OracleAdv.run (smAuthHopOracle C R G D ΔFS ΔPCS t k unifRoot) A s =
      (PMF.uniformFintype (RK × Sa)).bind fun y =>
        OracleAdv.run (smAuthHopOracle C R G D ΔFS ΔPCS t k (constRoot (Key := Key) y)) A s := by
  refine OracleAdv.run_eq_bind_eager _ _ (PMF.uniformFintype (RK × Sa))
    (smAuthRootCrit ΔFS ΔPCS k) ?_ ?_ (fun s => smOpened k s.1.1) ?_ ?_ ?_ A s
  · intro s d hc
    cases d with
    | sm q =>
      simp only [smAuthRootCrit, Bool.and_eq_true] at hc
      cases q with
      | ratchet p =>
        have hroot : ∀ rk I, (unifRoot rk I : PMF (RK × Sa)) =
            (PMF.uniformFintype (RK × Sa)).bind fun v => constRoot (Key := Key) v rk I :=
          fun _ _ => (PMF.bind_pure _).symm
        have hq := hc.2
        simp only [smCrit, Bool.and_eq_true] at hq
        have h : smOracleOfAt C R G D ΔFS ΔPCS t k false unifRoot s.1.1 (.ratchet p) =
            (PMF.uniformFintype (RK × Sa)).bind fun v =>
              smOracleOfAt C R G D ΔFS ΔPCS t k false (constRoot v) s.1.1 (.ratchet p) := by
          simp only [smOracleOfAt, smOracleOf, hq.1, hq.2, ite_true, hroot, PMF.bind_bind]
          exact PMF.bind_comm _ _ _
        simp only [smAuthHopOracle, hc.1, ite_true, smAuthHopStep, h, PMF.map_bind]
      | _ => simp [smCrit] at hc
    | deliver p j ad c => simp [smAuthRootCrit] at hc
  · intro v s d hc
    exact smAuthHopOracle_root_congr C R G D ΔFS ΔPCS t k _ _ s d hc
  · intro v s d hc x hx
    exact smAuthHopOracle_opened_of_crit C R G D ΔFS ΔPCS t k _ s d hc x hx
  · intro s d hs x hx
    exact smAuthHopOracle_opened C R G D ΔFS ΔPCS t k _ s d hs x hx
  · intro s d hs
    cases d with
    | sm q => simp [smAuthRootCrit, smCrit_of_opened k s.1.1 hs q]
    | deliver p j ad c => rfl

omit [SampleableType Ct] [Fintype Sa] [Nonempty Sa] in
/-- Running the FS-AEAD integrity reduction against an oracle is running the adversary against
the composed oracle from the drawn initial state, with the flag of a forgery as output. -/
theorem smAuthFSRed_run (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS k : ℕ) (initP : PMF (Msg × Sc × Sc)) (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa))
    {U : Type} (O' : U → FSIntQuery W Ct → PMF (FSIntAns Sa Ct W × U)) (u : U) :
    (OracleAdv.run O' (smAuthFSRed C R G D ΔFS ΔPCS k initP A) u).map Prod.fst =
      A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (PMF.uniformFintype RK).bind fun rkS =>
          (OracleAdv.run (OracleAdv.simOracle (smAuthFSImpl C R G D ΔFS ΔPCS t k rkS) O')
            (A.play t i.1) (((⟨smInit i rk, fun _ => false, fun _ => false, false⟩,
              SMAuthAux.init), false), u)).map fun x => x.2.1.2 := by
  simp only [smAuthFSRed, smAuthFSTree, OracleAdv.run_rand, PMF.map_bind]
  refine congrArg _ (funext fun t => congrArg _ (funext fun i =>
    congrArg _ (funext fun rk => congrArg _ (funext fun rkS => ?_))))
  rw [OracleAdv.run_bind, OracleAdv.run_simulate]
  simp [PMF.map_bind, PMF.bind_map, Function.comp_def, PMF.pure_map]
  rfl

omit [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK] [Fintype Sa]
  [Nonempty Sa] in
/-- The invariant holds at the initial state of the simulation. -/
theorem authFSInv_init (k : ℕ) (rk : RK) (i : Msg × Sc × Sc) (sa : Sa) :
    AuthFSInv k sa ((((⟨smInit i rk, fun _ => false, fun _ => false, false⟩ :
      FSSim Sc Msg RK Sa), (SMAuthAux.init : SMAuthAux W Ct)), false),
        (⟨sa, sa, [], false⟩ : FSIntSt Sa W Ct)) where
  fs := fsInv_init k rk i sa
  len := rfl
  dec _ _ _ := by simp [FSIntSt.logDec, SMAuthAux.logDec, SMAuthAux.init]
  outk p h _ := by cases p <;> simp [smInit, CKAGameSt.init, CKAGameSt.canRecv] at h
  rcvk p _ h := Or.inr ⟨by simpa [smInit, CKAGameSt.init] using h.symm, by simp [smInit,
    SMLoc.init]⟩
  zero _ := ⟨fun _ => rfl, rfl⟩

/-- **The real side of the integrity hop.** With `2 ≤ ΔFS` and `1 ≤ ΔPCS`, for an
initialisation that is the lift of `initP`, the real FS-AEAD integrity game of `smAuthFSRed` is
the game `smAuthRootIdealGame` after the root hop. -/
theorem smAuthFS_real_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS) (k : ℕ)
    (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa)) :
    fsaead_int_game G D false (smAuthFSRed C R G D ΔFS ΔPCS k initP A) =
      smAuthRootIdealGame C R G D ΔFS ΔPCS k A := by
  rw [smAuthRootIdealGame, smAuthHopGame_eq_liftPMF C initP hinit]
  unfold fsaead_int_game
  congr 1
  have h1 : ∀ sa : Sa,
      (OracleAdv.run (fsIntOracle G D false) (smAuthFSRed C R G D ΔFS ΔPCS k initP A)
        ⟨sa, sa, [], false⟩).map Prod.fst =
      A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (PMF.uniformFintype RK).bind fun rkS =>
          (OracleAdv.run (smAuthHopOracle C R G D ΔFS ΔPCS t k (constRoot (Key := Key) (rkS, sa)))
            (A.play t i.1) ((smInit i rk, SMAuthAux.init), false)).map fun x => x.2.2 := by
    intro sa
    rw [smAuthFSRed_run]
    refine congrArg _ (funext fun t => congrArg _ (funext fun i =>
      congrArg _ (funext fun rk => congrArg _ (funext fun rkS => ?_))))
    have h := OracleAdv.run_map_state_inv _ _ (fsIntAbsA rkS) (AuthFSInv k sa)
      (fun z d hz y hy => smAuthFS_inv C R G D ΔFS ΔPCS t k rkS sa false z hz d y hy)
      (fun z d hz => smAuthFS_step C R G D hFS hPCS t k rkS sa z hz d) (A.play t i.1) _
      (authFSInv_init k rk i sa)
    have he : fsIntAbsA rkS ((((⟨smInit i rk, fun _ => false, fun _ => false, false⟩ :
        FSSim Sc Msg RK Sa), (SMAuthAux.init : SMAuthAux W Ct)), false),
          (⟨sa, sa, [], false⟩ : FSIntSt Sa W Ct)) = ((smInit i rk, SMAuthAux.init), false) := by
      simp only [fsIntAbsA, fsIntAbs, fsStOfInt]
      rw [fsAbs_init]
    rw [he] at h
    refine Eq.trans ?_ (congrArg (PMF.map fun x => x.2.2) h)
    rw [PMF.map_comp]
    rfl
  simp only [h1]
  have h2 : ∀ (t : ℕ) (i : Msg × Sc × Sc) (rk : RK),
      (OracleAdv.run (smAuthHopOracle C R G D ΔFS ΔPCS t k unifRoot) (A.play t i.1)
        ((smInit i rk, SMAuthAux.init), false)).map (fun x => x.2.2) =
      (PMF.uniformFintype RK).bind fun rkS => (PMF.uniformFintype Sa).bind fun sa =>
        (OracleAdv.run (smAuthHopOracle C R G D ΔFS ΔPCS t k (constRoot (Key := Key) (rkS, sa)))
          (A.play t i.1) ((smInit i rk, SMAuthAux.init), false)).map fun x => x.2.2 := by
    intro t i rk
    rw [smAuthHop_run_eager_unif, PMF.map_bind, PMF.uniform_prod_eq_bind, PMF.bind_bind]
    refine congrArg _ (funext fun rkS => ?_)
    rw [PMF.bind_map]
    rfl
  simp only [h2, PMF.bind_comm (PMF.uniformFintype Sa)]

/-- **The ideal side of the integrity hop.** Against the integrity game with decryption from its
log, the reduction `smAuthFSRed` never outputs `true`. -/
theorem smAuthFS_ideal_eq_zero (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS k : ℕ) (initP : PMF (Msg × Sc × Sc)) (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa)) :
    prTrue (fsaead_int_game G D true (smAuthFSRed C R G D ΔFS ΔPCS k initP A)) Heap.empty = 0 := by
  unfold fsaead_int_game
  rw [prTrue_liftPMF, PMF.apply_eq_zero_iff]
  simp only [PMF.support_bind, Set.mem_iUnion, not_exists]
  intro sa _
  rw [smAuthFSRed_run]
  simp only [PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image, not_exists,
    not_and]
  intro t _ i _ rk _ rkS _ x hx
  have h := OracleAdv.run_support_inv _ (fun z => AuthFSInv k sa z ∧ z.1.2 = false)
    (fun z d y hz hy => ⟨smAuthFS_inv C R G D ΔFS ΔPCS t k rkS sa true z hz.1 d y hy,
      smAuthFS_ideal_flag C R G D ΔFS ΔPCS t k rkS sa z hz.1 hz.2 d y hy⟩) (A.play t i.1) _
    ⟨authFSInv_init k rk i sa, rfl⟩ x hx
  simp [h.2]

/-- **The FS-AEAD integrity hop of the forgery event at the epoch `k`.** With `2 ≤ ΔFS` and
`1 ≤ ΔPCS`, for an initialisation that is the lift of `initP`, the probability of a forgery at
the epoch `k` in `smAuthRootIdealGame` is at most the FS-AEAD integrity advantage of `G` and `D`
at the reduction `smAuthFSRed C R G D ΔFS ΔPCS k initP A`. -/
theorem smAuthRootIdealGame_le_fsint (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS) (k : ℕ)
    (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa)) :
    prTrue (smAuthRootIdealGame C R G D ΔFS ΔPCS k A) Heap.empty ≤
      FSAEAD_Int_Advantage G D (smAuthFSRed C R G D ΔFS ΔPCS k initP A) := by
  rw [← smAuthFS_real_eq C initP hinit R G D hFS hPCS k A]
  have h0 := smAuthFS_ideal_eq_zero C R G D ΔFS ΔPCS k initP A
  unfold FSAEAD_Int_Advantage Advantage
  simp [h0]

end FSIntGame

section FSIntMain

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [DecidableEq W] [DecidableEq Ct] [Fintype RK] [Nonempty RK] [Fintype Key]
  [Nonempty Key] [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [DecidableEq Key]

/-- **The CKA, root and FS-AEAD integrity hops of the forgery event at the epoch `k`.** For a
CKA correct along `J` with a sound explicit-randomness sending algorithm, an initialisation that
is the lift of `initP`, initial states related by `J`, `2 ≤ ΔFS` and `1 ≤ ΔPCS`, the probability
of a forgery at the epoch `k` in the truncated game over `acdAuthSM C R G D` is at most the CKA
corruption advantage of `smAuthCKARed R G D ΔFS ΔPCS k A`, plus the PRF-PRNG advantage of `R` at
`smAuthRootRed C R G D ΔFS ΔPCS k initP A`, plus the FS-AEAD integrity advantage of `G` and `D`
at `smAuthFSRed C R G D ΔFS ΔPCS k initP A`. -/
theorem acdAuthSM_truncGame_le_fsint (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hS : CKACoins.Sound C) {J : Sc → Sc → Prop} (hJ : CKACorrect C J)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS)
    (hPCS : 1 ≤ ΔPCS) (k : ℕ) (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa)) :
    prTrue (smAuthTruncGame (acdAuthSM C R G D) ΔFS ΔPCS k A) Heap.empty ≤
      CKA_Corrupt_Advantage C ΔFS ΔPCS (smAuthCKARed R G D ΔFS ΔPCS k A) +
        PRFPRNG_Advantage R (smAuthRootRed C R G D ΔFS ΔPCS k initP A) +
        FSAEAD_Int_Advantage G D (smAuthFSRed C R G D ΔFS ΔPCS k initP A) :=
  (acdAuthSM_truncGame_le_root C hS hJ initP hinit hJi R G D ΔFS ΔPCS k A).trans
    (add_le_add le_rfl (smAuthRootIdealGame_le_fsint C initP hinit R G D hFS hPCS k A))

end FSIntMain

end CatCrypt.Crypto.Messaging
