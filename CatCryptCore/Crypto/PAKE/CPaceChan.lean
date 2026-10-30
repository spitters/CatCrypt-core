/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PAKE.CPaceSquare
public import CatCryptCore.Crypto.UCWake
public import CatCryptCore.Crypto.UCChannel
public import CatCryptCore.Crypto.UCChannelLift

/-!
# CPace with two parties over a channel

**Real world.** `cpaceChan G` runs the parties `0` and `1` of CPace over the ideal channel
`FChan ChannelCap.insecure`, with activation on delivery (`Sys.wakeClose`). Its components:

* the CPace functionality `cpaceG G`: the oracle system of the game `realGame G` of
  `CatCryptCore.Crypto.PAKE.CPaceSquare` (the table of `H1` sampled at the first activation, `H2`
  lazily sampled, the secrets and keys of the parties) behind the protocol `gProt`, which
  presents it on an honest port for the parties (`GHEv`: session events, and the delivery of a
  received message to a party) and on an adversary port with the events of `RAEv`;
* the party code `partyHyb`: on a new session it calls `cpaceG G` and sends the party's message
  `H1(pw)^y` on the channel; on the wake of the party `pid` it receives the delivered message
  from the channel and hands it to `cpaceG G` for the key derivation; on `getKey` it returns
  the key;
* the adversary relay `advHyb`: `send pid m` injects `m` into the channel by `tamper`, and every
  other adversary event goes to the adversary port of `cpaceG G`.

The adversary event `send pid m` is a delivery to the party `pid` (`chanDlv`): the wake closure
activates the party `pid` in the same outer activation, and the output of that activation is the
party's output `ok`.

**Bridge.** The real world realizes at distance `0` the monolithic real protocol `cpaceReal G`
behind the relabelling `bridgeSim`, which forwards every event and answers `send pid m` with the
honest output `ok` of the woken party (`cpaceChan_realizes`). The proof is a state map that
forgets the party, relay and channel states, under the invariant that the inbox of the channel
is empty between activations.

**Result.** With `cpace_realizesSim_oracleGame`, the parties over the channel realize
`F_lePAKE` behind `bridgeSim` composed with `cpaceSim G`, with the oracle-game bound at the
environment reduced through the relabelling (`cpaceChan_realizesSim_oracleGame`).

## Main definitions

* `gProt`, `cpaceG`: the CPace functionality of the parties.
* `partyHyb`, `advHyb`: the party code and the adversary relay.
* `cpaceChan`: the parties over the channel, wake-closed.
* `bridgeSim`: the relabelling between the two real worlds.

## Main results

* `cpaceChan_realizes`: distance `0` between `cpaceChan G` and the relabelling of `cpaceReal G`.
* `cpaceChan_realizesSim_oracleGame`: the CPace square for the parties over the channel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PAKE.CPaceChan

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational CatCrypt.NonUniform
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FPAKE
open CatCrypt.Crypto.PAKE.DHExtract CatCrypt.Crypto.PAKE.CPaceSquare
open CatCrypt.Crypto.Choreography (ChannelCap)
open scoped ENNReal

/-! ## The CPace functionality of the parties -/

/-- Events of the honest port of the CPace functionality. -/
inductive GHEv (Pw W : Type) where
  /-- A session event of a party. -/
  | sess (h : LeHEv Pw)
  /-- The party `pid` received the message `m`. -/
  | deliver (pid : PartyId) (m : W)

/-- The answers of the game `realGame`. -/
abbrev Ans (W K : Type) := HOut K ⊕ ROut W K

/-- The protocol that presents `realGame` to the parties and to the adversary: a new session
of `pid` is followed by the query of its message, a delivery is the query `send`, and every
other event is its own query. -/
def gProt {Pw W K : Type} :
    OProt Unit (GHEv Pw W ⊕ RAEv Pw W) (Ans W K ⊕ Ans W K) (LeHEv Pw ⊕ RAEv Pw W) (Ans W K) where
  init := ()
  step _ e := match e with
    | .inl (.sess (.newSession sid pid peer role pw)) =>
      .query (.inl (.newSession sid pid peer role pw)) fun _ =>
        .query (.inr (.msg pid)) fun a => .ret ((), .inl a)
    | .inl (.sess (.getKey sid pid)) => .query (.inl (.getKey sid pid)) fun a => .ret ((), .inl a)
    | .inl (.deliver pid m) => .query (.inr (.send pid m)) fun a => .ret ((), .inl a)
    | .inr a => .query (.inr a) fun b => .ret ((), .inr b)

section Real

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]
  [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] (G : DHGroup S W)

/-- **The CPace functionality of the parties**: `gProt` over the game `realGame G`. -/
noncomputable def cpaceG :=
  (gProt (Pw := Pw) (W := W) (K := K)).sys (realGame G)

end Real

/-! ## The party code and the adversary relay -/

/-- The phase of the party code within an activation. -/
inductive PPhase where
  /-- No call pending. -/
  | rest
  /-- A new session was passed to the functionality. -/
  | newS
  /-- A key request was passed to the functionality. -/
  | fwd
  /-- The message was sent on the channel. -/
  | sent
  /-- The party `pid` was woken and receives from the channel. -/
  | wake (pid : PartyId)
  /-- The received message was handed to the functionality. -/
  | deliv

/-- The next decision of the party code on an answer. -/
def partyResume {Pw W K : Type} :
    PPhase → Ans W K ⊕ ChanHOut W → PPhase × ((GHEv Pw W ⊕ ChanHEv W) ⊕ HOut K)
  | .newS, .inl (.inr (.msg (some m))) => (.sent, .inl (.inr (.send m)))
  | .fwd, .inl (.inl o) => (.rest, .inr o)
  | .wake pid, .inr (.got (some m)) => (.deliv, .inl (.inl (.deliver pid m)))
  | _, _ => (.rest, .inr .ok)

/-- **The party code** of the parties `0` and `1`, on the honest port and the wakes. A new
session goes to the functionality, and the returned message is sent on the channel; a wake of
`pid` receives from the channel and hands the message to the functionality; a key request is
answered by the functionality. -/
noncomputable def partyHyb {Pw W K : Type} :
    MultiHybrid PPhase (LeHEv Pw ⊕ PartyId) (HOut K) (GHEv Pw W ⊕ ChanHEv W)
      (Ans W K ⊕ ChanHOut W) where
  init := .rest
  fuel := 1
  start _ e := match e with
    | .inl (.newSession sid pid peer role pw) =>
      SPComp.pure (.newS, .inl (.inl (.sess (.newSession sid pid peer role pw))))
    | .inl (.getKey sid pid) => SPComp.pure (.fwd, .inl (.inl (.sess (.getKey sid pid))))
    | .inr pid => SPComp.pure (.wake pid, .inl (.inr .recv))
  resume s o := SPComp.pure (partyResume s o)
  finish _ _ := SPComp.pure (.rest, .ok)
  start_noFail _ e := by rcases e with (_ | _) | _ <;> exact SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

/-- The output of the adversary relay on an answer. -/
def advOut {W K : Type} : Ans W K ⊕ ChanAOut W Unit → ROut W K
  | .inl (.inr r) => r
  | _ => .ack

/-- The event of the adversary relay: `send pid m` is the channel event `tamper m`, every other
event goes to the functionality. -/
def advEv {Pw W : Type} : RAEv Pw W → RAEv Pw W ⊕ ChanAEv W
  | .send _ m => .inr (.tamper m)
  | a => .inl a

/-- **The adversary relay**: one call per activation, by `advEv`. -/
noncomputable def advHyb {Pw W K : Type} :
    MultiHybrid Unit (RAEv Pw W) (ROut W K) (RAEv Pw W ⊕ ChanAEv W)
      (Ans W K ⊕ ChanAOut W Unit) where
  init := ()
  fuel := 0
  start _ a := SPComp.pure ((), .inl (advEv a))
  resume _ o := SPComp.pure ((), .inr (advOut o))
  finish _ o := SPComp.pure ((), advOut o)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

/-- The delivery map: `send pid m` delivers to the party `pid`. -/
def chanDlv {Pw W : Type} : RAEv Pw W → Option PartyId
  | .send pid _ => some pid
  | _ => none

/-- The cut-off map of the wake closure: `ok`. -/
def chanCut {W K : Type} (_ : PartyId) : HOut K ⊕ ROut W K := .inl .ok

section Real

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]
  [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] (G : DHGroup S W)

/-- The channel of the parties: `FChan` with every adversary power and no leakage beyond the
plaintext. -/
noncomputable def chan : Sys (ChanSt W) (ChanHEv W ⊕ ChanAEv W) (ChanHOut W ⊕ ChanAOut W Unit) :=
  FChan ChannelCap.insecure fun _ => ()

/-- The parties and the adversary relay over the functionality beside the channel, before the
wake closure. -/
noncomputable def chanOpen :=
  ((partyHyb (Pw := Pw) (W := W) (K := K)).tensor advHyb).withSub
    ((cpaceG G (Pw := Pw) (K := K)).withChan chan)

/-- **CPace with two parties over the channel**, wake-closed: a delivery by `send pid m`
activates the party `pid`. -/
noncomputable def cpaceChan :=
  (chanOpen G (Pw := Pw) (K := K)).wakeClose chanDlv chanCut

end Real

/-! ## The bridge -/

/-- The tag of the bridge: whether the event is a delivery. -/
def bridgeEv {Pw W : Type} : OEv Pw W → Bool × OEv Pw W
  | .inr (.send pid m) => (true, .inr (.send pid m))
  | e => (false, e)

/-- The output of the bridge: the output `ok` of the woken party at a delivery. -/
def bridgeOut {W K : Type} : Bool → OOut W K → OOut W K
  | true, _ => .inl .ok
  | false, o => o

/-- The relabelling hybrid of the bridge is opaque for the password-blind view. -/
theorem bridge_opaque {Pw W K : Type} :
    (MultiHybrid.ofHybrid (Hybrid.relabel false (bridgeEv (Pw := Pw) (W := W))
      (bridgeOut (K := K)))).Opaque outerView outerView := by
  refine MultiHybrid.relabel_opaque _ _ _ _ _ ?_ ?_
  · rintro (h | a) (h' | a') he
    · exact ⟨rfl, he⟩
    · exact absurd he Sum.not_liftRel_inl_inr
    · exact absurd he Sum.not_liftRel_inr_inl
    · have he' : a = a' := Sum.liftRel_inr_inr.mp he
      subst he'
      cases a <;> exact ⟨rfl, Sum.LiftRel.inr rfl⟩
  · rintro (_ | _) o o' ho
    · exact ho
    · exact Sum.LiftRel.inl trivial

/-- **The bridge** between the parties over the channel and `cpaceReal`: the relabelling by
`bridgeEv` and `bridgeOut`. -/
noncomputable def bridgeSim {Pw W K : Type} :
    Simulator (OEv Pw W) (OOut W K) (OEv Pw W) (OOut W K) outerView outerView :=
  Simulator.ofMultiHybrid _ (bridge_opaque (Pw := Pw) (W := W) (K := K))

/-- Sampling from a bound probability mass function is sampling the first value and then from
its continuation. -/
theorem sampleFrom_ofPMF_bind' {α β : Type} (p : PMF α) (f : α → PMF β) :
    sampleFrom (ofPMF (p.bind f)) =
      SPComp.bind (sampleFrom (ofPMF p)) fun a => sampleFrom (ofPMF (f a)) := by
  rw [sampleFrom_bind_sampleFrom]
  congr 1
  simp only [ofPMF, CatCrypt.Prob.SDistr.bind, PMF.map_bind, PMF.bind_map, Function.comp_def]

/-- Sampling from a point mass is returning its point. -/
theorem sampleFrom_ofPMF_pure {α : Type} (a : α) :
    sampleFrom (ofPMF (PMF.pure a)) = SPComp.pure a := by
  rw [← sampleFrom_pure]
  congr 1
  simp [ofPMF, CatCrypt.Prob.SDistr.pure, PMF.pure_map]

/-- Sampling from the image of a probability mass function is sampling from it and returning
the image. -/
theorem sampleFrom_ofPMF_map' {α β : Type} (p : PMF α) (g : α → β) :
    sampleFrom (ofPMF (p.map g)) =
      SPComp.bind (sampleFrom (ofPMF p)) fun a => SPComp.pure (g a) := by
  rw [PMF.map, sampleFrom_ofPMF_bind']
  simp only [Function.comp_apply, sampleFrom_ofPMF_pure]

/-- Mapping by `h` and then by a left inverse `k` of `h` is the identity. -/
theorem map_map_of_leftInv {α β : Type} (c : SPComp α) (h : α → β) (k : β → α)
    (hk : ∀ a, k (h a) = a) : SPComp.map k (SPComp.map h c) = c := by
  simp [SPComp.map, SPComp.bind_assoc, hk, SPComp.bind_pure]

section Bridge

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]
  [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] (G : DHGroup S W)

/-- The functionality state of a state of `cpaceChan G`. -/
def fState (t : Unit × ((PPhase × Unit) ×
    ((Option (Pw → Sˣ) × (Unit × RSt S W Pw K)) × ChanSt W))) :
    Option (Pw → Sˣ) × (Unit × RSt S W Pw K) :=
  t.2.2.1

/-- The message of the party `pid` at a state of `cpaceReal G`, once the table of `H1` is
sampled. -/
def msgAt (g : Option (Pw → Sˣ) × (Unit × RSt S W Pw K)) (pid : PartyId) : Option W :=
  match g.1 with
  | some td => realMsg G td g.2.2 pid
  | none => none

/-- A step of the functionality on an adversary event is the step of `cpaceReal G`. -/
theorem cpaceG_step_adv (g : Option (Pw → Sˣ) × (Unit × RSt S W Pw K)) (a : RAEv Pw W) :
    (cpaceG G).step g (.inr a) =
      SPComp.map (fun q => (q.1, .inr q.2)) ((cpaceReal G (K := K)).step g (.inr a)) := by
  obtain ⟨_ | td, u, s⟩ := g <;>
    simp [cpaceG, cpaceReal, OProt.sys, KeyedSys.lazy, KeyedSys.lazyStep, OProt.keyed,
      OProt.plugStep, gProt, OProt.oracle, sampleFrom_ofPMF_bind', sampleFrom_ofPMF_pure,
      OracleAdv.run_query, OracleAdv.run_ret, realGame,
      SPComp.map, SPComp.bind_assoc]

/-- A delivery to the functionality is the step of `cpaceReal G` on `send`. -/
theorem cpaceG_step_deliver (g : Option (Pw → Sˣ) × (Unit × RSt S W Pw K)) (pid : PartyId)
    (m : W) :
    (cpaceG G).step g (.inl (.deliver pid m)) =
      SPComp.map (fun q => (q.1, .inl q.2))
        ((cpaceReal G (K := K)).step g (.inr (.send pid m))) := by
  obtain ⟨_ | td, u, s⟩ := g <;>
    simp [cpaceG, cpaceReal, OProt.sys, KeyedSys.lazy, KeyedSys.lazyStep, OProt.keyed,
      OProt.plugStep, gProt, OProt.oracle, sampleFrom_ofPMF_bind', sampleFrom_ofPMF_pure,
      OracleAdv.run_query, OracleAdv.run_ret, realGame,
      SPComp.map, SPComp.bind_assoc]

/-- A key request to the functionality is the step of `cpaceReal G`. -/
theorem cpaceG_step_getKey (g : Option (Pw → Sˣ) × (Unit × RSt S W Pw K)) (sid pid : PartyId) :
    (cpaceG G).step g (.inl (.sess (.getKey sid pid))) =
      SPComp.map (fun q => (q.1, .inl q.2))
        ((cpaceReal G (K := K)).step g (.inl (.getKey sid pid))) := by
  obtain ⟨_ | td, u, s⟩ := g <;>
    simp [cpaceG, cpaceReal, OProt.sys, KeyedSys.lazy, KeyedSys.lazyStep, OProt.keyed,
      OProt.plugStep, gProt, OProt.oracle, sampleFrom_ofPMF_bind', sampleFrom_ofPMF_pure,
      OracleAdv.run_query, OracleAdv.run_ret, realGame,
      SPComp.map, SPComp.bind_assoc]

/-- A new session at the functionality is the step of `cpaceReal G`, answered by the message
of the party. -/
theorem cpaceG_step_newSession (g : Option (Pw → Sˣ) × (Unit × RSt S W Pw K))
    (sid pid peer : PartyId) (role : Role) (pw : Pw) :
    (cpaceG G).step g (.inl (.sess (.newSession sid pid peer role pw))) =
      SPComp.map (fun q => (q.1, .inl (.inr (.msg (msgAt G q.1 pid)))))
        ((cpaceReal G (K := K)).step g (.inl (.newSession sid pid peer role pw))) := by
  obtain ⟨_ | td, u, s⟩ := g <;>
    simp [cpaceG, cpaceReal, OProt.sys, KeyedSys.lazy, KeyedSys.lazyStep, OProt.keyed,
      OProt.plugStep, gProt, OProt.oracle, sampleFrom_ofPMF_bind', sampleFrom_ofPMF_pure,
      OracleAdv.run_query, OracleAdv.run_ret, realGame,
      SPComp.map, SPComp.bind_assoc, realAdv, msgAt]

/-- The output of `cpaceReal G` on a new session is `ok`. -/
theorem cpaceReal_step_newSession (g : Option (Pw → Sˣ) × (Unit × RSt S W Pw K))
    (sid pid peer : PartyId) (role : Role) (pw : Pw) :
    (cpaceReal G (K := K)).step g (.inl (.newSession sid pid peer role pw)) =
      SPComp.map (fun q => (q.1, .inl .ok))
        ((cpaceReal G (K := K)).step g (.inl (.newSession sid pid peer role pw))) := by
  obtain ⟨_ | td, u, s⟩ := g <;>
    by_cases hc : s.st.recs (sid, pid) = none ∧ Active sid pid peer = true <;>
    simp [cpaceReal, OProt.sys, KeyedSys.lazy, KeyedSys.lazyStep, OProt.keyed,
      OProt.plugStep, OProt.oracle, realGame, realHon, OracleAdv.run_query,
      OracleAdv.run_ret, hc, sampleFrom_ofPMF_bind', sampleFrom_ofPMF_pure, SPComp.map,
      SPComp.bind_assoc]

/-- The honest part of an answer of `realGame`. -/
def hOut : Ans W K → HOut K
  | .inl o => o
  | .inr _ => .ok

/-- The output of `cpaceReal G` on a key request is on the honest port. -/
theorem cpaceReal_step_getKey (g : Option (Pw → Sˣ) × (Unit × RSt S W Pw K))
    (sid pid : PartyId) :
    (cpaceReal G (K := K)).step g (.inl (.getKey sid pid)) =
      SPComp.map (fun q => (q.1, .inl (hOut q.2)))
        ((cpaceReal G (K := K)).step g (.inl (.getKey sid pid))) := by
  obtain ⟨_ | td, u, s⟩ := g <;>
    simp [cpaceReal, OProt.sys, KeyedSys.lazy, KeyedSys.lazyStep, OProt.keyed,
      OProt.plugStep, OProt.oracle, realGame, realHon, OracleAdv.run_query,
      OracleAdv.run_ret, sampleFrom_ofPMF_pure, SPComp.map, SPComp.bind_assoc, hOut]

/-- The output of `cpaceReal G` on an adversary event is on the adversary port. -/
theorem cpaceReal_step_adv (g : Option (Pw → Sˣ) × (Unit × RSt S W Pw K)) (a : RAEv Pw W) :
    (cpaceReal G (K := K)).step g (.inr a) =
      SPComp.map (fun q => (q.1, .inr (advOut (.inl q.2))))
        ((cpaceReal G (K := K)).step g (.inr a)) := by
  obtain ⟨_ | td, u, s⟩ := g <;>
    simp [cpaceReal, OProt.sys, KeyedSys.lazy, KeyedSys.lazyStep, OProt.keyed,
      OProt.plugStep, OProt.oracle, realGame, OracleAdv.run_query,
      OracleAdv.run_ret, sampleFrom_ofPMF_bind', sampleFrom_ofPMF_pure, SPComp.map,
      SPComp.bind_assoc, advOut]

/-- The phase of the party code after an outer event. -/
def phAfter (ph : PPhase) : OEv Pw W → PPhase
  | .inl _ => .rest
  | .inr (.send _ _) => .rest
  | .inr _ => ph

/-- The channel after an outer event that leads to the functionality state `g`. -/
def chanAfter (c : ChanSt W) (e : OEv Pw W) (g : Option (Pw → Sˣ) × (Unit × RSt S W Pw K)) :
    ChanSt W :=
  match e with
  | .inl (.newSession _ pid _ _ _) =>
    match msgAt G g pid with
    | some m => ⟨c.queue ++ [m], c.cursor, c.inbox⟩
    | none => c
  | .inr (.send _ _) => ⟨c.queue.tail, c.cursor - 1, []⟩
  | _ => c

/-- The state of `cpaceChan G` after an outer event from the state `t`, with the functionality
state `g`. -/
def lift (t : Unit × ((PPhase × Unit) ×
    ((Option (Pw → Sˣ) × (Unit × RSt S W Pw K)) × ChanSt W))) (e : OEv Pw W)
    (g : Option (Pw → Sˣ) × (Unit × RSt S W Pw K)) :
    Unit × ((PPhase × Unit) × ((Option (Pw → Sˣ) × (Unit × RSt S W Pw K)) × ChanSt W)) :=
  ((), ((phAfter t.2.1.1 e, ()), (g, chanAfter G t.2.2.2 e g)))

/-- **A step of the parties over the channel**, from a state with an empty inbox, is a step of
the relabelling of `cpaceReal G` from its functionality state, followed by `lift`. -/
theorem cpaceChan_step (t : Unit × ((PPhase × Unit) ×
    ((Option (Pw → Sˣ) × (Unit × RSt S W Pw K)) × ChanSt W))) (ht : t.2.2.2.inbox = [])
    (e : OEv Pw W) :
    (cpaceChan G).step t e = SPComp.map (fun q => (lift G t e q.1, q.2))
      (((cpaceReal G (K := K)).relabel bridgeEv bridgeOut).step (fState t) e) := by
  obtain ⟨⟨⟩, ⟨ph, ⟨⟩⟩, g, c⟩ := t
  simp only at ht
  rcases e with (⟨sid, pid, peer, role, pw⟩ | ⟨sid, pid⟩) | a
  · simp only [Sys.relabel, bridgeEv, bridgeOut, fState]
    rw [cpaceReal_step_newSession]
    simp only [cpaceChan, Sys.wakeClose, Sys.loopback, MultiHybrid.withSub,
      MultiHybrid.fbHybrid, Sys.relabel, chanOpen, MultiHybrid.tensor, partyHyb, advHyb, zero_le,
      sup_of_le_left, SPComp.map, SPComp.pure_bind, Sum.map_inl, Sum.map_inr, Sys.withChan,
      Sys.mapPorts, Sys.par, chan, FChan, Sys.ofPorts, FChan.honSys, FChan.honStep,
      FChan.advSys, FChan.advStep, cond_eq_ite, chanEv, chanOut, wakeEv, wakeOut,
      SPComp.bind_assoc, MultiHybrid.drive, Sum.elim_inl, cpaceG_step_newSession, Prod.mk.eta,
      SPComp.bind_pure, lift, phAfter, chanAfter]
    refine congrArg _ (funext fun q => ?_)
    cases msgAt G q.1 pid <;> simp [partyResume, MultiHybrid.drive] <;> rfl
  · simp only [cpaceChan, Sys.wakeClose, Sys.loopback, MultiHybrid.withSub,
      MultiHybrid.fbHybrid, Sys.relabel, chanOpen, MultiHybrid.tensor, partyHyb, advHyb, zero_le,
      sup_of_le_left, SPComp.map, SPComp.pure_bind, Sum.map_inl, Sum.map_inr, Sys.withChan,
      Sys.mapPorts, Sys.par, chan, FChan, Sys.ofPorts, FChan.honSys, FChan.honStep,
      FChan.advSys, FChan.advStep, cond_eq_ite, chanEv, chanOut, wakeEv, wakeOut,
      SPComp.bind_assoc, MultiHybrid.drive, Sum.elim_inl, cpaceG_step_getKey, Prod.mk.eta,
      SPComp.bind_pure, lift, phAfter, chanAfter, bridgeEv, bridgeOut, fState]
    rw [cpaceReal_step_getKey]
    simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, partyResume, Sum.map_inr,
      MultiHybrid.drive]
    rfl
  · cases a <;> simp only [Sys.relabel, bridgeEv, bridgeOut, fState] <;>
    rw [cpaceReal_step_adv] <;>
    simp [cpaceChan, chanOpen, Sys.wakeClose, Sys.loopback, Sys.relabel, MultiHybrid.withSub,
      MultiHybrid.fbHybrid, MultiHybrid.drive, wakeEv, wakeOut, MultiHybrid.tensor, partyHyb,
      advHyb, Sys.withChan, Sys.mapPorts, Sys.par, chanEv, chanOut, chan, FChan, Sys.ofPorts,
      FChan.honSys, FChan.advSys, FChan.honStep, FChan.advStep, cpaceG_step_adv,
      cpaceG_step_deliver, partyResume, advEv, advOut, chanDlv, FChan.popTo, ht,
      ChannelCap.insecure, SPComp.map, SPComp.bind_assoc, lift, phAfter, chanAfter] <;>
    rfl

omit [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype Pw] [DecidableEq Pw] [Fintype K]
  [Nonempty K] in
/-- The inbox of the channel is empty after `lift`, from a state with an empty inbox. -/
theorem lift_inbox (t : Unit × ((PPhase × Unit) ×
    ((Option (Pw → Sˣ) × (Unit × RSt S W Pw K)) × ChanSt W))) (ht : t.2.2.2.inbox = [])
    (e : OEv Pw W) (g : Option (Pw → Sˣ) × (Unit × RSt S W Pw K)) :
    (lift G t e g).2.2.2.inbox = [] := by
  rcases e with (⟨sid, pid, peer, role, pw⟩ | ⟨sid, pid⟩) | a
  · simp only [lift, chanAfter]
    cases msgAt G g pid <;> exact ht
  · exact ht
  · cases a <;> first | rfl | exact ht

/-- **The parties over the channel realize the monolithic real protocol** at distance `0`:
`cpaceChan G` realizes `cpaceReal G` relabelled by the bridge. -/
theorem cpaceChan_realizes :
    Realizes (cpaceChan G (Pw := Pw) (K := K)) ((cpaceReal G (K := K)).relabel bridgeEv bridgeOut)
      (fun _ _ => 0) :=
  realizes_zero_of_stepMap_on _ _ (fun t => t.2.2.2.inbox = []) fState rfl rfl
    (fun t e ht => ⟨_, ((cpaceReal G (K := K)).relabel bridgeEv bridgeOut).step (fState t) e,
      fun q => (lift G t e q.1, q.2), by rw [cpaceChan_step G t ht e]; rfl,
      fun q => lift_inbox G t ht e q.1⟩)
    (fun t e ht => by
      rw [cpaceChan_step G t ht e]
      exact map_map_of_leftInv _ _ _ fun _ => rfl)

end Bridge

/-- The bridge running with `X` has the view of the relabelling of `X`. -/
theorem view_bridgeSim {Pw W K τ ζ : Type} (X : Sys τ (OEv Pw W) (OOut W K))
    (Z : Strat ζ _ _) :
    view ((bridgeSim (Pw := Pw) (W := W) (K := K)).withSub X) Z =
      view (X.relabel bridgeEv bridgeOut) Z := by
  change view ((MultiHybrid.ofHybrid (Hybrid.relabel false bridgeEv bridgeOut)).withSub X) Z = _
  rw [MultiHybrid.ofHybrid_withSub]
  refine view_eq_of_stepMap _ _ Prod.snd rfl (fun t e => ?_) Z
  simp [Hybrid.withSub, Hybrid.relabel, Sys.relabel, SPComp.map, SPComp.bind_assoc]

section Square

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]
  [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- **CPace with two parties over the channel realizes `F_lePAKE`** behind the bridge composed
with `cpaceSim G` (genuine UC). For every environment `Z`, the distance is at most the advantage
of the oracle adversary `OProt.oracle.reduction` of the environment reduced through the bridge,
between `realGame G` and `simGame G`. -/
theorem cpaceChan_realizesSim_oracleGame :
    RealizesSim (cpaceChan G (Pw := Pw) (K := K)) (F_lePAKE (Pw := Pw) (SPComp.sample K))
      (bridgeSim.comp (cpaceSim G))
      (fun _ Z => KeyedGame.advantage (realGame G) (simGame G)
        (OProt.oracle.reduction ((Open.relabel false bridgeEv bridgeOut).reduceEnv Z))) := by
  have h := Realizes.trans (cpaceChan_realizes G (Pw := Pw) (K := K))
    (Open.realizes_relabel false bridgeEv bridgeOut (cpace_realizesSim_oracleGame G (K := K)))
  intro ζ
  have hv : (view ((bridgeSim.comp (cpaceSim G)).withSub
      (F_lePAKE (Pw := Pw) (SPComp.sample K))) : Strat ζ _ _ → _) =
      view (((cpaceSim G).withSub (F_lePAKE (Pw := Pw) (SPComp.sample K))).relabel
        bridgeEv bridgeOut) :=
    funext fun Z => view_bridgeSim _ Z
  change DistC _ (view ((bridgeSim.comp (cpaceSim G)).withSub _)) _
  rw [hv]
  exact (h ζ).mono fun _ => le_of_eq (zero_add _)

end Square

end CatCrypt.Crypto.PAKE.CPaceChan
