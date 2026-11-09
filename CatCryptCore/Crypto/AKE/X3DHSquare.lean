/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.FAKESys
public import CatCryptCore.Crypto.PAKE.CPaceSquare
public import CatCryptCore.Crypto.KDFLazyEager

/-!
# X3DH against the authenticated key-exchange functionality

**Ideal functionality.** `F_AKE (SPComp.sample K) true` of `CatCryptCore.Crypto.AKE.FAKESys`:
the multi-session authenticated key exchange of Canetti and Krawczyk with adversarial key
delivery and corruption of parties, with uniform keys in `K`, in its variant `unlinked` for
implicitly authenticated key exchange without key confirmation. In that variant the unlinked
delivery `newKeyUnlinked` gives a session a key independent of its partner's: an attacker that
replaces the initiator's ephemeral key on its way to the responder causes the two to derive
different keys. Below, `F_AKE` names this variant. Corruption in `F_AKE` is adaptive; the real
protocol and the simulator use it statically.

**Algorithms.** `AKEAlg S W` is the record of the algorithms of the protocol: the public key of
a secret and the inputs of the key derivation computed by the initiator and by the responder.
`x3dhRealOf A` is the real protocol of the record `A`, with secrets drawn uniformly from `S`;
X3DH over a group `G : DHGroup S W` is the record `x3dhAlg G` (also the coercion of `G`), and
`x3dhReal G` is `x3dhRealOf (x3dhAlg G)`.

**Real protocol.** `x3dhReal G` runs X3DH (Marlinspike and Perrin, *The X3DH Key Agreement
Protocol*, 2016) for every session, over the group `G : DHGroup S W` and with the key-derivation
function a lazily sampled random function into `K`. The variant:
* every party `p` has an identity key `ik` and a signed prekey `spk`, sampled at their first
  use; their public parts are read on the adversary port (`pub p`) and are authentic: a party
  uses the public keys of its peer as registered, so the signature on the prekey is not
  modelled;
* a session of the responder `b` in `sid` draws a one-time prekey `opk` at its start, and a
  session of the initiator `a` an ephemeral key `ek`; their public parts are read with
  `ephPub sid p`;
* the initiator completes on `complete sid a`, once its peer `b` has a responder session in
  `sid`, with the key `KDF(sid, a, b, DH1, DH2, DH3, DH4)` where `DH1 = SPK_b^{ik_a}`,
  `DH2 = IK_b^{ek}`, `DH3 = SPK_b^{ek}`, `DH4 = OPK_b^{ek}` (`aliceInp`);
* the responder completes on `send sid b E`, the delivery of the ephemeral public key `E`, with
  the key `KDF(sid, a, b, IK_a^{spk_b}, E^{ik_b}, E^{spk_b}, E^{opk_b})` (`bobInp`);
* corruption is static: `corrupt p` reveals the long-term secrets of `p` and marks it corrupt
  when no session names `p`, and is refused otherwise;
* `kdf x` queries the key-derivation function.

The initiator's and the responder's inputs agree when the responder receives the initiator's
ephemeral key (`aliceInp_eq_bobInp`), so partners derive the same key.

**Simulator.** `x3dhSim G` keeps a copy of the real state: the honest events carry no secret, so
it draws every long-term and session secret itself, forwards the honest events to `F_AKE`, and
answers `poll`, `pub`, `ephPub` and `kdf` as the real protocol does on its copy. On `corrupt p`
it corrupts `p` in `F_AKE` under the same static rule. When a session completes it computes the
session's key-derivation input `ip` (`deliver`):
* for an exposed session (its party or its peer corrupt), it samples the key derivation at `ip`
  and passes the value to `newKey`, which `F_AKE` delivers;
* otherwise it leaves the key-derivation table unchanged and calls `newKey` when the partner has
  not completed or completed with the input `ip`, and `newKeyUnlinked` otherwise; `F_AKE`
  delivers a uniform key or the partner's.
The simulator reads no key of `F_AKE` (`simProt_opaque`).

**Results.** The simulator running with `F_AKE` is a system whose steps do not read the heap; it
is at distance `0` from the oracle system of the game `simGame G` (`simWorld_realizes`). The
square is the oracle-game bound `x3dh_realizesSim_oracleGame`: `x3dhRealOf (x3dhAlg G)`
realizes `F_AKE` behind `x3dhSim G` with bound, at the environment `Z`, the advantage of the
oracle adversary `OProt.oracle.reduction Z` between `realGame G` and `simGame G`.

## Main definitions

* `Inp`, `aliceInp`, `bobInp`: the inputs of the key derivation.
* `AKEAlg`, `x3dhAlg`: the record of the algorithms, and its instance at a group.
* `KDFOp`: a key-derivation operation with state; `lazyKDF` (a lazily sampled random function),
  `eagerKDF` (a value drawn at the start of each session), `fixedKDF` (a fixed function).
* `RStT`, `RSt`, `RAEv`, `ROut`: the state and the adversary port of the real protocol.
* `realGameK`, `x3dhRealOfK`: the real protocol of a record with a key-derivation operation as an
  oracle game and as a system; `realGame` and `x3dhRealOf` are their applications at `lazyKDF`.
* `eagerKernel`: the pool of keys of the pending sessions, the kernel from `lazyKDF` to
  `eagerKDF`.
* `x3dhReal`: the real X3DH protocol over a group, `x3dhRealOf (x3dhAlg G)`.
* `simStart`: the start of an activation of the simulator, a computation over uniform draws of
  the secrets and of the key-derivation values (`ltStep`, `roStep`, `deliver`).
* `simProt`, `x3dhSim`: the simulator.
* `simGame`: the oracle game of the simulated world.

## Main results

* `aliceInp_eq_bobInp`: the two sides of an unmodified exchange derive from the same input.
* `simProt_opaque`: opacity of the simulator.
* `F_AKE_pureNF`, `simWorld_realizes`.
* `x3dh_realizesSim_oracleGame`: X3DH realizes `F_AKE` behind `x3dhSim` with the oracle-game
  bound.
* `x3dhRealOf_lazy_eager`: the real protocol with the lazily sampled key derivation and the real
  protocol with each session's key-derivation value drawn at its start are at distance `0`
  (`Realizes.ofKernel` at `eagerKernel`, with `drawPool_consume`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquare

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Crypto.PAKE.CPaceSquare (roAt PureNF pureNF_pure pureNF_sample PureNF.map PureNF.bind
  withSub_pureNF pureGame pureGame_realizes)
open PubView (eqView)
open scoped ENNReal

/-! ## Inputs of the key derivation -/

/-- An input of the key derivation: the session, the initiator, the responder, and the four
Diffie–Hellman values. -/
structure Inp (W : Type) where
  /-- The session. -/
  sid : SessionId
  /-- The initiator. -/
  ini : PartyId
  /-- The responder. -/
  res : PartyId
  /-- `DH1`, between the initiator's identity key and the responder's signed prekey. -/
  dh1 : W
  /-- `DH2`, between the initiator's ephemeral key and the responder's identity key. -/
  dh2 : W
  /-- `DH3`, between the initiator's ephemeral key and the responder's signed prekey. -/
  dh3 : W
  /-- `DH4`, between the initiator's ephemeral key and the responder's one-time prekey. -/
  dh4 : W
  deriving DecidableEq

section Inputs

variable {S W : Type} [Field S] (G : DHGroup S W)

/-- The input of the initiator `a` with identity secret `ik` and ephemeral secret `ek`, for the
responder `b` with public identity key `IKB`, signed prekey `SPKB` and one-time prekey
`OPKB`. -/
def aliceInp (sid : SessionId) (a b : PartyId) (ik ek : S) (IKB SPKB OPKB : W) : Inp W :=
  ⟨sid, a, b, G.exp SPKB ik, G.exp IKB ek, G.exp SPKB ek, G.exp OPKB ek⟩

/-- The input of the responder `b` with identity secret `ik`, signed-prekey secret `spk` and
one-time-prekey secret `opk`, for the initiator `a` with public identity key `IKA`, on the
ephemeral public key `E`. -/
def bobInp (sid : SessionId) (a b : PartyId) (IKA E : W) (ik spk opk : S) : Inp W :=
  ⟨sid, a, b, G.exp IKA spk, G.exp E ik, G.exp E spk, G.exp E opk⟩

/-- **Agreement of an unmodified exchange.** The responder that receives the initiator's
ephemeral public key derives from the initiator's input. -/
theorem aliceInp_eq_bobInp (sid : SessionId) (a b : PartyId) (ikA ek ikB spkB opkB : S) :
    aliceInp G sid a b ikA ek (G.pub ikB) (G.pub spkB) (G.pub opkB) =
      bobInp G sid a b (G.pub ikA) (G.pub ek) ikB spkB opkB := by
  simp only [aliceInp, bobInp, G.exp_pub, mul_comm]

end Inputs

/-! ## The algorithms of the protocol -/

/-- **The algorithms of an X3DH key exchange.** Secrets are scalars `S`, public keys are values
`W`, and a party computes the input of the key derivation from its own secrets and the public
keys of its peer:
* `pub` is the public key of a secret;
* `initInp sid a b ik ek IKB SPKB OPKB` is the input of the initiator `a` with identity secret
  `ik` and ephemeral secret `ek`, for the responder `b` with public identity key `IKB`, signed
  prekey `SPKB` and one-time prekey `OPKB`;
* `respInp sid a b IKA E ik spk opk` is the input of the responder `b` with identity secret `ik`,
  signed-prekey secret `spk` and one-time-prekey secret `opk`, for the initiator `a` with public
  identity key `IKA`, on the ephemeral public key `E`.
The real protocol `x3dhRealOf` is defined for every record; the secrets are drawn uniformly
from `S`. X3DH over a group `G` is the record `x3dhAlg G`. -/
structure AKEAlg (S W : Type) where
  /-- The public key of a secret. -/
  pub : S → W
  /-- The input of the key derivation of the initiator. -/
  initInp : SessionId → PartyId → PartyId → S → S → W → W → W → Inp W
  /-- The input of the key derivation of the responder. -/
  respInp : SessionId → PartyId → PartyId → W → W → S → S → S → Inp W

/-- **The algorithms of X3DH over the group `G`**: the public key `g^s`, and the inputs
`aliceInp G` and `bobInp G`. -/
abbrev x3dhAlg {S W : Type} [Field S] (G : DHGroup S W) : AKEAlg S W :=
  ⟨G.pub, aliceInp G, bobInp G⟩

/-- A group gives the algorithms of X3DH over it. -/
instance {S W : Type} [Field S] : Coe (DHGroup S W) (AKEAlg S W) := ⟨x3dhAlg⟩

/-! ## The real protocol -/

/-- **A key-derivation operation** on inputs `D` with keys `K` and state `T`: the initial state,
the update of the state at the start of a session, the key of a session at an input, and the
answer to a query of the adversary at an input. -/
structure KDFOp (T D K : Type) where
  /-- The initial state. -/
  init : T
  /-- The update of the state at the start of a session. -/
  start : T → Inst → PMF T
  /-- The key of a session at an input. -/
  derive : T → Inst → D → PMF (K × T)
  /-- The answer to a query of the adversary at an input. -/
  query : T → D → PMF (K × T)

/-- **The key derivation as a fixed function** `H`, without state. -/
noncomputable def fixedKDF {D K : Type} (H : D → K) : KDFOp Unit D K where
  init := ()
  start t _ := PMF.pure t
  derive t _ d := PMF.pure (H d, t)
  query t d := PMF.pure (H d, t)

section KDFOps

variable {D K : Type} [DecidableEq D] [Fintype K] [Nonempty K]

/-- **The key derivation as a lazily sampled random function**: a table, answered by `roAt` for
the sessions and for the adversary. -/
noncomputable def lazyKDF : KDFOp (List (D × K)) D K where
  init := []
  start t _ := PMF.pure t
  derive t _ d := roAt t d
  query := roAt

/-- **The key derivation with values drawn in advance**: a table and a pool of keys. A session
draws a uniform key into the pool at its start; its key derivation is `roAtDrawn` with the key of
the pool, which is removed, and `roAt` when the pool has none. The adversary's queries are
answered by `roAt` on the table. -/
noncomputable def eagerKDF : KDFOp (List (D × K) × (Inst → Option K)) D K where
  init := ([], fun _ => none)
  start t x := (PMF.uniformFintype K).map fun k => (t.1, Function.update t.2 x (some k))
  derive t x d :=
    match t.2 x with
    | some k =>
      PMF.pure ((roAtDrawn t.1 d k).1, (roAtDrawn t.1 d k).2, Function.update t.2 x none)
    | none => (roAt t.1 d).map fun p => (p.1, p.2, t.2)
  query t d := (roAt t.1 d).map fun p => (p.1, p.2, t.2)

end KDFOps

/-- The state of the real protocol with key-derivation state `T`: the session records, corrupt
parties and notices as in `F_AKE`, the long-term secrets `(ik, spk)` of the parties, the session
secrets (`ek` of an initiator, `opk` of a responder), and the state of the key derivation. -/
structure RStT (S K T : Type) where
  /-- Session records, corrupt parties and notices. -/
  st : St K
  /-- The long-term secrets of a party, once sampled. -/
  lt : PartyId → Option (S × S)
  /-- The secret of a session. -/
  eph : Inst → Option S
  /-- The state of the key derivation. -/
  ro : T

/-- The state of the real protocol with the key derivation `lazyKDF`, whose state is the table
of the key derivation. -/
abbrev RSt (S W K : Type) := RStT S K (List (Inp W × K))

/-- Events of the adversary port of the real protocol. -/
inductive RAEv (W : Type) where
  /-- No action. -/
  | idle
  /-- Read the next notice of a new session. -/
  | poll
  /-- Read the public identity key and signed prekey of a party. -/
  | pub (pid : PartyId)
  /-- Read the public session key of the party `pid` in `sid`. -/
  | ephPub (sid : SessionId) (pid : PartyId)
  /-- Corrupt the party `pid`. -/
  | corrupt (pid : PartyId)
  /-- Let the initiator `pid` of `sid` complete. -/
  | complete (sid : SessionId) (pid : PartyId)
  /-- Deliver the ephemeral public key `e` to the responder `pid` of `sid`. -/
  | send (sid : SessionId) (pid : PartyId) (e : W)
  /-- Query the key derivation at `x`. -/
  | kdf (x : Inp W)

/-- Outputs of the adversary port of the real protocol. -/
inductive ROut (S W K : Type) where
  /-- Acknowledgement. -/
  | ack
  /-- The next notice, if any. -/
  | notice (o : Option Notice)
  /-- The public identity key and signed prekey of a party. -/
  | pub (ik spk : W)
  /-- The public session key of a session, if any. -/
  | eph (o : Option W)
  /-- The long-term secrets of a corrupted party, or `none` when the corruption is refused. -/
  | secret (o : Option (S × S))
  /-- An answer of the key derivation. -/
  | hash (k : K)

section Real

variable {S W K : Type} [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K]
  {T : Type}

/-- The long-term secrets of the party `pid`, sampled at their first use. -/
noncomputable def ltAt (s : RStT S K T) (pid : PartyId) : PMF ((S × S) × RStT S K T) :=
  match s.lt pid with
  | some l => PMF.pure (l, s)
  | none => (PMF.uniformFintype (S × S)).map fun l =>
      (l, { s with lt := Function.update s.lt pid (some l) })

/-- Whether a session names the party `pid`, as party or as peer. -/
def Named (t : St K) (pid : PartyId) : Bool :=
  t.notices.any fun n => n.pid == pid || n.peer == pid

/-- The state with the key `k` and the key-derivation state `ro` at the session `x` with record
`r`. -/
def keyed (s : RStT S K T) (x : Inst) (r : Rec K) (k : K) (ro : T) : RStT S K T :=
  { s with st := setRec s.st x { r with key := some k }, ro := ro }

variable (κ : KDFOp T (Inp W) K)

/-- A step of the honest port of the real protocol with the key derivation `κ`: a new session
draws its secret and starts in `κ`. -/
noncomputable def realHonK (s : RStT S K T) : HEv → PMF (HOut K × RStT S K T)
  | .newSession sid pid peer role =>
    if (s.st.recs (sid, pid)).isNone then
      (PMF.uniformFintype S).bind fun y => (κ.start s.ro (sid, pid)).map fun t =>
        (.ok, { s with st := addSession s.st (sid, pid) peer role,
                       eph := Function.update s.eph (sid, pid) (some y), ro := t })
    else PMF.pure (.ok, s)
  | .getKey sid pid => PMF.pure (.key (keyOf s.st (sid, pid)), s)

/-- A step of the honest port of the real protocol with the lazily sampled key derivation. -/
noncomputable def realHon (s : RSt S W K) : HEv → PMF (HOut K × RSt S W K) :=
  realHonK lazyKDF s

variable (A : AKEAlg S W)

/-- The public session key of the session `x`. -/
def ephPubOf (s : RStT S K T) (x : Inst) : Option W := (s.eph x).map A.pub

/-- The one-time prekey of the responder `b` in `sid`, if `b` has a responder session there. -/
def opkOf (s : RStT S K T) (sid : SessionId) (b : PartyId) : Option S :=
  match s.st.recs (sid, b) with
  | some p => if p.role = .responder then s.eph (sid, b) else none
  | none => none

/-- The completion of the initiator session `x = (sid, a)` with the key derivation `κ`: its key
is the key derivation of `x` at the initiator's input `A.initInp`. -/
noncomputable def completeStepK (s : RStT S K T) (x : Inst) : PMF (ROut S W K × RStT S K T) :=
  match s.st.recs x, s.eph x with
  | some r, some ek =>
    match opkOf s x.1 r.peer with
    | some opk =>
      if r.role = .initiator ∧ r.key.isNone then
        (ltAt s x.2).bind fun la => (ltAt la.2 r.peer).bind fun lb =>
          (κ.derive lb.2.ro x (A.initInp x.1 x.2 r.peer la.1.1 ek (A.pub lb.1.1)
            (A.pub lb.1.2) (A.pub opk))).map fun p => (.ack, keyed lb.2 x r p.1 p.2)
      else PMF.pure (.ack, s)
    | none => PMF.pure (.ack, s)
  | _, _ => PMF.pure (.ack, s)

/-- The completion of the responder session `x = (sid, b)` on the ephemeral public key `e` with
the key derivation `κ`: its key is the key derivation of `x` at the responder's input
`A.respInp`. -/
noncomputable def sendStepK (s : RStT S K T) (x : Inst) (e : W) :
    PMF (ROut S W K × RStT S K T) :=
  match s.st.recs x, s.eph x with
  | some r, some opk =>
    if r.role = .responder ∧ r.key.isNone then
      (ltAt s x.2).bind fun lb => (ltAt lb.2 r.peer).bind fun la =>
        (κ.derive la.2.ro x (A.respInp x.1 r.peer x.2 (A.pub la.1.1) e lb.1.1 lb.1.2 opk)).map
          fun p => (.ack, keyed la.2 x r p.1 p.2)
    else PMF.pure (.ack, s)
  | _, _ => PMF.pure (.ack, s)

/-- The completion of the initiator session `x` with the lazily sampled key derivation. -/
noncomputable def completeStep (s : RSt S W K) (x : Inst) : PMF (ROut S W K × RSt S W K) :=
  completeStepK lazyKDF A s x

/-- The completion of the responder session `x` with the lazily sampled key derivation. -/
noncomputable def sendStep (s : RSt S W K) (x : Inst) (e : W) : PMF (ROut S W K × RSt S W K) :=
  sendStepK lazyKDF A s x e

/-- `corrupt pid`: the long-term secrets of `pid` and the mark, when no session names `pid`. -/
noncomputable def corruptRStep (s : RStT S K T) (pid : PartyId) :
    PMF (ROut S W K × RStT S K T) :=
  if Named s.st pid then PMF.pure (.secret none, s) else
    (ltAt s pid).map fun l => (.secret (some l.1), { l.2 with st := corruptStep l.2.st pid })

/-- A step of the adversary port of the real protocol with the key derivation `κ`. -/
noncomputable def realAdvK (s : RStT S K T) : RAEv W → PMF (ROut S W K × RStT S K T)
  | .idle => PMF.pure (.ack, s)
  | .poll => PMF.pure (.notice (pollStep s.st).2, { s with st := (pollStep s.st).1 })
  | .pub pid => (ltAt s pid).map fun l => (.pub (A.pub l.1.1) (A.pub l.1.2), l.2)
  | .ephPub sid pid => PMF.pure (.eph (ephPubOf A s (sid, pid)), s)
  | .corrupt pid => corruptRStep s pid
  | .complete sid pid => completeStepK κ A s (sid, pid)
  | .send sid pid e => sendStepK κ A s (sid, pid) e
  | .kdf x => (κ.query s.ro x).map fun p => (.hash p.1, { s with ro := p.2 })

/-- A step of the adversary port of the real protocol with the lazily sampled key derivation. -/
noncomputable def realAdv (s : RSt S W K) : RAEv W → PMF (ROut S W K × RSt S W K) :=
  realAdvK lazyKDF A s

/-- The initial state of the real protocol. -/
def rInit : RSt S W K := ⟨initSt, fun _ => none, fun _ => none, []⟩

/-- **The real game of the algorithms `A` with the key derivation `κ`**: a trivial key, and the
oracle is the step of the real protocol. -/
noncomputable def realGameK : KeyedGame (HEv ⊕ RAEv W) (HOut K ⊕ ROut S W K) where
  Key := Unit
  State := RStT S K T
  keyDist := PMF.pure ()
  oracle _ s
    | .inl h => (realHonK κ s h).map fun p => (.inl p.1, p.2)
    | .inr a => (realAdvK κ A s a).map fun p => (.inr p.1, p.2)
  init := ⟨initSt, fun _ => none, fun _ => none, κ.init⟩

/-- **The real game of the algorithms `A`**, with the key derivation a lazily sampled random
function. -/
noncomputable def realGame : KeyedGame (HEv ⊕ RAEv W) (HOut K ⊕ ROut S W K) :=
  realGameK lazyKDF A

/-- **The real protocol of the algorithms `A` with the key derivation `κ`** as a system: each
event is a query to the oracle of `realGameK κ A`. -/
noncomputable def x3dhRealOfK :=
  (OProt.oracle (Q := HEv ⊕ RAEv W) (A := HOut K ⊕ ROut S W K)).sys (realGameK κ A)

/-- **The real protocol of the algorithms `A`** as a system, with the key derivation a lazily
sampled random function. -/
noncomputable def x3dhRealOf := x3dhRealOfK (lazyKDF (D := Inp W) (K := K)) A

end Real

/-- **The real X3DH protocol** over the group `G`: the real protocol of the algorithms
`x3dhAlg G`. -/
noncomputable def x3dhReal {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
    [Nonempty K] (G : DHGroup S W) :=
  x3dhRealOf (K := K) (x3dhAlg G)

/-! ## The simulator -/

/-- The phase of the simulator within an activation. -/
inductive Phase (S W K : Type) where
  /-- Forward the answer of `F_AKE` on its honest port. -/
  | fwd
  /-- Output `o` after the call to `F_AKE`. -/
  | out (o : ROut S W K)

/-- The state of the simulator: its copy of the real state, the key-derivation input of each
session it completed, and the phase. -/
abbrev SimSt (S W K : Type) := RSt S W K × (Inst → Option (Inp W)) × Phase S W K

/-- The outer events of the simulator: the interface of the real protocol. -/
abbrev OEv (W : Type) := HEv ⊕ RAEv W

/-- The outer outputs of the simulator. -/
abbrev OOut (S W K : Type) := HOut K ⊕ ROut S W K

/-- The events of `F_AKE`. -/
abbrev FEv (K : Type) := HEv ⊕ AEv K

/-- The outputs of `F_AKE`. -/
abbrev FOut (K : Type) := HOut K ⊕ AOut

/-- A decision of the simulator. -/
abbrev Dec (S W K : Type) := FEv K ⊕ OOut S W K

/-- The simulator's answer to an answer of `F_AKE`: in the phase `fwd`, the answer on the
honest port, and an acknowledgement for an answer on the adversary port; otherwise the
stored output otherwise. -/
def simOut {S W K : Type} : Phase S W K → FOut K → OOut S W K
  | .fwd, .inl o => .inl o
  | .fwd, .inr _ => .inr .ack
  | .out r, _ => .inr r

section Sim

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- The long-term secrets of the party `pid` on the simulator's copy, as in `ltAt`: the
recorded pair, or a uniform pair that is recorded. -/
noncomputable def ltStep (s : RSt S W K) (pid : PartyId) : SPComp ((S × S) × RSt S W K) :=
  match s.lt pid with
  | some l => SPComp.pure (l, s)
  | none => SPComp.map (fun l => (l, { s with lt := Function.update s.lt pid (some l) }))
      (SPComp.sample (S × S))

/-- The key derivation on the simulator's copy of the table `tb` at `x`, as in `roAt`: the
recorded value, or a uniform value that is recorded. -/
noncomputable def roStep {D : Type} [DecidableEq D] (tb : List (D × K)) (x : D) :
    SPComp (K × List (D × K)) :=
  match tb.lookup x with
  | some v => SPComp.pure (v, tb)
  | none => SPComp.map (fun v => (v, (x, v) :: tb)) (SPComp.sample K)

/-- The delivery of the key of the session `x` with record `r` and input `ip`. An exposed session
receives the key-derivation value at `ip`, which the simulator samples and passes to `newKey`.
Any other session receives the key of `F_AKE`: `newKey` when its partner has not completed or
completed with the same input, `newKeyUnlinked` otherwise; the key-derivation table is
unchanged. -/
noncomputable def deliver (rs : RSt S W K) (inp : Inst → Option (Inp W)) (x : Inst) (r : Rec K)
    (ip : Inp W) : SPComp (SimSt S W K × Dec S W K) :=
  if Exposed rs.st x r then
    SPComp.map (fun p => ((keyed rs x r p.1 p.2, Function.update inp x (some ip), .out .ack),
        .inl (.inr (.newKey x.1 x.2 p.1)))) (roStep rs.ro ip)
  else
    SPComp.pure ((keyed rs x r default rs.ro, Function.update inp x (some ip), .out .ack),
      .inl (.inr (if (inp (x.1, r.peer)).all (· = ip) then .newKey x.1 x.2 default
        else .newKeyUnlinked x.1 x.2 default)))

/-- The simulator on `complete sid pid`: the computation of `completeStep` on its copy, and the
delivery by `deliver`. -/
noncomputable def simComplete (s : SimSt S W K) (x : Inst) :
    SPComp (SimSt S W K × Dec S W K) :=
  match s.1.st.recs x, s.1.eph x with
  | some r, some ek =>
    match opkOf s.1 x.1 r.peer with
    | some opk =>
      if r.role = .initiator ∧ r.key.isNone then
        SPComp.bind (ltStep s.1 x.2) fun la => SPComp.bind (ltStep la.2 r.peer) fun lb =>
          deliver lb.2 s.2.1 x r
            (aliceInp G x.1 x.2 r.peer la.1.1 ek (G.pub lb.1.1) (G.pub lb.1.2) (G.pub opk))
      else SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))
    | none => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | _, _ => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))

/-- The simulator on `send sid pid e`: the computation of `sendStep` on its copy, and the
delivery by `deliver`. -/
noncomputable def simSend (s : SimSt S W K) (x : Inst) (e : W) :
    SPComp (SimSt S W K × Dec S W K) :=
  match s.1.st.recs x, s.1.eph x with
  | some r, some opk =>
    if r.role = .responder ∧ r.key.isNone then
      SPComp.bind (ltStep s.1 x.2) fun lb => SPComp.bind (ltStep lb.2 r.peer) fun la =>
        deliver la.2 s.2.1 x r (bobInp G x.1 r.peer x.2 (G.pub la.1.1) e lb.1.1 lb.1.2 opk)
    else SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | _, _ => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))

/-- The simulator on `corrupt pid`: refused as in the real protocol when a session names `pid`;
otherwise the secrets of its copy are output and `pid` is corrupted in `F_AKE`. -/
noncomputable def simCorrupt (s : SimSt S W K) (pid : PartyId) :
    SPComp (SimSt S W K × Dec S W K) :=
  if Named s.1.st pid then SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.secret none))) else
    SPComp.map (fun l =>
      (({ l.2 with st := corruptStep l.2.st pid }, s.2.1, .out (.secret (some l.1))),
        .inl (.inr (.corrupt pid)))) (ltStep s.1 pid)

/-- The start of an activation of the simulator. Honest events go to `F_AKE` and update the
copy as `realHon` does (a new session draws its secret); `complete`, `send` and `corrupt` are
handled as above; every other adversary event is answered as `realAdv` does on the copy. -/
noncomputable def simStart (s : SimSt S W K) : OEv W → SPComp (SimSt S W K × Dec S W K)
  | .inl (.newSession sid pid peer role) =>
    if (s.1.st.recs (sid, pid)).isNone then
      SPComp.map (fun y =>
        (({ s.1 with st := addSession s.1.st (sid, pid) peer role,
                     eph := Function.update s.1.eph (sid, pid) (some y) }, s.2.1, .fwd),
          .inl (.inl (.newSession sid pid peer role)))) (SPComp.sample S)
    else SPComp.pure ((s.1, s.2.1, .fwd), .inl (.inl (.newSession sid pid peer role)))
  | .inl (.getKey sid pid) => SPComp.pure ((s.1, s.2.1, .fwd), .inl (.inl (.getKey sid pid)))
  | .inr .idle => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | .inr .poll => SPComp.pure (({ s.1 with st := (pollStep s.1.st).1 }, s.2.1, .fwd),
      .inr (.inr (.notice (pollStep s.1.st).2)))
  | .inr (.pub pid) => SPComp.map (fun l =>
      ((l.2, s.2.1, .fwd), .inr (.inr (.pub (G.pub l.1.1) (G.pub l.1.2))))) (ltStep s.1 pid)
  | .inr (.ephPub sid pid) =>
    SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.eph (ephPubOf G s.1 (sid, pid)))))
  | .inr (.corrupt pid) => simCorrupt s pid
  | .inr (.complete sid pid) => simComplete G s (sid, pid)
  | .inr (.send sid pid e) => simSend G s (sid, pid) e
  | .inr (.kdf x) => SPComp.map (fun p =>
      (({ s.1 with ro := p.2 }, s.2.1, .fwd), .inr (.inr (.hash p.1)))) (roStep s.1.ro x)

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- `ltStep` neither touches the heap nor fails. -/
theorem ltStep_pureNF (s : RSt S W K) (pid : PartyId) : PureNF (ltStep s pid) := by
  unfold ltStep
  split
  · exact pureNF_pure _
  · exact (pureNF_sample _).map _

omit [Inhabited K] in
/-- `roStep` neither touches the heap nor fails. -/
theorem roStep_pureNF {D : Type} [DecidableEq D] (tb : List (D × K)) (x : D) :
    PureNF (roStep tb x) := by
  unfold roStep
  split
  · exact pureNF_pure _
  · exact (pureNF_sample _).map _

omit [Field S] [Fintype S] in
/-- `deliver` neither touches the heap nor fails. -/
theorem deliver_pureNF (rs : RSt S W K) (inp : Inst → Option (Inp W)) (x : Inst) (r : Rec K)
    (ip : Inp W) : PureNF (deliver rs inp x r ip) := by
  unfold deliver
  split
  · exact (roStep_pureNF _ _).map _
  · exact pureNF_pure _

/-- The start of the simulator neither touches the heap nor fails. -/
theorem simStart_pureNF (s : SimSt S W K) (e : OEv W) : PureNF (simStart G s e) := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ | pid |
    ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | x)
  · simp only [simStart]
    split
    · exact (pureNF_sample _).map _
    · exact pureNF_pure _
  · exact pureNF_pure _
  · exact pureNF_pure _
  · exact pureNF_pure _
  · exact (ltStep_pureNF _ _).map _
  · exact pureNF_pure _
  · simp only [simStart, simCorrupt]
    split
    · exact pureNF_pure _
    · exact (ltStep_pureNF _ _).map _
  · simp only [simStart, simComplete]
    repeat' split
    all_goals first
      | exact pureNF_pure _
      | exact (ltStep_pureNF _ _).bind fun _ => (ltStep_pureNF _ _).bind fun _ =>
          deliver_pureNF _ _ _ _ _
  · simp only [simStart, simSend]
    repeat' split
    all_goals first
      | exact pureNF_pure _
      | exact (ltStep_pureNF _ _).bind fun _ => (ltStep_pureNF _ _).bind fun _ =>
          deliver_pureNF _ _ _ _ _
  · exact (roStep_pureNF _ _).map _

/-- **The X3DH simulator** as a multi-call simulator over `F_AKE`, one call per activation. -/
noncomputable def simProt :
    MultiHybrid (SimSt S W K) (OEv W) (OOut S W K) (FEv K) (FOut K) where
  init := (rInit, fun _ => none, .fwd)
  fuel := 0
  start := simStart G
  resume s o := SPComp.pure ((s.1, s.2.1, .fwd), .inr (simOut s.2.2 o))
  finish s o := SPComp.pure ((s.1, s.2.1, .fwd), simOut s.2.2 o)
  start_noFail s e := (simStart_pureNF G s e).2
  resume_noFail _ _ := CatCrypt.Crypto.SPComp.pure_noFail _
  finish_noFail _ _ := CatCrypt.Crypto.SPComp.pure_noFail _

end Sim

/-! ## Opacity of the simulator -/

/-- The view of the real interface: equal events, any two honest outputs, equal adversary
outputs. -/
abbrev outerView {S W K : Type} : PubView (OEv W) (OOut S W K) := keHonView.sum eqView

/-- The view of `F_AKE`, for which `F_AKE_opaque` holds. -/
abbrev subView {K : Type} : PubView (FEv K) (FOut K) := keHonView.sum eqView

/-- Every decision is related to itself. -/
theorem stepRel_refl {S W K : Type} (d : Dec S W K) :
    PubView.StepRel (outerView (W := W)) subView d d := by
  rcases d with (h | a) | (o | o)
  · exact Sum.LiftRel.inl rfl
  · exact Sum.LiftRel.inr rfl
  · exact Sum.LiftRel.inl trivial
  · exact Sum.LiftRel.inr rfl

/-- The answers of the simulator to related answers of `F_AKE` are related. -/
theorem simOut_rel {S W K : Type} (ph : Phase S W K) {o o' : FOut K}
    (h : (subView (K := K)).out o o') :
    (outerView (W := W)).out (simOut ph o) (simOut ph o') := by
  cases ph with
  | fwd =>
    cases h with
    | inl _ => exact Sum.LiftRel.inl trivial
    | inr _ => exact Sum.LiftRel.inr rfl
  | out r => exact Sum.LiftRel.inr rfl

section SimOpaque

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- **The unwinding condition of the simulator** for the equality of states: its state and its
decisions depend on its events and not on the answers of `F_AKE` on its honest port. -/
theorem simProt_unwinding : (simProt (K := K) G).Unwinding outerView subView Eq := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rintro s _ e e' rfl he
    have he' : e = e' := by
      cases he with
      | inl h => exact congrArg Sum.inl h
      | inr h => exact congrArg Sum.inr h
    subst he'
    exact rHoare_conseq (fun _ _ h => h)
      (fun _ _ _ _ hp => by obtain ⟨rfl, rfl⟩ := hp; exact ⟨rfl, rfl, stepRel_refl _⟩)
      (rHoare_refl _)
  · rintro s _ o o' rfl ho
    exact rHoare_ret fun _ _ hh => ⟨hh, rfl, simOut_rel _ ho⟩
  · rintro s _ o o' rfl ho
    exact rHoare_ret fun _ _ hh => ⟨hh, rfl, simOut_rel _ ho⟩

/-- **Opacity of the simulator**: it reads no key of `F_AKE`. -/
theorem simProt_opaque : (simProt (K := K) G).Opaque outerView subView :=
  ⟨Eq, simProt_unwinding G⟩

/-- **The X3DH simulator** as a bundled opaque simulator. -/
noncomputable def x3dhSim :
    Simulator (OEv W) (OOut S W K) (FEv K) (FOut K) outerView subView :=
  Simulator.ofMultiHybrid (simProt G) (simProt_opaque G)

end SimOpaque

/-! ## The square in oracle-game form -/

/-- The steps of `F_AKE` with uniform keys do not touch the heap. -/
theorem F_AKE_pureNF {K : Type} [Fintype K] [Nonempty K] {unlinked : Bool} (t : St K)
    (e : FEv K) : PureNF ((F_AKE (SPComp.sample K) unlinked).step t e) := by
  rcases e with h | a
  · simp only [F_AKE, F_AKEK, Sys.ofPorts_step_inl, honSys]
    exact (pureNF_pure _).map _
  · simp only [F_AKE, F_AKEK, Sys.ofPorts_step_inr, advSysK]
    refine PureNF.map _ ?_
    cases a <;> first | exact pureNF_pure _ | exact (pureNF_sample K).map _

section SimWorld

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- The steps of the simulated world, the simulator running with `F_AKE`, do not touch the
heap. -/
theorem simWorld_pureNF :
    ∀ t e, PureNF (((simProt (K := K) G).withSub (F_AKE (SPComp.sample K) true)).step t e) :=
  withSub_pureNF _ _ F_AKE_pureNF (simStart_pureNF G)
    (fun _ _ => pureNF_pure _) (fun _ _ => pureNF_pure _)

/-- **The simulated X3DH game**: the oracle game of the simulator running with `F_AKE`. -/
noncomputable def simGame : KeyedGame (OEv W) (OOut S W K) :=
  pureGame ((simProt (K := K) G).withSub (F_AKE (SPComp.sample K) true)) (simWorld_pureNF G)

/-- **The simulated world as an oracle game**: the oracle system of `simGame G` realizes the
simulator running with `F_AKE` at distance `0`. -/
theorem simWorld_realizes :
    Realizes ((OProt.oracle (Q := OEv W) (A := OOut S W K)).sys (simGame G))
      ((simProt (K := K) G).withSub (F_AKE (SPComp.sample K) true)) (fun _ _ => 0) :=
  pureGame_realizes _ _

/-- **X3DH realizes `F_AKE` behind `x3dhSim`, in oracle-game form.** For every environment `Z`,
the distance between the real protocol of the algorithms `x3dhAlg G` (the real X3DH protocol
`x3dhReal G`) and the simulator running with `F_AKE` is at most the advantage of the oracle
adversary `OProt.oracle.reduction Z` between the real game `realGame G` and the simulated game
`simGame G`. -/
theorem x3dh_realizesSim_oracleGame :
    RealizesSim (x3dhRealOf (K := K) (x3dhAlg G)) (F_AKE (SPComp.sample K) true) (x3dhSim G)
      (fun _ Z => KeyedGame.advantage (realGame G) (simGame G) (OProt.oracle.reduction Z)) :=
  fun ζ Z => le_of_le_of_eq
    ((Realizes.trans
      (Realizes.ofOracleGame OProt.oracle (realGame (K := K) (x3dhAlg G)) (simGame G))
      (simWorld_realizes G)) ζ Z) (add_zero _)

end SimWorld

/-! ## The key derivation drawn in advance -/

section Pool

variable {I K : Type} [DecidableEq I] [Fintype K] [Nonempty K]

/-- The pool of keys of a list of sessions depends on the list up to permutation. -/
theorem drawPool_perm {l l' : List I} (h : l.Perm l') : drawPool (K := K) l = drawPool l' := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [drawPool, ih]
  | swap x y l =>
    simp only [drawPool, PMF.map_bind, PMF.map_comp, Function.comp_def]
    by_cases hxy : x = y
    · subst hxy; rfl
    · rw [PMF.bind_comm]
      simp only [Function.update_comm hxy]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **A key derivation from the pool.** Drawing the pool of the sessions `l` and deriving the key
of the session `x` at `d` with `eagerKDF` is the lazily sampled derivation at `d` followed by the
pool of the sessions of `l` other than `x`. -/
theorem drawPool_bind_eagerKDF {D β : Type} [DecidableEq D] (tb : List (D × K)) (l : List Inst)
    (hl : l.Nodup) (x : Inst) (d : D) (g : K × List (D × K) → (Inst → Option K) → β) :
    ((drawPool (K := K) l).bind fun pool =>
      ((eagerKDF (D := D)).derive (tb, pool) x d).map fun p => g (p.1, p.2.1) p.2.2) =
      (roAt tb d).bind fun p => (drawPool (l.erase x)).map fun pool => g p pool := by
  by_cases hx : x ∈ l
  · let H : Option K × (Inst → Option K) → PMF β := fun q =>
      match q.1 with
      | some k => PMF.pure (g (roAtDrawn tb d k) q.2)
      | none => (roAt tb d).map fun p => g p q.2
    have hH : ∀ pool : Inst → Option K,
        ((eagerKDF (D := D)).derive (tb, pool) x d).map (fun p => g (p.1, p.2.1) p.2.2) =
          H (pool x, Function.update pool x none) := by
      intro pool
      cases hp : pool x with
      | some k => simp [eagerKDF, H, hp, PMF.pure_map]
      | none =>
        have : Function.update pool x none = pool := Function.update_eq_self_iff.2 hp.symm
        simp [eagerKDF, H, hp, this, PMF.map_comp, Function.comp_def]
    simp only [hH]
    rw [show ((drawPool (K := K) l).bind fun pool => H (pool x, Function.update pool x none)) =
        ((drawPool l).map fun pool => (pool x, Function.update pool x none)).bind H by
      rw [PMF.bind_map]; rfl, drawPool_consume l hl x hx, roAt_eq_map_roAtDrawn, PMF.bind_bind,
      PMF.bind_map]
    refine congrArg _ (funext fun k => ?_)
    simp only [H, PMF.bind_map, Function.comp_def]
    rfl
  · have hnone : ∀ pool ∈ (drawPool (K := K) l).support, pool x = none :=
      fun pool hp => drawPool_none l pool hp x hx
    rw [List.erase_of_not_mem hx]
    rw [PMF.bind_congr_support (drawPool l) _ (fun pool => (roAt tb d).map fun p => g p pool)
      fun pool hp => by simp [eagerKDF, hnone pool hp, PMF.map_comp, Function.comp_def]]
    simp only [← PMF.bind_pure_comp]
    exact PMF.bind_comm _ _ _

end Pool

section LazyEager

variable {S W K : Type} [Fintype S] [Nonempty S]

/-- The sessions of the notices of `t` that have a record without a key. -/
def pendingOf (t : St K) : List Inst :=
  ((t.notices.map fun n => (n.sid, n.pid)).dedup).filter fun x =>
    (t.recs x).any fun r => r.key.isNone

/-- A pending session is a session of the notices with a record without a key. -/
theorem mem_pendingOf {t : St K} {x : Inst} : x ∈ pendingOf t ↔
    x ∈ t.notices.map (fun n => (n.sid, n.pid)) ∧ (t.recs x).any (fun r => r.key.isNone) := by
  simp only [pendingOf, List.mem_filter, List.mem_dedup]

/-- The pending sessions are distinct. -/
theorem nodup_pendingOf (t : St K) : (pendingOf t).Nodup :=
  (List.nodup_dedup _).filter _

/-- A new session is pending, and the other sessions keep their status. -/
theorem pendingOf_addSession (t : St K) (x : Inst) (peer : PartyId) (role : Role)
    (h : t.recs x = none) : (pendingOf (addSession t x peer role)).Perm (x :: pendingOf t) := by
  have hx : x ∉ pendingOf t := by simp [mem_pendingOf, h]
  rw [List.perm_ext_iff_of_nodup (nodup_pendingOf _) (List.nodup_cons.2 ⟨hx, nodup_pendingOf _⟩)]
  intro a
  by_cases hax : a = x
  · subst hax
    simp [mem_pendingOf, addSession, h]
  · simp [mem_pendingOf, addSession, h, hax]

/-- A session that receives its key leaves the pending sessions. -/
theorem pendingOf_setRec_key (t : St K) (x : Inst) (r : Rec K) (h : r.key.isNone = false) :
    (pendingOf (setRec t x r)).Perm ((pendingOf t).erase x) := by
  rw [List.perm_ext_iff_of_nodup (nodup_pendingOf _) ((nodup_pendingOf _).erase _)]
  intro a
  rw [(nodup_pendingOf t).mem_erase_iff]
  by_cases hax : a = x
  · subst hax
    simp [mem_pendingOf, setRec, h]
  · simp [mem_pendingOf, setRec, hax]

/-- The state `s` with the key-derivation state `t`. -/
def withRo {T T' : Type} (s : RStT S K T) (t : T') : RStT S K T' := ⟨s.st, s.lt, s.eph, t⟩

/-- The draw of the long-term secrets of `pid`: the recorded pair, or a uniform pair that is
recorded. -/
noncomputable def ltDraw (lt : PartyId → Option (S × S)) (pid : PartyId) :
    PMF ((S × S) × (PartyId → Option (S × S))) :=
  match lt pid with
  | some l => PMF.pure (l, lt)
  | none => (PMF.uniformFintype (S × S)).map fun l => (l, Function.update lt pid (some l))

/-- `ltAt` changes only the long-term secrets: it is `ltDraw` on them. -/
theorem ltAt_eq_ltDraw {T : Type} (s : RStT S K T) (pid : PartyId) :
    ltAt s pid = (ltDraw s.lt pid).map fun q => (q.1, { s with lt := q.2 }) := by
  unfold ltAt ltDraw
  cases s.lt pid with
  | some l => rw [PMF.pure_map]
  | none => rw [PMF.map_comp]; rfl

variable [DecidableEq W] [Fintype K] [Nonempty K]

/-- **The kernel from lazy to eager key derivation**: the pool of keys of the pending sessions,
drawn independently and uniformly, beside the table. -/
noncomputable def eagerKernel (s : RSt S W K) :
    PMF (RStT S K (List (Inp W × K) × (Inst → Option K))) :=
  (drawPool (pendingOf s.st)).map fun pool => withRo s (s.ro, pool)

variable (A : AKEAlg S W)

/-- **The honest port, lazy and eager.** -/
theorem eagerKernel_realHonK (s : RSt S W K) (h : HEv) :
    ((eagerKernel s).bind fun s' => realHonK eagerKDF s' h) =
      (realHonK lazyKDF s h).bind fun p => (eagerKernel p.2).map fun s' => (p.1, s') := by
  simp only [eagerKernel, PMF.bind_map, Function.comp_def]
  cases h with
  | newSession sid pid peer role =>
    by_cases hx : (s.st.recs (sid, pid)).isNone
    · have hn : s.st.recs (sid, pid) = none := Option.isNone_iff_eq_none.1 hx
      simp only [realHonK, withRo, hx, ↓reduceIte, eagerKDF, lazyKDF, PMF.pure_map,
        PMF.map_comp, Function.comp_def]
      rw [PMF.bind_bind]
      simp only [PMF.pure_bind, drawPool_perm (pendingOf_addSession s.st (sid, pid) peer role hn),
        drawPool, PMF.map_bind, PMF.map_comp, Function.comp_def]
      rw [PMF.bind_comm]
      refine congrArg _ (funext fun y => ?_)
      simp only [← PMF.bind_pure_comp]
      exact PMF.bind_comm _ _ _
    · simp only [realHonK, withRo, hx, ↓reduceIte, Bool.false_eq_true, PMF.pure_bind,
        PMF.map_comp, Function.comp_def]
      rfl
  | getKey sid pid =>
    simp only [realHonK, withRo, PMF.pure_bind, PMF.map_comp, Function.comp_def]
    rfl

omit [DecidableEq W] [Fintype K] [Nonempty K] in
/-- `poll` leaves the pending sessions unchanged. -/
theorem pendingOf_pollStep (t : St K) : pendingOf (pollStep t).1 = pendingOf t := by
  unfold pollStep
  split <;> rfl

omit [DecidableEq W] in
/-- The pool of the pending sessions after a session receives its key is the pool of the other
pending sessions. -/
theorem drawPool_pendingOf_setRec (t : St K) (x : Inst) (p : PartyId) (ro : Role)
    (st : Status) (k : K) :
    drawPool (K := K) (pendingOf (setRec t x ⟨p, ro, st, some k⟩)) =
      drawPool ((pendingOf t).erase x) :=
  drawPool_perm (pendingOf_setRec_key t x _ rfl)

/-- **The adversary port, lazy and eager.** -/
theorem eagerKernel_realAdvK (s : RSt S W K) (e : RAEv W) :
    ((eagerKernel s).bind fun s' => realAdvK eagerKDF A s' e) =
      (realAdvK lazyKDF A s e).bind fun p => (eagerKernel p.2).map fun s' => (p.1, s') := by
  simp only [eagerKernel, PMF.bind_map, Function.comp_def]
  cases e with
  | idle =>
    simp only [realAdvK, withRo, PMF.pure_bind, PMF.map_comp, Function.comp_def]
    rfl
  | poll =>
    simp only [realAdvK, withRo, PMF.pure_bind, PMF.map_comp, Function.comp_def,
      pendingOf_pollStep]
    rfl
  | pub pid =>
    simp only [realAdvK, ltAt_eq_ltDraw, withRo, PMF.map_comp, PMF.bind_map, Function.comp_def]
    simp only [← PMF.bind_pure_comp]
    exact PMF.bind_comm _ _ _
  | ephPub sid pid =>
    simp only [realAdvK, withRo, PMF.pure_bind, PMF.map_comp, Function.comp_def]
    rfl
  | corrupt pid =>
    simp only [realAdvK, corruptRStep, withRo]
    by_cases hN : Named s.st pid
    · simp only [hN, ↓reduceIte, PMF.pure_bind, PMF.map_comp, Function.comp_def]
      rfl
    · simp only [hN, Bool.false_eq_true, ↓reduceIte, ltAt_eq_ltDraw, PMF.map_comp,
        PMF.bind_map, Function.comp_def]
      simp only [← PMF.bind_pure_comp]
      exact PMF.bind_comm _ _ _
  | kdf x =>
    simp only [realAdvK, withRo, eagerKDF, lazyKDF, PMF.map_comp, PMF.bind_map,
      Function.comp_def]
    simp only [← PMF.bind_pure_comp]
    exact PMF.bind_comm _ _ _
  | complete sid pid =>
    simp only [realAdvK, completeStepK]
    have hop : ∀ (t : List (Inp W × K) × (Inst → Option K)) (b : PartyId),
        opkOf (withRo s t) sid b = opkOf s sid b := fun _ _ => rfl
    cases hr : s.st.recs (sid, pid) with
    | none =>
      simp only [withRo, hr, PMF.pure_bind, PMF.map_comp, Function.comp_def]
      rfl
    | some r =>
      cases he : s.eph (sid, pid) with
      | none =>
        simp only [withRo, hr, he, PMF.pure_bind, PMF.map_comp, Function.comp_def]
        rfl
      | some ek =>
        cases ho : opkOf s sid r.peer with
        | none =>
          simp only [hop, ho]
          simp only [withRo, hr, he, ho, PMF.pure_bind, PMF.map_comp, Function.comp_def]
          rfl
        | some opk =>
          simp only [hop, ho]
          by_cases hc : r.role = .initiator ∧ r.key.isNone
          · simp only [withRo, hr, he, ho, hc, and_self, ↓reduceIte, ltAt_eq_ltDraw,
              lazyKDF, keyed, PMF.bind_map, PMF.bind_bind, PMF.map_comp,
              Function.comp_def]
            simp only [drawPool_pendingOf_setRec]
            rw [PMF.bind_comm]
            refine congrArg _ (funext fun qa => ?_)
            rw [PMF.bind_comm]
            refine congrArg _ (funext fun qb => ?_)
            exact drawPool_bind_eagerKDF (D := Inp W) s.ro _ (nodup_pendingOf _) _ _
              fun p pool => (ROut.ack, (⟨setRec s.st (sid, pid)
                ⟨r.peer, .initiator, r.status, some p.1⟩, qb.2, s.eph, (p.2, pool)⟩ :
                  RStT S K (List (Inp W × K) × (Inst → Option K))))
          · simp only [withRo, hr, he, ho, hc, ↓reduceIte, PMF.pure_bind, PMF.map_comp,
              Function.comp_def]
            rfl
  | send sid pid e =>
    simp only [realAdvK, sendStepK]
    cases hr : s.st.recs (sid, pid) with
    | none =>
      simp only [withRo, hr, PMF.pure_bind, PMF.map_comp, Function.comp_def]
      rfl
    | some r =>
      cases he : s.eph (sid, pid) with
      | none =>
        simp only [withRo, hr, he, PMF.pure_bind, PMF.map_comp, Function.comp_def]
        rfl
      | some opk =>
        by_cases hc : r.role = .responder ∧ r.key.isNone
        · simp only [withRo, hr, he, hc, and_self, ↓reduceIte, ltAt_eq_ltDraw, lazyKDF,
            keyed, PMF.bind_map, PMF.bind_bind, PMF.map_comp, Function.comp_def]
          simp only [drawPool_pendingOf_setRec]
          rw [PMF.bind_comm]
          refine congrArg _ (funext fun qb => ?_)
          rw [PMF.bind_comm]
          refine congrArg _ (funext fun qa => ?_)
          exact drawPool_bind_eagerKDF (D := Inp W) s.ro _ (nodup_pendingOf _) _ _
            fun p pool => (ROut.ack, (⟨setRec s.st (sid, pid)
              ⟨r.peer, .responder, r.status, some p.1⟩, qa.2, s.eph, (p.2, pool)⟩ :
                RStT S K (List (Inp W × K) × (Inst → Option K))))
        · simp only [withRo, hr, he, hc, ↓reduceIte, PMF.pure_bind, PMF.map_comp,
            Function.comp_def]
          rfl

/-- **Lazy and eager key derivation in the real X3DH protocol.** The real protocol of the
algorithms `A` with the key derivation a lazily sampled random function and the real protocol
with each session's key-derivation value drawn in advance at its start (`eagerKDF`) are at
distance `0`. -/
theorem x3dhRealOf_lazy_eager :
    Realizes (x3dhRealOf (K := K) A) (x3dhRealOfK eagerKDF A) fun _ _ => 0 := by
  refine Realizes.ofKernel _ (realGameK lazyKDF A) (realGameK eagerKDF A) id
    (PMF.map_id _).symm eagerKernel (fun _ => True) ?_ trivial ?_ fun _ _ _ _ _ _ => trivial
  · simp [eagerKernel, realGameK, pendingOf, initSt, drawPool, PMF.pure_map, withRo, lazyKDF,
      eagerKDF]
  · intro _ s q _
    cases q with
    | inl h =>
      have e := congrArg (PMF.map fun p => (Sum.inl (β := ROut S W K) p.1, p.2))
        (eagerKernel_realHonK (W := W) s h)
      simp only [realGameK, id, PMF.map_bind, PMF.bind_map, PMF.map_comp,
        Function.comp_def] at e ⊢
      exact e
    | inr a =>
      have e := congrArg (PMF.map fun p => (Sum.inr (α := HOut K) p.1, p.2))
        (eagerKernel_realAdvK A s a)
      simp only [realGameK, id, PMF.map_bind, PMF.bind_map, PMF.map_comp,
        Function.comp_def] at e ⊢
      exact e

end LazyEager

end CatCrypt.Crypto.AKE.X3DHSquare
