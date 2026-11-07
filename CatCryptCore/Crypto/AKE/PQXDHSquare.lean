/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHSquare
public import CatCryptCore.Crypto.KEM.Games

/-!
# PQXDH against the authenticated key-exchange functionality

**Ideal functionality.** `F_AKE (SPComp.sample K) true` of `CatCryptCore.Crypto.AKE.FAKESys`
(the variant for implicitly authenticated key exchange without key confirmation), as for X3DH
(`CatCryptCore.Crypto.AKE.X3DHSquare`): the multi-session authenticated key exchange with
adversarial key delivery, the unlinked delivery `newKeyUnlinked`, corruption of parties, and
uniform keys in `K`.

**Real protocol.** `pqxdhReal G P` runs PQXDH (Kret and Schmidt, *The PQXDH Key Agreement
Protocol*, Signal, 2023) for every session, over the group `G : DHGroup S W`, the key
encapsulation mechanism `P : KEM.Games.Scheme PK SK SS C`, and the key-derivation function a
lazily sampled random function into `K`. It is X3DH as in `X3DHSquare` with a post-quantum
prekey:
* a session of the responder `b` in `sid` draws, besides its one-time prekey, a KEM key pair
  `(pk, sk)` from `P.keygen` at its start; the public key is read with `pqPub sid b`;
* the initiator `a` completes on `complete sid a` once `b` has a responder session in `sid`: it
  encapsulates to `pk`, obtaining `(ss, c)`, stores the encapsulation `c` (read with
  `pqPub sid a`), and takes the key `KDF((aliceInp …, ss))`;
* the responder completes on `send sid b E c`, the delivery of the ephemeral public key `E` and
  the encapsulation `c`: when `P.decaps sk c = some ss`, with the key `KDF((bobInp …, ss))`, and
  it ignores the delivery when decapsulation rejects;
* corruption is static and reveals the long-term secrets, as in X3DH.

**Simulator.** `pqxdhSim G P` is the simulator of X3DH with the key-derivation input extended
by the shared secret: it keeps a copy of the real state, draws every long-term and session
secret and every KEM key pair itself, and encapsulates itself on `complete`. When a session
completes it computes the session's input `ip` and delivers by `deliver`: an exposed session
receives the key-derivation value at `ip` through `newKey`; any other session receives the key
of `F_AKE` by `newKey` when its partner has not completed or completed with the input `ip`,
and by `newKeyUnlinked` otherwise. The simulator reads no key of `F_AKE` (`simProt_opaque`).
It is the simulator `pqxdhSimK` over the operations of a KEM as computations (`KemOps`) at the
operations `kemOps P` of `P`, so that a costed form of `pqxdhSimK` prices key generation,
encapsulation and decapsulation by parameters.

**Results.** The simulator running with `F_AKE` is at distance `0` from the oracle system of
the game `simGame G P` (`simWorld_realizes`). The square is the oracle-game bound
`pqxdh_realizesSim_oracleGame`: `pqxdhReal G P` realizes `F_AKE` behind `pqxdhSim G P` with
bound, at the environment `Z`, the advantage of the oracle adversary
`OProt.oracle.reduction Z` between `realGame G P` and `simGame G P`.

The hops that bound this advantage take one of two routes per session. The route of X3DH: when
the session's party and peer are honest, the Diffie–Hellman values of its input are not
computable by the adversary under the gap Diffie–Hellman assumption on `G`, so its input is not
queried to the key derivation and the key is uniform. The route of the KEM: when the responder's
KEM key pair is honest, the shared secret of the initiator's encapsulation is indistinguishable
from a uniform one under the IND-CCA security of `P` (`KEM.Games.indccaAdvantage`; the
decapsulation oracle answers the responder's decapsulations of other encapsulations), so the
input is again unqueried. Either route bounds the distance at a session.

## Main definitions

* `PInp`: the inputs of the key derivation.
* `PStT`, `PSt`, `PAEv`, `POut`: the state and the adversary port of the real protocol.
* `realGameK`, `pqxdhRealK`: the real protocol with a key-derivation operation `KDFOp` as an
  oracle game and as a system; `realGame` and `pqxdhReal` are their applications at `lazyKDF`.
* `eagerKernel`: the pool of keys of the pending sessions, the kernel from `lazyKDF` to
  `eagerKDF`.
* `KemOps`, `kemOps`: the operations of a KEM as computations, and those of `P`.
* `simProtK`, `pqxdhSimK`: the simulator over the operations of a KEM.
* `simProt`, `pqxdhSim`: the simulator.
* `simGame`: the oracle game of the simulated world.

## Main results

* `simProt_opaque`: opacity of the simulator.
* `simWorld_realizes`.
* `pqxdh_realizesSim_oracleGame`: PQXDH realizes `F_AKE` behind `pqxdhSim` with the oracle-game
  bound.
* `pqxdhRealOf_lazy_eager`: the real protocol with lazily sampled and with eagerly drawn
  key-derivation values are at distance `0`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.PQXDHSquare

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Crypto.PAKE.CPaceSquare (roAt PureNF pureNF_pure pureNF_sample PureNF.map
  PureNF.bind withSub_pureNF pureGame pureGame_realizes sampleFrom_ofPMF_eq_liftPMF)
open CatCrypt.Crypto.AKE.X3DHSquare (Inp aliceInp bobInp RSt ROut RAEv ltAt Named keyed realHon
  ephPubOf opkOf corruptRStep realAdv rInit FEv FOut subView F_AKE_pureNF ltStep ltStep_pureNF
  roStep roStep_pureNF KDFOp lazyKDF eagerKDF)
open CatCrypt.NonUniform (sampleFrom ofPMF)
open CatCrypt.Crypto.KEM.Games (Scheme)
open PubView (eqView)
open scoped ENNReal

/-! ## The real protocol -/

/-- An input of the key derivation: the input of X3DH and the shared secret of the KEM. -/
abbrev PInp (W SS : Type) := Inp W × SS

/-- The state of the real protocol with key-derivation state `T`: the state of X3DH (session
records, long-term secrets and the Diffie–Hellman secrets of sessions; its key-derivation table
is not used), the KEM key pair of each responder session, the encapsulation of each completed
initiator session, and the state of the key derivation. -/
structure PStT (S W K PK SK C T : Type) where
  /-- The state of X3DH. -/
  x : RSt S W K
  /-- The KEM key pair of a responder session. -/
  kem : Inst → Option (PK × SK)
  /-- The encapsulation of a completed initiator session. -/
  ct : Inst → Option C
  /-- The state of the key derivation. -/
  ro : T

/-- The state of the real protocol with the key derivation `lazyKDF`, whose state is the table
of the key derivation. -/
abbrev PSt (S W K PK SK SS C : Type) := PStT S W K PK SK C (List (PInp W SS × K))

/-- Events of the adversary port of the real protocol. -/
inductive PAEv (W SS C : Type) where
  /-- No action. -/
  | idle
  /-- Read the next notice of a new session. -/
  | poll
  /-- Read the public identity key and signed prekey of a party. -/
  | pub (pid : PartyId)
  /-- Read the public Diffie–Hellman key of the party `pid` in `sid`. -/
  | ephPub (sid : SessionId) (pid : PartyId)
  /-- Read the KEM public key and the encapsulation of the party `pid` in `sid`. -/
  | pqPub (sid : SessionId) (pid : PartyId)
  /-- Corrupt the party `pid`. -/
  | corrupt (pid : PartyId)
  /-- Let the initiator `pid` of `sid` complete. -/
  | complete (sid : SessionId) (pid : PartyId)
  /-- Deliver the ephemeral public key `e` and the encapsulation `c` to the responder `pid` of
  `sid`. -/
  | send (sid : SessionId) (pid : PartyId) (e : W) (c : C)
  /-- Query the key derivation at `x`. -/
  | kdf (x : PInp W SS)

/-- Outputs of the adversary port of the real protocol: an output of X3DH, or the KEM public key
and the encapsulation of a session. -/
abbrev POut (S W K PK C : Type) := ROut S W K ⊕ (Option PK × Option C)

section Real

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [DecidableEq SS] {T : Type}

/-- A step on the state of X3DH, with its output. -/
noncomputable def onX (s : PStT S W K PK SK C T) (c : PMF (ROut S W K × RSt S W K)) :
    PMF (POut S W K PK C × PStT S W K PK SK C T) :=
  c.map fun p => (.inl p.1, { s with x := p.2 })

/-- The KEM public key of the responder session of `b` in `sid`, if any. -/
def pkOf (s : PStT S W K PK SK C T) (sid : SessionId) (b : PartyId) : Option PK :=
  (s.kem (sid, b)).map Prod.fst

/-- The state with the key `k` and the key-derivation state `ro` at the session `x` with record
`r`. -/
def pKeyed (s : PStT S W K PK SK C T) (x : Inst) (r : Rec K) (k : K) (ro : T) :
    PStT S W K PK SK C T :=
  { s with x := keyed s.x x r k s.x.ro, ro := ro }

variable (P : Scheme PK SK SS C) (κ : KDFOp T (PInp W SS) K)

/-- A step of the honest port of the real protocol with the key derivation `κ`: a new session
draws its Diffie–Hellman secret, a new responder session also its KEM key pair, and a new
session starts in `κ`. -/
noncomputable def pqHonK (s : PStT S W K PK SK C T) :
    HEv → PMF (HOut K × PStT S W K PK SK C T)
  | .newSession sid pid peer role =>
    (realHon s.x (.newSession sid pid peer role)).bind fun p =>
      (if (s.x.st.recs (sid, pid)).isNone ∧ role = .responder then
        P.keygen.map fun kp =>
          { s with x := p.2, kem := Function.update s.kem (sid, pid) (some kp) }
      else PMF.pure { s with x := p.2 }).bind fun s₁ =>
      (if (s.x.st.recs (sid, pid)).isNone then κ.start s.ro (sid, pid) else PMF.pure s.ro).map
        fun t => (p.1, { s₁ with ro := t })
  | .getKey sid pid => PMF.pure (.key (keyOf s.x.st (sid, pid)), s)

/-- A step of the honest port of the real protocol with the lazily sampled key derivation. -/
noncomputable def pqHon (s : PSt S W K PK SK SS C) :
    HEv → PMF (HOut K × PSt S W K PK SK SS C) :=
  pqHonK P lazyKDF s

variable (G : DHGroup S W)

/-- The completion of the initiator session `x = (sid, a)` with the key derivation `κ`: it
encapsulates to the KEM public key of its peer, and its key is the key derivation of `x` at
`aliceInp` and the shared secret. -/
noncomputable def pqCompleteK (s : PStT S W K PK SK C T) (x : Inst) :
    PMF (POut S W K PK C × PStT S W K PK SK C T) :=
  match s.x.st.recs x, s.x.eph x with
  | some r, some ek =>
    match opkOf s.x x.1 r.peer, pkOf s x.1 r.peer with
    | some opk, some pk =>
      if r.role = .initiator ∧ r.key.isNone then
        (ltAt s.x x.2).bind fun la => (ltAt la.2 r.peer).bind fun lb =>
          (P.encaps pk).bind fun kc =>
            (κ.derive s.ro x (aliceInp G x.1 x.2 r.peer la.1.1 ek (G.pub lb.1.1) (G.pub lb.1.2)
              (G.pub opk), kc.1)).map fun q =>
                (.inl .ack, pKeyed { s with x := lb.2, ct := Function.update s.ct x (some kc.2) }
                  x r q.1 q.2)
      else PMF.pure (.inl .ack, s)
    | _, _ => PMF.pure (.inl .ack, s)
  | _, _ => PMF.pure (.inl .ack, s)

/-- The completion of the responder session `x = (sid, b)` on the ephemeral public key `e` and
the encapsulation `c` with the key derivation `κ`: when `c` decapsulates to `ss`, its key is the
key derivation of `x` at `bobInp` and `ss`; a rejected encapsulation is ignored. -/
noncomputable def pqSendK (s : PStT S W K PK SK C T) (x : Inst) (e : W) (c : C) :
    PMF (POut S W K PK C × PStT S W K PK SK C T) :=
  match s.x.st.recs x, s.x.eph x, s.kem x with
  | some r, some opk, some kp =>
    match P.decaps kp.2 c with
    | some ss =>
      if r.role = .responder ∧ r.key.isNone then
        (ltAt s.x x.2).bind fun lb => (ltAt lb.2 r.peer).bind fun la =>
          (κ.derive s.ro x (bobInp G x.1 r.peer x.2 (G.pub la.1.1) e lb.1.1 lb.1.2 opk, ss)).map
            fun q => (.inl .ack, pKeyed { s with x := la.2 } x r q.1 q.2)
      else PMF.pure (.inl .ack, s)
    | none => PMF.pure (.inl .ack, s)
  | _, _, _ => PMF.pure (.inl .ack, s)

/-- The completion of the initiator session `x` with the lazily sampled key derivation. -/
noncomputable def pqComplete (s : PSt S W K PK SK SS C) (x : Inst) :
    PMF (POut S W K PK C × PSt S W K PK SK SS C) :=
  pqCompleteK P lazyKDF G s x

/-- The completion of the responder session `x` with the lazily sampled key derivation. -/
noncomputable def pqSend (s : PSt S W K PK SK SS C) (x : Inst) (e : W) (c : C) :
    PMF (POut S W K PK C × PSt S W K PK SK SS C) :=
  pqSendK P lazyKDF G s x e c

/-- A step of the adversary port of the real protocol with the key derivation `κ`. The events of
X3DH that do not complete a session are steps of `realAdv` on the state of X3DH. -/
noncomputable def pqAdvK (s : PStT S W K PK SK C T) :
    PAEv W SS C → PMF (POut S W K PK C × PStT S W K PK SK C T)
  | .idle => onX s (realAdv G s.x .idle)
  | .poll => onX s (realAdv G s.x .poll)
  | .pub pid => onX s (realAdv G s.x (.pub pid))
  | .ephPub sid pid => onX s (realAdv G s.x (.ephPub sid pid))
  | .pqPub sid pid => PMF.pure (.inr (pkOf s sid pid, s.ct (sid, pid)), s)
  | .corrupt pid => onX s (corruptRStep s.x pid)
  | .complete sid pid => pqCompleteK P κ G s (sid, pid)
  | .send sid pid e c => pqSendK P κ G s (sid, pid) e c
  | .kdf x => (κ.query s.ro x).map fun p => (.inl (.hash p.1), { s with ro := p.2 })

/-- A step of the adversary port of the real protocol with the lazily sampled key derivation. -/
noncomputable def pqAdv (s : PSt S W K PK SK SS C) :
    PAEv W SS C → PMF (POut S W K PK C × PSt S W K PK SK SS C) :=
  pqAdvK P lazyKDF G s

/-- The initial state of the real protocol. -/
def pInit : PSt S W K PK SK SS C := ⟨rInit, fun _ => none, fun _ => none, []⟩

/-- **The real PQXDH game with the key derivation `κ`**: a trivial key, and the oracle is the
step of the real protocol. -/
noncomputable def realGameK : KeyedGame (HEv ⊕ PAEv W SS C) (HOut K ⊕ POut S W K PK C) where
  Key := Unit
  State := PStT S W K PK SK C T
  keyDist := PMF.pure ()
  oracle _ s
    | .inl h => (pqHonK P κ s h).map fun p => (.inl p.1, p.2)
    | .inr a => (pqAdvK P κ G s a).map fun p => (.inr p.1, p.2)
  init := ⟨rInit, fun _ => none, fun _ => none, κ.init⟩

/-- **The real PQXDH game**, with the key derivation a lazily sampled random function. -/
noncomputable def realGame : KeyedGame (HEv ⊕ PAEv W SS C) (HOut K ⊕ POut S W K PK C) :=
  realGameK P lazyKDF G

/-- **The real PQXDH protocol with the key derivation `κ`** as a system: each event is a query
to the oracle of `realGameK P κ G`. -/
noncomputable def pqxdhRealK :=
  (OProt.oracle (Q := HEv ⊕ PAEv W SS C) (A := HOut K ⊕ POut S W K PK C)).sys (realGameK P κ G)

/-- **The real PQXDH protocol** as a system, with the key derivation a lazily sampled random
function. -/
noncomputable def pqxdhReal := pqxdhRealK P (lazyKDF (D := PInp W SS) (K := K)) G

end Real

/-! ## The simulator -/

/-- The phase of the simulator within an activation. -/
inductive Phase (S W K PK C : Type) where
  /-- Forward the answer of `F_AKE` on its honest port. -/
  | fwd
  /-- Output `o` after the call to `F_AKE`. -/
  | out (o : POut S W K PK C)

/-- The state of the simulator: its copy of the real state, the key-derivation input of each
session it completed, and the phase. -/
abbrev SimSt (S W K PK SK SS C : Type) :=
  PSt S W K PK SK SS C × (Inst → Option (PInp W SS)) × Phase S W K PK C

/-- The outer events of the simulator: the interface of the real protocol. -/
abbrev OEv (W SS C : Type) := HEv ⊕ PAEv W SS C

/-- The outer outputs of the simulator. -/
abbrev OOut (S W K PK C : Type) := HOut K ⊕ POut S W K PK C

/-- A decision of the simulator. -/
abbrev Dec (S W K PK C : Type) := FEv K ⊕ OOut S W K PK C

/-- The simulator's answer to an answer of `F_AKE`: in the phase `fwd`, the answer on the
honest port, and an acknowledgement for an answer on the adversary port; otherwise the stored
output. -/
def simOut {S W K PK C : Type} : Phase S W K PK C → FOut K → OOut S W K PK C
  | .fwd, .inl o => .inl o
  | .fwd, .inr _ => .inr (.inl .ack)
  | .out r, _ => .inr r

/-- The operations of a key encapsulation mechanism as computations: key generation,
encapsulation and decapsulation, where key generation and encapsulation neither touch the heap
nor fail. -/
structure KemOps (PK SK SS C : Type) where
  /-- Key generation, returning `(pk, sk)`. -/
  keygen : SPComp (PK × SK)
  /-- Encapsulation to a public key, returning `(shared secret, encapsulation)`. -/
  encaps : PK → SPComp (SS × C)
  /-- Decapsulation with a secret key, `none` on rejection. -/
  decaps : SK → C → Option SS
  /-- Key generation neither touches the heap nor fails. -/
  keygen_pureNF : PureNF keygen
  /-- Encapsulation neither touches the heap nor fails. -/
  encaps_pureNF : ∀ pk, PureNF (encaps pk)

/-- Sampling from a total distribution neither touches the heap nor fails. -/
theorem pureNF_sampleFrom_ofPMF {α : Type} (p : PMF α) : PureNF (sampleFrom (ofPMF p)) := by
  rw [sampleFrom_ofPMF_eq_liftPMF]
  exact ⟨liftPMF_isPure _, liftPMF_noFail _⟩

/-- The operations of the KEM `P`: key generation and encapsulation sample from the
distributions of `P`, and decapsulation is `P.decaps`. -/
noncomputable def kemOps {PK SK SS C : Type} (P : Scheme PK SK SS C) : KemOps PK SK SS C where
  keygen := sampleFrom (ofPMF P.keygen)
  encaps pk := sampleFrom (ofPMF (P.encaps pk))
  decaps := P.decaps
  keygen_pureNF := pureNF_sampleFrom_ofPMF _
  encaps_pureNF _ := pureNF_sampleFrom_ofPMF _

section Sim

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (O : KemOps PK SK SS C) (G : DHGroup S W)

/-- The delivery of the key of the session `x` with record `r` and input `ip`, as in X3DH. An
exposed session receives the key-derivation value at `ip`, which the simulator samples and
passes to `newKey`. Any other session receives the key of `F_AKE`: `newKey` when its partner
has not completed or completed with the same input, `newKeyUnlinked` otherwise; the
key-derivation table is unchanged. -/
noncomputable def deliver (s : PSt S W K PK SK SS C) (inp : Inst → Option (PInp W SS))
    (x : Inst) (r : Rec K) (ip : PInp W SS) :
    SPComp (SimSt S W K PK SK SS C × Dec S W K PK C) :=
  if Exposed s.x.st x r then
    SPComp.map (fun p =>
      ((pKeyed s x r p.1 p.2, Function.update inp x (some ip), .out (.inl .ack)),
        .inl (.inr (.newKey x.1 x.2 p.1)))) (roStep s.ro ip)
  else
    SPComp.pure ((pKeyed s x r default s.ro, Function.update inp x (some ip), .out (.inl .ack)),
      .inl (.inr (if (inp (x.1, r.peer)).all (· = ip) then .newKey x.1 x.2 default
        else .newKeyUnlinked x.1 x.2 default)))

/-- The simulator on `complete sid pid`: the computation of `pqComplete` on its copy, with its
own encapsulation, and the delivery by `deliver`. -/
noncomputable def simComplete (s : SimSt S W K PK SK SS C) (x : Inst) :
    SPComp (SimSt S W K PK SK SS C × Dec S W K PK C) :=
  match s.1.x.st.recs x, s.1.x.eph x with
  | some r, some ek =>
    match opkOf s.1.x x.1 r.peer, pkOf s.1 x.1 r.peer with
    | some opk, some pk =>
      if r.role = .initiator ∧ r.key.isNone then
        SPComp.bind (ltStep s.1.x x.2) fun la => SPComp.bind (ltStep la.2 r.peer) fun lb =>
          SPComp.bind (O.encaps pk) fun kc =>
            deliver { s.1 with x := lb.2, ct := Function.update s.1.ct x (some kc.2) } s.2.1 x r
              (aliceInp G x.1 x.2 r.peer la.1.1 ek (G.pub lb.1.1) (G.pub lb.1.2) (G.pub opk),
                kc.1)
      else SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
    | _, _ => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
  | _, _ => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))

/-- The simulator on `send sid pid e c`: the computation of `pqSend` on its copy, and the
delivery by `deliver`. -/
noncomputable def simSend (s : SimSt S W K PK SK SS C) (x : Inst) (e : W) (c : C) :
    SPComp (SimSt S W K PK SK SS C × Dec S W K PK C) :=
  match s.1.x.st.recs x, s.1.x.eph x, s.1.kem x with
  | some r, some opk, some kp =>
    match O.decaps kp.2 c with
    | some ss =>
      if r.role = .responder ∧ r.key.isNone then
        SPComp.bind (ltStep s.1.x x.2) fun lb => SPComp.bind (ltStep lb.2 r.peer) fun la =>
          deliver { s.1 with x := la.2 } s.2.1 x r
            (bobInp G x.1 r.peer x.2 (G.pub la.1.1) e lb.1.1 lb.1.2 opk, ss)
      else SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
    | none => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
  | _, _, _ => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))

/-- The simulator on `corrupt pid`: refused as in the real protocol when a session names `pid`;
otherwise the secrets of its copy are output and `pid` is corrupted in `F_AKE`. -/
noncomputable def simCorrupt (s : SimSt S W K PK SK SS C) (pid : PartyId) :
    SPComp (SimSt S W K PK SK SS C × Dec S W K PK C) :=
  if Named s.1.x.st pid then SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl (.secret none))))
  else
    SPComp.map (fun l =>
      (({ s.1 with x := { l.2 with st := corruptStep l.2.st pid } }, s.2.1,
        .out (.inl (.secret (some l.1)))), .inl (.inr (.corrupt pid)))) (ltStep s.1.x pid)

/-- The start of an activation of the simulator. Honest events go to `F_AKE` and update the
copy as `pqHon` does (a new session draws its Diffie–Hellman secret, and a new responder session
its KEM key pair from `O.keygen`); `complete`, `send` and `corrupt` are handled as above; every
other adversary event is answered as `pqAdv` does on the copy. -/
noncomputable def simStart (s : SimSt S W K PK SK SS C) :
    OEv W SS C → SPComp (SimSt S W K PK SK SS C × Dec S W K PK C)
  | .inl (.newSession sid pid peer role) =>
    if (s.1.x.st.recs (sid, pid)).isNone then
      SPComp.bind (SPComp.sample S) fun y =>
        if role = .responder then
          SPComp.map (fun kp =>
            (({ s.1 with
                x := { s.1.x with st := addSession s.1.x.st (sid, pid) peer role,
                                  eph := Function.update s.1.x.eph (sid, pid) (some y) },
                kem := Function.update s.1.kem (sid, pid) (some kp) }, s.2.1, .fwd),
              .inl (.inl (.newSession sid pid peer role)))) O.keygen
        else
          SPComp.pure
            (({ s.1 with
                x := { s.1.x with st := addSession s.1.x.st (sid, pid) peer role,
                                  eph := Function.update s.1.x.eph (sid, pid) (some y) } },
                s.2.1, .fwd), .inl (.inl (.newSession sid pid peer role)))
    else SPComp.pure ((s.1, s.2.1, .fwd), .inl (.inl (.newSession sid pid peer role)))
  | .inl (.getKey sid pid) => SPComp.pure ((s.1, s.2.1, .fwd), .inl (.inl (.getKey sid pid)))
  | .inr .idle => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
  | .inr .poll =>
    SPComp.pure (({ s.1 with x := { s.1.x with st := (pollStep s.1.x.st).1 } }, s.2.1, .fwd),
      .inr (.inr (.inl (.notice (pollStep s.1.x.st).2))))
  | .inr (.pub pid) => SPComp.map (fun l =>
      (({ s.1 with x := l.2 }, s.2.1, .fwd),
        .inr (.inr (.inl (.pub (G.pub l.1.1) (G.pub l.1.2)))))) (ltStep s.1.x pid)
  | .inr (.ephPub sid pid) =>
    SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl (.eph (ephPubOf G s.1.x (sid, pid))))))
  | .inr (.pqPub sid pid) =>
    SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inr (pkOf s.1 sid pid, s.1.ct (sid, pid)))))
  | .inr (.corrupt pid) => simCorrupt s pid
  | .inr (.complete sid pid) => simComplete O G s (sid, pid)
  | .inr (.send sid pid e c) => simSend O G s (sid, pid) e c
  | .inr (.kdf x) => SPComp.map (fun p =>
      (({ s.1 with ro := p.2 }, s.2.1, .fwd), .inr (.inr (.inl (.hash p.1))))) (roStep s.1.ro x)

omit [Field S] [Fintype S] in
/-- `deliver` neither touches the heap nor fails. -/
theorem deliver_pureNF (s : PSt S W K PK SK SS C) (inp : Inst → Option (PInp W SS)) (x : Inst)
    (r : Rec K) (ip : PInp W SS) : PureNF (deliver s inp x r ip) := by
  unfold deliver
  split
  · exact (roStep_pureNF _ _).map _
  · exact pureNF_pure _

/-- The start of the simulator neither touches the heap nor fails. -/
theorem simStart_pureNF (s : SimSt S W K PK SK SS C) (e : OEv W SS C) :
    PureNF (simStart O G s e) := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e, c⟩ | x)
  · simp only [simStart]
    split
    · refine (pureNF_sample _).bind fun _ => ?_
      split
      · exact O.keygen_pureNF.map _
      · exact pureNF_pure _
    · exact pureNF_pure _
  · exact pureNF_pure _
  · exact pureNF_pure _
  · exact pureNF_pure _
  · exact (ltStep_pureNF _ _).map _
  · exact pureNF_pure _
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
          (O.encaps_pureNF _).bind fun _ => deliver_pureNF _ _ _ _ _
  · simp only [simStart, simSend]
    repeat' split
    all_goals first
      | exact pureNF_pure _
      | exact (ltStep_pureNF _ _).bind fun _ => (ltStep_pureNF _ _).bind fun _ =>
          deliver_pureNF _ _ _ _ _
  · exact (roStep_pureNF _ _).map _

/-- **The PQXDH simulator over the KEM operations `O`** as a multi-call simulator over `F_AKE`,
one call per activation. -/
noncomputable def simProtK :
    MultiHybrid (SimSt S W K PK SK SS C) (OEv W SS C) (OOut S W K PK C) (FEv K) (FOut K) where
  init := (pInit, fun _ => none, .fwd)
  fuel := 0
  start := simStart O G
  resume s o := SPComp.pure ((s.1, s.2.1, .fwd), .inr (simOut s.2.2 o))
  finish s o := SPComp.pure ((s.1, s.2.1, .fwd), simOut s.2.2 o)
  start_noFail s e := (simStart_pureNF O G s e).2
  resume_noFail _ _ := CatCrypt.Crypto.SPComp.pure_noFail _
  finish_noFail _ _ := CatCrypt.Crypto.SPComp.pure_noFail _

end Sim

/-! ## Opacity of the simulator -/

/-- The view of the real interface: equal events, any two honest outputs, equal adversary
outputs. -/
abbrev outerView {S W K PK SS C : Type} : PubView (OEv W SS C) (OOut S W K PK C) :=
  keHonView.sum eqView

/-- Every decision is related to itself. -/
theorem stepRel_refl {S W K PK SS C : Type} (d : Dec S W K PK C) :
    PubView.StepRel (outerView (SS := SS)) subView d d := by
  rcases d with (h | a) | (o | o)
  · exact Sum.LiftRel.inl rfl
  · exact Sum.LiftRel.inr rfl
  · exact Sum.LiftRel.inl trivial
  · exact Sum.LiftRel.inr rfl

/-- The answers of the simulator to related answers of `F_AKE` are related. -/
theorem simOut_rel {S W K PK SS C : Type} (ph : Phase S W K PK C) {o o' : FOut K}
    (h : (subView (K := K)).out o o') :
    (outerView (SS := SS)).out (simOut ph o) (simOut ph o') := by
  cases ph with
  | fwd =>
    cases h with
    | inl _ => exact Sum.LiftRel.inl trivial
    | inr _ => exact Sum.LiftRel.inr rfl
  | out r => exact Sum.LiftRel.inr rfl

section SimOpaque

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (O : KemOps PK SK SS C) (P : Scheme PK SK SS C)
  (G : DHGroup S W)

/-- **The unwinding condition of the simulator over the KEM operations `O`** for the equality
of states: its state and its decisions depend on its events and not on the answers of `F_AKE` on
its honest port. -/
theorem simProtK_unwinding : (simProtK (K := K) O G).Unwinding outerView subView Eq := by
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

/-- **Opacity of the simulator over the KEM operations `O`**: it reads no key of `F_AKE`. -/
theorem simProtK_opaque : (simProtK (K := K) O G).Opaque outerView subView :=
  ⟨Eq, simProtK_unwinding O G⟩

/-- **The PQXDH simulator over the KEM operations `O`** as a bundled opaque simulator. -/
noncomputable def pqxdhSimK :
    Simulator (OEv W SS C) (OOut S W K PK C) (FEv K) (FOut K) outerView subView :=
  Simulator.ofMultiHybrid (simProtK O G) (simProtK_opaque O G)

/-- **The PQXDH simulator** for the KEM `P`: the simulator over the operations `kemOps P`. -/
noncomputable def simProt :
    MultiHybrid (SimSt S W K PK SK SS C) (OEv W SS C) (OOut S W K PK C) (FEv K) (FOut K) :=
  simProtK (kemOps P) G

/-- **The unwinding condition of the simulator** for the equality of states: its state and its
decisions depend on its events and not on the answers of `F_AKE` on its honest port. -/
theorem simProt_unwinding : (simProt (K := K) P G).Unwinding outerView subView Eq :=
  simProtK_unwinding (kemOps P) G

/-- **Opacity of the simulator**: it reads no key of `F_AKE`. -/
theorem simProt_opaque : (simProt (K := K) P G).Opaque outerView subView :=
  simProtK_opaque (kemOps P) G

/-- **The PQXDH simulator** as a bundled opaque simulator: `pqxdhSimK` at the operations
`kemOps P`. -/
noncomputable def pqxdhSim :
    Simulator (OEv W SS C) (OOut S W K PK C) (FEv K) (FOut K) outerView subView :=
  pqxdhSimK (kemOps P) G

end SimOpaque

/-! ## The square in oracle-game form -/

section SimWorld

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (G : DHGroup S W)

/-- The steps of the simulated world, the simulator running with `F_AKE`, do not touch the
heap. -/
theorem simWorld_pureNF :
    ∀ t e, PureNF (((simProt (K := K) P G).withSub (F_AKE (SPComp.sample K) true)).step t e) :=
  withSub_pureNF _ _ F_AKE_pureNF (simStart_pureNF (kemOps P) G)
    (fun _ _ => pureNF_pure _) (fun _ _ => pureNF_pure _)

/-- **The simulated PQXDH game**: the oracle game of the simulator running with `F_AKE`. -/
noncomputable def simGame : KeyedGame (OEv W SS C) (OOut S W K PK C) :=
  pureGame ((simProt (K := K) P G).withSub (F_AKE (SPComp.sample K) true)) (simWorld_pureNF P G)

/-- **The simulated world as an oracle game**: the oracle system of `simGame P G` realizes the
simulator running with `F_AKE` at distance `0`. -/
theorem simWorld_realizes :
    Realizes ((OProt.oracle (Q := OEv W SS C) (A := OOut S W K PK C)).sys (simGame P G))
      ((simProt (K := K) P G).withSub (F_AKE (SPComp.sample K) true)) (fun _ _ => 0) :=
  pureGame_realizes _ _

/-- **PQXDH realizes `F_AKE` behind `pqxdhSim`, in oracle-game form.** For every environment
`Z`, the distance between the real PQXDH protocol and the simulator running with `F_AKE` is at
most the advantage of the oracle adversary `OProt.oracle.reduction Z` between the real game
`realGame P G` and the simulated game `simGame P G`. -/
theorem pqxdh_realizesSim_oracleGame :
    RealizesSim (pqxdhReal (K := K) P G) (F_AKE (SPComp.sample K) true) (pqxdhSim P G)
      (fun _ Z => KeyedGame.advantage (realGame P G) (simGame P G) (OProt.oracle.reduction Z)) :=
  fun ζ Z => le_of_le_of_eq
    ((Realizes.trans (Realizes.ofOracleGame OProt.oracle (realGame P G) (simGame P G))
      (simWorld_realizes P G)) ζ Z) (add_zero _)

end SimWorld

/-! ## The key derivation drawn in advance -/

section LazyEager

open CatCrypt.Crypto.AKE.X3DHSquare (pendingOf nodup_pendingOf pendingOf_addSession
  pendingOf_pollStep drawPool_perm drawPool_bind_eagerKDF drawPool_pendingOf_setRec ltAt_eq_ltDraw
  realAdvK realHonK)

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [DecidableEq SS]

/-- The state `s` with the key-derivation state `t`. -/
def pWithRo {T T' : Type} (s : PStT S W K PK SK C T) (t : T') : PStT S W K PK SK C T' :=
  ⟨s.x, s.kem, s.ct, t⟩

/-- **The kernel from lazy to eager key derivation**: the pool of keys of the pending sessions,
drawn independently and uniformly, beside the table. -/
noncomputable def eagerKernel (s : PSt S W K PK SK SS C) :
    PMF (PStT S W K PK SK C (List (PInp W SS × K) × (Inst → Option K))) :=
  (drawPool (pendingOf s.x.st)).map fun pool => pWithRo s (s.ro, pool)

variable (P : Scheme PK SK SS C)

/-- **The honest port, lazy and eager.** -/
theorem eagerKernel_pqHonK (s : PSt S W K PK SK SS C) (h : HEv) :
    ((eagerKernel s).bind fun s' => pqHonK P eagerKDF s' h) =
      (pqHonK P lazyKDF s h).bind fun p => (eagerKernel p.2).map fun s' => (p.1, s') := by
  simp only [eagerKernel, PMF.bind_map, Function.comp_def]
  cases h with
  | newSession sid pid peer role =>
    by_cases hx : (s.x.st.recs (sid, pid)).isNone
    · have hn : s.x.st.recs (sid, pid) = none := Option.isNone_iff_eq_none.1 hx
      simp only [pqHonK, realHon, realHonK, pWithRo, hx, ↓reduceIte, true_and, eagerKDF,
        lazyKDF, PMF.pure_map, PMF.map_comp, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
      split_ifs with hr <;> simp only [PMF.bind_map, PMF.map_bind, PMF.map_comp, PMF.pure_bind,
        Function.comp_def, drawPool_perm (pendingOf_addSession s.x.st (sid, pid) peer role hn),
        drawPool]
      · rw [PMF.bind_comm]
        refine congrArg _ (funext fun a => ?_)
        rw [PMF.bind_comm]
        refine congrArg _ (funext fun kp => ?_)
        simp only [← PMF.bind_pure_comp]
        exact PMF.bind_comm _ _ _
      · rw [PMF.bind_comm]
        refine congrArg _ (funext fun a => ?_)
        simp only [← PMF.bind_pure_comp]
        exact PMF.bind_comm _ _ _
    · simp only [pqHonK, realHon, realHonK, pWithRo, hx, Bool.false_eq_true, ↓reduceIte,
        false_and, PMF.pure_bind, PMF.pure_map, PMF.map_comp, Function.comp_def]
      rfl
  | getKey sid pid =>
    simp only [pqHonK, pWithRo, PMF.pure_bind, PMF.map_comp, Function.comp_def]
    rfl

variable (G : DHGroup S W)

/-- **The adversary port, lazy and eager.** -/
theorem eagerKernel_pqAdvK (s : PSt S W K PK SK SS C) (e : PAEv W SS C) :
    ((eagerKernel s).bind fun s' => pqAdvK P eagerKDF G s' e) =
      (pqAdvK P lazyKDF G s e).bind fun p => (eagerKernel p.2).map fun s' => (p.1, s') := by
  simp only [eagerKernel, PMF.bind_map, Function.comp_def]
  cases e with
  | idle =>
    simp only [pqAdvK, onX, realAdv, realAdvK, pWithRo, PMF.pure_bind, PMF.pure_map,
      PMF.map_comp, Function.comp_def]
    rfl
  | poll =>
    simp only [pqAdvK, onX, realAdv, realAdvK, pWithRo, PMF.pure_bind, PMF.pure_map,
      PMF.map_comp, Function.comp_def, pendingOf_pollStep]
    rfl
  | pub pid =>
    simp only [pqAdvK, onX, realAdv, realAdvK, ltAt_eq_ltDraw, pWithRo, PMF.map_comp,
      PMF.bind_map, Function.comp_def]
    simp only [← PMF.bind_pure_comp]
    exact PMF.bind_comm _ _ _
  | ephPub sid pid =>
    simp only [pqAdvK, onX, realAdv, realAdvK, pWithRo, PMF.pure_bind, PMF.pure_map,
      PMF.map_comp, Function.comp_def]
    rfl
  | pqPub sid pid =>
    simp only [pqAdvK, pWithRo, PMF.pure_bind, PMF.map_comp, Function.comp_def]
    rfl
  | corrupt pid =>
    simp only [pqAdvK, onX, corruptRStep]
    by_cases hN : Named s.x.st pid
    · simp only [hN, ↓reduceIte, pWithRo, PMF.pure_bind, PMF.pure_map, PMF.map_comp,
        Function.comp_def]
      rfl
    · simp only [hN, Bool.false_eq_true, ↓reduceIte, ltAt_eq_ltDraw, pWithRo, PMF.map_comp,
        PMF.bind_map, Function.comp_def]
      simp only [← PMF.bind_pure_comp]
      exact PMF.bind_comm _ _ _
  | kdf x =>
    simp only [pqAdvK, pWithRo, eagerKDF, lazyKDF, PMF.map_comp, PMF.bind_map,
      Function.comp_def]
    simp only [← PMF.bind_pure_comp]
    exact PMF.bind_comm _ _ _
  | complete sid pid =>
    simp only [pqAdvK, pqCompleteK]
    have hop : ∀ (t : List (PInp W SS × K) × (Inst → Option K)) (b : PartyId),
        opkOf (pWithRo s t).x sid b = opkOf s.x sid b := fun _ _ => rfl
    have hpk : ∀ (t : List (PInp W SS × K) × (Inst → Option K)) (b : PartyId),
        pkOf (pWithRo s t) sid b = pkOf s sid b := fun _ _ => rfl
    cases hr : s.x.st.recs (sid, pid) with
    | none =>
      simp only [pWithRo, hr, PMF.pure_bind, PMF.map_comp, Function.comp_def]
      rfl
    | some r =>
      cases he : s.x.eph (sid, pid) with
      | none =>
        simp only [pWithRo, hr, he, PMF.pure_bind, PMF.map_comp, Function.comp_def]
        rfl
      | some ek =>
        simp only [hop, hpk]
        cases ho : opkOf s.x sid r.peer with
        | none =>
          simp only [pWithRo, hr, he, ho, PMF.pure_bind, PMF.map_comp, Function.comp_def]
          rfl
        | some opk =>
          cases hk : pkOf s sid r.peer with
          | none =>
            simp only [pWithRo, hr, he, ho, hk, PMF.pure_bind, PMF.map_comp, Function.comp_def]
            rfl
          | some pk =>
            by_cases hc : r.role = .initiator ∧ r.key.isNone
            · simp only [pWithRo, hr, he, ho, hk, hc, and_self, ↓reduceIte, ltAt_eq_ltDraw,
                lazyKDF, pKeyed, keyed, PMF.bind_map, PMF.bind_bind, PMF.map_comp,
                Function.comp_def]
              simp only [drawPool_pendingOf_setRec]
              rw [PMF.bind_comm]
              refine congrArg _ (funext fun qa => ?_)
              rw [PMF.bind_comm]
              refine congrArg _ (funext fun qb => ?_)
              rw [PMF.bind_comm]
              refine congrArg _ (funext fun kc => ?_)
              exact drawPool_bind_eagerKDF (D := PInp W SS) s.ro _ (nodup_pendingOf _) _ _
                fun p pool => (Sum.inl ROut.ack, (⟨⟨setRec s.x.st (sid, pid)
                  ⟨r.peer, .initiator, r.status, some p.1⟩, qb.2, s.x.eph, s.x.ro⟩, s.kem,
                  Function.update s.ct (sid, pid) (some kc.2), (p.2, pool)⟩ :
                    PStT S W K PK SK C (List (PInp W SS × K) × (Inst → Option K))))
            · simp only [pWithRo, hr, he, ho, hk, hc, ↓reduceIte, PMF.pure_bind, PMF.map_comp,
                Function.comp_def]
              rfl
  | send sid pid e c =>
    simp only [pqAdvK, pqSendK]
    cases hr : s.x.st.recs (sid, pid) with
    | none =>
      simp only [pWithRo, hr, PMF.pure_bind, PMF.map_comp, Function.comp_def]
      rfl
    | some r =>
      cases he : s.x.eph (sid, pid) with
      | none =>
        simp only [pWithRo, hr, he, PMF.pure_bind, PMF.map_comp, Function.comp_def]
        rfl
      | some opk =>
        cases hm : s.kem (sid, pid) with
        | none =>
          simp only [pWithRo, hr, he, hm, PMF.pure_bind, PMF.map_comp, Function.comp_def]
          rfl
        | some kp =>
          cases hd : P.decaps kp.2 c with
          | none =>
            simp only [pWithRo, hr, he, hm, hd, PMF.pure_bind, PMF.map_comp, Function.comp_def]
            rfl
          | some ss =>
            by_cases hc : r.role = .responder ∧ r.key.isNone
            · simp only [pWithRo, hr, he, hm, hd, hc, and_self, ↓reduceIte, ltAt_eq_ltDraw,
                lazyKDF, pKeyed, keyed, PMF.bind_map, PMF.bind_bind, PMF.map_comp,
                Function.comp_def]
              simp only [drawPool_pendingOf_setRec]
              rw [PMF.bind_comm]
              refine congrArg _ (funext fun qb => ?_)
              rw [PMF.bind_comm]
              refine congrArg _ (funext fun qa => ?_)
              exact drawPool_bind_eagerKDF (D := PInp W SS) s.ro _ (nodup_pendingOf _) _ _
                fun p pool => (Sum.inl ROut.ack, (⟨⟨setRec s.x.st (sid, pid)
                  ⟨r.peer, .responder, r.status, some p.1⟩, qa.2, s.x.eph, s.x.ro⟩, s.kem,
                  s.ct, (p.2, pool)⟩ :
                    PStT S W K PK SK C (List (PInp W SS × K) × (Inst → Option K))))
            · simp only [pWithRo, hr, he, hm, hd, hc, ↓reduceIte, PMF.pure_bind, PMF.map_comp,
                Function.comp_def]
              rfl

/-- **Lazy and eager key derivation in the real PQXDH protocol.** The real protocol with the key
derivation a lazily sampled random function and the real protocol with each session's
key-derivation value drawn in advance at its start (`eagerKDF`) are at distance `0`. -/
theorem pqxdhRealOf_lazy_eager :
    Realizes (pqxdhReal (K := K) P G) (pqxdhRealK P eagerKDF G) fun _ _ => 0 := by
  refine Realizes.ofKernel _ (realGameK P lazyKDF G) (realGameK P eagerKDF G) id
    (PMF.map_id _).symm eagerKernel (fun _ => True) ?_ trivial ?_ fun _ _ _ _ _ _ => trivial
  · simp [eagerKernel, realGameK, pendingOf, initSt, rInit, drawPool, PMF.pure_map, pWithRo,
      lazyKDF, eagerKDF]
  · intro _ s q _
    cases q with
    | inl h =>
      have e := congrArg (PMF.map fun p => (Sum.inl (β := POut S W K PK C) p.1, p.2))
        (eagerKernel_pqHonK (W := W) P s h)
      simp only [realGameK, id, PMF.map_bind, PMF.bind_map, PMF.map_comp,
        Function.comp_def] at e ⊢
      exact e
    | inr a =>
      have e := congrArg (PMF.map fun p => (Sum.inr (α := HOut K) p.1, p.2))
        (eagerKernel_pqAdvK P G s a)
      simp only [realGameK, id, PMF.map_bind, PMF.bind_map, PMF.map_comp,
        Function.comp_def] at e ⊢
      exact e

end LazyEager

end CatCrypt.Crypto.AKE.PQXDHSquare
