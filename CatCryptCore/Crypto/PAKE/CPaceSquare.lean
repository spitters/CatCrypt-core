/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PAKE.FPAKESys
public import CatCryptCore.Crypto.PAKE.CPaceH1
public import CatCryptCore.Crypto.UCOracleGame
public import CatCryptCore.Crypto.UCSimulator
public import CatCryptCore.Crypto.UCCoupling

/-!
# CPace against the lazy-extraction PAKE functionality

**Ideal functionality.** `F_lePAKE (SPComp.sample K)` of `CatCryptCore.Crypto.PAKE.FPAKESys`,
the functionality `F_lePAKE` of Abdalla, Barbosa, Bradley, Jarecki, Katz and Xu (CRYPTO 2020,
Fig. 1): an honest port (`newSession`, `getKey`) and an adversary port (`poll`, `testPwd`,
`registerTest`, `newKey`, `lateTestPwd`) on which passwords and keys appear only through the
test answers and the late-test values.

**Real protocol.** `cpaceReal G` runs CPace for the parties `0` and `1` of the protocol session
`0`, each with the other as peer (`Active`). It keeps the session records and notices of
`F_lePAKE` for every session. The password generator `H1` is a table `td : Pw → Sˣ`, sampled at
the first activation, with `H1(pw) = g^{td pw}`. A party with password `pw` draws `y ∈ S` at its
new session and sends `H1(pw)^y`. On a message `m` other than the identity it derives the key
`H2(r₀, Y₀, Y₁, m^y)`, where `Y₀, Y₁` are the messages of the parties `0` and `1` as it sees them
and `r₀` the role of party `0` as it sees it (`h2Inp`); `H2` is a lazily sampled random function
into `K`. The adversary port (`RAEv`) has `poll` (the notices), `msg pid` (the message of a
party), `h1 pw`, `h2 x`, and `send pid m` (deliver `m` to the party `pid`). The system is
`OProt.oracle.sys (realGame G)`: the steps are the oracle of the game `realGame G`, whose key is
the table of `H1`.

**Simulator.** `cpaceSim G` forwards the honest events to `F_lePAKE` and keeps their public part
(identifiers and roles). It samples its own table `td` for `H1` at the first activation and
answers `h1 pw` with `g^{td pw}`, recording the queried passwords. A party's message is `g^z` for
a secret `z ∈ S` the simulator draws at the party's new session. `H2` is a lazily sampled random
function, except at the inputs programmed by late tests. On `send pid m` to a party with secret
`z` and no key:
* if `m` is the partner's message, it calls `newKey`;
* otherwise, if an earlier `H2` query for the party's transcript extracts a queried password
  `pw` (`DHExtractKit.extract` of the CPace kit with the trapdoors `z / td pw`), it calls
  `testPwd pw` and then `newKey` with the answer of that query;
* otherwise it calls `registerTest` and `newKey`, and records the transcript. A later `H2` query
  for the transcript that extracts a password `pw` calls `lateTestPwd pw` and programs `H2` at the
  query with the returned value.
The simulator reads no password and no key: it is opaque from the password-blind view of
`F_lePAKE` to the password-blind view of the real interface, which relates any two `H2` answers
(`simProt_opaque`).

**Results.** The composite of the simulator with `F_lePAKE` is a system whose steps do not read
the heap; it is at distance `0` from the oracle system of the game `simGame G`
(`simWorld_realizes`). The square is the oracle-game bound `cpace_realizesSim_oracleGame`:
`cpaceReal G` realizes `F_lePAKE` behind `cpaceSim G` with bound, at the environment `Z`, the
advantage of the oracle adversary `OProt.oracle.reduction Z` between `realGame G` and
`simGame G`.

## Main definitions

* `RAEv`, `ROut`: the adversary port of the real protocol.
* `realGame`, `cpaceReal`: the real protocol.
* `simProt`, `cpaceSim`: the simulator.
* `simGame`: the oracle game of the simulated world.

## Main results

* `simProt_opaque`: opacity of the simulator.
* `simWorld_realizes`: the simulated world and the oracle system of `simGame` at distance `0`.
* `cpace_realizesSim_oracleGame`: CPace realizes `F_lePAKE` behind `cpaceSim` with the
  oracle-game bound.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PAKE.CPaceSquare

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FPAKE
open CatCrypt.Crypto.PAKE.DHExtract CatCrypt.NonUniform
open scoped ENNReal

/-! ## Roles, parties and hash inputs -/

/-- The other role. -/
def otherRole : Role → Role
  | .client => .server
  | .server => .client

/-- The role of party `0` as seen by the party `pid` with role `r`. -/
def role0 (pid : PartyId) (r : Role) : Role := if pid = 0 then r else otherRole r

/-- An input of the key-derivation hash `H2`: the role of party `0`, the messages of the
parties `0` and `1`, and the Diffie–Hellman value. -/
abbrev Inp (W : Type) := Role × W × W × W

/-- The input of `H2` of the party `pid` with role `r`, own message `own`, received message `m`
and Diffie–Hellman value `k`. -/
def h2Inp {W : Type} (pid : PartyId) (r : Role) (own m k : W) : Inp W :=
  (role0 pid r, if pid = 0 then own else m, if pid = 0 then m else own, k)

/-- The transcript part of an `H2` input: the role of party `0` and the two messages. -/
def Inp.tr {W : Type} (x : Inp W) : Role × W × W := (x.1, x.2.1, x.2.2.1)

/-- A protocol party: party `0` or `1` of the session `0`, with the other as peer. -/
def Active (sid pid peer : ℕ) : Bool := decide (sid = 0 ∧ pid ≤ 1 ∧ peer = 1 - pid)

/-- The answer of a lazily sampled random function with the table `tb` at `x`: the recorded
value, or a fresh uniform value that is recorded. -/
noncomputable def roAt {D K : Type} [DecidableEq D] [Fintype K] [Nonempty K]
    (tb : List (D × K)) (x : D) : PMF (K × List (D × K)) :=
  match tb.lookup x with
  | some v => PMF.pure (v, tb)
  | none => (PMF.uniformFintype K).map fun v => (v, (x, v) :: tb)

/-! ## The adversary port of the real protocol -/

/-- Events of the adversary port of the real protocol. -/
inductive RAEv (Pw W : Type) where
  /-- No action. -/
  | idle
  /-- Read the next notice of a new session. -/
  | poll
  /-- Read the message of the party `pid` of the session `0`. -/
  | msg (pid : PartyId)
  /-- Query `H1` at `pw`. -/
  | h1 (pw : Pw)
  /-- Query `H2` at `x`. -/
  | h2 (x : Inp W)
  /-- Deliver the message `m` to the party `pid` of the session `0`. -/
  | send (pid : PartyId) (m : W)

/-- Outputs of the adversary port of the real protocol. -/
inductive ROut (W K : Type) where
  /-- Acknowledgement. -/
  | ack
  /-- The next notice, if any. -/
  | notice (o : Option Notice)
  /-- The message of a party, if it started. -/
  | msg (o : Option W)
  /-- An answer of `H1`. -/
  | gen (Y : W)
  /-- An answer of `H2`. -/
  | hash (k : K)

/-! ## The real protocol -/

/-- The state of the real protocol: the session records and notices, the secrets of the parties
of the session `0`, and the table of `H2`. -/
structure RSt (S W Pw K : Type) where
  /-- Session records and notices, as in `F_lePAKE`. -/
  st : St Pw K
  /-- The secret `y` of the party `pid` of the session `0`, once it started. -/
  ys : PartyId → Option S
  /-- The table of `H2`. -/
  h2 : List (Inp W × K)

section Real

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]
  [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K]

/-- A step of the honest port of the real protocol with the table `td` of `H1`: a new session
is recorded, and a protocol party draws its secret. -/
noncomputable def realHon (s : RSt S W Pw K) : LeHEv Pw → PMF (HOut K × RSt S W Pw K)
  | .newSession sid pid peer role pw =>
    if (s.st.recs (sid, pid)).isNone ∧ Active sid pid peer = true then
      (PMF.uniformFintype S).map fun y =>
        (.ok, { s with st := addSession s.st (sid, pid) peer role pw,
                       ys := Function.update s.ys pid (some y) })
    else PMF.pure (.ok, { s with st := addSession s.st (sid, pid) peer role pw })
  | .getKey sid pid => PMF.pure (.key (keyOf s.st (sid, pid)), s)

variable (G : DHGroup S W)

/-- The message of the party `pid` of the session `0`: `H1(pw)^y`. -/
def realMsg (td : Pw → Sˣ) (s : RSt S W Pw K) (pid : PartyId) : Option W :=
  match s.ys pid, s.st.recs (0, pid) with
  | some y, some r => some (G.exp (G.pub (td r.pw)) y)
  | _, _ => none

/-- A step of the adversary port of the real protocol with the table `td` of `H1`. -/
noncomputable def realAdv (td : Pw → Sˣ) (s : RSt S W Pw K) :
    RAEv Pw W → PMF (ROut W K × RSt S W Pw K)
  | .idle => PMF.pure (.ack, s)
  | .poll => PMF.pure (.notice (pollStep s.st).2, { s with st := (pollStep s.st).1 })
  | .msg pid => PMF.pure (.msg (realMsg G td s pid), s)
  | .h1 pw => PMF.pure (.gen (G.pub (td pw)), s)
  | .h2 x => (roAt s.h2 x).map fun p => (.hash p.1, { s with h2 := p.2 })
  | .send pid m =>
    match s.ys pid, s.st.recs (0, pid) with
    | some y, some r =>
      if r.key = none ∧ m ≠ G.pub 0 then
        (roAt s.h2 (h2Inp pid r.role (G.exp (G.pub (td r.pw)) y) m (G.exp m y))).map fun p =>
          (.ack, { s with st := setRec s.st (0, pid) { r with key := some p.1 }, h2 := p.2 })
      else PMF.pure (.ack, s)
    | _, _ => PMF.pure (.ack, s)

/-- **The real CPace game**: the key is the table of `H1`, and the oracle is the step of the
real protocol. -/
noncomputable def realGame : KeyedGame (LeHEv Pw ⊕ RAEv Pw W) (HOut K ⊕ ROut W K) where
  Key := Pw → Sˣ
  State := RSt S W Pw K
  keyDist := PMF.uniformFintype (Pw → Sˣ)
  oracle td s
    | .inl h => (realHon s h).map fun p => (.inl p.1, p.2)
    | .inr a => (realAdv G td s a).map fun p => (.inr p.1, p.2)
  init := ⟨initSt, fun _ => none, []⟩

/-- **The real CPace protocol** as a system: the table of `H1` is sampled at the first
activation, and each event is a query to the oracle of `realGame G`. -/
noncomputable def cpaceReal :=
  (OProt.oracle (Q := LeHEv Pw ⊕ RAEv Pw W) (A := HOut K ⊕ ROut W K)).sys (realGame G)

end Real

/-! ## The simulator -/

/-- The phase of the simulator within an activation. -/
inductive Phase (W K : Type) where
  /-- No call pending. -/
  | rest
  /-- Forward the answer of `F_lePAKE`. -/
  | fwd
  /-- After a password test, deliver the key `k` to the party `pid`. -/
  | key (pid : PartyId) (k : K)
  /-- After `newKey`, acknowledge. -/
  | done
  /-- After `lateTestPwd`, program `H2` at `x` with the returned value and output it. -/
  | late (x : Inp W)

/-- The state of the simulator apart from the inputs programmed by late tests. -/
structure SimCore (S W Pw K : Type) [Monoid S] where
  /-- The table of `H1`, once sampled. -/
  td : Option (Pw → Sˣ)
  /-- The passwords queried at `H1`. -/
  cands : List Pw
  /-- The peer and role of the party `pid` of the session `0`, once it has a record. -/
  info : PartyId → Option (PartyId × Role)
  /-- The secret `z` of the party `pid` of the session `0`, once it started. -/
  zs : PartyId → Option S
  /-- Whether the simulator delivered a key to the party `pid`. -/
  keyed : PartyId → Bool
  /-- The transcript of a registered late test of the party `pid`. -/
  pend : PartyId → Option (Role × W × W)
  /-- The values of `H2` sampled by the simulator. -/
  h2 : List (Inp W × K)
  /-- The phase. -/
  phase : Phase W K

/-- The state of the simulator: the core and the inputs of `H2` programmed by late tests. -/
abbrev SimSt (S W Pw K : Type) [Monoid S] := SimCore S W Pw K × List (Inp W × K)

/-- The outer events of the simulator: the interface of the real protocol. -/
abbrev OEv (Pw W : Type) := LeHEv Pw ⊕ RAEv Pw W

/-- The outer outputs of the simulator. -/
abbrev OOut (W K : Type) := HOut K ⊕ ROut W K

/-- The events of `F_lePAKE`. -/
abbrev FEv (Pw K : Type) := LeHEv Pw ⊕ LeAEv Pw K

/-- The outputs of `F_lePAKE`. -/
abbrev FOut (K : Type) := HOut K ⊕ AOut K

/-- A decision of the simulator. -/
abbrev Dec (Pw W K : Type) := FEv Pw K ⊕ OOut W K

/-- An output of the simulator on the adversary port. -/
abbrev sOut {Pw W K : Type} (a : ROut W K) : Dec Pw W K := .inr (.inr a)

/-- A call of the simulator to the adversary port of `F_lePAKE`. -/
abbrev sCall {Pw W K : Type} (a : LeAEv Pw K) : Dec Pw W K := .inl (.inr a)

/-- An answer of `F_lePAKE` as an output of the real interface: honest outputs and notices are
forwarded, every other answer becomes an acknowledgement. -/
def convert {W K : Type} : FOut K → OOut W K
  | .inl o => .inl o
  | .inr (.notice o) => .inr (.notice o)
  | .inr _ => .inr .ack

/-- The value returned by `lateTestPwd`, and `default` for any other answer. -/
def revealVal {K : Type} [Inhabited K] : FOut K → K
  | .inr (.reveal (some k)) => k
  | _ => default

section Sim

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]
  [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- The CPace extraction kit for the table `td`. -/
def kit (td : Pw → Sˣ) : DHExtractKit S W W Pw :=
  cpaceKit G (fun pw => (td pw : S)) fun pw => (td pw).ne_zero

/-- The password that the `H2` query `x` extracts for the party `pid` with secret `z`, received
message `m` among the transcript, from the queried passwords `cands`. -/
def extractAt (td : Pw → Sˣ) (cands : List Pw) (z : S) (pid : PartyId) (x : Inp W) :
    Option Pw :=
  (kit G td).extract z cands (if pid = 0 then x.2.2.1 else x.2.1) x.2.2.2

/-- The late test that the fresh `H2` query `x` triggers for the party `pid`: the extracted
password, when the party registered a test for the transcript of `x`. -/
def lateAt (td : Pw → Sˣ) (c : SimCore S W Pw K) (x : Inp W) (pid : PartyId) : Option Pw :=
  match c.pend pid, c.zs pid with
  | some T, some z => if x.tr = T then extractAt G td c.cands z pid x else none
  | _, _ => none

/-- The late test that the fresh `H2` query `x` triggers: a party and the extracted password. -/
def lateTarget (td : Pw → Sˣ) (c : SimCore S W Pw K) (x : Inp W) : Option (PartyId × Pw) :=
  match lateAt G td c x 0 with
  | some pw => some (0, pw)
  | none => (lateAt G td c x 1).map fun pw => (1, pw)

/-- An earlier `H2` query of the simulator's table for the transcript `T` of the party `pid`
with secret `z` that extracts a password: the password and the value of the query. -/
def findMatch (td : Pw → Sˣ) (c : SimCore S W Pw K) (z : S) (pid : PartyId)
    (T : Role × W × W) : Option (Pw × K) :=
  c.h2.findSome? fun e =>
    if e.1.tr = T then (extractAt G td c.cands z pid e.1).map fun pw => (pw, e.2) else none

/-- The simulator on a new session: it records the peer and role of a party of the session `0`
and draws the secret of a protocol party. -/
noncomputable def honCore (c : SimCore S W Pw K) (sid pid peer : PartyId) (role : Role) :
    SPComp (SimCore S W Pw K) :=
  if sid = 0 ∧ pid ≤ 1 ∧ c.info pid = none then
    if Active sid pid peer = true then
      SPComp.map (fun z => { c with info := Function.update c.info pid (some (peer, role)),
                                    zs := Function.update c.zs pid (some z) }) (SPComp.sample S)
    else SPComp.pure { c with info := Function.update c.info pid (some (peer, role)) }
  else SPComp.pure c

/-- The simulator on `send pid m`, with the table `td`. -/
def sendCore (td : Pw → Sˣ) (c : SimCore S W Pw K) (pid : PartyId) (m : W) :
    SimCore S W Pw K × Dec Pw W K :=
  match c.zs pid, c.info pid with
  | some z, some (_, role) =>
    if c.keyed pid = false ∧ m ≠ G.pub 0 then
      let c₁ := { c with keyed := Function.update c.keyed pid true }
      if (c.zs (1 - pid)).map G.pub = some m then
        ({ c₁ with phase := .done }, sCall (.newKey 0 pid default))
      else
        let T := (h2Inp pid role (G.pub z) m m).tr
        match findMatch G td c z pid T with
        | some (pw, k) => ({ c₁ with phase := .key pid k }, sCall (.testPwd 0 pid pw))
        | none => ({ c₁ with phase := .key pid default,
                             pend := Function.update c.pend pid (some T) },
                   sCall (.registerTest 0 pid))
    else ({ c with phase := .rest }, sOut .ack)
  | _, _ => ({ c with phase := .rest }, sOut .ack)

/-- The simulator on a fresh `H2` query `x` (neither programmed nor in its table), with the
table `td`: a late test, or a fresh uniform value. -/
noncomputable def h2Core (td : Pw → Sˣ) (c : SimCore S W Pw K) (x : Inp W) :
    SPComp (SimCore S W Pw K × Dec Pw W K) :=
  match lateTarget G td c x with
  | some (pid, pw) =>
    SPComp.pure ({ c with pend := Function.update c.pend pid none, phase := .late x },
      sCall (.lateTestPwd 0 pid pw))
  | none =>
    SPComp.map (fun k => ({ c with h2 := (x, k) :: c.h2, phase := .rest }, sOut (.hash k)))
      (SPComp.sample K)

/-- The simulator on an adversary event, with the table `td`, apart from programmed inputs. -/
noncomputable def advCore (td : Pw → Sˣ) (c : SimCore S W Pw K) :
    RAEv Pw W → SPComp (SimCore S W Pw K × Dec Pw W K)
  | .idle => SPComp.pure ({ c with phase := .rest }, sOut .ack)
  | .poll => SPComp.pure ({ c with phase := .fwd }, sCall .poll)
  | .msg pid => SPComp.pure ({ c with phase := .rest }, sOut (.msg ((c.zs pid).map G.pub)))
  | .h1 pw => SPComp.pure ({ c with cands := if pw ∈ c.cands then c.cands else c.cands ++ [pw],
                                    phase := .rest }, sOut (.gen (G.pub (td pw))))
  | .h2 x =>
    match c.h2.lookup x with
    | some k => SPComp.pure ({ c with phase := .rest }, sOut (.hash k))
    | none => h2Core G td c x
  | .send pid m => SPComp.pure (sendCore G td c pid m)

/-- The public part of an honest event: its identifiers and role. -/
def honPub : LeHEv Pw → Option (PartyId × PartyId × PartyId × Role)
  | .newSession sid pid peer role _ => some (sid, pid, peer, role)
  | .getKey _ _ => none

/-- The table of `H1` of the simulator, sampled at the first activation. -/
noncomputable def tdStep (c : SimCore S W Pw K) : SPComp ((Pw → Sˣ) × SimCore S W Pw K) :=
  match c.td with
  | some td => SPComp.pure (td, c)
  | none => SPComp.map (fun td => (td, { c with td := some td })) (SPComp.sample (Pw → Sˣ))

/-- The simulator on the public part of an honest event. -/
noncomputable def honStep (c : SimCore S W Pw K) :
    Option (PartyId × PartyId × PartyId × Role) → SPComp (SimCore S W Pw K)
  | some (sid, pid, peer, role) =>
    SPComp.map (fun c' => { c' with phase := .fwd }) (honCore c sid pid peer role)
  | none => SPComp.pure { c with phase := .fwd }

/-- The simulator on an outer event, apart from programmed inputs: it samples the table of `H1`
at the first activation. -/
noncomputable def simCore (c : SimCore S W Pw K) (e : OEv Pw W) :
    SPComp (SimCore S W Pw K × Dec Pw W K) :=
  SPComp.bind (tdStep c) fun p => match e with
    | .inl h => SPComp.map (fun c' => (c', .inl (.inl h))) (honStep p.2 (honPub h))
    | .inr a => advCore G p.1 p.2 a

/-- The start of an activation of the simulator: an `H2` query at a programmed input is answered
from the programmed value; every other event goes to `simCore`. -/
noncomputable def simStart (s : SimSt S W Pw K) (e : OEv Pw W) :
    SPComp (SimSt S W Pw K × Dec Pw W K) :=
  match e with
  | .inr (.h2 x) =>
    match s.2.lookup x with
    | some k => SPComp.pure (({ s.1 with phase := .rest }, s.2), sOut (.hash k))
    | none => SPComp.map (fun r => ((r.1, s.2), r.2)) (simCore G s.1 e)
  | _ => SPComp.map (fun r => ((r.1, s.2), r.2)) (simCore G s.1 e)

/-- The simulator on an answer of `F_lePAKE` that ends the activation: a late-test value is
programmed into `H2` and output; a key delivery is acknowledged; other answers are converted. -/
def simAnswer (s : SimSt S W Pw K) (o : FOut K) : SimSt S W Pw K × OOut W K :=
  match s.1.phase with
  | .late x => (({ s.1 with phase := .rest }, (x, revealVal o) :: s.2),
      .inr (.hash (revealVal o)))
  | .done => (({ s.1 with phase := .rest }, s.2), .inr .ack)
  | .fwd => (({ s.1 with phase := .rest }, s.2), convert o)
  | _ => (({ s.1 with phase := .rest }, s.2), .inr .ack)

/-- The simulator on an answer of `F_lePAKE` with a call left: after a password test it
delivers the key; otherwise it ends the activation with `simAnswer`. -/
noncomputable def simResume (s : SimSt S W Pw K) (o : FOut K) :
    SPComp (SimSt S W Pw K × Dec Pw W K) :=
  match s.1.phase with
  | .key pid k => SPComp.pure (({ s.1 with phase := .done }, s.2), sCall (.newKey 0 pid k))
  | _ => SPComp.pure ((simAnswer s o).1, .inr (simAnswer s o).2)

/-- The simulator on the answer of `F_lePAKE` to its last call. -/
noncomputable def simFinish (s : SimSt S W Pw K) (o : FOut K) :
    SPComp (SimSt S W Pw K × OOut W K) :=
  SPComp.pure (simAnswer s o)

end Sim

/-! ## Computations that do not touch the heap -/

/-- A computation that does not read or write the heap and never fails. -/
def PureNF {α : Type} (c : SPComp α) : Prop := SPComp.IsPure c ∧ SPComp.NoFail c

/-- `pure` neither touches the heap nor fails. -/
theorem pureNF_pure {α : Type} (a : α) : PureNF (SPComp.pure a) :=
  ⟨SPComp.pure_isPure a, CatCrypt.Crypto.SPComp.pure_noFail a⟩

/-- Uniform sampling neither touches the heap nor fails. -/
theorem pureNF_sample (α : Type) [Fintype α] [Nonempty α] : PureNF (SPComp.sample α) :=
  ⟨SPComp.sample_isPure α, Assumptions.SPComp.sample_noFail⟩

/-- `PureNF` is closed under bind. -/
theorem PureNF.bind {α β : Type} {c : SPComp α} {f : α → SPComp β} (hc : PureNF c)
    (hf : ∀ a, PureNF (f a)) : PureNF (SPComp.bind c f) :=
  ⟨SPComp.bind_isPure hc.1 fun a => (hf a).1,
    Assumptions.SPComp.bind_noFail hc.2 fun a => (hf a).2⟩

/-- `PureNF` is closed under map. -/
theorem PureNF.map {α β : Type} {c : SPComp α} (f : α → β) (hc : PureNF c) :
    PureNF (SPComp.map f c) :=
  hc.bind fun a => pureNF_pure (f a)

section SimProt

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]
  [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- The start of the simulator neither touches the heap nor fails. -/
theorem simStart_pureNF (s : SimSt S W Pw K) (e : OEv Pw W) : PureNF (simStart G s e) := by
  have hcore : PureNF (simCore G s.1 e) := by
    unfold simCore
    refine PureNF.bind ?_ fun p => ?_
    · unfold tdStep
      split
      · exact pureNF_pure _
      · exact (pureNF_sample _).map _
    · rcases e with h | a
      · refine PureNF.map _ ?_
        unfold honStep
        split
        · refine PureNF.map _ ?_
          unfold honCore
          split
          · split
            · exact (pureNF_sample _).map _
            · exact pureNF_pure _
          · exact pureNF_pure _
        · exact pureNF_pure _
      · cases a <;> simp only [advCore]
        all_goals first
          | exact pureNF_pure _
          | (split
             · exact pureNF_pure _
             · unfold h2Core
               split
               · exact pureNF_pure _
               · exact (pureNF_sample _).map _)
  unfold simStart
  split
  · split
    · exact pureNF_pure _
    · exact hcore.map _
  · exact hcore.map _

/-- **The CPace simulator** as a multi-call simulator over `F_lePAKE`, at most two calls per
activation. -/
noncomputable def simProt :
    MultiHybrid (SimSt S W Pw K) (OEv Pw W) (OOut W K) (FEv Pw K) (FOut K) where
  init := (⟨none, [], fun _ => none, fun _ => none, fun _ => false, fun _ => none, [], .rest⟩, [])
  fuel := 1
  start := simStart G
  resume := simResume
  finish := simFinish
  start_noFail s e := (simStart_pureNF G s e).2
  resume_noFail s o := by
    unfold simResume
    split <;> exact CatCrypt.Crypto.SPComp.pure_noFail _
  finish_noFail s o := CatCrypt.Crypto.SPComp.pure_noFail _

end SimProt

/-! ## Opacity of the simulator -/

/-- The view of the adversary port of the real protocol: equal events, any two `H2` answers, and
equality on the other outputs. -/
def realView {Pw W K : Type} : PubView (RAEv Pw W) (ROut W K) where
  ev := Eq
  out
    | .ack, .ack => True
    | .notice o, .notice o' => o = o'
    | .msg o, .msg o' => o = o'
    | .gen Y, .gen Y' => Y = Y'
    | .hash _, .hash _ => True
    | _, _ => False

/-- The password-blind view of the real interface. -/
abbrev outerView {Pw W K : Type} : PubView (OEv Pw W) (OOut W K) := lePAKEHonView.sum realView

/-- The password-blind view of `F_lePAKE`, for which `F_lePAKE_opaque` holds. -/
abbrev subView {Pw K : Type} : PubView (FEv Pw K) (FOut K) := lePAKEHonView.sum answerView

/-- The unwinding relation of the simulator: equal cores, and programmed inputs at the same
points. -/
def SimRel {S W Pw K : Type} [Monoid S] (s s' : SimSt S W Pw K) : Prop :=
  s.1 = s'.1 ∧ s.2.map Prod.fst = s'.2.map Prod.fst

/-- A computation mapped by two functions, coupled with itself. -/
theorem rHoare_map_self {α β γ : Type} (c : SPComp α) (f : α → β) (g : α → γ) :
    rHoare eqPre (SPComp.map f c) (SPComp.map g c)
      (fun r h r' h' => h = h' ∧ ∃ a, r = f a ∧ r' = g a) :=
  rHoare_bind (rHoare_refl c) fun a b => rHoare_ret fun _ _ hh => by
    obtain ⟨rfl, rfl⟩ := (hh : a = b ∧ _)
    exact ⟨rfl, a, rfl, rfl⟩

/-- Lists with the same keys have lookups defined at the same points. -/
theorem lookup_isSome_of_map_fst {α β : Type} [DecidableEq α] {l l' : List (α × β)}
    (h : l.map Prod.fst = l'.map Prod.fst) (x : α) :
    (l.lookup x).isSome = (l'.lookup x).isSome := by
  induction l generalizing l' with
  | nil => cases l' <;> simp_all
  | cons a l ih =>
    cases l' with
    | nil => simp at h
    | cons b l' =>
      simp only [List.map_cons, List.cons.injEq] at h
      grind

/-- The password-blind honest view relates an honest event to itself. -/
theorem honView_refl {Pw K : Type} (h : LeHEv Pw) : (lePAKEHonView (K := K)).ev h h := by
  cases h <;> simp [lePAKEHonView]

/-- The view of the real interface relates an output to itself. -/
theorem outerView_out_refl {Pw W K : Type} (o : OOut W K) : (outerView (Pw := Pw)).out o o := by
  rcases o with o | (_ | _ | _ | _ | _) <;>
    simp [outerView, PubView.sum, lePAKEHonView, realView]

/-- A decision of the simulator is related to itself. -/
theorem stepRel_refl {Pw W K : Type} (d : Dec Pw W K) :
    PubView.StepRel (outerView (Pw := Pw)) subView d d := by
  rcases d with (g | g) | o
  · exact Sum.LiftRel.inl (honView_refl g)
  · exact Sum.LiftRel.inr rfl
  · exact outerView_out_refl o

/-- Honest events with equal public parts have the same `honPub`. -/
theorem honPub_eq_of_view {Pw K : Type} {h h' : LeHEv Pw} (hv : (lePAKEHonView (K := K)).ev h h') :
    honPub h = honPub h' := by
  cases h <;> cases h' <;> simp only [lePAKEHonView] at hv <;> grind [honPub]

/-- The answers of `F_lePAKE` related by its view convert to related outputs. -/
theorem convert_rel {Pw W K : Type} {o o' : FOut K} (h : (subView (Pw := Pw)).out o o') :
    (outerView (Pw := Pw) (W := W)).out (convert o) (convert o') := by
  cases h with
  | inl _ => exact Sum.LiftRel.inl trivial
  | inr h =>
    rename_i a a'
    cases a <;> cases a' <;> simp only [answerView] at h <;>
      exact Sum.LiftRel.inr (by simp_all [realView])

/-- The end of an activation from related states on related answers: related states and
related outputs. -/
theorem simAnswer_rel {S W Pw K : Type} [Field S] [Inhabited K] {s s' : SimSt S W Pw K}
    {o o' : FOut K} (hs : SimRel s s') (ho : (subView (Pw := Pw)).out o o') :
    SimRel (simAnswer s o).1 (simAnswer s' o').1 ∧
      (outerView (Pw := Pw)).out (simAnswer s o).2 (simAnswer s' o').2 := by
  rcases s with ⟨c, p⟩
  rcases s' with ⟨c', p'⟩
  obtain ⟨hc, hp⟩ := hs
  simp only at hc hp
  subst hc
  rcases c with ⟨_, _, _, _, _, _, _, ph⟩
  cases ph
  · exact ⟨⟨rfl, hp⟩, Sum.LiftRel.inr trivial⟩
  · exact ⟨⟨rfl, hp⟩, convert_rel ho⟩
  · exact ⟨⟨rfl, hp⟩, Sum.LiftRel.inr trivial⟩
  · exact ⟨⟨rfl, hp⟩, Sum.LiftRel.inr trivial⟩
  · exact ⟨⟨rfl, by simp [simAnswer, hp]⟩, Sum.LiftRel.inr trivial⟩

section SimOpaque

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]
  [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- The start of the simulator on an honest event (unfolding lemma of `simStart`). -/
theorem simStart_inl (c : SimCore S W Pw K) (p : List (Inp W × K)) (h : LeHEv Pw) :
    simStart G (c, p) (.inl h) = SPComp.map (fun c' => ((c', p), .inl (.inl h)))
      (SPComp.bind (tdStep c) fun q => honStep q.2 (honPub h)) := by
  simp only [simStart, simCore, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- The start of the simulator on an adversary event other than an `H2` query at a programmed
input (unfolding lemma of `simStart`). -/
theorem simStart_inr (c : SimCore S W Pw K) (p : List (Inp W × K)) (a : RAEv Pw W)
    (ha : ∀ x, a = .h2 x → p.lookup x = none) :
    simStart G (c, p) (.inr a) = SPComp.map (fun r => ((r.1, p), r.2)) (simCore G c (.inr a)) := by
  cases a with
  | h2 x => simp only [simStart, ha x rfl]
  | _ => rfl

/-- **The unwinding condition of the simulator** from the view of `F_lePAKE` to the view of the
real interface, for `SimRel`. -/
theorem simProt_unwinding :
    (simProt G (S := S) (Pw := Pw) (K := K)).Unwinding outerView subView SimRel := by
  refine ⟨⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · rintro ⟨c, p⟩ ⟨c', p'⟩ e e' ⟨hc, hp⟩ he
    simp only at hc hp
    subst hc
    change rHoare eqPre (simStart G (c, p) e) (simStart G (c, p') e') _
    cases he with
    | inl hv =>
      rename_i h h'
      rw [simStart_inl, simStart_inl, honPub_eq_of_view hv]
      refine rHoare_conseq (fun _ _ hh => hh) (fun r h₁ r' h₂ hr => ?_) (rHoare_map_self _ _ _)
      obtain ⟨rfl, a, rfl, rfl⟩ := hr
      exact ⟨rfl, ⟨rfl, hp⟩, Sum.LiftRel.inl hv⟩
    | inr hv =>
      rename_i a a'
      cases (hv : a = a')
      have hgen : (∀ x, a = .h2 x → p.lookup x = none) →
          rHoare eqPre (simStart G (c, p) (.inr a)) (simStart G (c, p') (.inr a))
            (fun r h₁ r' h₂ => h₁ = h₂ ∧ SimRel r.1 r'.1 ∧
              PubView.StepRel (outerView (Pw := Pw)) subView r.2 r'.2) := by
        intro ha
        have ha' : ∀ x, a = .h2 x → p'.lookup x = none := fun x hx => by
          have := lookup_isSome_of_map_fst hp x
          rw [ha x hx] at this
          exact Option.not_isSome_iff_eq_none.mp (by simp [← this])
        rw [simStart_inr G c p a ha, simStart_inr G c p' a ha']
        refine rHoare_conseq (fun _ _ hh => hh) (fun r h₁ r' h₂ hr => ?_)
          (rHoare_map_self _ _ _)
        obtain ⟨rfl, b, rfl, rfl⟩ := hr
        exact ⟨rfl, ⟨rfl, hp⟩, stepRel_refl _⟩
      cases a with
      | h2 x =>
        have hl := lookup_isSome_of_map_fst hp x
        cases h₁ : p.lookup x with
        | none => exact hgen fun y hy => by cases hy; exact h₁
        | some k =>
          cases h₂ : p'.lookup x with
          | none => simp [h₁, h₂] at hl
          | some k' =>
            simp only [simStart, h₁, h₂]
            exact rHoare_ret fun _ _ hh => ⟨hh, ⟨rfl, hp⟩, Sum.LiftRel.inr trivial⟩
      | _ => exact hgen fun y hy => by cases hy
  · rintro ⟨c, p⟩ ⟨c', p'⟩ o o' ⟨hc, hp⟩ ho
    simp only at hc hp
    subst hc
    have hans := simAnswer_rel (s := (c, p)) (s' := (c, p')) ⟨rfl, hp⟩ ho
    change rHoare eqPre (simResume (c, p) o) (simResume (c, p') o') _
    unfold simResume
    rcases c with ⟨_, _, _, _, _, _, _, ph⟩
    cases ph
    case key pid k => exact rHoare_ret fun _ _ hh => ⟨hh, ⟨rfl, hp⟩, Sum.LiftRel.inr rfl⟩
    all_goals exact rHoare_ret fun _ _ hh => ⟨hh, hans.1, hans.2⟩
  · rintro s s' o o' hs ho
    exact rHoare_ret fun _ _ hh => ⟨hh, simAnswer_rel hs ho⟩

/-- **Opacity of the simulator**: its outputs on the real interface, up to the `H2` answers,
and its calls to `F_lePAKE`, up to passwords, depend on its arguments only through their public
parts. -/
theorem simProt_opaque : (simProt G (S := S) (Pw := Pw) (K := K)).Opaque outerView subView :=
  ⟨_, simProt_unwinding G⟩

/-- **The CPace simulator** as a bundled opaque simulator. It reads no password and no key. -/
noncomputable def cpaceSim :
    Simulator (OEv Pw W) (OOut W K) (FEv Pw K) (FOut K) outerView subView :=
  Simulator.ofMultiHybrid (simProt G) (simProt_opaque G)

end SimOpaque

/-! ## Systems whose steps do not touch the heap, as oracle games -/

/-- A computation that does not touch the heap and never fails is the lift of a probability
mass function. -/
theorem PureNF.exists_liftPMF {α : Type} {c : SPComp α} (hc : PureNF c) :
    ∃ p : PMF α, c = liftPMF p := by
  obtain ⟨d, hd⟩ := hc.1
  have h0 : d none = 0 := isPure_noFail_d_none hd hc.2
  obtain ⟨o, ho⟩ := d.support_nonempty
  have hne : o ≠ none := fun h => by simp [h, PMF.mem_support_iff, h0] at ho
  obtain ⟨a, -⟩ := Option.ne_none_iff_exists'.mp hne
  refine ⟨PMF.bind d fun o => PMF.pure (o.getD a), funext fun h => ?_⟩
  rw [hd h]
  unfold liftPMF SDistr.bind
  rw [PMF.map_bind]
  refine PMF.ext fun x => ?_
  simp only [PMF.bind_apply, PMF.pure_map]
  refine tsum_congr fun o => ?_
  rcases o with _ | b
  · rw [h0, zero_mul, zero_mul]
  · rfl

/-- The distribution of a computation that does not touch the heap and never fails. -/
noncomputable def PureNF.pmf {α : Type} {c : SPComp α} (hc : PureNF c) : PMF α :=
  Classical.choose hc.exists_liftPMF

/-- A computation that does not touch the heap and never fails is the lift of its
distribution. -/
theorem PureNF.eq_liftPMF {α : Type} {c : SPComp α} (hc : PureNF c) : c = liftPMF hc.pmf :=
  Classical.choose_spec hc.exists_liftPMF

/-- **The oracle game of a system whose steps do not touch the heap**: the key is trivial, the
state is the system's state and the oracle is the distribution of a step. -/
noncomputable def pureGame {τ E O : Type} (X : Sys τ E O) (hX : ∀ t e, PureNF (X.step t e)) :
    KeyedGame E O where
  Key := Unit
  State := τ
  keyDist := PMF.pure ()
  oracle _ t e := (hX t e).pmf.map Prod.swap
  init := X.init

/-- Sampling from a total distribution is its lift. -/
theorem sampleFrom_ofPMF_eq_liftPMF {α : Type} (p : PMF α) :
    sampleFrom (ofPMF p) = liftPMF p := by
  funext h
  rw [sampleFrom_apply]
  exact sdistr_bind_map_some p id _

/-- **A system whose steps do not touch the heap is its oracle game**: the oracle system of
`pureGame X hX` realizes `X` at distance `0`. -/
theorem pureGame_realizes {τ E O : Type} (X : Sys τ E O) (hX : ∀ t e, PureNF (X.step t e)) :
    Realizes ((OProt.oracle (Q := E) (A := O)).sys (pureGame X hX)) X (fun _ _ => 0) := by
  refine realizes_zero_of_stepMap _ X (fun u => u.2.2) rfl fun u e => ?_
  have hkey : ∀ t : τ, SPComp.map (fun p => (p.1.2, p.2))
      ((OProt.oracle (Q := E) (A := O)).keyed (pureGame X hX) |>.step () ((), t) e) =
        X.step t e := by
    intro t
    rw [(hX t e).eq_liftPMF]
    simp only [OProt.keyed, OProt.plugStep, OProt.oracle, OracleAdv.run_query,
      OracleAdv.run_ret, pureGame, sampleFrom_ofPMF_eq_liftPMF, SPComp.map,
      liftPMF_bind_pure, PMF.map_comp]
    congr 1
    rw [PMF.bind_map, ← PMF.bind_pure_comp, PMF.bind_bind]
    simp only [Function.comp_apply, PMF.pure_bind]
    exact PMF.bind_pure _
  have hsome : ∀ t : τ, SPComp.map (fun p => (p.1.2.2, p.2))
      (((OProt.oracle (Q := E) (A := O)).sys (pureGame X hX)).step (some (), ((), t)) e) =
        X.step t e := by
    intro t
    rw [← hkey t]
    simp only [OProt.sys, KeyedSys.lazy, KeyedSys.lazyStep, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind]
  rcases u with ⟨_ | ⟨⟩, ⟨⟩, t⟩
  · rw [OProt.sys, KeyedSys.lazy_step_none_of_uses _ _ rfl, sampleFrom_ofPMF_eq_liftPMF]
    simp only [pureGame, ← liftPMF_pure, SPComp.pure_bind]
    rw [← hsome t]
    rfl
  · exact hsome t

/-- The rest of an activation of a multi-call simulator whose steps do not touch the heap, over a
subroutine whose steps do not touch the heap, does not touch the heap. -/
theorem drive_pureNF {σ τ E O EG OG : Type} (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG)
    (hX : ∀ t g, PureNF (X.step t g)) (hr : ∀ s o, PureNF (π.resume s o))
    (hf : ∀ s o, PureNF (π.finish s o)) :
    ∀ n s d t, PureNF (π.drive X n s d t) := by
  intro n
  induction n with
  | zero =>
    rintro s (g | o) t
    · exact (hX t g).bind fun q => (hf s q.2).bind fun _ => pureNF_pure _
    · exact pureNF_pure _
  | succ n ih =>
    rintro s (g | o) t
    · exact (hX t g).bind fun q => (hr s q.2).bind fun r => ih _ _ _
    · exact pureNF_pure _

/-- The steps of a multi-call simulator over a subroutine, both not touching the heap, do not
touch the heap. -/
theorem withSub_pureNF {σ τ E O EG OG : Type} (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG)
    (hX : ∀ t g, PureNF (X.step t g)) (hs : ∀ s e, PureNF (π.start s e))
    (hr : ∀ s o, PureNF (π.resume s o)) (hf : ∀ s o, PureNF (π.finish s o)) :
    ∀ t e, PureNF ((π.withSub X).step t e) := by
  intro t e
  unfold MultiHybrid.withSub
  exact (hs t.1 e).bind fun r => (drive_pureNF π X hX hr hf π.fuel r.1 r.2 t.2).bind
    fun p => pureNF_pure ((p.1, p.2.1), p.2.2)

/-- The steps of `F_lePAKE` with uniform keys do not touch the heap. -/
theorem F_lePAKE_pureNF {Pw K : Type} [DecidableEq Pw] [Fintype K] [Nonempty K]
    (t : St Pw K) (e : FEv Pw K) : PureNF ((F_lePAKE (Pw := Pw) (SPComp.sample K)).step t e) := by
  rcases e with h | a
  · simp only [F_lePAKE, Sys.ofPorts_step_inl, leHonSys]
    exact (pureNF_pure _).map _
  · simp only [F_lePAKE, Sys.ofPorts_step_inr, leAdvSys]
    refine PureNF.map _ ?_
    cases a <;> first | exact pureNF_pure _ | exact (pureNF_sample K).map _

section SimWorld

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]
  [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- The steps of the simulated world, the simulator running with `F_lePAKE`, do not touch the
heap. -/
theorem simWorld_pureNF :
    ∀ t e, PureNF (((simProt G).withSub (F_lePAKE (Pw := Pw) (SPComp.sample K))).step t e) :=
  withSub_pureNF _ _ F_lePAKE_pureNF (simStart_pureNF G)
    (fun s o => by unfold simProt simResume; dsimp only; split <;> exact pureNF_pure _)
    (fun _ _ => pureNF_pure _)

/-- **The simulated CPace game**: the oracle game of the simulator running with `F_lePAKE`. -/
noncomputable def simGame : KeyedGame (OEv Pw W) (OOut W K) :=
  pureGame ((simProt G).withSub (F_lePAKE (Pw := Pw) (SPComp.sample K))) (simWorld_pureNF G)

/-- **The simulated world as an oracle game**: the oracle system of `simGame G` realizes the
simulator running with `F_lePAKE` at distance `0`. -/
theorem simWorld_realizes :
    Realizes ((OProt.oracle (Q := OEv Pw W) (A := OOut W K)).sys (simGame G))
      ((simProt G).withSub (F_lePAKE (Pw := Pw) (SPComp.sample K))) (fun _ _ => 0) :=
  pureGame_realizes _ _

/-- **CPace realizes `F_lePAKE` behind `cpaceSim`, in oracle-game form** (genuine UC). For every
environment `Z`, the distance between the real CPace protocol and the simulator running with
`F_lePAKE` is at most the advantage of the oracle adversary `OProt.oracle.reduction Z` between
the real game `realGame G` and the simulated game `simGame G`. -/
theorem cpace_realizesSim_oracleGame :
    RealizesSim (cpaceReal G (K := K)) (F_lePAKE (Pw := Pw) (SPComp.sample K)) (cpaceSim G)
      (fun _ Z => KeyedGame.advantage (realGame G) (simGame G) (OProt.oracle.reduction Z)) :=
  fun ζ Z => le_of_le_of_eq
    ((Realizes.trans (Realizes.ofOracleGame OProt.oracle (realGame G) (simGame G))
      (simWorld_realizes G)) ζ Z) (add_zero _)

end SimWorld

end CatCrypt.Crypto.PAKE.CPaceSquare
