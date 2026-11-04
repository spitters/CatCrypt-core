/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHSquareGDH
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Crypto.UCSimulatorCostGraded

/-!
# Running time of the gap Diffie–Hellman reduction of the X3DH square

The reduction `gdhRed G a b B` of `X3DHSquareGDH.lean` outputs the distribution `gdhOut`: the
program `stepRedD (fun _ _ => PMF.uniformFintype (Draw S K × K)) (stepR …) (extractR …) B rInitR`
runs the oracle adversary `B` against the world of the reduction, one uniform draw per query, and
extracts its output from the final state. This module gives the costed form of the generic
reduction `stepRedD`, derived by `derive_timed`, its running time for an arbitrary draw
distribution, step and extraction (used by `PQXDHSquareGDHTimed` as well), and its running time at
the world of the X3DH reduction.

**The step programs.** A step of the world of the reduction is written as computations over
`sample` nodes, and `derive_reduction` builds the costed tree of each and its erasure theorem:
* `otherC`: the start of the simulator on the events other than `complete` and `send`;
* `cguardC`, `sguardC`: the guards of `complete` and `send`; `ltC`: a draw of long-term
  secrets; `deliverC`: the delivery of a key, with the symbolic lookup `sroStep`;
* `finishC`: the call to `F_AKE` (`fakeC`) and the finish of the simulator;
* `extractC`: the extraction.
These programs compute the step (`ltC_eq`, `sroStep_eq`, `deliverC_eq`, `completeR_eq`,
`sendR_eq`, `otherC_eq`, `finishC_eq`): each is the lift of the image of a uniform draw under the
corresponding part of `stepR`.

**The costed reduction.** `derive_timed stepRedD` defines `stepRedD.timed`, generic in the state,
the draw distribution, the step and the extraction, which become binders with cost companions, and
proves `stepRedD.erase_timed`. A query is the evaluation of the draw distribution, with its cost,
and one `rand` node over the draw, with the cost of the step; the leaf is the extraction with its
cost. At the world of the reduction the cost of the step is `stepTime`: one unit for the dispatch on
the event, the times of the costed trees of the programs on the states they read, and the time of
the finish; the cost of the extraction is `extTime`. Each costed tree is read with the tables of its
input state at unit cost (zero cost companions), the convention of the costed simulators of
`UCSimulatorCostGraded`. The uniform draw of X3DH costs zero beyond the unit of its evaluation. The
derivation does not price `stepR` itself: unfolding it exceeds the unfolding depth of `derive_timed`
at `ltD`, which is why the step is a binder of `stepRedD`.

**The time.** The derived trees are bounded by `time_bound`, linearly in the length of the
key-derivation table and of the lists of notices, given bounds `tO` on the decision oracle, `tm`
on the group operation, `te` on exponentiation and `tf`, `tc` on the public value of an exponent
(`otherC_time`, `delTime_le`, `finishC_time`, `extTime_le`, `slookup.timedCost_le`). A step adds
at most one entry to the table and to each list of notices (`sz_stepR`), so a step after `i` steps
costs less than `stepBound … i` (`stepTime_lt`), and an adversary of time `T` with at most `q`
queries gives a reduction of time at most `T + q · (stepBound … q + 2) + extBound … q + 1`
(`gdhOut_timeBound`, the instance of the generic bound `stepRedD.timeBound_timed` at the uniform
draw of cost zero and the step bound `stepBound … i - 1`): the time of the adversary
plus a polynomial of degree two in its number of queries.

## Main results

* `stepRedD.timed`, `stepRedD.erase_timed` (derived): the costed form of the generic reduction
  `stepRedD` and its erasure to `stepRedD`.
* `stepRedD.timeBound_timed`: its time under a state invariant bounding the draw and the step and
  the extraction.
* `gdhOut_erase_timed`, `gdhOut_timeBound`: the costed reduction of the X3DH square erases to the
  program of `gdhRed` and its time bound.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquareGDH

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.AKE.X3DHSquareHops
open CatCrypt.Crypto.OracleGameUpToBad

section Prog

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W) (a b : PartyId) (O : W → W → W → Bool) (X Y : W)

/-- The symbolic key derivation as a computation: the recorded value, or a uniform value that is
recorded. -/
noncomputable def sroStep (ZA ZB : W) (tb : List (Inp (W ⊕ W) × K)) (j : Inp (W ⊕ W)) :
    SPComp (K × List (Inp (W ⊕ W) × K)) :=
  match slookup G O ZA ZB j tb with
  | some v => SPComp.pure (v, tb)
  | none => SPComp.map (fun v => (v, (j, v) :: tb)) (SPComp.sample K)

/-- `deliverR` as a computation. -/
noncomputable def deliverC (rs : RSt S (W ⊕ W) K) (inp : Inst → Option (Inp (W ⊕ W))) (x : Inst)
    (r : Rec K) (ip : Inp (W ⊕ W)) : SPComp (RSim S W K × Dec S W K) :=
  if Exposed rs.st x r then
    SPComp.map (fun p => ((keyed rs x r p.1 p.2, Function.update inp x (some ip), .out .ack),
        .inl (.inr (.newKey x.1 x.2 p.1))))
      (sroStep G O (keyA G a X rs) (keyB G b Y rs) rs.ro ip)
  else
    SPComp.pure ((keyed rs x r default rs.ro, Function.update inp x (some ip), .out .ack),
      .inl (.inr (if (inp (x.1, r.peer)).all (fun j => inpEq G O (keyA G a X rs) (keyB G b Y rs) j ip)
        then .newKey x.1 x.2 default else .newKeyUnlinked x.1 x.2 default)))

/-- The guard of `complete`: the record, the ephemeral secret and the one-time prekey of the
session when it completes. -/
def cguard (s : RSim S W K) (sid : SessionId) (pid : PartyId) : Option (Rec K × S × S) :=
  match s.1.st.recs (sid, pid), s.1.eph (sid, pid) with
  | some rc, some ek =>
    match opkOf s.1 sid rc.peer with
    | some opk => if rc.role = .initiator ∧ rc.key.isNone then some (rc, ek, opk) else none
    | none => none
  | _, _ => none

/-- The guard of `send`: the record and the one-time prekey of the session when it completes. -/
def sguard (s : RSim S W K) (sid : SessionId) (pid : PartyId) : Option (Rec K × S) :=
  match s.1.st.recs (sid, pid), s.1.eph (sid, pid) with
  | some rc, some opk => if rc.role = .responder ∧ rc.key.isNone then some (rc, opk) else none
  | _, _ => none

/-- The guard of `complete` as a computation. -/
noncomputable def cguardC (s : RSim S W K) (sid : SessionId) (pid : PartyId) :
    SPComp (Option (Rec K × S × S)) :=
  SPComp.pure (cguard s sid pid)

/-- The guard of `send` as a computation. -/
noncomputable def sguardC (s : RSim S W K) (sid : SessionId) (pid : PartyId) :
    SPComp (Option (Rec K × S)) :=
  SPComp.pure (sguard s sid pid)

/-- The long-term secrets of a party in the world of the reduction, as a computation. -/
noncomputable def ltC (rs : RSt S (W ⊕ W) K) (pid : PartyId) :
    SPComp ((S × S) × RSt S (W ⊕ W) K) :=
  ltStep rs pid

/-- The other events of the simulator of the reduction as a computation. -/
noncomputable def otherC (s : RSim S W K) : OEv W → SPComp (RSim S W K × Dec S W K)
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
      ((l.2, s.2.1, .fwd), .inr (.inr (.pub (pubIK G a X pid l.1) (pubSPK G b Y pid l.1)))))
      (ltStep s.1 pid)
  | .inr (.ephPub sid pid) =>
    SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.eph ((s.1.eph (sid, pid)).map G.pub))))
  | .inr (.corrupt pid) =>
    if Named s.1.st pid then SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.secret none))) else
      SPComp.map (fun l =>
        (({ l.2 with st := corruptStep l.2.st pid }, s.2.1, .out (.secret (some l.1))),
          .inl (.inr (.corrupt pid)))) (ltStep s.1 pid)
  | .inr (.complete _ _) => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | .inr (.send _ _ _) => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | .inr (.kdf x) => SPComp.map (fun p =>
      (({ s.1 with ro := p.2 }, s.2.1, .fwd), .inr (.inr (.hash p.1))))
      (sroStep G O (keyA G a X s.1) (keyB G b Y s.1) s.1.ro (ofInp x))

/-- A step of `F_AKE` with a uniform fresh key, as a computation. -/
noncomputable def fakeC (t : St K) (g : FEv K) : SPComp (St K × FOut K) :=
  SPComp.map (fStepD t g) (SPComp.sample K)

/-- The finish of a step of the world of the reduction as a computation: the decision of the
start is passed to `F_AKE` with a uniform fresh key, and its answer to `finR`. -/
noncomputable def finishC (p : RSim S W K × Dec S W K) (t : St K) :
    SPComp ((RSim S W K × St K) × OOut S W K) :=
  match p.2 with
  | .inr o => SPComp.pure ((p.1, t), o)
  | .inl g => SPComp.map (fun q => (((finR p.1 q.2).1, q.1), (finR p.1 q.2).2)) (fakeC t g)

/-- The extraction of the reduction as a computation. -/
noncomputable def extractC (rs : RSt S (W ⊕ W) K) : SPComp W :=
  SPComp.pure (extractR G a b O X Y rs)

end Prog

derive_reduction cguardC
derive_reduction sguardC
derive_reduction ltC
derive_reduction deliverC
derive_reduction otherC
derive_reduction fakeC
derive_reduction finishC
derive_reduction extractC

section Lookup

variable {S W K : Type} [Field S] [SampleableType W] (G : DHGroup S W)

/-- **The cost of the symbolic lookup** is linear in the length of the table. -/
theorem slookup.timedCost_le (O : W → W → W → Bool) (OCost : W → W → W → ℕ) (ZA ZB : W)
    (j : Inp (W ⊕ W)) (tb : List (Inp (W ⊕ W) × K)) (mulCost : W → W → ℕ)
    (expCost : W → S → ℕ) (toFunCost : S → ℕ) {tO tm te tf : ℕ}
    (hO : ∀ x y z, OCost x y z ≤ tO) (hm : ∀ x y, mulCost x y ≤ tm)
    (he : ∀ x y, expCost x y ≤ te) (hf : ∀ x, toFunCost x ≤ tf) :
    slookup.timedCost G O OCost ZA ZB j tb mulCost expCost toFunCost ≤
      (3 * (tO + tm + te + tf) + 60) * tb.length + 1 := by
  induction tb with
  | nil => simp [slookup.timedCost]
  | cons p tb ih =>
    simp only [slookup.timedCost]
    simp only [List.length_cons, Nat.mul_succ]
    repeat' split
    all_goals grind

end Lookup

/-! ## The costed reduction -/

/-- The costed copy of the real state in the world of the reduction. -/
abbrev RHatR (S W K : Type) : Type :=
  (((Inst → Option (Rec K)) × (Inst → ℕ)) × ((PartyId → Bool) × (PartyId → ℕ)) ×
      List Notice × ℕ) × ((PartyId → Option (S × S)) × (PartyId → ℕ)) ×
      ((Inst → Option S) × (Inst → ℕ)) × List (Inp (W ⊕ W) × K)

/-- The costed state of the simulator of the reduction: its tables with their cost companions. -/
abbrev RSimHat (S W K : Type) : Type :=
  ((((Inst → Option (Rec K)) × (Inst → ℕ)) × ((PartyId → Bool) × (PartyId → ℕ)) ×
      List Notice × ℕ) × ((PartyId → Option (S × S)) × (PartyId → ℕ)) ×
      ((Inst → Option S) × (Inst → ℕ)) × List (Inp (W ⊕ W) × K)) ×
    ((Inst → Option (Inp (W ⊕ W))) × (Inst → ℕ)) × Phase S W K

/-- A state of the simulator of the reduction with its tables read at unit cost: every cost
companion is zero. -/
def liftR {S W K : Type} (s : RSim S W K) : RSimHat S W K :=
  ((((s.1.st.recs, fun _ => 0), (s.1.st.corrupt, fun _ => 0), s.1.st.notices, s.1.st.cursor),
    (s.1.lt, fun _ => 0), (s.1.eph, fun _ => 0), s.1.ro), (s.2.1, fun _ => 0), s.2.2)

/-- The records and corruptions of a state read at unit cost. -/
def liftSt {K : Type} (t : St K) :
    ((Inst → Option (Rec K)) × (Inst → ℕ)) × ((PartyId → Bool) × (PartyId → ℕ)) × List Notice × ℕ :=
  ((t.recs, fun _ => 0), (t.corrupt, fun _ => 0), t.notices, t.cursor)

section Costed

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W) (a b : PartyId) (O : W → W → W → Bool)
  (OCost : W → W → W → ℕ) (X Y : W) (coeCost : S ≃ W → S → ℕ) (mulCost : W → W → ℕ)
  (toFunCost : S → ℕ) (expCost : W → S → ℕ)

/-- The time of drawing the long-term secrets of `pid`: the costed tree of `ltC` with the tables
read at unit cost. -/
noncomputable def ltTime (rs : RSt S (W ⊕ W) K) (pid : PartyId) : ℕ :=
  SPTree.Timed.stepTime (ltC.tree.timed rs pid rs.lt (fun _ => 0) rs.eph (fun _ => 0)
    (liftSt rs.st) (fun _ => 0) (fun _ => 0))

/-- The time of a delivery: the costed tree of `deliverC` with the tables read at unit cost. -/
noncomputable def delTime (rs : RSt S (W ⊕ W) K) (inp : Inst → Option (Inp (W ⊕ W))) (x : Inst)
    (r : Rec K) (ip : Inp (W ⊕ W)) : ℕ :=
  SPTree.Timed.stepTime (deliverC.tree.timed G a b O OCost X Y rs inp (fun _ => 0) x r ip mulCost
    toFunCost (fun _ => 0) expCost (liftSt rs.st) (fun _ => 0))

/-- The time of `complete` with the draw `r`: the guard, the two draws of long-term secrets, and
the delivery, each on the state it reads. -/
noncomputable def completeTime (s : RSim S W K) (sid : SessionId) (pid : PartyId)
    (r : Draw S K) : ℕ :=
  SPTree.Timed.stepTime (cguardC.tree.timed (liftR s) sid pid (fun _ => 0) (fun _ => 0)) +
    match cguard s sid pid with
    | some (rc, ek, opk) => ltTime s.1 pid + ltTime (ltD s.1 pid r.2.1).2 rc.peer +
        delTime G a b O OCost X Y mulCost toFunCost expCost
          (ltD (ltD s.1 pid r.2.1).2 rc.peer r.2.2.1).2 s.2.1 (sid, pid) rc
          (aliceS G a b X Y sid pid rc.peer (ltD s.1 pid r.2.1).1
            (ltD (ltD s.1 pid r.2.1).2 rc.peer r.2.2.1).1 ek opk)
    | none => 0

/-- The time of `send` on the ephemeral key `e` with the draw `r`. -/
noncomputable def sendTime (s : RSim S W K) (sid : SessionId) (pid : PartyId) (e : W)
    (r : Draw S K) : ℕ :=
  SPTree.Timed.stepTime (sguardC.tree.timed (liftR s) sid pid (fun _ => 0) (fun _ => 0)) +
    match sguard s sid pid with
    | some (rc, opk) => ltTime s.1 pid + ltTime (ltD s.1 pid r.2.1).2 rc.peer +
        delTime G a b O OCost X Y mulCost toFunCost expCost
          (ltD (ltD s.1 pid r.2.1).2 rc.peer r.2.2.1).2 s.2.1 (sid, pid) rc
          (bobS G a b X Y sid rc.peer pid e (ltD s.1 pid r.2.1).1
            (ltD (ltD s.1 pid r.2.1).2 rc.peer r.2.2.1).1 opk)
    | none => 0

/-- **The time of the start** of the simulator of the reduction on the event `e` with the draw
`r`: one unit for the dispatch on the event, and the time of `complete`, of `send` or of the
costed tree of `otherC`. -/
noncomputable def startTime (s : RSim S W K) (e : OEv W) (r : Draw S K) : ℕ :=
  1 + match e with
    | .inr (.complete sid pid) =>
      completeTime G a b O OCost X Y mulCost toFunCost expCost s sid pid r
    | .inr (.send sid pid e') =>
      sendTime G a b O OCost X Y mulCost toFunCost expCost s sid pid e' r
    | e => SPTree.Timed.stepTime (otherC.tree.timed G a b O OCost X Y (liftR s) e s.1.lt
        (fun _ => 0) s.1.eph (fun _ => 0) s.1.st.recs (fun _ => 0) s.2.1 (fun _ => 0)
        DFunLike.coe coeCost mulCost toFunCost expCost)

/-- The time of the finish of a step: the costed tree of `finishC`. -/
noncomputable def finTime (p : RSim S W K × Dec S W K) (t : St K) : ℕ :=
  SPTree.Timed.stepTime (finishC.tree.timed (liftR p.1, p.2) t (fun _ => 0) (fun _ => 0))

/-- **The time of a step** of the world of the reduction with the draw `r`: the time of the
start and the time of the finish at the decision of the start. -/
noncomputable def stepTime (t : RSim S W K × St K) (e : OEv W) (r : Draw S K × K) : ℕ :=
  startTime G a b O OCost X Y coeCost mulCost toFunCost expCost t.1 e r.1 +
    finTime (startR G a b O X Y t.1 e r.1) t.2

/-- The time of the extraction: the costed tree of `extractC`. -/
noncomputable def extTime (rs : RSt S (W ⊕ W) K) : ℕ :=
  SPTree.Timed.stepTime (extractC.tree.timed G a b O OCost X Y rs mulCost toFunCost (fun _ => 0)
    expCost)

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem extTime_le (rs : RSt S (W ⊕ W) K) {tO tm tf te : ℕ} (hO : ∀ x y z, OCost x y z ≤ tO)
    (hm : ∀ x y, mulCost x y ≤ tm) (hf : ∀ x, toFunCost x ≤ tf) (he : ∀ x y, expCost x y ≤ te) :
    extTime G a b O OCost X Y mulCost toFunCost expCost rs ≤
      100 + 4 * tm + 3 * te + 3 * tf + (tO + 2 * tm + 2 * tf + 40) * rs.ro.length := by
  unfold extTime
  simp only [extractC.tree.timed, SPTree.Timed.stepTime, SPTree.Timed.time_ret]
  have hF : ∀ (f : Inp (W ⊕ W) × K → Option W) (fc : Inp (W ⊕ W) × K → ℕ),
      (∀ p, fc p ≤ tO + 2 * tm + 2 * tf + 36) →
        List.findSome?.timedCost f fc rs.ro ≤ (tO + 2 * tm + 2 * tf + 40) * rs.ro.length + 1 :=
    fun f fc h => List.findSome?.timedCost_le f fc h rs.ro
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_right
    (Nat.add_le_add_left (hF _ _ fun p => ?_) _) _) _) _) ?_
  · split_ifs
    · split
      · have := hO (keyA G a X rs) (keyB G b Y rs) ‹_›
        have := hm X (G.pub (off1 a rs))
        have := hm Y (G.pub (off2 b rs))
        have := hf (off1 a rs)
        have := hf (off2 b rs)
        omega
      · omega
    · omega
  · split
    · have := hm ‹_› (G.exp (G.mul (G.mul (G.exp X (off2 b rs)) (G.exp Y (off1 a rs)))
        (G.pub (off1 a rs * off2 b rs))) (-1))
      have := he (G.mul (G.mul (G.exp X (off2 b rs)) (G.exp Y (off1 a rs)))
        (G.pub (off1 a rs * off2 b rs))) (-1)
      have := hm (G.mul (G.exp X (off2 b rs)) (G.exp Y (off1 a rs))) (G.pub (off1 a rs * off2 b rs))
      have := hm (G.exp X (off2 b rs)) (G.exp Y (off1 a rs))
      have := he X (off2 b rs)
      have := he Y (off1 a rs)
      have := hf (off1 a rs * off2 b rs)
      omega
    · have := hf 0
      omega

omit [Inhabited K] in
theorem otherC_time (s : RSim S W K) (e : OEv W) {tO tm tf te tc : ℕ}
    (hO : ∀ x y z, OCost x y z ≤ tO) (hm : ∀ x y, mulCost x y ≤ tm) (hf : ∀ x, toFunCost x ≤ tf)
    (he : ∀ x y, expCost x y ≤ te) (hc : ∀ x y, coeCost x y ≤ tc) :
    SPTree.Timed.stepTime (otherC.tree.timed G a b O OCost X Y (liftR s) e s.1.lt (fun _ => 0)
        s.1.eph (fun _ => 0) s.1.st.recs (fun _ => 0) s.2.1 (fun _ => 0) DFunLike.coe coeCost
        mulCost toFunCost expCost) ≤
      200 + 10 * (tO + tm + te + tf + tc) + (3 * (tO + tm + te + tf) + 60) * s.1.ro.length +
        10 * s.1.st.notices.length := by
  time_bound

omit [Field S] [Fintype S] [SampleableType W] [Inhabited K] in
theorem finishC_time (p : RSim S W K × Dec S W K) (t : St K) :
    SPTree.Timed.stepTime (finishC.tree.timed (liftR p.1, p.2) t (fun _ => 0) (fun _ => 0)) ≤
      100 + 10 * t.notices.length := by
  time_bound

omit [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem ltTime_le (rs : RSt S (W ⊕ W) K) (pid : PartyId) : ltTime rs pid ≤ 4 := by
  unfold ltTime
  time_bound

omit [Fintype S] in
theorem delTime_le (rs : RSt S (W ⊕ W) K) (inp : Inst → Option (Inp (W ⊕ W))) (x : Inst)
    (r : Rec K) (ip : Inp (W ⊕ W)) {tO tm tf te : ℕ}
    (hO : ∀ x y z, OCost x y z ≤ tO) (hm : ∀ x y, mulCost x y ≤ tm) (hf : ∀ x, toFunCost x ≤ tf)
    (he : ∀ x y, expCost x y ≤ te) :
    delTime G a b O OCost X Y mulCost toFunCost expCost rs inp x r ip ≤
      200 + 20 * (tO + tm + te + tf) + (3 * (tO + tm + te + tf) + 60) * rs.ro.length := by
  unfold delTime
  time_bound

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem cguard_time (s : RSim S W K) (sid : SessionId) (pid : PartyId) :
    SPTree.Timed.stepTime (cguardC.tree.timed (liftR s) sid pid (fun _ => 0) (fun _ => 0)) ≤ 20 := by
  time_bound

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem sguard_time (s : RSim S W K) (sid : SessionId) (pid : PartyId) :
    SPTree.Timed.stepTime (sguardC.tree.timed (liftR s) sid pid (fun _ => 0) (fun _ => 0)) ≤ 20 := by
  time_bound

end Costed

/-! ## The step programs compute the step of the reduction -/

section Correct

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W) (a b : PartyId) (O : W → W → W → Bool) (X Y : W)

omit [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- `ltC` draws the long-term secrets of `ltD` uniformly. -/
theorem ltC_eq (rs : RSt S (W ⊕ W) K) (pid : PartyId) :
    ltC rs pid = liftPMF ((PMF.uniformFintype (S × S)).map (ltD rs pid)) := by
  rw [ltC, ltStep_eq, ltAt_eq_map]

omit [Fintype S] [Inhabited K] in
/-- `sroStep` draws the fresh value of `sroDet` uniformly. -/
theorem sroStep_eq (ZA ZB : W) (tb : List (Inp (W ⊕ W) × K)) (j : Inp (W ⊕ W)) :
    sroStep G O ZA ZB tb j = liftPMF ((PMF.uniformFintype K).map (sroDet G O ZA ZB tb j)) := by
  unfold sroStep sroDet
  cases h : slookup G O ZA ZB j tb with
  | some v =>
    simp only [liftPMF_pure]
    exact congrArg liftPMF (PMF.map_const _ _).symm
  | none =>
    simp only [sample_eq_liftPMF, map_liftPMF]

omit [Fintype S] in
/-- `deliverC` draws the fresh value of `deliverR` uniformly. -/
theorem deliverC_eq (rs : RSt S (W ⊕ W) K) (inp : Inst → Option (Inp (W ⊕ W))) (x : Inst)
    (r : Rec K) (ip : Inp (W ⊕ W)) :
    deliverC G a b O X Y rs inp x r ip =
      liftPMF ((PMF.uniformFintype K).map (deliverR G a b O X Y rs inp x r ip)) := by
  change _ = liftPMF ((PMF.uniformFintype K).map fun k => deliverR G a b O X Y rs inp x r ip k)
  by_cases h : Exposed rs.st x r
  · simp only [deliverC, h, ↓reduceIte, sroStep_eq, map_liftPMF, PMF.map_comp]
    congr 2
    funext k
    simp only [deliverR, h, ↓reduceIte, Function.comp_apply]
  · simp only [deliverC, h, ↓reduceIte, liftPMF_pure]
    congr 1
    rw [← PMF.map_const (PMF.uniformFintype K)]
    congr 1
    funext k
    simp only [deliverR, h, ↓reduceIte, Function.const_apply]

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- **`complete` through its guard**: `completeR` is the delivery at the input of the initiator
after the two draws of long-term secrets, when the guard `cguard` holds. -/
theorem completeR_eq (s : RSim S W K) (sid : SessionId) (pid : PartyId) (r : Draw S K) :
    completeR G a b O X Y s (sid, pid) r =
      match cguard s sid pid with
      | some (rc, ek, opk) =>
        deliverR G a b O X Y (ltD (ltD s.1 pid r.2.1).2 rc.peer r.2.2.1).2 s.2.1 (sid, pid) rc
          (aliceS G a b X Y sid pid rc.peer (ltD s.1 pid r.2.1).1
            (ltD (ltD s.1 pid r.2.1).2 rc.peer r.2.2.1).1 ek opk) r.2.2.2
      | none => ((s.1, s.2.1, .fwd), .inr (.inr .ack)) := by
  unfold completeR cguard
  cases hr : s.1.st.recs (sid, pid) with
  | none => rfl
  | some rc =>
    cases he : s.1.eph (sid, pid) with
    | none => rfl
    | some ek =>
      dsimp only
      cases ho : opkOf s.1 sid rc.peer with
      | none => rfl
      | some opk =>
        by_cases hc : rc.role = .initiator ∧ rc.key.isNone = true
        · simp only [hc, and_self, ↓reduceIte]
        · simp only [hc, ↓reduceIte]

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- **`send` through its guard.** -/
theorem sendR_eq (s : RSim S W K) (sid : SessionId) (pid : PartyId) (e : W) (r : Draw S K) :
    sendR G a b O X Y s (sid, pid) e r =
      match sguard s sid pid with
      | some (rc, opk) =>
        deliverR G a b O X Y (ltD (ltD s.1 pid r.2.1).2 rc.peer r.2.2.1).2 s.2.1 (sid, pid) rc
          (bobS G a b X Y sid rc.peer pid e (ltD s.1 pid r.2.1).1
            (ltD (ltD s.1 pid r.2.1).2 rc.peer r.2.2.1).1 opk) r.2.2.2
      | none => ((s.1, s.2.1, .fwd), .inr (.inr .ack)) := by
  unfold sendR sguard
  cases hr : s.1.st.recs (sid, pid) with
  | none => rfl
  | some rc =>
    cases he : s.1.eph (sid, pid) with
    | none => rfl
    | some opk =>
      by_cases hc : rc.role = .responder ∧ rc.key.isNone = true
      · simp only [hc, and_self, ↓reduceIte]
      · simp only [hc, ↓reduceIte]

/-- **`otherC` computes `startR`** on the events other than `complete` and `send`, with the draw
uniform. -/
theorem otherC_eq (s : RSim S W K) (e : OEv W)
    (hc : ∀ sid pid, e ≠ .inr (.complete sid pid)) (hs : ∀ sid pid E, e ≠ .inr (.send sid pid E)) :
    otherC G a b O X Y s e =
      liftPMF ((PMF.uniformFintype (Draw S K)).map (startR G a b O X Y s e)) := by
  have hP : ∀ p : RSim S W K × Dec S W K,
      (SPComp.pure p : SPComp _) = liftPMF ((PMF.uniformFintype (Draw S K)).map fun _ => p) :=
    fun p => by rw [liftPMF_pure]; exact congrArg liftPMF (PMF.map_const _ _).symm
  change _ = liftPMF ((PMF.uniformFintype (Draw S K)).map fun r => startR G a b O X Y s e r)
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ | pid |
    ⟨sid, pid⟩ | ⟨sid, pid, E⟩ | q)
  · by_cases h : (s.1.st.recs (sid, pid)).isNone = true
    · simp only [otherC, h, ↓reduceIte, sample_eq_liftPMF, map_liftPMF]
      rw [map_uniform_eq_map_prod_fst (B := (S × S) × (S × S) × K)]
      congr 2
      funext r
      simp only [startR, h, ↓reduceIte]
    · simp only [otherC, h, Bool.false_eq_true, ↓reduceIte, hP]
      congr 3
      funext r
      simp only [startR, h, Bool.false_eq_true, ↓reduceIte]
  · simp only [otherC, hP]
    rfl
  · simp only [otherC, hP]
    rfl
  · simp only [otherC, hP]
    rfl
  · simp only [otherC, ltStep_eq, map_liftPMF]
    exact congrArg liftPMF (ltAt_map_eq s.1 pid _)
  · simp only [otherC, hP]
    rfl
  · by_cases h : Named s.1.st pid = true
    · simp only [otherC, h, ↓reduceIte, hP]
      congr 3
      funext r
      simp only [startR, h, ↓reduceIte]
    · simp only [otherC, h, Bool.false_eq_true, ↓reduceIte, ltStep_eq, map_liftPMF]
      refine congrArg liftPMF ((ltAt_map_eq s.1 pid _).trans ?_)
      congr 1
      funext r
      simp only [startR, h, Bool.false_eq_true, ↓reduceIte]
  · exact absurd rfl (hc sid pid)
  · exact absurd rfl (hs sid pid E)
  · simp only [otherC, sroStep_eq, map_liftPMF, PMF.map_comp]
    rw [map_uniform_eq_map_prod_snd (A := S × S), map_uniform_eq_map_prod_snd (A := S × S),
      map_uniform_eq_map_prod_snd (A := S)]
    rfl

omit [Field S] [Fintype S] [SampleableType W] [Inhabited K] in
/-- **`finishC` computes the finish of a step**, `F_AKE` with a uniform fresh key and `finR`,
as in `stepR`. -/
theorem finishC_eq (p : RSim S W K × Dec S W K) (t : St K) :
    finishC p t = liftPMF ((PMF.uniformFintype K).map fun kf =>
      (((drive0D fStepD finR p.1 p.2 t kf).1, (drive0D fStepD finR p.1 p.2 t kf).2.1),
        (drive0D fStepD finR p.1 p.2 t kf).2.2)) := by
  obtain ⟨s, d⟩ := p
  rcases d with g | o
  · simp only [finishC, fakeC, sample_eq_liftPMF, map_liftPMF, PMF.map_comp]
    rfl
  · simp only [finishC, liftPMF_pure]
    exact congrArg liftPMF (PMF.map_const _ _).symm

end Correct

/-! ## The sizes of the state -/

section Size

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W) (a b : PartyId) (O : W → W → W → Bool) (X Y : W)

/-- The sizes of a state of the world of the reduction after `i` steps: the table and the two
lists of notices have at most `i` entries. -/
def Sz (i : ℕ) (t : RSim S W K × St K) : Prop :=
  t.1.1.ro.length ≤ i ∧ t.1.1.st.notices.length ≤ i ∧ t.2.notices.length ≤ i

omit [Fintype S] [Fintype K] [Nonempty K] [Inhabited K] in
theorem sroDet_length (ZA ZB : W) (tb : List (Inp (W ⊕ W) × K)) (j : Inp (W ⊕ W)) (k : K) :
    (sroDet G O ZA ZB tb j k).2.length ≤ tb.length + 1 := by
  rcases sroDet_snd G O ZA ZB tb j k with h | h <;> rw [h] <;> simp

omit [Fintype K] [Nonempty K] [Inhabited K] in
theorem addSession_notices (t : St K) (z : Inst) (peer : PartyId) (role : Role) :
    (addSession t z peer role).notices.length ≤ t.notices.length + 1 := by
  unfold addSession
  split <;> simp

omit [Fintype S] [Fintype K] [Nonempty K] in
theorem deliverR_len (rs : RSt S (W ⊕ W) K) (inp : Inst → Option (Inp (W ⊕ W))) (z : Inst)
    (rc : Rec K) (ip : Inp (W ⊕ W)) (k : K) :
    (deliverR G a b O X Y rs inp z rc ip k).1.1.ro.length ≤ rs.ro.length + 1 ∧
      (deliverR G a b O X Y rs inp z rc ip k).1.1.st.notices.length ≤ rs.st.notices.length := by
  unfold deliverR
  split
  · exact ⟨sroDet_length G O _ _ _ _ _, le_rfl⟩
  · exact ⟨Nat.le_succ _, le_rfl⟩

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- **A start of the simulator of the reduction adds at most one entry** to the table and to the
notices. -/
theorem startR_len (s : RSim S W K) (e : OEv W) (r : Draw S K) :
    (startR G a b O X Y s e r).1.1.ro.length ≤ s.1.ro.length + 1 ∧
      (startR G a b O X Y s e r).1.1.st.notices.length ≤ s.1.st.notices.length + 1 := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ | pid |
    ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | q)
  · simp only [startR]
    split
    · exact ⟨Nat.le_succ _, addSession_notices _ _ _ _⟩
    · exact ⟨Nat.le_succ _, Nat.le_succ _⟩
  · exact ⟨Nat.le_succ _, Nat.le_succ _⟩
  · exact ⟨Nat.le_succ _, Nat.le_succ _⟩
  · simp only [startR, (pollStep_fst _).2.2]
    exact ⟨Nat.le_succ _, Nat.le_succ _⟩
  · simp only [startR, ltD_ro, ltD_st]
    exact ⟨Nat.le_succ _, Nat.le_succ _⟩
  · exact ⟨Nat.le_succ _, Nat.le_succ _⟩
  · simp only [startR]
    split
    · exact ⟨Nat.le_succ _, Nat.le_succ _⟩
    · simp only [corruptStep, ltD_ro, ltD_st]
      exact ⟨Nat.le_succ _, Nat.le_succ _⟩
  · simp only [startR, completeR]
    repeat' split
    all_goals first
      | exact ⟨Nat.le_succ _, Nat.le_succ _⟩
      | refine ⟨(deliverR_len G a b O X Y _ _ _ _ _ _).1.trans ?_,
          (deliverR_len G a b O X Y _ _ _ _ _ _).2.trans ?_⟩ <;> simp only [ltD_ro, ltD_st] <;> omega
  · simp only [startR, sendR]
    repeat' split
    all_goals first
      | exact ⟨Nat.le_succ _, Nat.le_succ _⟩
      | refine ⟨(deliverR_len G a b O X Y _ _ _ _ _ _).1.trans ?_,
          (deliverR_len G a b O X Y _ _ _ _ _ _).2.trans ?_⟩ <;> simp only [ltD_ro, ltD_st] <;> omega
  · simp only [startR]
    exact ⟨sroDet_length G O _ _ _ _ _, Nat.le_succ _⟩

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- A step of `F_AKE` adds at most one notice. -/
theorem fStepD_len (t : St K) (g : FEv K) (kf : K) :
    (fStepD t g kf).1.notices.length ≤ t.notices.length + 1 := by
  rcases g with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ | ⟨sid, pid, k⟩ |
    ⟨sid, pid, k⟩)
  · exact addSession_notices _ _ _ _
  · exact Nat.le_succ _
  · exact Nat.le_succ _
  · simp only [fStepD, advD, (pollStep_fst _).2.2]
    exact Nat.le_succ _
  · exact Nat.le_succ _
  · exact Nat.le_succ _
  · simp only [fStepD, advD, newKeyStep]
    repeat' split
    all_goals exact Nat.le_succ _
  · simp only [fStepD, advD, newKeyFreshStep]
    repeat' split
    all_goals exact Nat.le_succ _

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- **A step of the world of the reduction keeps the sizes** after one more step. -/
theorem sz_stepR {i : ℕ} {t : RSim S W K × St K} (h : Sz i t) (e : OEv W) (r : Draw S K × K) :
    Sz (i + 1) (stepR G a b O X Y t e r).1 := by
  obtain ⟨hs1, hs2⟩ := startR_len G a b O X Y t.1 e r.1
  obtain ⟨h1, h2, h3⟩ := h
  simp only [Sz, stepR]
  rw [stop_drive0D _ _ (fun _ _ => rfl)]
  refine ⟨by omega, by omega, ?_⟩
  unfold drive0D
  split
  · dsimp only
    omega
  · have := fStepD_len t.2 ‹_› r.2
    dsimp only
    omega

end Size

/-! ## The time of the reduction -/

section Time

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W) (a b : PartyId) (O : W → W → W → Bool)
  (OCost : W → W → W → ℕ) (X Y : W) (coeCost : S ≃ W → S → ℕ) (mulCost : W → W → ℕ)
  (toFunCost : S → ℕ) (expCost : W → S → ℕ)

/-- The bound of a step after `i` steps, for primitive costs at most `tO` (decision oracle),
`tm` (group operation), `te` (exponentiation), `tf` and `tc` (public value of an exponent). -/
def stepBound (tO tm te tf tc i : ℕ) : ℕ :=
  1000 + 50 * (tO + tm + te + tf + tc) + (3 * (tO + tm + te + tf) + 60) * i + 20 * i

/-- The bound of the extraction after `i` steps. -/
def extBound (tO tm te tf i : ℕ) : ℕ :=
  100 + 4 * tm + 3 * te + 3 * tf + (tO + 2 * tm + 2 * tf + 40) * i

/-- **The time of a step** of the world of the reduction after `i` steps is less than
`stepBound … i`; the unit left over is the evaluation of the draw distribution. -/
theorem stepTime_lt {i : ℕ} {t : RSim S W K × St K} (hsz : Sz i t) (e : OEv W)
    (r : Draw S K × K) {tO tm tf te tc : ℕ}
    (hO : ∀ x y z, OCost x y z ≤ tO) (hm : ∀ x y, mulCost x y ≤ tm) (hf : ∀ x, toFunCost x ≤ tf)
    (he : ∀ x y, expCost x y ≤ te) (hc : ∀ x y, coeCost x y ≤ tc) :
    stepTime G a b O OCost X Y coeCost mulCost toFunCost expCost t e r <
      stepBound tO tm te tf tc i := by
  obtain ⟨h1, h2, h3⟩ := hsz
  have hfin := finishC_time (startR G a b O X Y t.1 e r.1) t.2
  have hL : (3 * (tO + tm + te + tf) + 60) * t.1.1.ro.length ≤
      (3 * (tO + tm + te + tf) + 60) * i := Nat.mul_le_mul_left _ h1
  have hdel : ∀ (rs : RSt S (W ⊕ W) K) (inp : Inst → Option (Inp (W ⊕ W))) (z : Inst)
      (rc : Rec K) (ip : Inp (W ⊕ W)),
      delTime G a b O OCost X Y mulCost toFunCost expCost rs inp z rc ip ≤
        200 + 20 * (tO + tm + te + tf) + (3 * (tO + tm + te + tf) + 60) * rs.ro.length :=
    fun rs inp z rc ip => delTime_le G a b O OCost X Y mulCost toFunCost expCost rs inp z rc ip
      hO hm hf he
  unfold stepTime finTime stepBound
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ | pid |
    ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | q)
  rotate_left 7
  · simp only [startTime, completeTime]
    have := cguard_time t.1 sid pid
    split
    · rename_i rc ek opk _
      have := ltTime_le t.1.1 pid
      have := ltTime_le (ltD t.1.1 pid r.1.2.1).2 rc.peer
      refine lt_of_le_of_lt (Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_left
        (Nat.add_le_add_left (hdel _ _ _ _ _) _) _) _) _) ?_
      simp only [ltD_ro]
      generalize (3 * (tO + tm + te + tf) + 60) * t.1.1.ro.length = P₁ at hL ⊢
      generalize (3 * (tO + tm + te + tf) + 60) * i = P₂ at hL ⊢
      omega
    · omega
  · simp only [startTime, sendTime]
    have := sguard_time t.1 sid pid
    split
    · rename_i rc opk _
      have := ltTime_le t.1.1 pid
      have := ltTime_le (ltD t.1.1 pid r.1.2.1).2 rc.peer
      refine lt_of_le_of_lt (Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_left
        (Nat.add_le_add_left (hdel _ _ _ _ _) _) _) _) _) ?_
      simp only [ltD_ro]
      generalize (3 * (tO + tm + te + tf) + 60) * t.1.1.ro.length = P₁ at hL ⊢
      generalize (3 * (tO + tm + te + tf) + 60) * i = P₂ at hL ⊢
      omega
    · omega
  all_goals
    simp only [startTime]
    refine lt_of_le_of_lt (Nat.add_le_add_right (Nat.add_le_add_left
      (otherC_time G a b O OCost X Y coeCost mulCost toFunCost expCost t.1 _ hO hm hf he hc) _) _) ?_
    generalize (3 * (tO + tm + te + tf) + 60) * t.1.1.ro.length = P₁ at hL ⊢
    generalize (3 * (tO + tm + te + tf) + 60) * i = P₂ at hL ⊢
    omega

theorem stepBound_mono (tO tm te tf tc : ℕ) {i j : ℕ} (h : i ≤ j) :
    stepBound tO tm te tf tc i ≤ stepBound tO tm te tf tc j := by
  unfold stepBound
  have := Nat.mul_le_mul_left (3 * (tO + tm + te + tf) + 60) h
  omega

theorem extBound_mono (tO tm te tf : ℕ) {i j : ℕ} (h : i ≤ j) :
    extBound tO tm te tf i ≤ extBound tO tm te tf j := by
  unfold extBound
  have := Nat.mul_le_mul_left (tO + 2 * tm + 2 * tf + 40) h
  omega

end Time

/-! ## The derived costed reduction -/

derive_timed stepRedD

section Generic

variable {σ E A V Out : Type}

/-- **The time of `stepRedD`.** Let `Inv i` hold of the states reached after `i` steps, with the
cost of the draw distribution and of a step from a state of `Inv i` together at most `F i` (`F`
monotone) and an extraction from a state of `Inv i` of cost at most `Ext i`. Then a costed
adversary `B` of time `T` with at most `q` queries gives a costed reduction of time at most
`T + q · (F q + 3) + Ext q + 1`: per query the draw distribution, one `rand` node and the step,
and at the end the extraction. -/
theorem stepRedD.timeBound_timed (μ : σ → E → PMF V) (μCost : σ → E → ℕ)
    (step : σ → E → V → σ × A) (stepCost : σ → E → V → ℕ) (ext : σ → Out) (extCost : σ → ℕ)
    (Inv : ℕ → σ → Prop) (F Ext : ℕ → ℕ) (hF : Monotone F)
    (hmono : ∀ i t, Inv i t → Inv (i + 1) t)
    (hstep : ∀ i t e r, Inv i t → Inv (i + 1) (step t e r).1)
    (hcost : ∀ i t e r, Inv i t → μCost t e + stepCost t e r ≤ F i)
    (hext : ∀ i t, Inv i t → extCost t ≤ Ext i)
    (B : OracleAdv.Timed E A Bool) {T q : ℕ} (hB : B.TimeBound T) (hq : B.erase.IsQueryBound q)
    (s₀ : σ) (h0 : Inv 0 s₀) :
    OracleAdv.Timed.StepTimeBound (stepRedD.timed μ μCost step stepCost ext extCost B s₀)
      (T + q * (F q + 3) + (Ext q + 1)) := by
  unfold stepRedD.timed
  generalize hI : (fun (t : σ) (e : E) => (1 + μCost t e, OracleAdv.Timed.rand (μ t e)
    (fun r => 1 + stepCost t e r) fun r =>
      have p := step t e r; OracleAdv.Timed.ret (p.2, p.1))) = impl
  have himpl : ∀ i s d, Inv i s →
      OracleAdv.Timed.StepTimeBound (impl s d) (F i + 3) ∧
        OracleAdv.Timed.AllRet (fun y => Inv (i + 1) y.2) (impl s d).2 := by
    intro i s d hs
    subst hI
    beta_reduce
    have hr : ∀ r, μCost s d + stepCost s d r ≤ F i := fun r => hcost i s d r hs
    obtain ⟨r₀, -⟩ := (μ s d).support_nonempty
    have := hr r₀
    refine ⟨⟨by omega, by dsimp only; omega, fun r => ⟨?_, trivial⟩⟩,
      fun r => hstep i s d r hs⟩
    have := hr r
    dsimp only
    omega
  have hsim := OracleAdv.Timed.timeBound_simulateHat_inv id id impl Inv (fun i => F i + 3) himpl
    hB hq 0 s₀ h0
  have hall := OracleAdv.Timed.allRet_simulateHat_inv id id impl Inv (fun i s d h => (himpl i s d h).2)
    hmono hq 0 s₀ h0
  unfold OracleAdv.Timed.simulateHat at hsim hall
  simp only [Nat.zero_add] at hsim hall
  have hsum : ∑ j ∈ Finset.range q, (F j + 3) ≤ q * (F q + 3) := by
    calc ∑ j ∈ Finset.range q, (F j + 3) ≤ ∑ _j ∈ Finset.range q, (F q + 3) :=
          Finset.sum_le_sum fun j hj => by
            have := hF (le_of_lt (Finset.mem_range.mp hj)); omega
      _ = q * (F q + 3) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hbind := OracleAdv.Timed.timeBound_bind_of_allRet (n := Ext q + 1)
    (f := fun p => (1 + extCost p.2, OracleAdv.Timed.ret (ext p.2))) hsim.2 hall
    fun y hy => ⟨by have := hext q y.2 hy; dsimp only; omega, trivial⟩
  refine (OracleAdv.Timed.stepTimeBound_delay hbind).mono ?_
  have := hsim.1
  omega

end Generic

section Instance

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W) (a b : PartyId) (O : W → W → W → Bool)
  (OCost : W → W → W → ℕ) (X Y : W) (coeCost : S ≃ W → S → ℕ) (mulCost : W → W → ℕ)
  (toFunCost : S → ℕ) (expCost : W → S → ℕ)

/-- **Erasure of the costed reduction of the X3DH square**: the derived costed form of `stepRedD`
at the uniform draw of `Draw S K × K`, of cost zero, the step `stepR`, of cost `stepTime`, and the
extraction `extractR`, of cost `extTime`, erases to the program whose output distribution is
`gdhOut`, the output of `gdhRed G a b`. -/
theorem gdhOut_erase_timed (B : OracleAdv.Timed (OEv W) (OOut S W K) Bool) :
    (stepRedD.timed (fun _ _ => PMF.uniformFintype (Draw S K × K)) (fun _ _ => 0)
        (stepR G a b O X Y) (stepTime G a b O OCost X Y coeCost mulCost toFunCost expCost)
        (fun t => extractR G a b O X Y t.1.1)
        (fun t => extTime G a b O OCost X Y mulCost toFunCost expCost t.1.1) B rInitR).2.erase =
      stepRedD (fun _ _ => PMF.uniformFintype (Draw S K × K)) (stepR G a b O X Y)
        (fun t => extractR G a b O X Y t.1.1) B.erase rInitR :=
  stepRedD.erase_timed _ _ _ _ _ _ B rInitR

/-- **The time of the gap Diffie–Hellman reduction.** For a costed oracle adversary `B` of time `T`
with at most `q` queries and primitive costs at most `tO` (decision oracle), `tm` (group operation),
`te` (exponentiation), `tf` and `tc` (public value of an exponent), the derived costed form of
`stepRedD` at the uniform draw of `Draw S K × K` (of cost zero), the step `stepR` (of cost
`stepTime`) and the extraction `extractR` (of cost `extTime`), whose erasure is the program of
`gdhRed G a b`, runs in time at most `T + q · (stepBound … q + 2) + extBound … q + 1`, the time of
the adversary plus a polynomial of degree two in its number of queries. -/
theorem gdhOut_timeBound (B : OracleAdv.Timed (OEv W) (OOut S W K) Bool) {T q : ℕ}
    (hB : B.TimeBound T) (hq : B.erase.IsQueryBound q) {tO tm tf te tc : ℕ}
    (hO : ∀ x y z, OCost x y z ≤ tO) (hm : ∀ x y, mulCost x y ≤ tm) (hf : ∀ x, toFunCost x ≤ tf)
    (he : ∀ x y, expCost x y ≤ te) (hc : ∀ x y, coeCost x y ≤ tc) :
    OracleAdv.Timed.StepTimeBound
      (stepRedD.timed (fun _ _ => PMF.uniformFintype (Draw S K × K)) (fun _ _ => 0)
        (stepR G a b O X Y) (stepTime G a b O OCost X Y coeCost mulCost toFunCost expCost)
        (fun t => extractR G a b O X Y t.1.1)
        (fun t => extTime G a b O OCost X Y mulCost toFunCost expCost t.1.1) B rInitR)
      (T + q * (stepBound tO tm te tf tc q + 2) + (extBound tO tm te tf q + 1)) := by
  have hpos : ∀ i, 1 ≤ stepBound tO tm te tf tc i := fun i => by unfold stepBound; omega
  refine (stepRedD.timeBound_timed _ _ _ _ _ _ Sz (fun i => stepBound tO tm te tf tc i - 1)
    (extBound tO tm te tf) (fun _ _ h => Nat.sub_le_sub_right (stepBound_mono tO tm te tf tc h) 1)
    (fun i t h => ?_) (fun i t e r h => sz_stepR G a b O X Y h e r) (fun i t e r h => ?_)
    (fun i t h => ?_) B hB hq rInitR ⟨le_rfl, le_rfl, le_rfl⟩).mono ?_
  · obtain ⟨h1, h2, h3⟩ := h
    exact ⟨by omega, by omega, by omega⟩
  · have := stepTime_lt G a b O OCost X Y coeCost mulCost toFunCost expCost h e r hO hm hf he hc
    omega
  · have h1 := extTime_le G a b O OCost X Y mulCost toFunCost expCost t.1.1 hO hm hf he
    have h2 := Nat.mul_le_mul_left (tO + 2 * tm + 2 * tf + 40) h.1
    unfold extBound
    omega
  · have hq' := Nat.mul_le_mul_left q
      (show stepBound tO tm te tf tc q - 1 + 3 ≤ stepBound tO tm te tf tc q + 2 by
        have := hpos q; omega)
    omega

end Instance


end CatCrypt.Crypto.AKE.X3DHSquareGDH
