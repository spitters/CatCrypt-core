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
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquareGDH

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.AKE.X3DHSquareHops

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

/-- **The costed reduction**: the costed adversary `B` run against the world of the reduction,
each query answered by one draw at the time `stepTime` of the step, followed by the extraction
at the time `extTime`. -/
noncomputable def redLoop : OracleAdv.Timed (OEv W) (OOut S W K) Bool → RSim S W K × St K →
    ℕ × OracleAdv.Timed Empty Empty W
  | .ret _, t => (extTime G a b O OCost X Y mulCost toFunCost expCost t.1.1,
      .ret (extractR G a b O X Y t.1.1))
  | .rand p c k, t => (0, .rand p (fun x => c x + (redLoop (k x) t).1) fun x => (redLoop (k x) t).2)
  | .query d c k, t => (0, .rand (PMF.uniformFintype (Draw S K × K))
      (fun r => stepTime G a b O OCost X Y coeCost mulCost toFunCost expCost t d r +
        c (stepR G a b O X Y t d r).2 +
        (redLoop (k (stepR G a b O X Y t d r).2) (stepR G a b O X Y t d r).1).1)
      fun r => (redLoop (k (stepR G a b O X Y t d r).2) (stepR G a b O X Y t d r).1).2)

/-- The erasure of the costed reduction loop. -/
theorem redLoop_erase (B : OracleAdv.Timed (OEv W) (OOut S W K) Bool) (t : RSim S W K × St K) :
    (redLoop G a b O OCost X Y coeCost mulCost toFunCost expCost B t).2.erase =
      (OracleAdv.simulate (implR G a b O X Y) B.erase t).bind
        fun p => .ret (extractR G a b O X Y p.2.1.1) := by
  induction B generalizing t with
  | ret o => rfl
  | rand p c k ih =>
    simp only [redLoop, OracleAdv.Timed.erase, OracleAdv.simulate, OracleAdv.bind, ih]
  | query d c k ih =>
    simp only [redLoop, OracleAdv.Timed.erase, OracleAdv.simulate, implR, OracleAdv.bind, ih]

/-- **The costed gap Diffie–Hellman reduction** of the pair `(a, b)` for the costed adversary
`B`. -/
noncomputable def redTimed (B : OracleAdv.Timed (OEv W) (OOut S W K) Bool) :
    ℕ × OracleAdv.Timed Empty Empty W :=
  redLoop G a b O OCost X Y coeCost mulCost toFunCost expCost B rInitR

/-- **Erasure of the costed reduction**: erasing the costs gives the program `redTree` of the
reduction `gdhRed G a b`, for the erased adversary. -/
theorem redTimed_erase (B : OracleAdv.Timed (OEv W) (OOut S W K) Bool) :
    (redTimed G a b O OCost X Y coeCost mulCost toFunCost expCost B).2.erase =
      redTree G a b O X Y B.erase :=
  redLoop_erase G a b O OCost X Y coeCost mulCost toFunCost expCost B rInitR

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

theorem otherC_time (s : RSim S W K) (e : OEv W) {tO tm tf te tc : ℕ}
    (hO : ∀ x y z, OCost x y z ≤ tO) (hm : ∀ x y, mulCost x y ≤ tm) (hf : ∀ x, toFunCost x ≤ tf)
    (he : ∀ x y, expCost x y ≤ te) (hc : ∀ x y, coeCost x y ≤ tc) :
    SPTree.Timed.stepTime (otherC.tree.timed G a b O OCost X Y (liftR s) e s.1.lt (fun _ => 0)
        s.1.eph (fun _ => 0) s.1.st.recs (fun _ => 0) s.2.1 (fun _ => 0) DFunLike.coe coeCost
        mulCost toFunCost expCost) ≤
      200 + 10 * (tO + tm + te + tf + tc) + (3 * (tO + tm + te + tf) + 60) * s.1.ro.length +
        10 * s.1.st.notices.length := by
  time_bound

theorem finishC_time (p : RSim S W K × Dec S W K) (t : St K) :
    SPTree.Timed.stepTime (finishC.tree.timed (liftR p.1, p.2) t (fun _ => 0) (fun _ => 0)) ≤
      100 + 10 * t.notices.length := by
  time_bound

theorem ltTime_le (rs : RSt S (W ⊕ W) K) (pid : PartyId) : ltTime rs pid ≤ 4 := by
  unfold ltTime
  time_bound

theorem delTime_le (rs : RSt S (W ⊕ W) K) (inp : Inst → Option (Inp (W ⊕ W))) (x : Inst)
    (r : Rec K) (ip : Inp (W ⊕ W)) {tO tm tf te : ℕ}
    (hO : ∀ x y z, OCost x y z ≤ tO) (hm : ∀ x y, mulCost x y ≤ tm) (hf : ∀ x, toFunCost x ≤ tf)
    (he : ∀ x y, expCost x y ≤ te) :
    delTime G a b O OCost X Y mulCost toFunCost expCost rs inp x r ip ≤
      200 + 20 * (tO + tm + te + tf) + (3 * (tO + tm + te + tf) + 60) * rs.ro.length := by
  unfold delTime
  time_bound

theorem cguard_time (s : RSim S W K) (sid : SessionId) (pid : PartyId) :
    SPTree.Timed.stepTime (cguardC.tree.timed (liftR s) sid pid (fun _ => 0) (fun _ => 0)) ≤ 20 := by
  time_bound

theorem sguard_time (s : RSim S W K) (sid : SessionId) (pid : PartyId) :
    SPTree.Timed.stepTime (sguardC.tree.timed (liftR s) sid pid (fun _ => 0) (fun _ => 0)) ≤ 20 := by
  time_bound

end Costed

end CatCrypt.Crypto.AKE.X3DHSquareGDH
