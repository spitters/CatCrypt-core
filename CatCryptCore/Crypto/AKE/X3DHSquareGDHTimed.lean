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

/-- `complete` of the simulator of the reduction as a computation. -/
noncomputable def completeC (s : RSim S W K) (sid : SessionId) (pid : PartyId) :
    SPComp (RSim S W K × Dec S W K) :=
  match s.1.st.recs (sid, pid), s.1.eph (sid, pid) with
  | some rc, some ek =>
    match opkOf s.1 sid rc.peer with
    | some opk =>
      if rc.role = .initiator ∧ rc.key.isNone then
        SPComp.bind (ltStep s.1 pid) fun la => SPComp.bind (ltStep la.2 rc.peer) fun lb =>
          deliverC G a b O X Y lb.2 s.2.1 (sid, pid) rc
            (aliceS G a b X Y sid pid rc.peer la.1 lb.1 ek opk)
      else SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))
    | none => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | _, _ => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))

/-- `send` of the simulator of the reduction as a computation. -/
noncomputable def sendC (s : RSim S W K) (sid : SessionId) (pid : PartyId) (e : W) :
    SPComp (RSim S W K × Dec S W K) :=
  match s.1.st.recs (sid, pid), s.1.eph (sid, pid) with
  | some rc, some opk =>
    if rc.role = .responder ∧ rc.key.isNone then
      SPComp.bind (ltStep s.1 pid) fun lb => SPComp.bind (ltStep lb.2 rc.peer) fun la =>
        deliverC G a b O X Y la.2 s.2.1 (sid, pid) rc
          (bobS G a b X Y sid rc.peer pid e lb.1 la.1 opk)
    else SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | _, _ => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))

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

derive_reduction completeC
derive_reduction sendC
derive_reduction otherC
derive_reduction fakeC
derive_reduction finishC
derive_reduction extractC

/-! ## The costed reduction -/

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

section Costed

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W) (a b : PartyId) (O : W → W → W → Bool)
  (OCost : W → W → W → ℕ) (X Y : W) (coeCost : S ≃ W → S → ℕ) (mulCost : W → W → ℕ)
  (toFunCost : S → ℕ) (expCost : W → S → ℕ)

/-- **The time of the start** of the simulator of the reduction on the event `e`: one unit for
the dispatch on the event and the time of the costed tree of `completeC`, `sendC` or `otherC`. -/
noncomputable def startTime (s : RSim S W K) (e : OEv W) : ℕ :=
  1 + match e with
    | .inr (.complete sid pid) => SPTree.Timed.stepTime (completeC.tree.timed G a b O OCost X Y
        (liftR s) sid pid s.1.lt (fun _ => 0) s.1.eph (fun _ => 0) s.2.1 (fun _ => 0)
        s.1.st.recs (fun _ => 0) mulCost toFunCost expCost)
    | .inr (.send sid pid e') => SPTree.Timed.stepTime (sendC.tree.timed G a b O OCost X Y
        (liftR s) sid pid e' s.1.lt (fun _ => 0) s.1.eph (fun _ => 0) s.1.st.recs (fun _ => 0)
        s.2.1 (fun _ => 0) mulCost toFunCost expCost)
    | e => SPTree.Timed.stepTime (otherC.tree.timed G a b O OCost X Y (liftR s) e s.1.lt
        (fun _ => 0) s.1.eph (fun _ => 0) s.1.st.recs (fun _ => 0) s.2.1 (fun _ => 0)
        DFunLike.coe coeCost mulCost toFunCost expCost)

/-- The time of the finish of a step: the costed tree of `finishC`. -/
noncomputable def finTime (p : RSim S W K × Dec S W K) (t : St K) : ℕ :=
  SPTree.Timed.stepTime (finishC.tree.timed (liftR p.1, p.2) t (fun _ => 0) (fun _ => 0))

/-- **The time of a step** of the world of the reduction with the draw `r`: the time of the
start and the time of the finish at the decision of the start. -/
noncomputable def stepTime (t : RSim S W K × St K) (e : OEv W) (r : Draw S K × K) : ℕ :=
  startTime G a b O OCost X Y coeCost mulCost toFunCost expCost t.1 e +
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

end Costed

end CatCrypt.Crypto.AKE.X3DHSquareGDH
