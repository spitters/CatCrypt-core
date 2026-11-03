/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDHSquareGDH
public import CatCryptCore.Crypto.AKE.X3DHSquareGDHTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.AutoTime

/-!
# Test
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.PQXDHSquareGDH

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Crypto.AKE.X3DHSquare (Inp RSt Named opkOf ltStep)
open CatCrypt.Crypto.AKE.X3DHSquareHops (drive0D Draw ltD fStepD)
open CatCrypt.Crypto.AKE.X3DHSquareGDH (keyA keyB pubIK pubSPK aliceS bobS ofInp off1 off2 ltC fakeC)
open CatCrypt.Crypto.AKE.PQXDHSquare
open CatCrypt.Crypto.AKE.PQXDHSquareHops
open CatCrypt.Crypto.KEM.Games (Scheme)

section Prog

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (Ko : KemOps PK SK SS C) (G : DHGroup S W)
  (a b : PartyId) (O : W → W → W → Bool) (X Y : W)

/-- The symbolic key derivation of PQXDH as a computation: the recorded value, or a uniform value
that is recorded. -/
noncomputable def psroStep (ZA ZB : W) (tb : List (PInp (W ⊕ W) SS × K)) (j : PInp (W ⊕ W) SS) :
    SPComp (K × List (PInp (W ⊕ W) SS × K)) :=
  match pslookup G O ZA ZB j tb with
  | some v => SPComp.pure (v, tb)
  | none => SPComp.map (fun v => (v, (j, v) :: tb)) (SPComp.sample K)

/-- `deliverRP` as a computation. -/
noncomputable def deliverCP (rs : PSt S (W ⊕ W) K PK SK SS C)
    (inp : Inst → Option (PInp (W ⊕ W) SS)) (x : Inst) (r : Rec K) (ip : PInp (W ⊕ W) SS) :
    SPComp (RSimP S W K PK SK SS C × Dec S W K PK C) :=
  if Exposed rs.x.st x r then
    SPComp.map (fun p => ((pKeyed rs x r p.1 p.2, Function.update inp x (some ip), .out (.inl .ack)),
        .inl (.inr (.newKey x.1 x.2 p.1))))
      (psroStep G O (keyA G a X rs.x) (keyB G b Y rs.x) rs.ro ip)
  else
    SPComp.pure ((pKeyed rs x r default rs.ro, Function.update inp x (some ip), .out (.inl .ack)),
      .inl (.inr (if (inp (x.1, r.peer)).all
          (fun j => pinpEq G O (keyA G a X rs.x) (keyB G b Y rs.x) j ip)
        then .newKey x.1 x.2 default else .newKeyUnlinked x.1 x.2 default)))

/-- The guard of `complete`: the record, the ephemeral secret and the one-time prekey of the
session, and the KEM public key of the peer's session, when the session completes. -/
def cguardP (s : RSimP S W K PK SK SS C) (sid : SessionId) (pid : PartyId) :
    Option (Rec K × S × S × PK) :=
  match s.1.x.st.recs (sid, pid), s.1.x.eph (sid, pid) with
  | some rc, some ek =>
    match opkOf s.1.x sid rc.peer, pkOf s.1 sid rc.peer with
    | some opk, some pk =>
      if rc.role = .initiator ∧ rc.key.isNone then some (rc, ek, opk, pk) else none
    | _, _ => none
  | _, _ => none

/-- The guard of `send` on the encapsulation `c`: the record and the one-time prekey of the
session and the decapsulation of `c`, when the session completes. -/
def sguardP (s : RSimP S W K PK SK SS C) (sid : SessionId) (pid : PartyId) (c : C) :
    Option (Rec K × S × SS) :=
  match s.1.x.st.recs (sid, pid), s.1.x.eph (sid, pid), s.1.kem (sid, pid) with
  | some rc, some opk, some kp =>
    match Ko.decaps kp.2 c with
    | some ss => if rc.role = .responder ∧ rc.key.isNone then some (rc, opk, ss) else none
    | none => none
  | _, _, _ => none

/-- The guard of `complete` as a computation. -/
noncomputable def cguardCP (s : RSimP S W K PK SK SS C) (sid : SessionId) (pid : PartyId) :
    SPComp (Option (Rec K × S × S × PK)) :=
  SPComp.pure (cguardP s sid pid)

/-- The guard of `send` as a computation. -/
noncomputable def sguardCP (s : RSimP S W K PK SK SS C) (sid : SessionId) (pid : PartyId)
    (c : C) : SPComp (Option (Rec K × S × SS)) :=
  SPComp.pure (sguardP Ko s sid pid c)

/-- The encapsulation of an initiator as a computation. -/
noncomputable def encCP (pk : PK) : SPComp (SS × C) := Ko.encaps pk

/-- The other events of the simulator of the reduction as a computation. -/
noncomputable def otherCP (s : RSimP S W K PK SK SS C) :
    OEv W SS C → SPComp (RSimP S W K PK SK SS C × Dec S W K PK C)
  | .inl (.newSession sid pid peer role) =>
    if (s.1.x.st.recs (sid, pid)).isNone then
      SPComp.bind (SPComp.sample S) fun y =>
        if role = .responder then
          SPComp.map (fun kp =>
            (({ s.1 with
                x := { s.1.x with st := addSession s.1.x.st (sid, pid) peer role,
                                  eph := Function.update s.1.x.eph (sid, pid) (some y) },
                kem := Function.update s.1.kem (sid, pid) (some kp) }, s.2.1, .fwd),
              .inl (.inl (.newSession sid pid peer role)))) Ko.keygen
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
        .inr (.inr (.inl (.pub (pubIK G a X pid l.1) (pubSPK G b Y pid l.1))))))
      (ltStep s.1.x pid)
  | .inr (.ephPub sid pid) =>
    SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl (.eph ((s.1.x.eph (sid, pid)).map G.pub)))))
  | .inr (.pqPub sid pid) =>
    SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inr (pkOf s.1 sid pid, s.1.ct (sid, pid)))))
  | .inr (.corrupt pid) =>
    if Named s.1.x.st pid then
      SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl (.secret none))))
    else
      SPComp.map (fun l =>
        (({ s.1 with x := { l.2 with st := corruptStep l.2.st pid } }, s.2.1,
          .out (.inl (.secret (some l.1)))), .inl (.inr (.corrupt pid)))) (ltStep s.1.x pid)
  | .inr (.complete _ _) => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
  | .inr (.send _ _ _ _) => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
  | .inr (.kdf q) => SPComp.map (fun p =>
      (({ s.1 with ro := p.2 }, s.2.1, .fwd), .inr (.inr (.inl (.hash p.1)))))
      (psroStep G O (keyA G a X s.1.x) (keyB G b Y s.1.x) s.1.ro (ofInp q.1, q.2))

/-- The finish of a step of the world of the reduction as a computation: the decision of the
start is passed to `F_AKE` with a uniform fresh key, and its answer to `finRP`. -/
noncomputable def finishCP (p : RSimP S W K PK SK SS C × Dec S W K PK C) (t : St K) :
    SPComp ((RSimP S W K PK SK SS C × St K) × OOut S W K PK C) :=
  match p.2 with
  | .inr o => SPComp.pure ((p.1, t), o)
  | .inl g => SPComp.map (fun q => (((finRP p.1 q.2).1, q.1), (finRP p.1 q.2).2)) (fakeC t g)

/-- The extraction of the reduction as a computation. -/
noncomputable def extractCP (rs : PSt S (W ⊕ W) K PK SK SS C) : SPComp W :=
  SPComp.pure (extractRP G a b O X Y rs)

end Prog

derive_reduction cguardCP
derive_reduction sguardCP
derive_reduction encCP
derive_reduction deliverCP
derive_reduction otherCP
derive_reduction finishCP
derive_reduction extractCP

/-! ## The costed reduction -/

/-- The costed copy of the X3DH part of the real state in the world of the reduction. -/
abbrev XHatR (S W K : Type) : Type :=
  (((Inst → Option (Rec K)) × (Inst → ℕ)) × ((PartyId → Bool) × (PartyId → ℕ)) ×
      List Notice × ℕ) × ((PartyId → Option (S × S)) × (PartyId → ℕ)) ×
      ((Inst → Option S) × (Inst → ℕ)) × List (Inp (W ⊕ W) × K)

/-- The costed state of the simulator of the reduction: its tables with their cost companions. -/
abbrev RSimHatP (S W K PK SK SS C : Type) : Type :=
  (XHatR S W K × ((Inst → Option (PK × SK)) × (Inst → ℕ)) × ((Inst → Option C) × (Inst → ℕ)) ×
      List (PInp (W ⊕ W) SS × K)) ×
    ((Inst → Option (PInp (W ⊕ W) SS)) × (Inst → ℕ)) × Phase S W K PK C

/-- The records and corruptions of a state read at unit cost. -/
abbrev liftStP {K : Type} (t : St K) :
    ((Inst → Option (Rec K)) × (Inst → ℕ)) × ((PartyId → Bool) × (PartyId → ℕ)) × List Notice × ℕ :=
  ((t.recs, fun _ => 0), (t.corrupt, fun _ => 0), t.notices, t.cursor)

/-- The X3DH part of a state with its tables read at unit cost. -/
abbrev liftXR {S W K : Type} (rs : RSt S (W ⊕ W) K) : XHatR S W K :=
  (liftStP rs.st, (rs.lt, fun _ => 0), (rs.eph, fun _ => 0), rs.ro)

/-- A state of the simulator of the reduction with its tables read at unit cost: every cost
companion is zero. -/
abbrev liftRP {S W K PK SK SS C : Type} (s : RSimP S W K PK SK SS C) : RSimHatP S W K PK SK SS C :=
  ((liftXR s.1.x, (s.1.kem, fun _ => 0), (s.1.ct, fun _ => 0), s.1.ro), (s.2.1, fun _ => 0), s.2.2)

section Costed

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (Ko : KemOps PK SK SS C)
  (G : DHGroup S W) (a b : PartyId) (O : W → W → W → Bool) (OCost : W → W → W → ℕ) (X Y : W)
  (coeCost : S ≃ W → S → ℕ) (mulCost : W → W → ℕ) (toFunCost : S → ℕ) (expCost : W → S → ℕ)
  (keygenT : SPTree.Timed (PK × SK)) (encT : PK → SPTree.Timed (SS × C)) (encTC : PK → ℕ)
  (decCost : SK → C → ℕ)

/-- The time of a delivery: the costed tree of `deliverCP` with the tables read at unit cost. -/
noncomputable def delTimeP (rs : PSt S (W ⊕ W) K PK SK SS C)
    (inp : Inst → Option (PInp (W ⊕ W) SS)) (x : Inst) (r : Rec K) (ip : PInp (W ⊕ W) SS) : ℕ :=
  SPTree.Timed.stepTime (deliverCP.tree.timed G a b O OCost X Y rs inp (fun _ => 0) x r ip mulCost
    toFunCost (fun _ => 0) expCost
    (X3DHSquareGDH.liftSt rs.x.st, (rs.x.lt, fun _ => 0), (rs.x.eph, fun _ => 0), rs.x.ro)
    (fun _ => 0) (fun _ => 0))

/-- The time of the encapsulation to `pk`: the costed tree of `encCP`. -/
noncomputable def encTimeP (pk : PK) : ℕ :=
  SPTree.Timed.stepTime (encCP.tree.timed Ko pk encT encTC)

/-- The time of `complete` with the draw `d` of X3DH and the encapsulation `kc`: the guard, the
two draws of long-term secrets, the encapsulation and the delivery, each on the state it
reads. -/
noncomputable def completeTimeP (s : RSimP S W K PK SK SS C) (sid : SessionId) (pid : PartyId)
    (d : Draw S K) (kc : Option (SS × C)) : ℕ :=
  SPTree.Timed.stepTime (cguardCP.tree.timed (liftRP s) sid pid (fun _ => 0) (fun _ => 0)
      (fun _ => 0)) +
    match cguardP s sid pid, kc with
    | some (rc, ek, opk, pk), some kc =>
      X3DHSquareGDH.ltTime s.1.x pid + X3DHSquareGDH.ltTime (ltD s.1.x pid d.2.1).2 rc.peer +
        encTimeP Ko encT encTC pk +
        delTimeP G a b O OCost X Y mulCost toFunCost expCost
          { s.1 with x := (ltD (ltD s.1.x pid d.2.1).2 rc.peer d.2.2.1).2,
                     ct := Function.update s.1.ct (sid, pid) (some kc.2) } s.2.1 (sid, pid) rc
          (aliceS G a b X Y sid pid rc.peer (ltD s.1.x pid d.2.1).1
            (ltD (ltD s.1.x pid d.2.1).2 rc.peer d.2.2.1).1 ek opk, kc.1)
    | _, _ => 0

/-- The time of `send` on the ephemeral key `e` and the encapsulation `c` with the draw `d`: the
guard with its decapsulation, the two draws of long-term secrets and the delivery. -/
noncomputable def sendTimeP (s : RSimP S W K PK SK SS C) (sid : SessionId) (pid : PartyId) (e : W)
    (c : C) (d : Draw S K) : ℕ :=
  SPTree.Timed.stepTime (sguardCP.tree.timed Ko (liftRP s) sid pid c (fun _ => 0) (fun _ => 0)
      (fun _ => 0) decCost) +
    match sguardP Ko s sid pid c with
    | some (rc, opk, ss) =>
      X3DHSquareGDH.ltTime s.1.x pid + X3DHSquareGDH.ltTime (ltD s.1.x pid d.2.1).2 rc.peer +
        delTimeP G a b O OCost X Y mulCost toFunCost expCost
          { s.1 with x := (ltD (ltD s.1.x pid d.2.1).2 rc.peer d.2.2.1).2 } s.2.1 (sid, pid) rc
          (bobS G a b X Y sid rc.peer pid e (ltD s.1.x pid d.2.1).1
            (ltD (ltD s.1.x pid d.2.1).2 rc.peer d.2.2.1).1 opk, ss)
    | none => 0

/-- The time of the other events: the costed tree of `otherCP` with the tables read at unit
cost. -/
noncomputable def otherTimeP (s : RSimP S W K PK SK SS C) (e : OEv W SS C) : ℕ :=
  SPTree.Timed.stepTime (otherCP.tree.timed Ko G a b O OCost X Y (liftRP s) e s.1.x.lt
    (fun _ => 0) s.1.x.eph (fun _ => 0) s.1.x.st.recs (fun _ => 0) s.1.kem (fun _ => 0) s.2.1
    (fun _ => 0) DFunLike.coe coeCost s.1.ct (fun _ => 0) keygenT mulCost toFunCost expCost)

/-- **The time of the start** of the simulator of the reduction on the event `e` with the draw
`d`: one unit for the dispatch on the event, and the time of `complete`, of `send` or of the
costed tree of `otherCP`. -/
noncomputable def startTimeP (s : RSimP S W K PK SK SS C) (e : OEv W SS C)
    (d : PDraw S K PK SK SS C) : ℕ :=
  1 + match e with
    | .inr (.complete sid pid) =>
      completeTimeP Ko G a b O OCost X Y mulCost toFunCost expCost encT encTC s sid pid d.1 d.2.2
    | .inr (.send sid pid e' c) =>
      sendTimeP Ko G a b O OCost X Y mulCost toFunCost expCost decCost s sid pid e' c d.1
    | e => otherTimeP Ko G a b O OCost X Y coeCost mulCost toFunCost expCost keygenT s e

/-- The time of the finish of a step: the costed tree of `finishCP`. -/
noncomputable def finTimeP (p : RSimP S W K PK SK SS C × Dec S W K PK C) (t : St K) : ℕ :=
  SPTree.Timed.stepTime (finishCP.tree.timed (liftRP p.1, p.2) t (fun _ => 0) (fun _ => 0))

/-- **The time of a step** of the world of the reduction with the draw `r`: the time of the
start and the time of the finish at the decision of the start. -/
noncomputable def stepTimeP (t : RSimP S W K PK SK SS C × St K) (e : OEv W SS C)
    (r : PDraw S K PK SK SS C × K) : ℕ :=
  startTimeP Ko G a b O OCost X Y coeCost mulCost toFunCost expCost keygenT encT encTC decCost
      t.1 e r.1 +
    finTimeP (startRP P G a b O X Y t.1 e r.1) t.2

/-- The time of the extraction: the costed tree of `extractCP`. -/
noncomputable def extTimeP (rs : PSt S (W ⊕ W) K PK SK SS C) : ℕ :=
  SPTree.Timed.stepTime (extractCP.tree.timed G a b O OCost X Y rs mulCost toFunCost
    (fun _ => 0) expCost)

/-- **The costed reduction loop**: the costed adversary `B` run against the world of the
reduction, each query answered by one draw of the step at the time `stepTimeP` of the step,
followed by the extraction at the time `extTimeP`. -/
noncomputable def redLoopP :
    OracleAdv.Timed (OEv W SS C) (OOut S W K PK C) Bool → RSimP S W K PK SK SS C × St K →
      ℕ × OracleAdv.Timed Empty Empty W
  | .ret _, t => (extTimeP G a b O OCost X Y mulCost toFunCost expCost t.1.1,
      .ret (extractRP G a b O X Y t.1.1))
  | .rand p c k, t => (0, .rand p (fun x => c x + (redLoopP (k x) t).1) fun x => (redLoopP (k x) t).2)
  | .query d c k, t => (0, .rand (simDist P (encPkR t.1.1 d))
      (fun r => stepTimeP P Ko G a b O OCost X Y coeCost mulCost toFunCost expCost keygenT encT
          encTC decCost t d r +
        c (stepRP P G a b O X Y t d r).2 +
        (redLoopP (k (stepRP P G a b O X Y t d r).2) (stepRP P G a b O X Y t d r).1).1)
      fun r => (redLoopP (k (stepRP P G a b O X Y t d r).2) (stepRP P G a b O X Y t d r).1).2)

/-- The erasure of the costed reduction loop. -/
theorem redLoopP_erase (B : OracleAdv.Timed (OEv W SS C) (OOut S W K PK C) Bool)
    (t : RSimP S W K PK SK SS C × St K) :
    (redLoopP P Ko G a b O OCost X Y coeCost mulCost toFunCost expCost keygenT encT encTC decCost
        B t).2.erase =
      (OracleAdv.simulate (implRP P G a b O X Y) B.erase t).bind
        fun p => .ret (extractRP G a b O X Y p.2.1.1) := by
  induction B generalizing t with
  | ret o => rfl
  | rand p c k ih =>
    simp only [redLoopP, OracleAdv.Timed.erase, OracleAdv.simulate, OracleAdv.bind, ih]
  | query d c k ih =>
    simp only [redLoopP, OracleAdv.Timed.erase, OracleAdv.simulate, implRP, OracleAdv.bind, ih]

/-- **The costed gap Diffie–Hellman reduction of PQXDH** of the pair `(a, b)` for the costed
adversary `B`: the costed loop from the initial state. -/
noncomputable def redTimedP (B : OracleAdv.Timed (OEv W SS C) (OOut S W K PK C) Bool) :
    ℕ × OracleAdv.Timed Empty Empty W :=
  redLoopP P Ko G a b O OCost X Y coeCost mulCost toFunCost expCost keygenT encT encTC decCost B
    rInitRP

/-- **Erasure of the costed reduction**: erasing the costs gives the program `redTreeP` of the
reduction `pqGdhRed G P a b`, for the erased adversary. -/
theorem pqGdhRed.erase_timed (B : OracleAdv.Timed (OEv W SS C) (OOut S W K PK C) Bool) :
    (redTimedP P Ko G a b O OCost X Y coeCost mulCost toFunCost expCost keygenT encT encTC
        decCost B).2.erase =
      redTreeP P G a b O X Y B.erase :=
  redLoopP_erase P Ko G a b O OCost X Y coeCost mulCost toFunCost expCost keygenT encT encTC
    decCost B rInitRP

end Costed

section Lookup

variable {S W K SS : Type} [Field S] [SampleableType W] [DecidableEq SS] (G : DHGroup S W)

/-- **The cost of the symbolic lookup of PQXDH** is linear in the length of the table. -/
theorem pslookup.timedCost_le (O : W → W → W → Bool) (OCost : W → W → W → ℕ) (ZA ZB : W)
    (j : PInp (W ⊕ W) SS) (tb : List (PInp (W ⊕ W) SS × K)) (mulCost : W → W → ℕ)
    (expCost : W → S → ℕ) (toFunCost : S → ℕ) {tO tm te tf : ℕ}
    (hO : ∀ x y z, OCost x y z ≤ tO) (hm : ∀ x y, mulCost x y ≤ tm)
    (he : ∀ x y, expCost x y ≤ te) (hf : ∀ x, toFunCost x ≤ tf) :
    pslookup.timedCost G O OCost ZA ZB j tb mulCost expCost toFunCost ≤
      (3 * (tO + tm + te + tf) + 80) * tb.length + 1 := by
  induction tb with
  | nil => simp [pslookup.timedCost]
  | cons p tb ih =>
    simp only [pslookup.timedCost]
    simp only [List.length_cons, Nat.mul_succ]
    repeat' split
    all_goals grind

end Lookup

section Bounds

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (Ko : KemOps PK SK SS C)
  (G : DHGroup S W) (a b : PartyId) (O : W → W → W → Bool) (OCost : W → W → W → ℕ) (X Y : W)
  (coeCost : S ≃ W → S → ℕ) (mulCost : W → W → ℕ) (toFunCost : S → ℕ) (expCost : W → S → ℕ)
  (keygenT : SPTree.Timed (PK × SK)) (encT : PK → SPTree.Timed (SS × C)) (encTC : PK → ℕ)
  (decCost : SK → C → ℕ)

omit [Fintype S] in
theorem delTimeP_le (rs : PSt S (W ⊕ W) K PK SK SS C) (inp : Inst → Option (PInp (W ⊕ W) SS))
    (x : Inst) (r : Rec K) (ip : PInp (W ⊕ W) SS) {tO tm tf te : ℕ}
    (hO : ∀ x y z, OCost x y z ≤ tO) (hm : ∀ x y, mulCost x y ≤ tm) (hf : ∀ x, toFunCost x ≤ tf)
    (he : ∀ x y, expCost x y ≤ te) :
    delTimeP G a b O OCost X Y mulCost toFunCost expCost rs inp x r ip ≤
      300 + 30 * (tO + tm + te + tf) + 2 * ((3 * (tO + tm + te + tf) + 80) * rs.ro.length) := by
  unfold delTimeP
  time_bound

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
theorem cguardP_time (s : RSimP S W K PK SK SS C) (sid : SessionId) (pid : PartyId) :
    SPTree.Timed.stepTime (cguardCP.tree.timed (liftRP s) sid pid (fun _ => 0) (fun _ => 0)
      (fun _ => 0)) ≤ 40 := by
  time_bound

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
theorem sguardP_time (s : RSimP S W K PK SK SS C) (sid : SessionId) (pid : PartyId) (c : C)
    {tD : ℕ} (hd : ∀ sk c, decCost sk c ≤ tD) :
    SPTree.Timed.stepTime (sguardCP.tree.timed Ko (liftRP s) sid pid c (fun _ => 0) (fun _ => 0)
      (fun _ => 0) decCost) ≤ 40 + tD := by
  time_bound

omit [DecidableEq SS] in
theorem encTimeP_le (pk : PK) {tE : ℕ} (he : ∀ pk, (encT pk).time ≤ tE)
    (hec : ∀ pk, encTC pk ≤ tE) : encTimeP Ko encT encTC pk ≤ 2 + 2 * tE := by
  unfold encTimeP
  time_bound

omit [Field S] [Fintype S] [SampleableType W] [Inhabited K] [DecidableEq SS] in
theorem finTimeP_le (p : RSimP S W K PK SK SS C × Dec S W K PK C) (t : St K) :
    finTimeP p t ≤ 100 + 10 * t.notices.length := by
  unfold finTimeP
  time_bound

omit [Inhabited K] in
theorem otherTimeP_le (s : RSimP S W K PK SK SS C) (e : OEv W SS C) {tO tm tf te tc tK : ℕ}
    (hO : ∀ x y z, OCost x y z ≤ tO) (hm : ∀ x y, mulCost x y ≤ tm) (hf : ∀ x, toFunCost x ≤ tf)
    (he : ∀ x y, expCost x y ≤ te) (hc : ∀ x y, coeCost x y ≤ tc) (hk : keygenT.time ≤ tK) :
    otherTimeP Ko G a b O OCost X Y coeCost mulCost toFunCost expCost keygenT s e ≤
      300 + 20 * (tO + tm + te + tf + tc) + tK +
        2 * ((3 * (tO + tm + te + tf) + 80) * s.1.ro.length) + 20 * s.1.x.st.notices.length := by
  unfold otherTimeP
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e, c⟩ | q)
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · time_bound

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
theorem extTimeP_le (rs : PSt S (W ⊕ W) K PK SK SS C) {tO tm tf te : ℕ}
    (hO : ∀ x y z, OCost x y z ≤ tO) (hm : ∀ x y, mulCost x y ≤ tm) (hf : ∀ x, toFunCost x ≤ tf)
    (he : ∀ x y, expCost x y ≤ te) :
    extTimeP G a b O OCost X Y mulCost toFunCost expCost rs ≤
      100 + 4 * tm + 3 * te + 3 * tf + (tO + 2 * tm + 2 * tf + 40) * rs.ro.length := by
  unfold extTimeP
  simp only [extractCP.tree.timed, SPTree.Timed.stepTime, SPTree.Timed.time_ret]
  have hF : ∀ (f : PInp (W ⊕ W) SS × K → Option W) (fc : PInp (W ⊕ W) SS × K → ℕ),
      (∀ p, fc p ≤ tO + 2 * tm + 2 * tf + 36) →
        List.findSome?.timedCost f fc rs.ro ≤ (tO + 2 * tm + 2 * tf + 40) * rs.ro.length + 1 :=
    fun f fc h => List.findSome?.timedCost_le f fc h rs.ro
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_right
    (Nat.add_le_add_left (hF _ _ fun p => ?_) _) _) _) _) ?_
  · split_ifs
    · split
      · have := hO (keyA G a X rs.x) (keyB G b Y rs.x) ‹_›
        have := hm X (G.pub (off1 a rs.x))
        have := hm Y (G.pub (off2 b rs.x))
        have := hf (off1 a rs.x)
        have := hf (off2 b rs.x)
        omega
      · omega
    · omega
  · split
    · have := hm ‹_› (G.exp (G.mul (G.mul (G.exp X (off2 b rs.x)) (G.exp Y (off1 a rs.x)))
        (G.pub (off1 a rs.x * off2 b rs.x))) (-1))
      have := he (G.mul (G.mul (G.exp X (off2 b rs.x)) (G.exp Y (off1 a rs.x)))
        (G.pub (off1 a rs.x * off2 b rs.x))) (-1)
      have := hm (G.mul (G.exp X (off2 b rs.x)) (G.exp Y (off1 a rs.x)))
        (G.pub (off1 a rs.x * off2 b rs.x))
      have := hm (G.exp X (off2 b rs.x)) (G.exp Y (off1 a rs.x))
      have := he X (off2 b rs.x)
      have := he Y (off1 a rs.x)
      have := hf (off1 a rs.x * off2 b rs.x)
      omega
    · have := hf 0
      omega

end Bounds

/-! ## The sizes of the state -/

section Size

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (G : DHGroup S W)
  (a b : PartyId) (O : W → W → W → Bool) (X Y : W)

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- The sizes of a state of the world of the reduction after `i` steps: the table and the two
lists of notices have at most `i` entries. -/
def SzP (i : ℕ) (t : RSimP S W K PK SK SS C × St K) : Prop :=
  t.1.1.ro.length ≤ i ∧ t.1.1.x.st.notices.length ≤ i ∧ t.2.notices.length ≤ i

omit [Fintype S] [Fintype K] [Nonempty K] [Inhabited K] in
theorem psroDet_length (ZA ZB : W) (tb : List (PInp (W ⊕ W) SS × K)) (j : PInp (W ⊕ W) SS)
    (k : K) : (psroDet G O ZA ZB tb j k).2.length ≤ tb.length + 1 := by
  rcases psroDet_snd G O ZA ZB tb j k with h | h <;> rw [h] <;> simp

omit [Fintype S] [Fintype K] [Nonempty K] in
theorem deliverRP_len (rs : PSt S (W ⊕ W) K PK SK SS C) (inp : Inst → Option (PInp (W ⊕ W) SS))
    (z : Inst) (rc : Rec K) (ip : PInp (W ⊕ W) SS) (k : K) :
    (deliverRP G a b O X Y rs inp z rc ip k).1.1.ro.length ≤ rs.ro.length + 1 ∧
      (deliverRP G a b O X Y rs inp z rc ip k).1.1.x.st.notices.length ≤
        rs.x.st.notices.length := by
  unfold deliverRP
  split
  · exact ⟨psroDet_length G O _ _ _ _ _, le_rfl⟩
  · exact ⟨Nat.le_succ _, le_rfl⟩

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- **A start of the simulator of the reduction adds at most one entry** to the table and to the
notices. -/
theorem startRP_len (s : RSimP S W K PK SK SS C) (e : OEv W SS C) (d : PDraw S K PK SK SS C) :
    (startRP P G a b O X Y s e d).1.1.ro.length ≤ s.1.ro.length + 1 ∧
      (startRP P G a b O X Y s e d).1.1.x.st.notices.length ≤ s.1.x.st.notices.length + 1 := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e, c⟩ | q)
  · simp only [startRP]
    split
    · split
      · exact ⟨Nat.le_succ _, X3DHSquareGDH.addSession_notices _ _ _ _⟩
      · exact ⟨Nat.le_succ _, X3DHSquareGDH.addSession_notices _ _ _ _⟩
    · exact ⟨Nat.le_succ _, Nat.le_succ _⟩
  · exact ⟨Nat.le_succ _, Nat.le_succ _⟩
  · exact ⟨Nat.le_succ _, Nat.le_succ _⟩
  · simp only [startRP, (X3DHSquareHops.pollStep_fst _).2.2]
    exact ⟨Nat.le_succ _, Nat.le_succ _⟩
  · simp only [startRP, X3DHSquareHops.ltD_st]
    exact ⟨Nat.le_succ _, Nat.le_succ _⟩
  · exact ⟨Nat.le_succ _, Nat.le_succ _⟩
  · exact ⟨Nat.le_succ _, Nat.le_succ _⟩
  · simp only [startRP]
    split
    · exact ⟨Nat.le_succ _, Nat.le_succ _⟩
    · simp only [corruptStep, X3DHSquareHops.ltD_st]
      exact ⟨Nat.le_succ _, Nat.le_succ _⟩
  · simp only [startRP, completeRP]
    repeat' split
    all_goals first
      | exact ⟨Nat.le_succ _, Nat.le_succ _⟩
      | refine ⟨(deliverRP_len G a b O X Y _ _ _ _ _ _).1.trans ?_,
          (deliverRP_len G a b O X Y _ _ _ _ _ _).2.trans ?_⟩ <;>
          simp only [X3DHSquareHops.ltD_st] <;> omega
  · simp only [startRP, sendRP]
    repeat' split
    all_goals first
      | exact ⟨Nat.le_succ _, Nat.le_succ _⟩
      | refine ⟨(deliverRP_len G a b O X Y _ _ _ _ _ _).1.trans ?_,
          (deliverRP_len G a b O X Y _ _ _ _ _ _).2.trans ?_⟩ <;>
          simp only [X3DHSquareHops.ltD_st] <;> omega
  · simp only [startRP]
    exact ⟨psroDet_length G O _ _ _ _ _, Nat.le_succ _⟩

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- **A step of the world of the reduction keeps the sizes** after one more step. -/
theorem sz_stepRP {i : ℕ} {t : RSimP S W K PK SK SS C × St K} (h : SzP i t) (e : OEv W SS C)
    (r : PDraw S K PK SK SS C × K) : SzP (i + 1) (stepRP P G a b O X Y t e r).1 := by
  obtain ⟨hs1, hs2⟩ := startRP_len P G a b O X Y t.1 e r.1
  obtain ⟨h1, h2, h3⟩ := h
  simp only [SzP, stepRP]
  rw [X3DHSquareGDH.stop_drive0D _ _ (fun _ _ => rfl)]
  refine ⟨by omega, by omega, ?_⟩
  unfold drive0D
  split
  · dsimp only
    omega
  · have := X3DHSquareGDH.fStepD_len t.2 ‹_› r.2
    dsimp only
    omega

end Size

/-! ## The time of the reduction -/

section Time

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (Ko : KemOps PK SK SS C)
  (G : DHGroup S W) (a b : PartyId) (O : W → W → W → Bool) (OCost : W → W → W → ℕ) (X Y : W)
  (coeCost : S ≃ W → S → ℕ) (mulCost : W → W → ℕ) (toFunCost : S → ℕ) (expCost : W → S → ℕ)
  (keygenT : SPTree.Timed (PK × SK)) (encT : PK → SPTree.Timed (SS × C)) (encTC : PK → ℕ)
  (decCost : SK → C → ℕ)

/-- The bound of a step after `i` steps, for primitive costs at most `tO` (decision oracle),
`tm` (group operation), `te` (exponentiation), `tf` and `tc` (public value of an exponent), and
KEM costs at most `tK` (key generation), `tE` (encapsulation) and `tD` (decapsulation). -/
def stepBoundP (tO tm te tf tc tK tE tD i : ℕ) : ℕ :=
  1000 + 50 * (tO + tm + te + tf + tc) + tK + 2 * tE + tD +
    2 * ((3 * (tO + tm + te + tf) + 80) * i) + 30 * i

/-- The bound of the extraction after `i` steps. -/
def extBoundP (tO tm te tf i : ℕ) : ℕ :=
  100 + 4 * tm + 3 * te + 3 * tf + (tO + 2 * tm + 2 * tf + 40) * i

/-- **The time of a step** of the world of the reduction after `i` steps is at most
`stepBoundP … i`. -/
theorem stepTimeP_le {i : ℕ} {t : RSimP S W K PK SK SS C × St K} (hsz : SzP i t) (e : OEv W SS C)
    (r : PDraw S K PK SK SS C × K) {tO tm tf te tc tK tE tD : ℕ}
    (hO : ∀ x y z, OCost x y z ≤ tO) (hm : ∀ x y, mulCost x y ≤ tm) (hf : ∀ x, toFunCost x ≤ tf)
    (he : ∀ x y, expCost x y ≤ te) (hc : ∀ x y, coeCost x y ≤ tc) (hk : keygenT.time ≤ tK)
    (hE : ∀ pk, (encT pk).time ≤ tE) (hEC : ∀ pk, encTC pk ≤ tE)
    (hD : ∀ sk c, decCost sk c ≤ tD) :
    stepTimeP P Ko G a b O OCost X Y coeCost mulCost toFunCost expCost keygenT encT encTC decCost
        t e r ≤ stepBoundP tO tm te tf tc tK tE tD i := by
  obtain ⟨h1, h2, h3⟩ := hsz
  have hfin := finTimeP_le (startRP P G a b O X Y t.1 e r.1) t.2
  have hL : 2 * ((3 * (tO + tm + te + tf) + 80) * t.1.1.ro.length) ≤
      2 * ((3 * (tO + tm + te + tf) + 80) * i) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
  have hdel : ∀ (rs : PSt S (W ⊕ W) K PK SK SS C) (inp : Inst → Option (PInp (W ⊕ W) SS))
      (z : Inst) (rc : Rec K) (ip : PInp (W ⊕ W) SS),
      delTimeP G a b O OCost X Y mulCost toFunCost expCost rs inp z rc ip ≤
        300 + 30 * (tO + tm + te + tf) + 2 * ((3 * (tO + tm + te + tf) + 80) * rs.ro.length) :=
    fun rs inp z rc ip => delTimeP_le G a b O OCost X Y mulCost toFunCost expCost rs inp z rc ip
      hO hm hf he
  unfold stepTimeP stepBoundP
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e, c⟩ | q)
  rotate_left 8
  · simp only [startTimeP, completeTimeP]
    have := cguardP_time t.1 sid pid
    split
    · rename_i rc ek opk pk kc _ _
      have := X3DHSquareGDH.ltTime_le t.1.1.x pid
      have := X3DHSquareGDH.ltTime_le (ltD t.1.1.x pid r.1.1.2.1).2 rc.peer
      have := encTimeP_le Ko encT encTC pk hE hEC
      refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_left
        (Nat.add_le_add_left (hdel _ _ _ _ _) _) _) _) _) ?_
      generalize 2 * ((3 * (tO + tm + te + tf) + 80) * t.1.1.ro.length) = P₁ at hL ⊢
      generalize 2 * ((3 * (tO + tm + te + tf) + 80) * i) = P₂ at hL ⊢
      omega
    · omega
  · simp only [startTimeP, sendTimeP]
    have := sguardP_time Ko decCost t.1 sid pid c hD
    split
    · rename_i rc opk ss _
      have := X3DHSquareGDH.ltTime_le t.1.1.x pid
      have := X3DHSquareGDH.ltTime_le (ltD t.1.1.x pid r.1.1.2.1).2 rc.peer
      refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_left
        (Nat.add_le_add_left (hdel _ _ _ _ _) _) _) _) _) ?_
      generalize 2 * ((3 * (tO + tm + te + tf) + 80) * t.1.1.ro.length) = P₁ at hL ⊢
      generalize 2 * ((3 * (tO + tm + te + tf) + 80) * i) = P₂ at hL ⊢
      omega
    · omega
  all_goals
    simp only [startTimeP]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left
      (otherTimeP_le Ko G a b O OCost X Y coeCost mulCost toFunCost expCost keygenT t.1 _ hO hm hf
        he hc hk) _) _) ?_
    generalize 2 * ((3 * (tO + tm + te + tf) + 80) * t.1.1.ro.length) = P₁ at hL ⊢
    generalize 2 * ((3 * (tO + tm + te + tf) + 80) * i) = P₂ at hL ⊢
    omega

theorem stepBoundP_mono (tO tm te tf tc tK tE tD : ℕ) {i j : ℕ} (h : i ≤ j) :
    stepBoundP tO tm te tf tc tK tE tD i ≤ stepBoundP tO tm te tf tc tK tE tD j := by
  unfold stepBoundP
  have := Nat.mul_le_mul_left (3 * (tO + tm + te + tf) + 80) h
  omega

theorem extBoundP_mono (tO tm te tf : ℕ) {i j : ℕ} (h : i ≤ j) :
    extBoundP tO tm te tf i ≤ extBoundP tO tm te tf j := by
  unfold extBoundP
  have := Nat.mul_le_mul_left (tO + 2 * tm + 2 * tf + 40) h
  omega

/-- **The time of the costed reduction loop**: from a state of sizes at most `i`, a costed
adversary of time `T` with at most `q` queries runs in time at most
`T + q · stepBoundP … (i + q) + extBoundP … (i + q)`. -/
theorem redLoopP_timeBound {tO tm tf te tc tK tE tD : ℕ}
    (hO : ∀ x y z, OCost x y z ≤ tO) (hm : ∀ x y, mulCost x y ≤ tm) (hf : ∀ x, toFunCost x ≤ tf)
    (he : ∀ x y, expCost x y ≤ te) (hc : ∀ x y, coeCost x y ≤ tc) (hk : keygenT.time ≤ tK)
    (hE : ∀ pk, (encT pk).time ≤ tE) (hEC : ∀ pk, encTC pk ≤ tE)
    (hD : ∀ sk c, decCost sk c ≤ tD) :
    ∀ (B : OracleAdv.Timed (OEv W SS C) (OOut S W K PK C) Bool) (T q i : ℕ)
      (t : RSimP S W K PK SK SS C × St K),
      SzP i t → B.TimeBound T → B.erase.IsQueryBound q →
      OracleAdv.Timed.StepTimeBound
        (redLoopP P Ko G a b O OCost X Y coeCost mulCost toFunCost expCost keygenT encT encTC
          decCost B t)
        (T + q * stepBoundP tO tm te tf tc tK tE tD (i + q) + extBoundP tO tm te tf (i + q)) := by
  intro B
  induction B with
  | ret o =>
    intro T q i t hsz _ _
    refine ⟨?_, trivial⟩
    have h1 := extTimeP_le G a b O OCost X Y mulCost toFunCost expCost t.1.1 hO hm hf he
    have h2 := Nat.mul_le_mul_left (tO + 2 * tm + 2 * tf + 40) hsz.1
    have h3 := extBoundP_mono tO tm te tf (Nat.le_add_right i q)
    simp only [redLoopP, extBoundP] at h1 h3 ⊢
    omega
  | rand p c k ih =>
    intro T q i t hsz hB hq
    simp only [redLoopP]
    have h0 := hB.1
    refine ⟨Nat.zero_le _, by omega, fun x => ?_⟩
    have hx := (hB.2 x).1
    obtain ⟨h1, h2⟩ := ih x (T - 1 - c x) q i t hsz (hB.2 x).2 (hq x)
    dsimp only
    refine ⟨by omega, h2.mono (by omega)⟩
  | query d c k ih =>
    intro T q i t hsz hB hq
    cases q with
    | zero => exact (hq : False).elim
    | succ q =>
      simp only [redLoopP]
      refine ⟨Nat.zero_le _, by have := hB.1; omega, fun r => ?_⟩
      have hx := (hB.2 (stepRP P G a b O X Y t d r).2).1
      obtain ⟨h1, h2⟩ := ih (stepRP P G a b O X Y t d r).2
        (T - 1 - c (stepRP P G a b O X Y t d r).2) q (i + 1) (stepRP P G a b O X Y t d r).1
        (sz_stepRP P G a b O X Y hsz d r) (hB.2 (stepRP P G a b O X Y t d r).2).2
        (hq (stepRP P G a b O X Y t d r).2)
      have hs := stepTimeP_le P Ko G a b O OCost X Y coeCost mulCost toFunCost expCost keygenT
        encT encTC decCost hsz d r hO hm hf he hc hk hE hEC hD
      have hmono := stepBoundP_mono tO tm te tf tc tK tE tD (show i ≤ i + (q + 1) by omega)
      have h0 := hB.1
      rw [show i + 1 + q = i + (q + 1) by omega] at h1 h2
      generalize stepBoundP tO tm te tf tc tK tE tD (i + (q + 1)) = F at h1 h2 hmono ⊢
      generalize extBoundP tO tm te tf (i + (q + 1)) = E at h1 h2 ⊢
      rw [Nat.succ_mul]
      generalize q * F = Pq at h1 h2 ⊢
      dsimp only
      refine ⟨by omega, h2.mono (by omega)⟩

/-- **The time of the gap Diffie–Hellman reduction of PQXDH.** For a costed oracle adversary `B`
of time `T` with at most `q` queries, primitive costs at most `tO` (decision oracle), `tm`
(group operation), `te` (exponentiation), `tf` and `tc` (public value of an exponent), and KEM
costs at most `tK` (the costed key generation), `tE` (the costed encapsulation and its cost
companion) and `tD` (decapsulation), the costed reduction `redTimedP`, whose erasure is the
program `redTreeP` of `pqGdhRed G P a b` (`pqGdhRed.erase_timed`), runs in time at most
`T + q · stepBoundP … q + extBoundP … q`: the time of the adversary plus a polynomial of degree
two in its number of queries. -/
theorem pqGdhRed.timeBound_timed (B : OracleAdv.Timed (OEv W SS C) (OOut S W K PK C) Bool)
    {T q : ℕ} (hB : B.TimeBound T) (hq : B.erase.IsQueryBound q) {tO tm tf te tc tK tE tD : ℕ}
    (hO : ∀ x y z, OCost x y z ≤ tO) (hm : ∀ x y, mulCost x y ≤ tm) (hf : ∀ x, toFunCost x ≤ tf)
    (he : ∀ x y, expCost x y ≤ te) (hc : ∀ x y, coeCost x y ≤ tc) (hk : keygenT.time ≤ tK)
    (hE : ∀ pk, (encT pk).time ≤ tE) (hEC : ∀ pk, encTC pk ≤ tE)
    (hD : ∀ sk c, decCost sk c ≤ tD) :
    OracleAdv.Timed.StepTimeBound
      (redTimedP P Ko G a b O OCost X Y coeCost mulCost toFunCost expCost keygenT encT encTC
        decCost B)
      (T + q * stepBoundP tO tm te tf tc tK tE tD q + extBoundP tO tm te tf q) := by
  have h := redLoopP_timeBound P Ko G a b O OCost X Y coeCost mulCost toFunCost expCost keygenT
    encT encTC decCost hO hm hf he hc hk hE hEC hD B T q 0 rInitRP ⟨le_rfl, le_rfl, le_rfl⟩ hB hq
  unfold redTimedP
  simpa only [Nat.zero_add] using h

end Time

end CatCrypt.Crypto.AKE.PQXDHSquareGDH
