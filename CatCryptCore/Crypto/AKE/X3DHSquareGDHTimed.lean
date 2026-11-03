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

end Prog

derive_reduction completeC
derive_reduction sendC
derive_reduction otherC
derive_reduction fakeC


end CatCrypt.Crypto.AKE.X3DHSquareGDH
