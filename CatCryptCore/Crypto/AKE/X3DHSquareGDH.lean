/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHSquareHops
public import CatCryptCore.Crypto.Assumptions.GapDH

/-!
# The bad event of the X3DH square under the gap Diffie–Hellman assumption

PLACEHOLDER DOCSTRING
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquareGDH

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.AKE.X3DHSquareHops
open CatCrypt.Crypto.OracleGameUpToBad
open scoped ENNReal

/-! ## The gap Diffie–Hellman problem of a group -/

section GDH

variable {S W : Type} [Field S] [Fintype S] [SampleableType W] (G : DHGroup S W)

/-- **The gap Diffie–Hellman problem of the group `G`** as an instance of `GapDHDef`: the
Diffie–Hellman function `cdh X Y = Y^{dlog X}`, the key agreement `dh x Y = Y^{dlog x}` on a
private key stored as its public value, and the key generation of a uniform exponent `s` with
the pair `(g^s, g^s)`. The game samples two exponents and wins when the adversary, with the
decision oracle of `cdh`, outputs `g^{xy}` on `(g^x, g^y)`. -/
noncomputable def gapDHDef : GapDHDef W where
  dh x Y := G.exp Y (G.dlog x)
  cdh X Y := G.exp Y (G.dlog X)
  keygen := liftPMF ((PMF.uniformFintype S).map fun s => (G.pub s, G.pub s))
  keygen_isPure := liftPMF_isPure _

/-- The decision oracle of `gapDHDef G` on public values: `(g^x, Y, Z)` is accepted when
`Z = Y^x`. -/
theorem ddhOracle_pub (x : S) (Y Z : W) :
    ddhOracle (gapDHDef G) (G.pub x) Y Z = decide (Z = G.exp Y x) := by
  simp only [ddhOracle, gapDHDef, DHGroup.dlog_pub]

/-- The Diffie–Hellman value of two public values. -/
theorem cdh_pub (x y : S) : (gapDHDef G).cdh (G.pub x) (G.pub y) = G.pub (x * y) := by
  simp only [gapDHDef, DHGroup.dlog_pub, G.exp_pub, mul_comm]

end GDH

/-! ## Symbolic Diffie–Hellman values -/

section Sym

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] (G : DHGroup S W)

/-- The value of a symbolic Diffie–Hellman value at the secret exponent `k` of its position:
`inl w` is the known value `w`, `inr E` is `E^k`. -/
def ev (k : S) : W ⊕ W → W
  | .inl w => w
  | .inr E => G.exp E k

/-- The value of a symbolic input at the identity secret `ik` (positions `DH1` and `DH2`) and the
signed-prekey secret `spk` (position `DH3`). -/
def interp (ik spk : S) (i : Inp (W ⊕ W)) : Inp W :=
  ⟨i.sid, i.ini, i.res, ev G ik i.dh1, ev G ik i.dh2, ev G spk i.dh3, i.dh4.elim id id⟩

/-- A symbolic input as a table entry with its value. -/
def interpE (ik spk : S) (p : Inp (W ⊕ W) × K) : Inp W × K := (interp G ik spk p.1, p.2)

variable (O : W → W → W → Bool)

/-- **The equality of two symbolic values** of a position with public key `Z`, decided with the
decision oracle `O`: `w = E^z` is the triple `(Z, E, w)`, and `E^z = E'^z` is the triple
`(Z, E · E'^{-1}, 1)`. -/
def symEq (Z : W) : W ⊕ W → W ⊕ W → Bool
  | .inl w, .inl w' => decide (w = w')
  | .inl w, .inr E => O Z E w
  | .inr E, .inl w => O Z E w
  | .inr E, .inr E' => O Z (G.mul E (G.exp E' (-1))) (G.pub 0)

/-- The equality of two symbolic inputs, with the public identity key `ZA` and the public signed
prekey `ZB` of the positions. -/
def inpEq (ZA ZB : W) (i j : Inp (W ⊕ W)) : Bool :=
  decide (i.sid = j.sid) && decide (i.ini = j.ini) && decide (i.res = j.res) &&
    symEq G O ZA i.dh1 j.dh1 && symEq G O ZA i.dh2 j.dh2 && symEq G O ZB i.dh3 j.dh3 &&
    decide (i.dh4.elim id id = j.dh4.elim id id)

/-- The lookup of a symbolic input in a symbolic table. -/
def slookup (ZA ZB : W) (j : Inp (W ⊕ W)) : List (Inp (W ⊕ W) × K) → Option K
  | [] => none
  | p :: tb => if inpEq G O ZA ZB j p.1 then some p.2 else slookup ZA ZB j tb

/-- The lazily sampled key derivation on a symbolic table, with the fresh value `k`. -/
def sroDet (ZA ZB : W) (tb : List (Inp (W ⊕ W) × K)) (j : Inp (W ⊕ W)) (k : K) :
    K × List (Inp (W ⊕ W) × K) :=
  match slookup G O ZA ZB j tb with
  | some v => (v, tb)
  | none => (k, (j, k) :: tb)

/-- **Correctness of the symbolic equality** with the decision oracle of `gapDHDef G`. -/
theorem symEq_ddh (k : S) (s t : W ⊕ W) :
    symEq G (ddhOracle (gapDHDef G)) (G.pub k) s t = decide (ev G k s = ev G k t) := by
  rcases s with w | E <;> rcases t with w' | E'
  · rfl
  · simp only [symEq, ddhOracle_pub, ev]
    exact decide_eq_decide.mpr Iff.rfl
  · simp only [symEq, ddhOracle_pub, ev]
    exact decide_eq_decide.mpr eq_comm
  · simp only [symEq, ddhOracle_pub, ev]
    refine decide_eq_decide.mpr ?_
    simp only [G.exp_eq, G.mul_eq, DHGroup.dlog_pub, G.pub.injective.eq_iff]
    constructor <;> intro h <;> linear_combination -h

/-- **Correctness of the symbolic equality of inputs.** -/
theorem inpEq_ddh (ik spk : S) (i j : Inp (W ⊕ W)) :
    inpEq G (ddhOracle (gapDHDef G)) (G.pub ik) (G.pub spk) i j =
      decide (interp G ik spk i = interp G ik spk j) := by
  simp only [inpEq, symEq_ddh, interp, Inp.mk.injEq, Bool.decide_and, Bool.and_assoc]

/-- **Correctness of the symbolic lookup.** -/
theorem slookup_ddh (ik spk : S) (j : Inp (W ⊕ W)) (tb : List (Inp (W ⊕ W) × K)) :
    slookup G (ddhOracle (gapDHDef G)) (G.pub ik) (G.pub spk) j tb =
      (tb.map (interpE G ik spk)).lookup (interp G ik spk j) := by
  induction tb with
  | nil => rfl
  | cons p tb ih =>
    rw [slookup, inpEq_ddh, List.map_cons, lookup_cons, ih]
    simp only [interpE, decide_eq_true_eq]
    exact if_congr Iff.rfl rfl rfl

/-- **Correctness of the symbolic key derivation.** -/
theorem sroDet_ddh (ik spk : S) (tb : List (Inp (W ⊕ W) × K)) (j : Inp (W ⊕ W)) (k : K) :
    roDet (tb.map (interpE G ik spk)) (interp G ik spk j) k =
      ((sroDet G (ddhOracle (gapDHDef G)) (G.pub ik) (G.pub spk) tb j k).1,
        (sroDet G (ddhOracle (gapDHDef G)) (G.pub ik) (G.pub spk) tb j k).2.map
          (interpE G ik spk)) := by
  unfold sroDet
  rw [slookup_ddh]
  cases h : (tb.map (interpE G ik spk)).lookup (interp G ik spk j) with
  | some v => simp only [roDet, h]
  | none => simp only [roDet, h, List.map_cons, interpE]

end Sym

/-! ## The world of the reduction -/

/-- The state of the simulator in the world of the reduction: its copy of the real state with a
table of symbolic inputs and the draws of the long-term secrets, its symbolic recorded inputs,
and its phase. -/
abbrev RSim (S W K : Type) := RSt S (W ⊕ W) K × (Inst → Option (Inp (W ⊕ W))) × Phase S W K

section Red

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W) (a b : PartyId) (O : W → W → W → Bool) (X Y : W)

/-- The draw of the identity secret of `a`, the offset of `ik_a` from the challenge exponent. -/
def off1 (rs : RSt S (W ⊕ W) K) : S := ((rs.lt a).map Prod.fst).getD 0

/-- The draw of the signed-prekey secret of `b`, the offset of `spk_b` from the challenge
exponent. -/
def off2 (rs : RSt S (W ⊕ W) K) : S := ((rs.lt b).map Prod.snd).getD 0

/-- The public identity key of `a`: `X · g^u` for the draw `u`. -/
def keyA (rs : RSt S (W ⊕ W) K) : W := G.mul X (G.pub (off1 a rs))

/-- The public signed prekey of `b`: `Y · g^v` for the draw `v`. -/
def keyB (rs : RSt S (W ⊕ W) K) : W := G.mul Y (G.pub (off2 b rs))

/-- The public identity key of the party `p` with the drawn pair `l`. -/
def pubIK (p : PartyId) (l : S × S) : W := if p = a then G.mul X (G.pub l.1) else G.pub l.1

/-- The public signed prekey of the party `p` with the drawn pair `l`. -/
def pubSPK (p : PartyId) (l : S × S) : W := if p = b then G.mul Y (G.pub l.2) else G.pub l.2

/-- The symbolic input of the initiator `p` with the drawn pair `la` and ephemeral secret `ek`,
for the responder `q` with the drawn pair `lb` and one-time prekey `opk`: `DH1 = SPK_q^{ik_p}`
is symbolic when `p` is `a`. -/
def aliceS (sid : SessionId) (p q : PartyId) (la lb : S × S) (ek opk : S) : Inp (W ⊕ W) :=
  ⟨sid, p, q,
    if p = a then .inr (pubSPK G b Y q lb) else .inl (G.exp (pubSPK G b Y q lb) la.1),
    .inl (G.exp (pubIK G a X q lb) ek), .inl (G.exp (pubSPK G b Y q lb) ek),
    .inl (G.exp (G.pub opk) ek)⟩

/-- The symbolic input of the responder `q` with the drawn pair `lq` and one-time prekey `opk`,
for the initiator `p` with the drawn pair `lp`, on the ephemeral public key `E`: `DH1` is
symbolic for the pair `(a, b)`, `DH2 = E^{ik_q}` when `q` is `a`, `DH3 = E^{spk_q}` when `q` is
`b`. -/
def bobS (sid : SessionId) (p q : PartyId) (E : W) (lq lp : S × S) (opk : S) : Inp (W ⊕ W) :=
  ⟨sid, p, q,
    if q = b then (if p = a then .inr (pubSPK G b Y q lq) else .inl (G.exp (pubSPK G b Y q lq) lp.1))
      else .inl (G.exp (pubIK G a X p lp) lq.2),
    if q = a then .inr E else .inl (G.exp E lq.1),
    if q = b then .inr E else .inl (G.exp E lq.2),
    .inl (G.exp E opk)⟩

/-- The delivery of `deliverD` on the symbolic copy: the lookup in the table and the comparison
with the partner's input are symbolic. -/
def deliverR (rs : RSt S (W ⊕ W) K) (inp : Inst → Option (Inp (W ⊕ W))) (x : Inst) (r : Rec K)
    (ip : Inp (W ⊕ W)) (k : K) : RSim S W K × Dec S W K :=
  if Exposed rs.st x r then
    ((keyed rs x r (sroDet G O (keyA G a X rs) (keyB G b Y rs) rs.ro ip k).1
        (sroDet G O (keyA G a X rs) (keyB G b Y rs) rs.ro ip k).2,
        Function.update inp x (some ip), .out .ack),
      .inl (.inr (.newKey x.1 x.2 (sroDet G O (keyA G a X rs) (keyB G b Y rs) rs.ro ip k).1)))
  else
    ((keyed rs x r default rs.ro, Function.update inp x (some ip), .out .ack),
      .inl (.inr (if (inp (x.1, r.peer)).all (fun j => inpEq G O (keyA G a X rs) (keyB G b Y rs) j ip)
        then .newKey x.1 x.2 default else .newKeyUnlinked x.1 x.2 default)))

/-- `complete` in the world of the reduction. -/
def completeR (s : RSim S W K) (x : Inst) (r : Draw S K) : RSim S W K × Dec S W K :=
  match s.1.st.recs x, s.1.eph x with
  | some rc, some ek =>
    match opkOf s.1 x.1 rc.peer with
    | some opk =>
      if rc.role = .initiator ∧ rc.key.isNone then
        deliverR G a b O X Y (ltD (ltD s.1 x.2 r.2.1).2 rc.peer r.2.2.1).2 s.2.1 x rc
          (aliceS G a b X Y x.1 x.2 rc.peer (ltD s.1 x.2 r.2.1).1
            (ltD (ltD s.1 x.2 r.2.1).2 rc.peer r.2.2.1).1 ek opk) r.2.2.2
      else ((s.1, s.2.1, .fwd), .inr (.inr .ack))
    | none => ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | _, _ => ((s.1, s.2.1, .fwd), .inr (.inr .ack))

/-- `send` in the world of the reduction. -/
def sendR (s : RSim S W K) (x : Inst) (e : W) (r : Draw S K) : RSim S W K × Dec S W K :=
  match s.1.st.recs x, s.1.eph x with
  | some rc, some opk =>
    if rc.role = .responder ∧ rc.key.isNone then
      deliverR G a b O X Y (ltD (ltD s.1 x.2 r.2.1).2 rc.peer r.2.2.1).2 s.2.1 x rc
        (bobS G a b X Y x.1 rc.peer x.2 e (ltD s.1 x.2 r.2.1).1
          (ltD (ltD s.1 x.2 r.2.1).2 rc.peer r.2.2.1).1 opk) r.2.2.2
    else ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | _, _ => ((s.1, s.2.1, .fwd), .inr (.inr .ack))

/-- A symbolic input with known values. -/
def ofInp (x : Inp W) : Inp (W ⊕ W) := ⟨x.sid, x.ini, x.res, .inl x.dh1, .inl x.dh2, .inl x.dh3,
  .inl x.dh4⟩

/-- **The start of the simulator in the world of the reduction**, with the draw `r`: the start
`simStartD` of the simulator, with the identity key of `a` and the signed prekey of `b` read
from the challenge and the draws, and the inputs of the key derivation symbolic. -/
def startR (s : RSim S W K) (e : OEv W) (r : Draw S K) : RSim S W K × Dec S W K :=
  match e with
  | .inl (.newSession sid pid peer role) =>
    if (s.1.st.recs (sid, pid)).isNone then
      (({ s.1 with st := addSession s.1.st (sid, pid) peer role,
                   eph := Function.update s.1.eph (sid, pid) (some r.1) }, s.2.1, .fwd),
        .inl (.inl (.newSession sid pid peer role)))
    else ((s.1, s.2.1, .fwd), .inl (.inl (.newSession sid pid peer role)))
  | .inl (.getKey sid pid) => ((s.1, s.2.1, .fwd), .inl (.inl (.getKey sid pid)))
  | .inr .idle => ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | .inr .poll => (({ s.1 with st := (pollStep s.1.st).1 }, s.2.1, .fwd),
      .inr (.inr (.notice (pollStep s.1.st).2)))
  | .inr (.pub pid) =>
    (((ltD s.1 pid r.2.1).2, s.2.1, .fwd),
      .inr (.inr (.pub (pubIK G a X pid (ltD s.1 pid r.2.1).1)
        (pubSPK G b Y pid (ltD s.1 pid r.2.1).1))))
  | .inr (.ephPub sid pid) =>
    ((s.1, s.2.1, .fwd), .inr (.inr (.eph ((s.1.eph (sid, pid)).map G.pub))))
  | .inr (.corrupt pid) =>
    if Named s.1.st pid then ((s.1, s.2.1, .fwd), .inr (.inr (.secret none))) else
      (({ (ltD s.1 pid r.2.1).2 with st := corruptStep (ltD s.1 pid r.2.1).2.st pid }, s.2.1,
          .out (.secret (some (ltD s.1 pid r.2.1).1))), .inl (.inr (.corrupt pid)))
  | .inr (.complete sid pid) => completeR G a b O X Y s (sid, pid) r
  | .inr (.send sid pid e) => sendR G a b O X Y s (sid, pid) e r
  | .inr (.kdf x) =>
    (({ s.1 with ro := (sroDet G O (keyA G a X s.1) (keyB G b Y s.1) s.1.ro (ofInp x)
        r.2.2.2).2 }, s.2.1, .fwd),
      .inr (.inr (.hash (sroDet G O (keyA G a X s.1) (keyB G b Y s.1) s.1.ro (ofInp x)
        r.2.2.2).1)))

/-- The finish of the simulator in the world of the reduction. -/
def finR (s : RSim S W K) (o : FOut K) : RSim S W K × OOut S W K :=
  ((s.1, s.2.1, .fwd), simOut s.2.2 o)

/-- **A step of the world of the reduction** with the draw `r = (r₀, kf)`: the start reads
`r₀` and `F_AKE` reads `kf`, as in `simWorldD`. -/
def stepR (t : RSim S W K × St K) (e : OEv W) (r : Draw S K × K) :
    (RSim S W K × St K) × OOut S W K :=
  (((drive0D fStepD finR (startR G a b O X Y t.1 e r.1).1 (startR G a b O X Y t.1 e r.1).2
      t.2 r.2).1,
    (drive0D fStepD finR (startR G a b O X Y t.1 e r.1).1 (startR G a b O X Y t.1 e r.1).2
      t.2 r.2).2.1),
    (drive0D fStepD finR (startR G a b O X Y t.1 e r.1).1 (startR G a b O X Y t.1 e r.1).2
      t.2 r.2).2.2)

/-- The oracle of the world of the reduction. -/
noncomputable def oracleR (t : RSim S W K × St K) (e : OEv W) :
    PMF (OOut S W K × (RSim S W K × St K)) :=
  (PMF.uniformFintype (Draw S K × K)).map fun r => (stepR G a b O X Y t e r).swap

/-- The first `DH1` of an input of the table with initiator `a` and responder `b` that the
decision oracle accepts as the Diffie–Hellman value of the keys of `a` and `b`. -/
def hitR (rs : RSt S (W ⊕ W) K) : Option W :=
  rs.ro.findSome? fun p =>
    if p.1.ini = a ∧ p.1.res = b then
      match p.1.dh1 with
      | .inl w => if O (keyA G a X rs) (keyB G b Y rs) w then some w else none
      | .inr _ => none
    else none

/-- **The output of the reduction** on its final state: an accepted `DH1 = g^{(x+u)(y+v)}`,
divided by `X^v · Y^u · g^{uv}`, or the unit when there is none. -/
def extractR (rs : RSt S (W ⊕ W) K) : W :=
  match hitR G a b O X Y rs with
  | some w => G.mul w (G.exp (G.mul (G.mul (G.exp X (off2 b rs)) (G.exp Y (off1 a rs)))
      (G.pub (off1 a rs * off2 b rs))) (-1))
  | none => G.pub 0

/-- The initial state of the world of the reduction. -/
def rInitR : RSim S W K × St K :=
  ((⟨initSt, fun _ => none, fun _ => none, []⟩, fun _ => none, .fwd), initSt)

/-- The answer of the world of the reduction to the query `e` as a program: one draw. -/
noncomputable def implR (t : RSim S W K × St K) (e : OEv W) :
    OracleAdv Empty Empty (OOut S W K × (RSim S W K × St K)) :=
  .rand (PMF.uniformFintype (Draw S K × K)) fun r =>
    .ret ((stepR G a b O X Y t e r).2, (stepR G a b O X Y t e r).1)

/-- **The reduction as a program**: the oracle adversary `B` run against the world of the
reduction, followed by the extraction from the final state. -/
noncomputable def redTree (B : OracleAdv (OEv W) (OOut S W K) Bool) : OracleAdv Empty Empty W :=
  (OracleAdv.simulate (implR G a b O X Y) B rInitR).bind fun p => .ret (extractR G a b O X Y p.2.1.1)

/-- The output distribution of the reduction. -/
noncomputable def redPMF (B : OracleAdv (OEv W) (OOut S W K) Bool) : PMF W :=
  (OracleAdv.run (fun (_ : Unit) (q : Empty) => q.elim) (redTree G a b O X Y B) ()).map Prod.fst

end Red

/-- **The gap Diffie–Hellman reduction** for the pair `(a, b)`: on the challenge `(X, Y)` with
the decision oracle `O`, it runs the oracle adversary `B` against the world of the reduction and
outputs `extractR`. -/
noncomputable def gdhRed {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
    [Nonempty K] [Inhabited K] (G : DHGroup S W) (a b : PartyId)
    (B : OracleAdv (OEv W) (OOut S W K) Bool) : GapDH_Adversary W :=
  fun O X Y => liftPMF (redPMF G a b O X Y B)

/-! ## The simulated world with shifted draws -/

section Shift

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W) (a b : PartyId) (x y : S)

/-- The long-term secrets of the party `p` from the drawn pair `l`: the identity secret of `a` is
shifted by `x` and the signed-prekey secret of `b` by `y`. -/
def sh (p : PartyId) (l : S × S) : S × S :=
  (if p = a then x + l.1 else l.1, if p = b then y + l.2 else l.2)

/-- `sh` as a bijection of the pairs. -/
def shEquiv (p : PartyId) : (S × S) ≃ (S × S) where
  toFun := sh a b x y p
  invFun := sh a b (-x) (-y) p
  left_inv l := by
    simp only [sh]
    ext <;> split_ifs <;> simp
  right_inv l := by
    simp only [sh]
    ext <;> split_ifs <;> simp

/-- The shift of an optional party: the identity without a party. -/
def shO : Option PartyId → (S × S) ≃ (S × S)
  | none => Equiv.refl _
  | some p => shEquiv a b x y p

/-- The party whose long-term secrets an event draws first: the party of `pub`, `corrupt`,
`complete` and `send`. -/
def ev1 : OEv W → Option PartyId
  | .inr (.pub p) | .inr (.corrupt p) | .inr (.complete _ p) | .inr (.send _ p _) => some p
  | _ => none

/-- The party whose long-term secrets an event draws second: the peer of the session of
`complete` and `send`. -/
def ev2 (s : SimSt S W K) : OEv W → Option PartyId
  | .inr (.complete sid p) | .inr (.send sid p _) => (s.1.st.recs (sid, p)).map Rec.peer
  | _ => none

/-- The shifted draw of a step from the state `s` on the event `e`. -/
def transD (s : SimSt S W K) (e : OEv W) : Draw S K ≃ Draw S K :=
  Equiv.prodCongr (Equiv.refl S) (Equiv.prodCongr (shO a b x y (ev1 e))
    (Equiv.prodCongr (shO a b x y (ev2 s e)) (Equiv.refl K)))

/-- The shifted draw of a step of the simulated world. -/
def transW (t : SimSt S W K × St K) (e : OEv W) : (Draw S K × K) ≃ (Draw S K × K) :=
  Equiv.prodCongr (transD a b x y t.1 e) (Equiv.refl K)

/-- **The simulated world with shifted draws is the simulated world**: the oracle of `simGame G`
is the image of a uniform draw under `simWorldD` at the shifted draw. -/
theorem simGame_oracle_eq_trans (t : SimSt S W K × St K) (e : OEv W) :
    (simGame G).oracle () t e = (PMF.uniformFintype (Draw S K × K)).map
      fun r => (simWorldD G t e (transW a b x y t e r)).swap := by
  rw [simGame_oracle_eq]
  conv_lhs => rw [← PMF.uniformFintype_map_equiv (transW a b x y t e), PMF.map_comp]
  rfl

end Shift

/-! ## The coupling of the simulated world and the world of the reduction -/

section Coupling

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W) (a b : PartyId) (x y : S)

/-- The symbols of a symbolic input name only drawn secrets: `DH1` and `DH2` are known while `a`
has no long-term secrets, and `DH3` while `b` has none. -/
def SymOk (lt : PartyId → Option (S × S)) (i : Inp (W ⊕ W)) : Prop :=
  (lt a = none → i.dh1.isLeft = true ∧ i.dh2.isLeft = true) ∧ (lt b = none → i.dh3.isLeft = true)

/-- **The coupling relation** between a state `s₁` of the simulator with shifted draws and a
state `s₂` of the simulator in the world of the reduction: equal records, corruptions, notices,
session secrets and phases; the long-term secrets of `s₁` are the shifted draws of `s₂`; the
tables and the recorded inputs of `s₁` are the values of the symbolic ones of `s₂` at
`ik_a = x + u` and `spk_b = y + v`; the symbols name drawn secrets; the inputs of the table with
initiator `a` and responder `b` have a known `DH1`; the records are fresh; `a` and `b` are
uncorrupt. -/
structure RelC (rs₁ : RSt S W K) (inp₁ : Inst → Option (Inp W)) (ph₁ : Phase S W K)
    (rs₂ : RSt S (W ⊕ W) K) (inp₂ : Inst → Option (Inp (W ⊕ W))) (ph₂ : Phase S W K) : Prop where
  st : rs₁.st = rs₂.st
  eph : rs₁.eph = rs₂.eph
  lt : ∀ q, rs₁.lt q = (rs₂.lt q).map (sh a b x y q)
  ro : rs₁.ro = rs₂.ro.map (interpE G (x + off1 a rs₂) (y + off2 b rs₂))
  inp : ∀ z, inp₁ z = (inp₂ z).map (interp G (x + off1 a rs₂) (y + off2 b rs₂))
  ph : ph₁ = ph₂
  symRo : ∀ p ∈ rs₂.ro, SymOk a b rs₂.lt p.1
  symInp : ∀ z i, inp₂ z = some i → SymOk a b rs₂.lt i
  abL : ∀ p ∈ rs₂.ro, p.1.ini = a → p.1.res = b → p.1.dh1.isLeft = true
  fresh : ∀ z r, rs₂.st.recs z = some r → r.status = .fresh
  uncA : rs₂.st.corrupt a = false
  uncB : rs₂.st.corrupt b = false

/-- The coupling relation on the states of the simulators. -/
def Rel (s₁ : SimSt S W K) (s₂ : RSim S W K) : Prop :=
  RelC G a b x y s₁.1 s₁.2.1 s₁.2.2 s₂.1 s₂.2.1 s₂.2.2

/-- The parties `a` and `b`: one of them is corrupt in the simulator's copy. -/
def Stop (s : SimSt S W K) : Prop := s.1.st.corrupt a = true ∨ s.1.st.corrupt b = true

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The public identity key of the reduction is the public value of the shifted secret. -/
theorem pubIK_pub (p : PartyId) (l : S × S) :
    pubIK G a (G.pub x) p l = G.pub (sh a b x y p l).1 := by
  unfold pubIK sh
  split_ifs <;> simp [G.mul_pub]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The public signed prekey of the reduction is the public value of the shifted secret. -/
theorem pubSPK_pub (p : PartyId) (l : S × S) :
    pubSPK G b (G.pub y) p l = G.pub (sh a b x y p l).2 := by
  unfold pubSPK sh
  split_ifs <;> simp [G.mul_pub]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem keyA_pub (rs : RSt S (W ⊕ W) K) : keyA G a (G.pub x) rs = G.pub (x + off1 a rs) := by
  simp only [keyA, G.mul_pub]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem keyB_pub (rs : RSt S (W ⊕ W) K) : keyB G b (G.pub y) rs = G.pub (y + off2 b rs) := by
  simp only [keyB, G.mul_pub]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- A known value does not depend on the exponent. -/
theorem ev_of_isLeft {s : W ⊕ W} (h : s.isLeft = true) (k k' : S) : ev G k s = ev G k' s := by
  rcases s with w | E
  · rfl
  · cases h

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- `SymOk` holds for larger sets of drawn secrets. -/
theorem SymOk.mono {lt lt' : PartyId → Option (S × S)} {i : Inp (W ⊕ W)}
    (h : ∀ q v, lt q = some v → lt' q = some v) (hs : SymOk a b lt i) : SymOk a b lt' i := by
  refine ⟨fun ha => hs.1 ?_, fun hb => hs.2 ?_⟩
  · cases hq : lt a with
    | none => rfl
    | some v => rw [h a v hq] at ha; cases ha
  · cases hq : lt b with
    | none => rfl
    | some v => rw [h b v hq] at hb; cases hb

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The value of a symbolic input whose symbols name drawn secrets does not change when more
secrets are drawn. -/
theorem interp_stable {rs rs' : RSt S (W ⊕ W) K} (h : ∀ q v, rs.lt q = some v → rs'.lt q = some v)
    {i : Inp (W ⊕ W)} (hs : SymOk a b rs.lt i) :
    interp G (x + off1 a rs') (y + off2 b rs') i = interp G (x + off1 a rs) (y + off2 b rs) i := by
  have h1 : ev G (x + off1 a rs') i.dh1 = ev G (x + off1 a rs) i.dh1 ∧
      ev G (x + off1 a rs') i.dh2 = ev G (x + off1 a rs) i.dh2 := by
    cases hq : rs.lt a with
    | none => exact ⟨ev_of_isLeft G (hs.1 hq).1 _ _, ev_of_isLeft G (hs.1 hq).2 _ _⟩
    | some v => simp only [off1, hq, h a v hq, and_self]
  have h2 : ev G (y + off2 b rs') i.dh3 = ev G (y + off2 b rs) i.dh3 := by
    cases hq : rs.lt b with
    | none => exact ev_of_isLeft G (hs.2 hq) _ _
    | some v => simp only [off2, hq, h b v hq]
  simp only [interp, h1, h2]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The table of values of a symbolic table whose symbols name drawn secrets does not change when
more secrets are drawn. -/
theorem map_interpE_stable {rs rs' : RSt S (W ⊕ W) K}
    (h : ∀ q v, rs.lt q = some v → rs'.lt q = some v) {tb : List (Inp (W ⊕ W) × K)}
    (hs : ∀ p ∈ tb, SymOk a b rs.lt p.1) :
    tb.map (interpE G (x + off1 a rs') (y + off2 b rs')) =
      tb.map (interpE G (x + off1 a rs) (y + off2 b rs)) :=
  List.map_congr_left fun p hp => by
    simp only [interpE, interp_stable G a b x y h (hs p hp)]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- **Drawing long-term secrets** on both sides: the simulator with the shifted draw obtains the
shifted secrets, and the relation is kept. -/
theorem rel_ltD {rs₁ : RSt S W K} {inp₁ : Inst → Option (Inp W)} {ph₁ : Phase S W K}
    {rs₂ : RSt S (W ⊕ W) K} {inp₂ : Inst → Option (Inp (W ⊕ W))} {ph₂ : Phase S W K}
    (h : RelC G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂) (p : PartyId) (l : S × S) :
    (ltD rs₁ p (sh a b x y p l)).1 = sh a b x y p (ltD rs₂ p l).1 ∧
      RelC G a b x y (ltD rs₁ p (sh a b x y p l)).2 inp₁ ph₁ (ltD rs₂ p l).2 inp₂ ph₂ := by
  have hl : rs₁.lt p = (rs₂.lt p).map (sh a b x y p) := h.lt p
  cases hq : rs₂.lt p with
  | some l' =>
    rw [hq] at hl
    simp only [ltD, hq, hl, Option.map_some, true_and]
    exact h
  | none =>
    rw [hq] at hl
    have hext : ∀ q v, rs₂.lt q = some v → (Function.update rs₂.lt p (some l)) q = some v := by
      intro q v hv
      have hne : q ≠ p := fun hc => by subst hc; rw [hq] at hv; cases hv
      rw [Function.update_of_ne hne, hv]
    have hext' : ∀ q v, rs₂.lt q = some v →
        ({ rs₂ with lt := Function.update rs₂.lt p (some l) } : RSt S (W ⊕ W) K).lt q = some v :=
      hext
    simp only [ltD, hq, hl, Option.map_none, true_and]
    refine ⟨h.st, h.eph, fun q => ?_, ?_, fun z => ?_, h.ph, fun e he =>
      (h.symRo e he).mono a b hext, fun z i hi => (h.symInp z i hi).mono a b hext, h.abL, h.fresh,
      h.uncA, h.uncB⟩
    · by_cases hqp : q = p
      · subst hqp; simp only [Function.update_self, Option.map_some]
      · simp only [Function.update_of_ne hqp]; exact h.lt q
    · exact h.ro.trans (map_interpE_stable G a b x y hext' h.symRo).symm
    · rw [h.inp z]
      cases hz : inp₂ z with
      | none => rfl
      | some i =>
        simp only [Option.map_some]
        exact congrArg some (interp_stable G a b x y hext' (h.symInp z i hz)).symm

omit [Fintype S] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The symbolic key derivation keeps its table or adds the new input. -/
theorem sroDet_snd (O : W → W → W → Bool) (ZA ZB : W) (tb : List (Inp (W ⊕ W) × K))
    (j : Inp (W ⊕ W)) (k : K) :
    (sroDet G O ZA ZB tb j k).2 = tb ∨ (sroDet G O ZA ZB tb j k).2 = (j, k) :: tb := by
  unfold sroDet
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- **A key on both sides**: the relation holds after the same record update, related tables and
the same recorded input. -/
theorem RelC.keyedR {rs₁ : RSt S W K} {inp₁ : Inst → Option (Inp W)} {ph₁ : Phase S W K}
    {rs₂ : RSt S (W ⊕ W) K} {inp₂ : Inst → Option (Inp (W ⊕ W))} {ph₂ : Phase S W K}
    (h : RelC G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂) {z : Inst} {rc : Rec K}
    (hrc : rs₂.st.recs z = some rc) (v : K) {ro₁ : List (Inp W × K)}
    {ro₂ : List (Inp (W ⊕ W) × K)}
    (hro : ro₁ = ro₂.map (interpE G (x + off1 a rs₂) (y + off2 b rs₂)))
    (hsym : ∀ p ∈ ro₂, SymOk a b rs₂.lt p.1)
    (hab : ∀ p ∈ ro₂, p.1.ini = a → p.1.res = b → p.1.dh1.isLeft = true)
    {ip : Inp (W ⊕ W)} (hs : SymOk a b rs₂.lt ip) (ph : Phase S W K) :
    RelC G a b x y (keyed rs₁ z rc v ro₁)
      (Function.update inp₁ z (some (interp G (x + off1 a rs₂) (y + off2 b rs₂) ip))) ph
      (keyed rs₂ z rc v ro₂) (Function.update inp₂ z (some ip)) ph := by
  refine ⟨by simp only [X3DHSquare.keyed]; rw [h.st], h.eph, h.lt, hro, fun z' => ?_, rfl, hsym, fun z' i hi => ?_,
    hab, fun z' r hr => ?_, h.uncA, h.uncB⟩
  · by_cases hz : z' = z
    · subst hz; simp only [Function.update_self, Option.map_some]; rfl
    · simp only [Function.update_of_ne hz]; exact h.inp z'
  · by_cases hz : z' = z
    · subst hz; simp only [Function.update_self, Option.some.injEq] at hi; subst hi; exact hs
    · simp only [Function.update_of_ne hz] at hi; exact h.symInp z' i hi
  · simp only [X3DHSquare.keyed, setRec] at hr
    by_cases hz : z' = z
    · subst hz
      simp only [Function.update_self, Option.some.injEq] at hr
      subst hr
      exact h.fresh _ rc hrc
    · simp only [Function.update_of_ne hz] at hr; exact h.fresh z' r hr

omit [Fintype K] [Nonempty K] in
/-- **The delivery of a key** on both sides gives the same decision and keeps the relation. -/
theorem rel_deliver {rs₁ : RSt S W K} {inp₁ : Inst → Option (Inp W)} {ph₁ : Phase S W K}
    {rs₂ : RSt S (W ⊕ W) K} {inp₂ : Inst → Option (Inp (W ⊕ W))} {ph₂ : Phase S W K}
    (h : RelC G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂) {z : Inst} {rc : Rec K}
    (hrc : rs₂.st.recs z = some rc) {ip : Inp (W ⊕ W)} (hs : SymOk a b rs₂.lt ip)
    (hsh : (ip.ini = z.2 ∧ ip.res = rc.peer) ∨ (ip.ini = rc.peer ∧ ip.res = z.2)) (k : K) :
    (deliverD rs₁ inp₁ z rc (interp G (x + off1 a rs₂) (y + off2 b rs₂) ip) k).2 =
        (deliverR G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) rs₂ inp₂ z rc ip k).2 ∧
      Rel G a b x y (deliverD rs₁ inp₁ z rc (interp G (x + off1 a rs₂) (y + off2 b rs₂) ip) k).1
        (deliverR G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) rs₂ inp₂ z rc ip k).1 := by
  have hE1 : Exposed rs₁.st z rc ↔ Exposed rs₂.st z rc := by rw [h.st]
  unfold deliverD deliverR
  rw [keyA_pub, keyB_pub]
  by_cases hE : Exposed rs₂.st z rc
  · simp only [hE, hE1, ↓reduceIte]
    rw [h.ro, sroDet_ddh]
    refine ⟨rfl, h.keyedR G a b x y hrc _ rfl ?_ ?_ hs _⟩
    · rcases sroDet_snd G (ddhOracle (gapDHDef G)) (G.pub (x + off1 a rs₂)) (G.pub (y + off2 b rs₂))
        rs₂.ro ip k with he | he <;> rw [he]
      · exact h.symRo
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hs
        · exact h.symRo p hp
    · rcases sroDet_snd G (ddhOracle (gapDHDef G)) (G.pub (x + off1 a rs₂)) (G.pub (y + off2 b rs₂))
        rs₂.ro ip k with he | he <;> rw [he]
      · exact h.abL
      · intro p hp hpa hpb
        rcases List.mem_cons.mp hp with rfl | hp
        · exfalso
          have hf := h.fresh z rc hrc
          have ha := h.uncA
          have hb := h.uncB
          simp only [Exposed] at hE
          rcases hsh with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> grind
        · exact h.abL p hp hpa hpb
  · simp only [hE, hE1, ↓reduceIte]
    refine ⟨?_, h.keyedR G a b x y hrc _ h.ro h.symRo h.abL hs _⟩
    rw [h.inp]
    cases inp₂ (z.1, rc.peer) with
    | none => rfl
    | some j => simp only [Option.map_some, Option.all_some, inpEq_ddh]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The relation does not depend on the phases beyond their equality. -/
theorem RelC.setPh {rs₁ : RSt S W K} {inp₁ : Inst → Option (Inp W)} {ph₁ : Phase S W K}
    {rs₂ : RSt S (W ⊕ W) K} {inp₂ : Inst → Option (Inp (W ⊕ W))} {ph₂ : Phase S W K}
    (h : RelC G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂) (ph : Phase S W K) :
    RelC G a b x y rs₁ inp₁ ph rs₂ inp₂ ph :=
  ⟨h.st, h.eph, h.lt, h.ro, h.inp, rfl, h.symRo, h.symInp, h.abL, h.fresh, h.uncA, h.uncB⟩

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- `opkOf` reads the records and the session secrets. -/
theorem opkOf_congr {W' : Type} {rs₁ : RSt S W K} {rs₂ : RSt S W' K} (hst : rs₁.st = rs₂.st)
    (heph : rs₁.eph = rs₂.eph) (sid : SessionId) (q : PartyId) :
    opkOf rs₁ sid q = opkOf rs₂ sid q := by
  simp only [opkOf, hst, heph]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
@[simp] theorem transD_apply (s : SimSt S W K) (e : OEv W) (r : Draw S K) :
    transD a b x y s e r = (r.1, shO a b x y (ev1 e) r.2.1, shO a b x y (ev2 s e) r.2.2.1,
      r.2.2.2) := rfl

omit [Fintype S] in
@[simp] theorem shO_some (p : PartyId) (l : S × S) : shO a b x y (some p) l = sh a b x y p l := rfl

omit [Fintype S] in
@[simp] theorem shO_none (l : S × S) : shO a b x y none l = l := rfl

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The value of the symbolic input of an initiator is its input in the simulator. -/
theorem aliceS_interp {rs : RSt S (W ⊕ W) K} {sid : SessionId} {p q : PartyId} {la lb : S × S}
    (hp : rs.lt p = some la) (ek opk : S) :
    interp G (x + off1 a rs) (y + off2 b rs) (aliceS G a b (G.pub x) (G.pub y) sid p q la lb ek opk) =
      aliceInp G sid p q (sh a b x y p la).1 ek (G.pub (sh a b x y q lb).1)
        (G.pub (sh a b x y q lb).2) (G.pub opk) := by
  unfold aliceS
  by_cases hpa : p = a
  · subst hpa
    simp only [interp, aliceInp, ev, pubIK_pub G p b x y, pubSPK_pub G p b x y, off1, hp, sh,
      ↓reduceIte, Option.map_some, Option.getD_some, Sum.elim_inl, id]
  · simp only [interp, aliceInp, ev, pubIK_pub G a b x y, pubSPK_pub G a b x y, sh, hpa,
      ↓reduceIte, Sum.elim_inl, id]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The value of the symbolic input of a responder is its input in the simulator. -/
theorem bobS_interp {rs : RSt S (W ⊕ W) K} {sid : SessionId} {p q : PartyId} {lq lp : S × S}
    (hq : rs.lt q = some lq) (hp : rs.lt p = some lp) (E : W) (opk : S) :
    interp G (x + off1 a rs) (y + off2 b rs) (bobS G a b (G.pub x) (G.pub y) sid p q E lq lp opk) =
      bobInp G sid p q (G.pub (sh a b x y p lp).1) E (sh a b x y q lq).1 (sh a b x y q lq).2 opk := by
  unfold bobS
  simp only [interp, bobInp, Inp.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_, rfl⟩
  · by_cases hqb : q = b
    · subst hqb
      by_cases hpa : p = a
      · subst hpa
        simp only [ev, pubSPK_pub G p q x y, off1, hp, sh, ↓reduceIte, Option.map_some,
          Option.getD_some, G.exp_pub, mul_comm]
      · simp only [ev, pubSPK_pub G a q x y, sh, hpa, ↓reduceIte, G.exp_pub, mul_comm]
    · simp only [ev, pubIK_pub G a b x y, sh, hqb, ↓reduceIte, G.exp_pub]
  · by_cases hqa : q = a
    · subst hqa; simp only [ev, off1, hq, sh, ↓reduceIte, Option.map_some, Option.getD_some]
    · simp only [ev, sh, hqa, ↓reduceIte]
  · by_cases hqb : q = b
    · subst hqb; simp only [ev, off2, hq, sh, ↓reduceIte, Option.map_some, Option.getD_some]
    · simp only [ev, sh, hqb, ↓reduceIte]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem aliceS_symOk {lt : PartyId → Option (S × S)} {sid : SessionId} {p q : PartyId}
    {la lb : S × S} (hp : lt p = some la) (ek opk : S) :
    SymOk a b lt (aliceS G a b (G.pub x) (G.pub y) sid p q la lb ek opk) := by
  refine ⟨fun ha => ⟨?_, rfl⟩, fun _ => rfl⟩
  have hpa : p ≠ a := fun hc => by subst hc; rw [hp] at ha; cases ha
  simp only [aliceS, hpa, ↓reduceIte, Sum.isLeft_inl]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem bobS_symOk {lt : PartyId → Option (S × S)} {sid : SessionId} {p q : PartyId}
    {lq lp : S × S} (hq : lt q = some lq) (hp : lt p = some lp) (E : W) (opk : S) :
    SymOk a b lt (bobS G a b (G.pub x) (G.pub y) sid p q E lq lp opk) := by
  refine ⟨fun ha => ⟨?_, ?_⟩, fun hb => ?_⟩
  · have hpa : p ≠ a := fun hc => by subst hc; rw [hp] at ha; cases ha
    simp only [bobS, hpa, ↓reduceIte]
    split_ifs <;> rfl
  · have hqa : q ≠ a := fun hc => by subst hc; rw [hq] at ha; cases ha
    simp only [bobS, hqa, ↓reduceIte, Sum.isLeft_inl]
  · have hqb : q ≠ b := fun hc => by subst hc; rw [hq] at hb; cases hb
    simp only [bobS, hqb, ↓reduceIte, Sum.isLeft_inl]

end Coupling

end CatCrypt.Crypto.AKE.X3DHSquareGDH
