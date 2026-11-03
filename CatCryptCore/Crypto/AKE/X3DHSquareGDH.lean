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

end CatCrypt.Crypto.AKE.X3DHSquareGDH
