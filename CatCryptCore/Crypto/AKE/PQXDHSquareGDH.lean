/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDHSquareHops
public import CatCryptCore.Crypto.AKE.X3DHSquareGDH

/-!
# The bad event of the PQXDH square under the gap Diffie–Hellman assumption

DOCSTRING
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.PQXDHSquareGDH

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.AKE.X3DHSquare (Inp aliceInp bobInp RSt ROut Named keyed ephPubOf opkOf
  rInit FEv FOut subView)
open CatCrypt.Crypto.AKE.X3DHSquareHops (drive0D Draw ltD fStepD skRec InpShape DhOk Exp
  ltD_lt_mono ltD_lt_self ltD_st ltD_eph ltD_ro pollStep_fst lookup_cons)
open CatCrypt.Crypto.AKE.X3DHSquareGDH (gapDHDef ddhOracle_pub cdh_pub AllQ toOuterMeasure_le_one
  run_flag_true_one run_flag_le_final run_flag_union_le run_flag_le_of_inv_on ev val4 interp
  symEq inpEq inpEq_ddh off1 off2 keyA keyB pubIK pubSPK aliceS bobS ofInp sh shEquiv shO SymOk
  pubIK_pub pubSPK_pub keyA_pub keyB_pub ev_of_isLeft SymOk.mono interp_stable aliceS_interp
  bobS_interp aliceS_symOk bobS_symOk interp_ofInp sh_of_ne stop_drive0D lookup_mem roDet_mem
  addSession_corrupt opkOf_congr)
open CatCrypt.Crypto.AKE.PQXDHSquare
open CatCrypt.Crypto.AKE.PQXDHSquareHops
open CatCrypt.Crypto.KEM.Games (Scheme)
open CatCrypt.Crypto.OracleGameUpToBad
open scoped ENNReal

/-! ## Bad flags under a coupling of draws from a distribution of the state -/

section FlagCoupling

variable {σ σ₁ σ₂ D R α Ω : Type}

/-- A flagged oracle that is the image of a draw. -/
theorem flagWhen_map (μ : σ → D → PMF Ω) (f : σ → D → Ω → R × σ) (bad : σ → Prop)
    [DecidablePred bad] (s : σ) (b : Bool) (d : D) :
    OracleAdv.flagWhen (fun _ _ x => bad x.2) (fun s d => (μ s d).map (f s d)) (s, b) d =
      (μ s d).map fun r => ((f s d r).1, ((f s d r).2, b || decide (bad (f s d r).2))) := by
  simp only [OracleAdv.flagWhen, PMF.map_comp]
  rfl

/-- A run from a dead state never sets the flag. -/
theorem run_flag_dead_zeroD (μ₁ : σ₁ → D → PMF Ω) (f₁ : σ₁ → D → Ω → R × σ₁)
    (Dead bad₁ : σ₁ → Prop) [DecidablePred bad₁] (hdead : ∀ s d r, Dead s → Dead (f₁ s d r).2)
    (hdb : ∀ s, Dead s → ¬ bad₁ s) (A : OracleAdv D R α) (s : σ₁) (hs : Dead s) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => bad₁ x.2)
      (fun s d => (μ₁ s d).map (f₁ s d))) A (s, false)).toOuterMeasure
        {y | y.2.2 = true} = 0 := by
  induction A generalizing s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.toOuterMeasure_pure_apply]
    simp
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    simp only [fun b => ih b s hs, mul_zero, tsum_zero]
  | query d k ih =>
    rw [OracleAdv.run_query, flagWhen_map, PMF.bind_map, PMF.toOuterMeasure_bind_apply]
    refine ENNReal.tsum_eq_zero.mpr fun r => ?_
    simp only [Function.comp_apply, Bool.false_or, decide_eq_false (hdb _ (hdead s d r hs))]
    rw [ih _ _ (hdead s d r hs), mul_zero]

/-- **A bad flag under a coupling of draws from a distribution of the state.** Let two oracles
be images of draws from distributions that agree on related states, and let every step from
related states either reach a dead state of the first oracle, from which its bad event never
occurs, or give the same answer and reach related states. When the bad event of the first oracle
on related states implies the bad event of the second, the first run sets its flag with at most
the probability with which the second does. -/
theorem flag_le_of_couplingD (μ₁ : σ₁ → D → PMF Ω) (μ₂ : σ₂ → D → PMF Ω)
    (f₁ : σ₁ → D → Ω → R × σ₁) (f₂ : σ₂ → D → Ω → R × σ₂)
    (Rel : σ₁ → σ₂ → Prop) (Dead bad₁ : σ₁ → Prop) (bad₂ : σ₂ → Prop) [DecidablePred bad₁]
    [DecidablePred bad₂] (hμ : ∀ s₁ s₂ d, Rel s₁ s₂ → μ₁ s₁ d = μ₂ s₂ d)
    (hdead : ∀ s d r, Dead s → Dead (f₁ s d r).2)
    (hdb : ∀ s, Dead s → ¬ bad₁ s) (hbad : ∀ s₁ s₂, Rel s₁ s₂ → bad₁ s₁ → bad₂ s₂)
    (hstep : ∀ s₁ s₂ d r, Rel s₁ s₂ → Dead (f₁ s₁ d r).2 ∨
      ((f₁ s₁ d r).1 = (f₂ s₂ d r).1 ∧ Rel (f₁ s₁ d r).2 (f₂ s₂ d r).2))
    (A : OracleAdv D R α) (s₁ : σ₁) (s₂ : σ₂) (h : Rel s₁ s₂) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => bad₁ x.2)
      (fun s d => (μ₁ s d).map (f₁ s d))) A (s₁, false)).toOuterMeasure
        {y | y.2.2 = true} ≤
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => bad₂ x.2)
      (fun s d => (μ₂ s d).map (f₂ s d))) A (s₂, false)).toOuterMeasure
        {y | y.2.2 = true} := by
  induction A generalizing s₁ s₂ with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.toOuterMeasure_pure_apply]
    simp
  | rand p k ih =>
    rw [OracleAdv.run_rand, OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply,
      PMF.toOuterMeasure_bind_apply]
    refine ENNReal.tsum_le_tsum fun b => ?_
    gcongr
    exact ih b s₁ s₂ h
  | query d k ih =>
    rw [OracleAdv.run_query, OracleAdv.run_query, flagWhen_map, flagWhen_map,
      PMF.bind_map, PMF.bind_map, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply,
      hμ s₁ s₂ d h]
    refine ENNReal.tsum_le_tsum fun r => ?_
    gcongr
    simp only [Function.comp_apply, Bool.false_or]
    by_cases hb : bad₁ (f₁ s₁ d r).2
    · rcases hstep s₁ s₂ d r h with hd | ⟨-, hr⟩
      · exact absurd hb (hdb _ hd)
      · rw [decide_eq_true hb, decide_eq_true (hbad _ _ hr hb), run_flag_true_one,
          run_flag_true_one]
    · rw [decide_eq_false hb]
      rcases hstep s₁ s₂ d r h with hd | ⟨ho, hr⟩
      · rw [run_flag_dead_zeroD μ₁ f₁ Dead bad₁ hdead hdb _ _ hd]
        exact zero_le
      · by_cases hb₂ : bad₂ (f₂ s₂ d r).2
        · rw [decide_eq_true hb₂, run_flag_true_one]
          exact toOuterMeasure_le_one _ _
        · rw [decide_eq_false hb₂, ho]
          exact ih _ _ _ hr

end FlagCoupling

/-! ## Symbolic inputs of the key derivation of PQXDH -/

section Sym

variable {S W K SS : Type} [Field S] [Fintype S] [SampleableType W] [DecidableEq SS]
  (G : DHGroup S W)

/-- The value of a symbolic input of PQXDH: the value of its input of X3DH and its shared
secret. -/
def pinterp (ik spk : S) (i : PInp (W ⊕ W) SS) : PInp W SS := (interp G ik spk i.1, i.2)

/-- A symbolic input of PQXDH as a table entry with its value. -/
def pinterpE (ik spk : S) (p : PInp (W ⊕ W) SS × K) : PInp W SS × K :=
  (pinterp G ik spk p.1, p.2)

variable (O : W → W → W → Bool)

/-- The equality of two symbolic inputs of PQXDH, decided with the decision oracle `O`. -/
def pinpEq (ZA ZB : W) (i j : PInp (W ⊕ W) SS) : Bool :=
  inpEq G O ZA ZB i.1 j.1 && decide (i.2 = j.2)

/-- The lookup of a symbolic input in a symbolic table of PQXDH. -/
def pslookup (ZA ZB : W) (j : PInp (W ⊕ W) SS) : List (PInp (W ⊕ W) SS × K) → Option K
  | [] => none
  | p :: tb => if pinpEq G O ZA ZB j p.1 then some p.2 else pslookup ZA ZB j tb

/-- The lazily sampled key derivation on a symbolic table of PQXDH, with the fresh value `k`. -/
def psroDet (ZA ZB : W) (tb : List (PInp (W ⊕ W) SS × K)) (j : PInp (W ⊕ W) SS) (k : K) :
    K × List (PInp (W ⊕ W) SS × K) :=
  match pslookup G O ZA ZB j tb with
  | some v => (v, tb)
  | none => (k, (j, k) :: tb)

/-- **Correctness of the symbolic equality of inputs of PQXDH.** -/
theorem pinpEq_ddh (ik spk : S) (i j : PInp (W ⊕ W) SS) :
    pinpEq G (ddhOracle (gapDHDef G)) (G.pub ik) (G.pub spk) i j =
      decide (pinterp G ik spk i = pinterp G ik spk j) := by
  simp only [pinpEq, inpEq_ddh, pinterp, Prod.mk.injEq, Bool.decide_and]

/-- **Correctness of the symbolic lookup of PQXDH.** -/
theorem pslookup_ddh (ik spk : S) (j : PInp (W ⊕ W) SS) (tb : List (PInp (W ⊕ W) SS × K)) :
    pslookup G (ddhOracle (gapDHDef G)) (G.pub ik) (G.pub spk) j tb =
      (tb.map (pinterpE G ik spk)).lookup (pinterp G ik spk j) := by
  induction tb with
  | nil => rfl
  | cons p tb ih =>
    rw [pslookup, pinpEq_ddh, List.map_cons, lookup_cons, ih]
    simp only [pinterpE, decide_eq_true_eq]
    exact if_congr Iff.rfl rfl rfl

/-- **Correctness of the symbolic key derivation of PQXDH.** -/
theorem psroDet_ddh (ik spk : S) (tb : List (PInp (W ⊕ W) SS × K)) (j : PInp (W ⊕ W) SS)
    (k : K) :
    roDet (tb.map (pinterpE G ik spk)) (pinterp G ik spk j) k =
      ((psroDet G (ddhOracle (gapDHDef G)) (G.pub ik) (G.pub spk) tb j k).1,
        (psroDet G (ddhOracle (gapDHDef G)) (G.pub ik) (G.pub spk) tb j k).2.map
          (pinterpE G ik spk)) := by
  unfold psroDet
  rw [pslookup_ddh]
  cases h : (tb.map (pinterpE G ik spk)).lookup (pinterp G ik spk j) with
  | some v => simp only [roDet, h]
  | none => simp only [roDet, h, List.map_cons, pinterpE]

omit [Fintype S] in
/-- The symbolic key derivation keeps its table or adds the new input. -/
theorem psroDet_snd (ZA ZB : W) (tb : List (PInp (W ⊕ W) SS × K)) (j : PInp (W ⊕ W) SS)
    (k : K) :
    (psroDet G O ZA ZB tb j k).2 = tb ∨ (psroDet G O ZA ZB tb j k).2 = (j, k) :: tb := by
  unfold psroDet
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

end Sym

/-! ## The world of the reduction -/

/-- The state of the simulator in the world of the reduction: its copy of the real state with a
table of symbolic inputs, its symbolic recorded inputs, and its phase. -/
abbrev RSimP (S W K PK SK SS C : Type) :=
  PSt S (W ⊕ W) K PK SK SS C × (Inst → Option (PInp (W ⊕ W) SS)) × Phase S W K PK C

section Red

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (G : DHGroup S W)
  (a b : PartyId) (O : W → W → W → Bool) (X Y : W)

/-- The delivery of `deliverD` on the symbolic copy: the lookup in the table and the comparison
with the partner's input are symbolic. -/
def deliverRP (rs : PSt S (W ⊕ W) K PK SK SS C) (inp : Inst → Option (PInp (W ⊕ W) SS))
    (x : Inst) (r : Rec K) (ip : PInp (W ⊕ W) SS) (k : K) :
    RSimP S W K PK SK SS C × Dec S W K PK C :=
  if Exposed rs.x.st x r then
    ((pKeyed rs x r (psroDet G O (keyA G a X rs.x) (keyB G b Y rs.x) rs.ro ip k).1
        (psroDet G O (keyA G a X rs.x) (keyB G b Y rs.x) rs.ro ip k).2,
        Function.update inp x (some ip), .out (.inl .ack)),
      .inl (.inr (.newKey x.1 x.2 (psroDet G O (keyA G a X rs.x) (keyB G b Y rs.x) rs.ro ip k).1)))
  else
    ((pKeyed rs x r default rs.ro, Function.update inp x (some ip), .out (.inl .ack)),
      .inl (.inr (if (inp (x.1, r.peer)).all
          (fun j => pinpEq G O (keyA G a X rs.x) (keyB G b Y rs.x) j ip)
        then .newKey x.1 x.2 default else .newKeyUnlinked x.1 x.2 default)))

/-- `complete` in the world of the reduction, with the draw `d` of X3DH and the encapsulation
`kc`. -/
def completeRP (s : RSimP S W K PK SK SS C) (x : Inst) (d : Draw S K) (kc : Option (SS × C)) :
    RSimP S W K PK SK SS C × Dec S W K PK C :=
  match s.1.x.st.recs x, s.1.x.eph x with
  | some rc, some ek =>
    match opkOf s.1.x x.1 rc.peer, pkOf s.1 x.1 rc.peer, kc with
    | some opk, some _, some kc =>
      if rc.role = .initiator ∧ rc.key.isNone then
        deliverRP G a b O X Y { s.1 with x := (ltD (ltD s.1.x x.2 d.2.1).2 rc.peer d.2.2.1).2,
                                         ct := Function.update s.1.ct x (some kc.2) } s.2.1 x rc
          (aliceS G a b X Y x.1 x.2 rc.peer (ltD s.1.x x.2 d.2.1).1
            (ltD (ltD s.1.x x.2 d.2.1).2 rc.peer d.2.2.1).1 ek opk, kc.1) d.2.2.2
      else ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
    | _, _, _ => ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
  | _, _ => ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))

/-- `send` in the world of the reduction, with the draw `d` of X3DH: the decapsulation under the
KEM key pair of the session, which the reduction drew itself. -/
def sendRP (s : RSimP S W K PK SK SS C) (x : Inst) (e : W) (c : C) (d : Draw S K) :
    RSimP S W K PK SK SS C × Dec S W K PK C :=
  match s.1.x.st.recs x, s.1.x.eph x, s.1.kem x with
  | some rc, some opk, some kp =>
    match P.decaps kp.2 c with
    | some ss =>
      if rc.role = .responder ∧ rc.key.isNone then
        deliverRP G a b O X Y { s.1 with x := (ltD (ltD s.1.x x.2 d.2.1).2 rc.peer d.2.2.1).2 }
          s.2.1 x rc
          (bobS G a b X Y x.1 rc.peer x.2 e (ltD s.1.x x.2 d.2.1).1
            (ltD (ltD s.1.x x.2 d.2.1).2 rc.peer d.2.2.1).1 opk, ss) d.2.2.2
      else ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
    | none => ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
  | _, _, _ => ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))

/-- **The start of the simulator in the world of the reduction**, with the draw `d`: the start
`simStartD` of the simulator, with the identity key of `a` and the signed prekey of `b` read
from the challenge and the draws, and the inputs of the key derivation symbolic. The KEM key
pairs and the encapsulations are drawn as in the simulator. -/
def startRP (s : RSimP S W K PK SK SS C) (e : OEv W SS C) (d : PDraw S K PK SK SS C) :
    RSimP S W K PK SK SS C × Dec S W K PK C :=
  match e with
  | .inl (.newSession sid pid peer role) =>
    if (s.1.x.st.recs (sid, pid)).isNone then
      if role = .responder then
        (({ s.1 with
            x := { s.1.x with st := addSession s.1.x.st (sid, pid) peer role,
                              eph := Function.update s.1.x.eph (sid, pid) (some d.1.1) },
            kem := Function.update s.1.kem (sid, pid) (some d.2.1) }, s.2.1, .fwd),
          .inl (.inl (.newSession sid pid peer role)))
      else
        (({ s.1 with
            x := { s.1.x with st := addSession s.1.x.st (sid, pid) peer role,
                              eph := Function.update s.1.x.eph (sid, pid) (some d.1.1) } },
            s.2.1, .fwd), .inl (.inl (.newSession sid pid peer role)))
    else ((s.1, s.2.1, .fwd), .inl (.inl (.newSession sid pid peer role)))
  | .inl (.getKey sid pid) => ((s.1, s.2.1, .fwd), .inl (.inl (.getKey sid pid)))
  | .inr .idle => ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
  | .inr .poll =>
    (({ s.1 with x := { s.1.x with st := (pollStep s.1.x.st).1 } }, s.2.1, .fwd),
      .inr (.inr (.inl (.notice (pollStep s.1.x.st).2))))
  | .inr (.pub pid) =>
    (({ s.1 with x := (ltD s.1.x pid d.1.2.1).2 }, s.2.1, .fwd),
      .inr (.inr (.inl (.pub (pubIK G a X pid (ltD s.1.x pid d.1.2.1).1)
        (pubSPK G b Y pid (ltD s.1.x pid d.1.2.1).1)))))
  | .inr (.ephPub sid pid) =>
    ((s.1, s.2.1, .fwd), .inr (.inr (.inl (.eph ((s.1.x.eph (sid, pid)).map G.pub)))))
  | .inr (.pqPub sid pid) =>
    ((s.1, s.2.1, .fwd), .inr (.inr (.inr (pkOf s.1 sid pid, s.1.ct (sid, pid)))))
  | .inr (.corrupt pid) =>
    if Named s.1.x.st pid then ((s.1, s.2.1, .fwd), .inr (.inr (.inl (.secret none)))) else
      (({ s.1 with x := { (ltD s.1.x pid d.1.2.1).2 with
                            st := corruptStep (ltD s.1.x pid d.1.2.1).2.st pid } }, s.2.1,
          .out (.inl (.secret (some (ltD s.1.x pid d.1.2.1).1)))), .inl (.inr (.corrupt pid)))
  | .inr (.complete sid pid) => completeRP G a b O X Y s (sid, pid) d.1 d.2.2
  | .inr (.send sid pid e c) => sendRP P G a b O X Y s (sid, pid) e c d.1
  | .inr (.kdf q) =>
    (({ s.1 with ro := (psroDet G O (keyA G a X s.1.x) (keyB G b Y s.1.x) s.1.ro
        (ofInp q.1, q.2) d.1.2.2.2).2 }, s.2.1, .fwd),
      .inr (.inr (.inl (.hash (psroDet G O (keyA G a X s.1.x) (keyB G b Y s.1.x) s.1.ro
        (ofInp q.1, q.2) d.1.2.2.2).1))))

/-- The finish of the simulator in the world of the reduction. -/
def finRP (s : RSimP S W K PK SK SS C) (o : FOut K) :
    RSimP S W K PK SK SS C × OOut S W K PK C :=
  ((s.1, s.2.1, .fwd), simOut s.2.2 o)

/-- **A step of the world of the reduction** with the draw `r = (d, kf)`: the start reads `d`
and `F_AKE` reads `kf`, as in `simWorldD`. -/
def stepRP (t : RSimP S W K PK SK SS C × St K) (e : OEv W SS C)
    (r : PDraw S K PK SK SS C × K) :
    (RSimP S W K PK SK SS C × St K) × OOut S W K PK C :=
  (((drive0D fStepD finRP (startRP P G a b O X Y t.1 e r.1).1
      (startRP P G a b O X Y t.1 e r.1).2 t.2 r.2).1,
    (drive0D fStepD finRP (startRP P G a b O X Y t.1 e r.1).1
      (startRP P G a b O X Y t.1 e r.1).2 t.2 r.2).2.1),
    (drive0D fStepD finRP (startRP P G a b O X Y t.1 e r.1).1
      (startRP P G a b O X Y t.1 e r.1).2 t.2 r.2).2.2)

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- The public key to which the event `e` encapsulates from the state `s` of the world of the
reduction, as `encPk`. -/
def encPkR (s : PSt S (W ⊕ W) K PK SK SS C) : OEv W SS C → Option PK
  | .inr (.complete sid pid) =>
    match s.x.st.recs (sid, pid) with
    | some r => pkOf s sid r.peer
    | none => none
  | _ => none

/-- The oracle of the world of the reduction: a draw of a step of the simulated world. -/
noncomputable def oracleRP (t : RSimP S W K PK SK SS C × St K) (e : OEv W SS C) :
    PMF (OOut S W K PK C × (RSimP S W K PK SK SS C × St K)) :=
  (simDist P (encPkR t.1.1 e)).map fun r => (stepRP P G a b O X Y t e r).swap

/-- The first `DH1` of an input of the table with initiator `a` and responder `b` that the
decision oracle accepts as the Diffie–Hellman value of the keys of `a` and `b`. -/
def hitRP (rs : PSt S (W ⊕ W) K PK SK SS C) : Option W :=
  rs.ro.findSome? fun p =>
    if p.1.1.ini = a ∧ p.1.1.res = b then
      match p.1.1.dh1 with
      | .inl w => if O (keyA G a X rs.x) (keyB G b Y rs.x) w then some w else none
      | .inr _ => none
    else none

/-- **The output of the reduction** on its final state: an accepted `DH1 = g^{(x+u)(y+v)}`,
divided by `X^v · Y^u · g^{uv}`, or the unit when there is none. -/
def extractRP (rs : PSt S (W ⊕ W) K PK SK SS C) : W :=
  match hitRP G a b O X Y rs with
  | some w => G.mul w (G.exp (G.mul (G.mul (G.exp X (off2 b rs.x)) (G.exp Y (off1 a rs.x)))
      (G.pub (off1 a rs.x * off2 b rs.x))) (-1))
  | none => G.pub 0

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- The initial state of the world of the reduction. -/
def rInitRP : RSimP S W K PK SK SS C × St K := ((pInit, fun _ => none, .fwd), initSt)

/-- The answer of the world of the reduction to the query `e` as a program: one draw. -/
noncomputable def implRP (t : RSimP S W K PK SK SS C × St K) (e : OEv W SS C) :
    OracleAdv Empty Empty (OOut S W K PK C × (RSimP S W K PK SK SS C × St K)) :=
  .rand (simDist P (encPkR t.1.1 e)) fun r =>
    .ret ((stepRP P G a b O X Y t e r).2, (stepRP P G a b O X Y t e r).1)

/-- **The reduction as a program**: the oracle adversary `B` run against the world of the
reduction, followed by the extraction from the final state. -/
noncomputable def redTreeP (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) :
    OracleAdv Empty Empty W :=
  (OracleAdv.simulate (implRP P G a b O X Y) B rInitRP).bind fun p =>
    .ret (extractRP G a b O X Y p.2.1.1)

/-- The output distribution of the reduction. -/
noncomputable def redPMFP (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) : PMF W :=
  (OracleAdv.run (fun (_ : Unit) (q : Empty) => q.elim) (redTreeP P G a b O X Y B) ()).map
    Prod.fst

end Red

/-- **The gap Diffie–Hellman reduction of PQXDH** for the pair `(a, b)`: on the challenge
`(X, Y)` with the decision oracle `O`, it runs the oracle adversary `B` against the world of the
reduction, which draws the KEM key pairs and the encapsulations itself, and outputs
`extractRP`. -/
noncomputable def pqGdhRed {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W]
    [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] (G : DHGroup S W)
    (P : Scheme PK SK SS C) (a b : PartyId) (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) :
    GapDH_Adversary W :=
  fun O X Y => liftPMF (redPMFP P G a b O X Y B)

/-! ## The simulated world with shifted draws -/

section Shift

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (G : DHGroup S W)
  (a b : PartyId) (x y : S)

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- The party whose long-term secrets an event draws first: the party of `pub`, `corrupt`,
`complete` and `send`. -/
def ev1P : OEv W SS C → Option PartyId
  | .inr (.pub p) | .inr (.corrupt p) | .inr (.complete _ p) | .inr (.send _ p _ _) => some p
  | _ => none

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- The party whose long-term secrets an event draws second: the peer of the session of
`complete` and `send`. -/
def ev2P (s : SimSt S W K PK SK SS C) : OEv W SS C → Option PartyId
  | .inr (.complete sid p) | .inr (.send sid p _ _) => (s.1.x.st.recs (sid, p)).map Rec.peer
  | _ => none

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- The shifted draw of X3DH of a step from the state `s` on the event `e`. -/
def transDP (s : SimSt S W K PK SK SS C) (e : OEv W SS C) : Draw S K ≃ Draw S K :=
  Equiv.prodCongr (Equiv.refl S) (Equiv.prodCongr (shO a b x y (ev1P e))
    (Equiv.prodCongr (shO a b x y (ev2P s e)) (Equiv.refl K)))

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- The shifted draw of a step: the draw of X3DH shifted, the KEM draws unchanged. -/
def transPD (s : SimSt S W K PK SK SS C) (e : OEv W SS C) :
    PDraw S K PK SK SS C ≃ PDraw S K PK SK SS C :=
  Equiv.prodCongr (transDP a b x y s e) (Equiv.refl _)

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- The shifted draw of a step of the simulated world. -/
def transWP (t : SimSt S W K PK SK SS C × St K) (e : OEv W SS C) :
    (PDraw S K PK SK SS C × K) ≃ (PDraw S K PK SK SS C × K) :=
  Equiv.prodCongr (transPD a b x y t.1 e) (Equiv.refl K)

omit [SampleableType W] [Inhabited K] [DecidableEq SS] in
/-- A bijection of the draws of X3DH leaves the distribution of a draw of the simulated world
unchanged. -/
theorem simDist_map_equiv (o : Option PK) (φ : Draw S K ≃ Draw S K) :
    (simDist P o).map (fun r => ((φ r.1.1, r.1.2), r.2)) = simDist (S := S) (K := K) P o := by
  have h : ∀ ψ : Draw S K → Draw S K, (simDist P o).map (fun r => ((ψ r.1.1, r.1.2), r.2)) =
      (PMF.uniformFintype (Draw S K)).bind fun r => P.keygen.bind fun kp =>
        (encD P o).bind fun kc => (PMF.uniformFintype K).map fun kf => ((ψ r, kp, kc), kf) := by
    intro ψ
    simp only [simDist, pDist, PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp,
      Function.comp_def]
  rw [h φ]
  calc _ = ((PMF.uniformFintype (Draw S K)).map φ).bind fun r => P.keygen.bind fun kp =>
        (encD P o).bind fun kc => (PMF.uniformFintype K).map fun kf =>
          (((r, kp, kc), kf) : PDraw S K PK SK SS C × K) := by
        rw [PMF.bind_map]; rfl
    _ = (simDist P o).map (fun r => ((id r.1.1, r.1.2), r.2)) := by
        rw [PMF.uniformFintype_map_equiv, h]; rfl
    _ = simDist P o := PMF.map_id _

/-- **The simulated world with shifted draws is the simulated world**: the oracle of
`simGame P G` is the image of a draw under `simWorldD` at the shifted draw. -/
theorem simGame_oracle_eq_transP (t : SimSt S W K PK SK SS C × St K) (e : OEv W SS C) :
    (simGame P G).oracle () t e = (simDist P (encPk t.1.1 e)).map
      fun r => (simWorldD P G t e (transWP a b x y t e r)).swap := by
  rw [simGame_oracle_eq]
  have h := simDist_map_equiv P (encPk t.1.1 e) (transDP a b x y t.1 e)
  calc _ = ((simDist P (encPk t.1.1 e)).map
        (fun r => ((transDP a b x y t.1 e r.1.1, r.1.2), r.2))).map
          (fun r => (simWorldD P G t e r).swap) := by rw [h]
    _ = _ := by rw [PMF.map_comp]; rfl

end Shift

/-! ## The coupling of the simulated world and the world of the reduction -/

section Coupling

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (G : DHGroup S W)
  (a b : PartyId) (x y : S)

/-- **The coupling relation** between a state of the simulator with shifted draws and a state of
the simulator in the world of the reduction: the relation of X3DH (equal records, corruptions,
notices, session secrets and phases; shifted long-term secrets; the tables and the recorded
inputs the values of the symbolic ones at `ik_a = x + u` and `spk_b = y + v`; symbols naming
drawn secrets; a known `DH1` for the pair `(a, b)`; fresh records; `a` and `b` uncorrupt), with
equal KEM key pairs and encapsulations. -/
structure RelCP (rs₁ : PSt S W K PK SK SS C) (inp₁ : Inst → Option (PInp W SS))
    (ph₁ : Phase S W K PK C) (rs₂ : PSt S (W ⊕ W) K PK SK SS C)
    (inp₂ : Inst → Option (PInp (W ⊕ W) SS)) (ph₂ : Phase S W K PK C) : Prop where
  st : rs₁.x.st = rs₂.x.st
  eph : rs₁.x.eph = rs₂.x.eph
  lt : ∀ q, rs₁.x.lt q = (rs₂.x.lt q).map (sh a b x y q)
  ro : rs₁.ro = rs₂.ro.map (pinterpE G (x + off1 a rs₂.x) (y + off2 b rs₂.x))
  inp : ∀ z, inp₁ z = (inp₂ z).map (pinterp G (x + off1 a rs₂.x) (y + off2 b rs₂.x))
  ph : ph₁ = ph₂
  kem : rs₁.kem = rs₂.kem
  ct : rs₁.ct = rs₂.ct
  symRo : ∀ p ∈ rs₂.ro, SymOk a b rs₂.x.lt p.1.1
  symInp : ∀ z i, inp₂ z = some i → SymOk a b rs₂.x.lt i.1
  abL : ∀ p ∈ rs₂.ro, p.1.1.ini = a → p.1.1.res = b → p.1.1.dh1.isLeft = true
  fresh : ∀ z r, rs₂.x.st.recs z = some r → r.status = .fresh
  uncA : rs₂.x.st.corrupt a = false
  uncB : rs₂.x.st.corrupt b = false

/-- The coupling relation on the states of the simulators. -/
def RelP (s₁ : SimSt S W K PK SK SS C) (s₂ : RSimP S W K PK SK SS C) : Prop :=
  RelCP G a b x y s₁.1 s₁.2.1 s₁.2.2 s₂.1 s₂.2.1 s₂.2.2

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- The parties `a` and `b`: one of them is corrupt in the simulator's copy. -/
def StopP (s : SimSt S W K PK SK SS C) : Prop :=
  s.1.x.st.corrupt a = true ∨ s.1.x.st.corrupt b = true

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- `pkOf` reads the KEM key pairs. -/
theorem pkOf_congr {W' : Type} {rs₁ : PSt S W K PK SK SS C} {rs₂ : PSt S W' K PK SK SS C}
    (h : rs₁.kem = rs₂.kem) (sid : SessionId) (q : PartyId) : pkOf rs₁ sid q = pkOf rs₂ sid q := by
  simp only [pkOf, h]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- The value of a symbolic input whose symbols name drawn secrets does not change when more
secrets are drawn. -/
theorem pinterp_stable {rs rs' : RSt S (W ⊕ W) K}
    (h : ∀ q v, rs.lt q = some v → rs'.lt q = some v) {i : PInp (W ⊕ W) SS}
    (hs : SymOk a b rs.lt i.1) :
    pinterp G (x + off1 a rs') (y + off2 b rs') i = pinterp G (x + off1 a rs) (y + off2 b rs) i := by
  simp only [pinterp, interp_stable G a b x y h hs]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- The table of values of a symbolic table whose symbols name drawn secrets does not change when
more secrets are drawn. -/
theorem map_pinterpE_stable {rs rs' : RSt S (W ⊕ W) K}
    (h : ∀ q v, rs.lt q = some v → rs'.lt q = some v) {tb : List (PInp (W ⊕ W) SS × K)}
    (hs : ∀ p ∈ tb, SymOk a b rs.lt p.1.1) :
    tb.map (pinterpE G (x + off1 a rs') (y + off2 b rs')) =
      tb.map (pinterpE G (x + off1 a rs) (y + off2 b rs)) :=
  List.map_congr_left fun p hp => by
    simp only [pinterpE, pinterp_stable G a b x y h (hs p hp)]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- **Drawing long-term secrets** on both sides: the simulator with the shifted draw obtains the
shifted secrets, and the relation is kept. -/
theorem rel_ltDP {rs₁ : PSt S W K PK SK SS C} {inp₁ : Inst → Option (PInp W SS)}
    {ph₁ : Phase S W K PK C} {rs₂ : PSt S (W ⊕ W) K PK SK SS C}
    {inp₂ : Inst → Option (PInp (W ⊕ W) SS)} {ph₂ : Phase S W K PK C}
    (h : RelCP G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂) (p : PartyId) (l : S × S) :
    (ltD rs₁.x p (sh a b x y p l)).1 = sh a b x y p (ltD rs₂.x p l).1 ∧
      RelCP G a b x y { rs₁ with x := (ltD rs₁.x p (sh a b x y p l)).2 } inp₁ ph₁
        { rs₂ with x := (ltD rs₂.x p l).2 } inp₂ ph₂ := by
  have hl : rs₁.x.lt p = (rs₂.x.lt p).map (sh a b x y p) := h.lt p
  cases hq : rs₂.x.lt p with
  | some l' =>
    rw [hq] at hl
    simp only [ltD, hq, hl, Option.map_some, true_and]
    exact h
  | none =>
    rw [hq] at hl
    have hext : ∀ q v, rs₂.x.lt q = some v →
        (Function.update rs₂.x.lt p (some l)) q = some v := by
      intro q v hv
      have hne : q ≠ p := fun hc => by subst hc; rw [hq] at hv; cases hv
      rw [Function.update_of_ne hne, hv]
    have hext' : ∀ q v, rs₂.x.lt q = some v →
        ({ rs₂.x with lt := Function.update rs₂.x.lt p (some l) } : RSt S (W ⊕ W) K).lt q =
          some v :=
      hext
    simp only [ltD, hq, hl, Option.map_none, true_and]
    refine ⟨h.st, h.eph, fun q => ?_, ?_, fun z => ?_, h.ph, h.kem, h.ct, fun e he =>
      (h.symRo e he).mono a b hext, fun z i hi => (h.symInp z i hi).mono a b hext, h.abL, h.fresh,
      h.uncA, h.uncB⟩
    · by_cases hqp : q = p
      · subst hqp; simp only [Function.update_self, Option.map_some]
      · simp only [Function.update_of_ne hqp]; exact h.lt q
    · exact h.ro.trans (map_pinterpE_stable G a b x y hext' h.symRo).symm
    · rw [h.inp z]
      cases hz : inp₂ z with
      | none => rfl
      | some i =>
        simp only [Option.map_some]
        exact congrArg some (pinterp_stable G a b x y hext' (h.symInp z i hz)).symm

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- **A key on both sides**: the relation holds after the same record update, related tables and
the same recorded input. -/
theorem RelCP.keyedR {rs₁ : PSt S W K PK SK SS C} {inp₁ : Inst → Option (PInp W SS)}
    {ph₁ : Phase S W K PK C} {rs₂ : PSt S (W ⊕ W) K PK SK SS C}
    {inp₂ : Inst → Option (PInp (W ⊕ W) SS)} {ph₂ : Phase S W K PK C}
    (h : RelCP G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂) {z : Inst} {rc : Rec K}
    (hrc : rs₂.x.st.recs z = some rc) (v : K) {ro₁ : List (PInp W SS × K)}
    {ro₂ : List (PInp (W ⊕ W) SS × K)}
    (hro : ro₁ = ro₂.map (pinterpE G (x + off1 a rs₂.x) (y + off2 b rs₂.x)))
    (hsym : ∀ p ∈ ro₂, SymOk a b rs₂.x.lt p.1.1)
    (hab : ∀ p ∈ ro₂, p.1.1.ini = a → p.1.1.res = b → p.1.1.dh1.isLeft = true)
    {ip : PInp (W ⊕ W) SS} (hs : SymOk a b rs₂.x.lt ip.1) (ph : Phase S W K PK C) :
    RelCP G a b x y (pKeyed rs₁ z rc v ro₁)
      (Function.update inp₁ z (some (pinterp G (x + off1 a rs₂.x) (y + off2 b rs₂.x) ip))) ph
      (pKeyed rs₂ z rc v ro₂) (Function.update inp₂ z (some ip)) ph := by
  refine ⟨by simp only [pKeyed, X3DHSquare.keyed]; rw [h.st], h.eph, h.lt, hro, fun z' => ?_, rfl,
    h.kem, h.ct, hsym, fun z' i hi => ?_, hab, fun z' r hr => ?_, h.uncA, h.uncB⟩
  · by_cases hz : z' = z
    · subst hz; simp only [Function.update_self, Option.map_some]; rfl
    · simp only [Function.update_of_ne hz]; exact h.inp z'
  · by_cases hz : z' = z
    · subst hz; simp only [Function.update_self, Option.some.injEq] at hi; subst hi; exact hs
    · simp only [Function.update_of_ne hz] at hi; exact h.symInp z' i hi
  · simp only [pKeyed, X3DHSquare.keyed, setRec] at hr
    by_cases hz : z' = z
    · subst hz
      simp only [Function.update_self, Option.some.injEq] at hr
      subst hr
      exact h.fresh _ rc hrc
    · simp only [Function.update_of_ne hz] at hr; exact h.fresh z' r hr

omit [Fintype K] [Nonempty K] in
/-- **The delivery of a key** on both sides gives the same decision and keeps the relation. -/
theorem rel_deliverP {rs₁ : PSt S W K PK SK SS C} {inp₁ : Inst → Option (PInp W SS)}
    {ph₁ : Phase S W K PK C} {rs₂ : PSt S (W ⊕ W) K PK SK SS C}
    {inp₂ : Inst → Option (PInp (W ⊕ W) SS)} {ph₂ : Phase S W K PK C}
    (h : RelCP G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂) {z : Inst} {rc : Rec K}
    (hrc : rs₂.x.st.recs z = some rc) {ip : PInp (W ⊕ W) SS} (hs : SymOk a b rs₂.x.lt ip.1)
    (hsh : (ip.1.ini = z.2 ∧ ip.1.res = rc.peer) ∨ (ip.1.ini = rc.peer ∧ ip.1.res = z.2))
    (k : K) :
    (deliverD rs₁ inp₁ z rc (pinterp G (x + off1 a rs₂.x) (y + off2 b rs₂.x) ip) k).2 =
        (deliverRP G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) rs₂ inp₂ z rc ip k).2 ∧
      RelP G a b x y
        (deliverD rs₁ inp₁ z rc (pinterp G (x + off1 a rs₂.x) (y + off2 b rs₂.x) ip) k).1
        (deliverRP G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) rs₂ inp₂ z rc ip k).1 := by
  have hE1 : Exposed rs₁.x.st z rc ↔ Exposed rs₂.x.st z rc := by rw [h.st]
  unfold deliverD deliverRP
  rw [keyA_pub, keyB_pub]
  by_cases hE : Exposed rs₂.x.st z rc
  · simp only [hE, hE1, ↓reduceIte]
    rw [h.ro, psroDet_ddh]
    refine ⟨rfl, h.keyedR G a b x y hrc _ rfl ?_ ?_ hs _⟩
    · rcases psroDet_snd G (ddhOracle (gapDHDef G)) (G.pub (x + off1 a rs₂.x))
        (G.pub (y + off2 b rs₂.x)) rs₂.ro ip k with he | he <;> rw [he]
      · exact h.symRo
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hs
        · exact h.symRo p hp
    · rcases psroDet_snd G (ddhOracle (gapDHDef G)) (G.pub (x + off1 a rs₂.x))
        (G.pub (y + off2 b rs₂.x)) rs₂.ro ip k with he | he <;> rw [he]
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
    | some j => simp only [Option.map_some, Option.all_some, pinpEq_ddh]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- The relation does not depend on the phases beyond their equality. -/
theorem RelCP.setPh {rs₁ : PSt S W K PK SK SS C} {inp₁ : Inst → Option (PInp W SS)}
    {ph₁ : Phase S W K PK C} {rs₂ : PSt S (W ⊕ W) K PK SK SS C}
    {inp₂ : Inst → Option (PInp (W ⊕ W) SS)} {ph₂ : Phase S W K PK C}
    (h : RelCP G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂) (ph : Phase S W K PK C) :
    RelCP G a b x y rs₁ inp₁ ph rs₂ inp₂ ph :=
  ⟨h.st, h.eph, h.lt, h.ro, h.inp, rfl, h.kem, h.ct, h.symRo, h.symInp, h.abL, h.fresh, h.uncA,
    h.uncB⟩

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- The relation after the same update of the encapsulations on both sides. -/
theorem RelCP.ctUpd {rs₁ : PSt S W K PK SK SS C} {inp₁ : Inst → Option (PInp W SS)}
    {ph₁ : Phase S W K PK C} {rs₂ : PSt S (W ⊕ W) K PK SK SS C}
    {inp₂ : Inst → Option (PInp (W ⊕ W) SS)} {ph₂ : Phase S W K PK C}
    (h : RelCP G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂) (ct : Inst → Option C) :
    RelCP G a b x y { rs₁ with ct := ct } inp₁ ph₁ { rs₂ with ct := ct } inp₂ ph₂ :=
  ⟨h.st, h.eph, h.lt, h.ro, h.inp, h.ph, h.kem, rfl, h.symRo, h.symInp, h.abL, h.fresh, h.uncA,
    h.uncB⟩

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- The KEM key pairs of the first state may be read from the second. -/
theorem RelCP.kemR {rs₁ : PSt S W K PK SK SS C} {inp₁ : Inst → Option (PInp W SS)}
    {ph₁ : Phase S W K PK C} {rs₂ : PSt S (W ⊕ W) K PK SK SS C}
    {inp₂ : Inst → Option (PInp (W ⊕ W) SS)} {ph₂ : Phase S W K PK C}
    (h : RelCP G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂) :
    RelCP G a b x y { rs₁ with kem := rs₂.kem } inp₁ ph₁ rs₂ inp₂ ph₂ :=
  ⟨h.st, h.eph, h.lt, h.ro, h.inp, h.ph, rfl, h.ct, h.symRo, h.symInp, h.abL, h.fresh, h.uncA,
    h.uncB⟩

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
@[simp] theorem transPD_apply (s : SimSt S W K PK SK SS C) (e : OEv W SS C)
    (d : PDraw S K PK SK SS C) :
    transPD a b x y s e d = ((d.1.1, shO a b x y (ev1P e) d.1.2.1, shO a b x y (ev2P s e) d.1.2.2.1,
      d.1.2.2.2), d.2) := rfl

omit [Fintype K] [Nonempty K] in
/-- **`complete` on both sides** gives the same decision and keeps the relation. -/
theorem rel_completeP {s₁ : SimSt S W K PK SK SS C} {s₂ : RSimP S W K PK SK SS C}
    (h : RelP G a b x y s₁ s₂) (sid : SessionId) (pid : PartyId) (d : Draw S K)
    (kc : Option (SS × C)) :
    (simCompleteD G s₁ (sid, pid) (transDP a b x y s₁ (.inr (.complete sid pid)) d) kc).2 =
        (completeRP G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ (sid, pid) d kc).2 ∧
      RelP G a b x y
        (simCompleteD G s₁ (sid, pid) (transDP a b x y s₁ (.inr (.complete sid pid)) d) kc).1
        (completeRP G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ (sid, pid) d kc).1 := by
  obtain ⟨rs₁, inp₁, ph₁⟩ := s₁
  obtain ⟨rs₂, inp₂, ph₂⟩ := s₂
  have h' : RelCP G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂ := h
  simp only [simCompleteD, completeRP, transDP, Equiv.prodCongr_apply, Equiv.coe_refl,
    Prod.map, id, ev1P, ev2P]
  rw [h'.st, h'.eph, h'.ct]
  simp only [opkOf_congr h'.st h'.eph, pkOf_congr h'.kem]
  cases hr : rs₂.x.st.recs (sid, pid) with
  | none => dsimp only; exact ⟨rfl, h'.setPh G a b x y _⟩
  | some rc =>
    cases he : rs₂.x.eph (sid, pid) with
    | none => dsimp only; exact ⟨rfl, h'.setPh G a b x y _⟩
    | some ek =>
      dsimp only
      cases ho : opkOf rs₂.x sid rc.peer with
      | none => dsimp only; exact ⟨rfl, h'.setPh G a b x y _⟩
      | some opk =>
        cases hk : pkOf rs₂ sid rc.peer with
        | none => dsimp only; exact ⟨rfl, h'.setPh G a b x y _⟩
        | some pk =>
          cases kc with
          | none => dsimp only; exact ⟨rfl, h'.setPh G a b x y _⟩
          | some kc =>
            dsimp only
            by_cases hc : rc.role = .initiator ∧ rc.key.isNone
            · simp only [hc, and_self, ↓reduceIte, Option.map_some, shO, shEquiv,
                Equiv.coe_fn_mk]
              obtain ⟨e₁, h₁⟩ := rel_ltDP G a b x y h' pid d.2.1
              obtain ⟨e₂, h₂⟩ := rel_ltDP G a b x y h₁ rc.peer d.2.2.1
              dsimp only at e₂ h₂
              rw [e₁, e₂]
              have hp : (ltD (ltD rs₂.x pid d.2.1).2 rc.peer d.2.2.1).2.lt pid =
                  some (ltD rs₂.x pid d.2.1).1 :=
                ltD_lt_mono _ _ _ _ _ (ltD_lt_self rs₂.x pid d.2.1)
              rw [← aliceS_interp G a b x y hp]
              exact rel_deliverP G a b x y (h₂.ctUpd G a b x y _) (z := (sid, pid)) (rc := rc)
                (ip := (aliceS G a b (G.pub x) (G.pub y) sid pid rc.peer (ltD rs₂.x pid d.2.1).1
                  (ltD (ltD rs₂.x pid d.2.1).2 rc.peer d.2.2.1).1 ek opk, kc.1))
                (by simp only [ltD_st, hr]) (aliceS_symOk G a b x y hp ek opk)
                (Or.inl ⟨rfl, rfl⟩) _
            · simp only [hc, ↓reduceIte, true_and]
              exact h'.setPh G a b x y _

omit [Fintype K] [Nonempty K] in
/-- **`send` on both sides** gives the same decision and keeps the relation. -/
theorem rel_sendP {s₁ : SimSt S W K PK SK SS C} {s₂ : RSimP S W K PK SK SS C}
    (h : RelP G a b x y s₁ s₂) (sid : SessionId) (pid : PartyId) (e : W) (c : C)
    (d : Draw S K) :
    (simSendD P G s₁ (sid, pid) e c (transDP a b x y s₁ (.inr (.send sid pid e c)) d)).2 =
        (sendRP P G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ (sid, pid) e c d).2 ∧
      RelP G a b x y
        (simSendD P G s₁ (sid, pid) e c (transDP a b x y s₁ (.inr (.send sid pid e c)) d)).1
        (sendRP P G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ (sid, pid) e c d).1 := by
  obtain ⟨rs₁, inp₁, ph₁⟩ := s₁
  obtain ⟨rs₂, inp₂, ph₂⟩ := s₂
  have h' : RelCP G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂ := h
  simp only [simSendD, sendRP, transDP, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id,
    ev1P, ev2P]
  rw [h'.st, h'.eph, h'.kem]
  cases hr : rs₂.x.st.recs (sid, pid) with
  | none => dsimp only; exact ⟨rfl, h'.setPh G a b x y _⟩
  | some rc =>
    cases he : rs₂.x.eph (sid, pid) with
    | none => dsimp only; exact ⟨rfl, h'.setPh G a b x y _⟩
    | some opk =>
      cases hk : rs₂.kem (sid, pid) with
      | none => dsimp only; exact ⟨rfl, h'.setPh G a b x y _⟩
      | some kp =>
        dsimp only
        cases hd : P.decaps kp.2 c with
        | none => dsimp only; exact ⟨rfl, h'.setPh G a b x y _⟩
        | some ss =>
          dsimp only
          by_cases hc : rc.role = .responder ∧ rc.key.isNone
          · simp only [hc, and_self, ↓reduceIte, Option.map_some, shO, shEquiv,
              Equiv.coe_fn_mk]
            obtain ⟨e₁, h₁⟩ := rel_ltDP G a b x y h' pid d.2.1
            obtain ⟨e₂, h₂⟩ := rel_ltDP G a b x y h₁ rc.peer d.2.2.1
            dsimp only at e₂ h₂
            rw [e₁, e₂]
            have hq : (ltD (ltD rs₂.x pid d.2.1).2 rc.peer d.2.2.1).2.lt pid =
                some (ltD rs₂.x pid d.2.1).1 :=
              ltD_lt_mono _ _ _ _ _ (ltD_lt_self rs₂.x pid d.2.1)
            have hp : (ltD (ltD rs₂.x pid d.2.1).2 rc.peer d.2.2.1).2.lt rc.peer =
                some (ltD (ltD rs₂.x pid d.2.1).2 rc.peer d.2.2.1).1 := ltD_lt_self _ _ _
            rw [← bobS_interp G a b x y hq hp]
            exact rel_deliverP G a b x y (h₂.kemR G a b x y) (z := (sid, pid)) (rc := rc)
              (ip := (bobS G a b (G.pub x) (G.pub y) sid rc.peer pid e (ltD rs₂.x pid d.2.1).1
                (ltD (ltD rs₂.x pid d.2.1).2 rc.peer d.2.2.1).1 opk, ss))
              (by simp only [ltD_st, hr]) (bobS_symOk G a b x y hq hp e opk)
              (Or.inr ⟨rfl, rfl⟩) _
          · simp only [hc, ↓reduceIte, true_and]
            exact h'.setPh G a b x y _

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- The relation after the same update of the records, corruptions, notices, session secrets and
KEM key pairs on both sides, with fresh records and `a`, `b` uncorrupt. -/
theorem RelCP.upd {rs₁ : PSt S W K PK SK SS C} {inp₁ : Inst → Option (PInp W SS)}
    {ph₁ : Phase S W K PK C} {rs₂ : PSt S (W ⊕ W) K PK SK SS C}
    {inp₂ : Inst → Option (PInp (W ⊕ W) SS)} {ph₂ : Phase S W K PK C}
    (h : RelCP G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂) {t₁ t₂ : St K} (ht : t₁ = t₂)
    {eph₁ eph₂ : Inst → Option S} (he : eph₁ = eph₂) {kem₁ kem₂ : Inst → Option (PK × SK)}
    (hk : kem₁ = kem₂)
    (hf : ∀ z r, t₂.recs z = some r → r.status = .fresh) (ha : t₂.corrupt a = false)
    (hb : t₂.corrupt b = false) (ph : Phase S W K PK C) :
    RelCP G a b x y { rs₁ with x := { rs₁.x with st := t₁, eph := eph₁ }, kem := kem₁ } inp₁ ph
      { rs₂ with x := { rs₂.x with st := t₂, eph := eph₂ }, kem := kem₂ } inp₂ ph :=
  ⟨ht, he, h.lt, h.ro, h.inp, rfl, hk, h.ct, h.symRo, h.symInp, h.abL, hf, ha, hb⟩

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- The relation after a new entry of the tables. -/
theorem RelCP.roUpd {rs₁ : PSt S W K PK SK SS C} {inp₁ : Inst → Option (PInp W SS)}
    {ph₁ : Phase S W K PK C} {rs₂ : PSt S (W ⊕ W) K PK SK SS C}
    {inp₂ : Inst → Option (PInp (W ⊕ W) SS)} {ph₂ : Phase S W K PK C}
    (h : RelCP G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂) {ro₁ : List (PInp W SS × K)}
    {ro₂ : List (PInp (W ⊕ W) SS × K)}
    (hro : ro₁ = ro₂.map (pinterpE G (x + off1 a rs₂.x) (y + off2 b rs₂.x)))
    (hsym : ∀ p ∈ ro₂, SymOk a b rs₂.x.lt p.1.1)
    (hab : ∀ p ∈ ro₂, p.1.1.ini = a → p.1.1.res = b → p.1.1.dh1.isLeft = true)
    (ph : Phase S W K PK C) :
    RelCP G a b x y { rs₁ with ro := ro₁ } inp₁ ph { rs₂ with ro := ro₂ } inp₂ ph :=
  ⟨h.st, h.eph, h.lt, hro, h.inp, rfl, h.kem, h.ct, hsym, h.symInp, hab, h.fresh, h.uncA, h.uncB⟩

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
theorem pinterp_ofInp (ik spk : S) (q : PInp W SS) : pinterp G ik spk (ofInp q.1, q.2) = q := by
  simp only [pinterp, interp_ofInp]

omit [Fintype K] [Nonempty K] in
/-- **The coupling of a start of the simulator**: from related states, the simulator with the
shifted draw and the simulator of the reduction make the same decision and reach related
states, unless the step corrupts `a` or `b`. -/
theorem rel_startP {s₁ : SimSt S W K PK SK SS C} {s₂ : RSimP S W K PK SK SS C}
    (h : RelP G a b x y s₁ s₂) (e : OEv W SS C) (d : PDraw S K PK SK SS C) :
    StopP a b (simStartD P G s₁ e (transPD a b x y s₁ e d)).1 ∨
      ((simStartD P G s₁ e (transPD a b x y s₁ e d)).2 =
          (startRP P G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ e d).2 ∧
        RelP G a b x y (simStartD P G s₁ e (transPD a b x y s₁ e d)).1
          (startRP P G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ e d).1) := by
  obtain ⟨rs₁, inp₁, ph₁⟩ := s₁
  obtain ⟨rs₂, inp₂, ph₂⟩ := s₂
  have h' : RelCP G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂ := h
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e, c⟩ | q)
  · right
    have hn : (rs₁.x.st.recs (sid, pid)).isNone = (rs₂.x.st.recs (sid, pid)).isNone := by
      rw [h'.st]
    dsimp only [simStartD, startRP, transPD_apply]
    by_cases hc : (rs₂.x.st.recs (sid, pid)).isNone = true
    · rw [ite_eq_left (hn.trans hc), ite_eq_left hc]
      have hf : ∀ z rz, (addSession rs₂.x.st (sid, pid) peer role).recs z = some rz →
          rz.status = .fresh := by
        intro z rz hz
        unfold addSession at hz
        split at hz
        · exact h'.fresh z rz hz
        · by_cases hzx : z = (sid, pid)
          · subst hzx; simp only [Function.update_self, Option.some.injEq] at hz; rw [← hz]
          · simp only [Function.update_of_ne hzx] at hz; exact h'.fresh z rz hz
      have ha : (addSession rs₂.x.st (sid, pid) peer role).corrupt a = false := by
        rw [addSession_corrupt]; exact h'.uncA
      have hb : (addSession rs₂.x.st (sid, pid) peer role).corrupt b = false := by
        rw [addSession_corrupt]; exact h'.uncB
      by_cases hro : role = .responder
      · rw [ite_eq_left hro, ite_eq_left hro]
        exact ⟨rfl, h'.upd G a b x y (by rw [h'.st]) (by rw [h'.eph]) (by rw [h'.kem]) hf ha hb _⟩
      · rw [ite_eq_right hro, ite_eq_right hro]
        exact ⟨rfl, h'.upd G a b x y (by rw [h'.st]) (by rw [h'.eph]) h'.kem hf ha hb _⟩
    · rw [ite_eq_right (hn ▸ hc), ite_eq_right hc]
      exact ⟨rfl, h'.setPh G a b x y _⟩
  · exact Or.inr ⟨rfl, h'.setPh G a b x y _⟩
  · exact Or.inr ⟨rfl, h'.setPh G a b x y _⟩
  · right
    dsimp only [simStartD, startRP]
    rw [h'.st]
    refine ⟨rfl, h'.upd G a b x y rfl h'.eph h'.kem ?_ ?_ ?_ _⟩
    · rw [(pollStep_fst _).1]; exact h'.fresh
    · rw [(pollStep_fst _).2.1]; exact h'.uncA
    · rw [(pollStep_fst _).2.1]; exact h'.uncB
  · right
    obtain ⟨e₁, h₁⟩ := rel_ltDP G a b x y h' pid d.1.2.1
    dsimp only [simStartD, startRP, transPD_apply, ev1P, shO, shEquiv, Equiv.coe_fn_mk]
    rw [e₁, pubIK_pub G a b x y, pubSPK_pub G a b x y]
    exact ⟨rfl, h₁.setPh G a b x y _⟩
  · right
    dsimp only [simStartD, startRP, ephPubOf]
    rw [h'.eph]
    exact ⟨rfl, h'.setPh G a b x y _⟩
  · right
    dsimp only [simStartD, startRP]
    rw [pkOf_congr h'.kem, h'.ct]
    exact ⟨rfl, h'.setPh G a b x y _⟩
  · have hn : Named rs₁.x.st pid = Named rs₂.x.st pid := by rw [h'.st]
    dsimp only [simStartD, startRP, transPD_apply, ev1P, shO, shEquiv, Equiv.coe_fn_mk]
    by_cases hc : Named rs₂.x.st pid = true
    · rw [ite_eq_left (hn.trans hc), ite_eq_left hc]
      exact Or.inr ⟨rfl, h'.setPh G a b x y _⟩
    · rw [ite_eq_right (hn ▸ hc), ite_eq_right hc]
      obtain ⟨e₁, h₁⟩ := rel_ltDP G a b x y h' pid d.1.2.1
      by_cases hab : pid = a ∨ pid = b
      · left
        simp only [StopP, corruptStep, ltD_st]
        rcases hab with rfl | rfl <;> simp
      · right
        have hpa : pid ≠ a := fun hc => hab (Or.inl hc)
        have hpb : pid ≠ b := fun hc => hab (Or.inr hc)
        simp only [sh_of_ne a b x y hpa hpb] at e₁ h₁
        rw [sh_of_ne a b x y hpa hpb, e₁]
        refine ⟨rfl, h₁.upd G a b x y (t₁ := corruptStep (ltD rs₁.x pid d.1.2.1).2.st pid)
          (t₂ := corruptStep (ltD rs₂.x pid d.1.2.1).2.st pid)
          (congrArg (corruptStep · pid) h₁.st) h₁.eph h₁.kem h₁.fresh ?_ ?_ _⟩
        · simp only [corruptStep, Function.update_of_ne hpa.symm]; exact h₁.uncA
        · simp only [corruptStep, Function.update_of_ne hpb.symm]; exact h₁.uncB
  · exact Or.inr (rel_completeP G a b x y h sid pid d.1 d.2.2)
  · exact Or.inr (rel_sendP P G a b x y h sid pid e c d.1)
  · right
    dsimp only [simStartD, startRP, transPD_apply]
    rw [h'.ro, keyA_pub, keyB_pub, ← pinterp_ofInp G (x + off1 a rs₂.x) (y + off2 b rs₂.x) q,
      psroDet_ddh]
    refine ⟨rfl, h'.roUpd G a b x y rfl ?_ ?_ _⟩
    · rcases psroDet_snd G (ddhOracle (gapDHDef G)) (G.pub (x + off1 a rs₂.x))
        (G.pub (y + off2 b rs₂.x)) rs₂.ro (ofInp q.1, q.2) d.1.2.2.2 with he | he <;> rw [he]
      · exact h'.symRo
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩
        · exact h'.symRo p hp
    · rcases psroDet_snd G (ddhOracle (gapDHDef G)) (G.pub (x + off1 a rs₂.x))
        (G.pub (y + off2 b rs₂.x)) rs₂.ro (ofInp q.1, q.2) d.1.2.2.2 with he | he <;> rw [he]
      · exact h'.abL
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact fun _ _ => rfl
        · exact h'.abL p hp

end Coupling

end CatCrypt.Crypto.AKE.PQXDHSquareGDH
