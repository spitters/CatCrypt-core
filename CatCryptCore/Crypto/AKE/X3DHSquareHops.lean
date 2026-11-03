/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHSquare
public import CatCryptCore.Crypto.OracleGameUpToBad
public import CatCryptCore.Crypto.OracleLazyMulti

/-!
# The hops of the X3DH square

`x3dh_realizesSim_oracleGame` (`CatCryptCore.Crypto.AKE.X3DHSquare`) bounds the X3DH square by
the advantage of an oracle adversary between the real game `realGame G` and the simulated game
`simGame G`. This file bounds that advantage by the probability of one bad event in a joint run
of the two worlds on one state.

## Steps as functions of one draw

A step of the real world draws at most a secret of a new session, the long-term secrets of two
parties and one value of the key derivation; it is the image of a uniform draw `Draw S K` under
`realD` (`realGame_oracle_eq`). A step of the simulated world draws the same at the start of the
simulator and one key at its call to `F_AKE`; it is the image of a uniform pair in
`Draw S K × K` under `simWorldD` (`simGame_oracle_eq`).

## The joint world

`jointD` runs both worlds on one draw `(r, kf)`. When the simulator delivers a key of `F_AKE` to
an unexposed session (`FKeyAt`), the real world reads the fresh value of the key derivation from
`kf`, the slot from which `F_AKE` draws the key; otherwise it reads `r` (`cpl`). With this
coupling a completing session has the same key in both worlds unless the real table of the key
derivation already holds its input, and an answer of `kdf` is the same in both worlds unless it
is asked at the input of a session that received a key of `F_AKE`: the outputs of the two worlds
differ only after the adversary queries the key derivation at the input of such a session. The
state of the joint world records whether the outputs differed at the last step. Answering with
the real outputs (`jointReal`), its real part is the real game; answering with the simulated
outputs (`jointSim`), its simulated part is the simulated game. The two answers agree on every
transition whose outputs agree, so the advantage is at most the probability `badGame G B` that
the outputs differ at some step of the run against `jointSim` (`x3dh_advantage_le_badGame`).

## Main definitions

* `Draw`, `ltD`, `realD`: a draw and the step of the real world as a function of it.
* `simStartD`, `fStepD`, `simWorldD`: the step of the simulated world as a function of a draw.
* `FKeyAt`, `cpl`, `jointD`, `jointReal`, `jointSim`: the joint world.
* `badGame`: the bad-event experiment.

## Main results

* `realGame_oracle_eq`, `simGame_oracle_eq`: the oracles as images of uniform draws.
* `x3dh_advantage_le_badGame`: the advantage between `realGame G` and `simGame G` is at most the
  probability of the bad event.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquareHops

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Crypto.PAKE.CPaceSquare (roAt PureNF pureGame)
open CatCrypt.Crypto.AKE.X3DHSquare
open CatCrypt.Crypto.OracleGameUpToBad
open scoped ENNReal

/-! ## Computations given by probability mass functions -/

/-- The distribution of a computation that is the lift of `p` is `p`. -/
theorem pmf_eq_of_eq_liftPMF {α : Type} {c : SPComp α} (hc : PureNF c) {p : PMF α}
    (h : c = liftPMF p) : hc.pmf = p :=
  liftPMF_injective (hc.eq_liftPMF.symm.trans h)

/-! ## Activations with one call as functions of draws -/

section Drive0

variable {σ τ E O EG OG Rs Rf : Type} [Fintype Rs] [Nonempty Rs] [Fintype Rf] [Nonempty Rf]

/-- An activation with at most one call over deterministic components: the subroutine step
`stepD` reads the draw `k`. -/
def drive0D (stepD : τ → EG → Rf → τ × OG) (finV : σ → OG → σ × O) (s : σ) (d : EG ⊕ O)
    (t : τ) (k : Rf) : σ × τ × O :=
  match d with
  | .inr o => (s, t, o)
  | .inl g => ((finV s (stepD t g k).2).1, (stepD t g k).1, (finV s (stepD t g k).2).2)

/-- `driveP` without resumption, over a subroutine step that is the image of a uniform draw and
a deterministic finish, is the image of one draw under `drive0D`. -/
theorem driveP_zero_eq (step : τ → EG → PMF (τ × OG)) (res : σ → OG → PMF (σ × (EG ⊕ O)))
    (fin : σ → OG → PMF (σ × O)) (stepD : τ → EG → Rf → τ × OG) (finV : σ → OG → σ × O)
    (hstep : ∀ t g, step t g = (PMF.uniformFintype Rf).map (stepD t g))
    (hfin : ∀ s o, fin s o = PMF.pure (finV s o)) (s : σ) (d : EG ⊕ O) (t : τ) :
    driveP step res fin 0 s d t =
      (PMF.uniformFintype Rf).map (drive0D stepD finV s d t) := by
  rcases d with g | o
  · simp only [driveP, hstep, hfin, PMF.bind_map, PMF.pure_map, Function.comp_def]
    rfl
  · simp only [driveP]
    rw [← PMF.map_const (PMF.uniformFintype Rf)]
    rfl

/-- `withSubP` without resumption, over components that are images of uniform draws, is the
image of independent draws for the start and the call. -/
theorem withSubP_zero_eq (start : σ → E → PMF (σ × (EG ⊕ O))) (step : τ → EG → PMF (τ × OG))
    (res : σ → OG → PMF (σ × (EG ⊕ O))) (fin : σ → OG → PMF (σ × O))
    (startD : σ → E → Rs → σ × (EG ⊕ O)) (stepD : τ → EG → Rf → τ × OG)
    (finV : σ → OG → σ × O) (t : σ × τ) (e : E)
    (hstart : start t.1 e = (PMF.uniformFintype Rs).map (startD t.1 e))
    (hstep : ∀ t g, step t g = (PMF.uniformFintype Rf).map (stepD t g))
    (hfin : ∀ s o, fin s o = PMF.pure (finV s o)) :
    withSubP start step res fin 0 t e =
      (PMF.uniformFintype (Rs × Rf)).map fun r =>
        (((drive0D stepD finV (startD t.1 e r.1).1 (startD t.1 e r.1).2 t.2 r.2).1,
          (drive0D stepD finV (startD t.1 e r.1).1 (startD t.1 e r.1).2 t.2 r.2).2.1),
        (drive0D stepD finV (startD t.1 e r.1).1 (startD t.1 e r.1).2 t.2 r.2).2.2) := by
  simp only [withSubP, hstart, PMF.bind_map, Function.comp_def,
    driveP_zero_eq step res fin stepD finV hstep hfin, PMF.map_comp]
  rw [PMF.uniform_prod_eq_bind (A := Rs) (B := Rf), PMF.map_bind]
  refine congrArg _ (funext fun a => ?_)
  rw [PMF.map_comp]
  rfl

end Drive0

/-! ## Uniform draws in sequence -/

section Seq

variable {A B γ : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]

/-- Two uniform draws in sequence are one uniform pair. -/
theorem uniform_bind_map (f : A → B → γ) :
    (PMF.uniformFintype A).bind (fun a => (PMF.uniformFintype B).map (f a)) =
      (PMF.uniformFintype (A × B)).map fun p => f p.1 p.2 := by
  rw [PMF.uniform_prod_eq_bind, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]

end Seq

/-! ## The real world as a function of one draw -/

/-- A draw of a step: a secret of a new session, the long-term secrets of two parties, and a
value of the key derivation. -/
abbrev Draw (S K : Type) := S × (S × S) × (S × S) × K

section RealDraw

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K]

/-- `ltAt` with the draw `l` for a party without long-term secrets. -/
def ltD (s : RSt S W K) (pid : PartyId) (l : S × S) : (S × S) × RSt S W K :=
  match s.lt pid with
  | some l' => (l', s)
  | none => (l, { s with lt := Function.update s.lt pid (some l) })

omit [DecidableEq W] [Fintype K] [Nonempty K] in
/-- `ltAt` is the image of a uniform pair under `ltD`. -/
theorem ltAt_eq_map (s : RSt S W K) (pid : PartyId) :
    ltAt s pid = (PMF.uniformFintype (S × S)).map (ltD s pid) := by
  cases h : s.lt pid with
  | some l =>
    simp only [ltAt, h]
    rw [← PMF.map_const (PMF.uniformFintype (S × S))]
    congr 1
    funext l'
    simp only [ltD, h, Function.const_apply]
  | none =>
    simp only [ltAt, h]
    congr 1
    funext l'
    simp only [ltD, h]

/-- The lazily sampled random function is the image of a uniform value under `roDet`. -/
theorem roAt_eq_map {D : Type} [DecidableEq D] (tb : List (D × K)) (x : D) :
    roAt tb x = (PMF.uniformFintype K).map (roDet tb x) :=
  (map_uniform_roDet tb x).symm

omit [DecidableEq W] [Fintype K] [Nonempty K] in
/-- An image of the long-term secrets of one party is an image of a uniform draw. -/
theorem ltAt_map_eq {γ : Type} [Nonempty K] [Fintype K] (s : RSt S W K) (pid : PartyId)
    (g : (S × S) × RSt S W K → γ) :
    (ltAt s pid).map g = (PMF.uniformFintype (Draw S K)).map fun r => g (ltD s pid r.2.1) := by
  rw [ltAt_eq_map, PMF.map_comp, map_uniform_eq_map_prod_fst (B := (S × S) × K),
    map_uniform_eq_map_prod_snd (A := S)]
  rfl

omit [DecidableEq W] in
/-- The long-term secrets of two parties and a value of the key derivation, in sequence, are an
image of a uniform draw. -/
theorem ltAt_bind_ltAt_eq {γ : Type} (s : RSt S W K) (p q : PartyId)
    (g : (S × S) × RSt S W K → (S × S) × RSt S W K → K → γ) :
    (ltAt s p).bind (fun la => (ltAt la.2 q).bind fun lb => (PMF.uniformFintype K).map (g la lb))
      = (PMF.uniformFintype (Draw S K)).map fun r =>
          g (ltD s p r.2.1) (ltD (ltD s p r.2.1).2 q r.2.2.1) r.2.2.2 := by
  simp only [ltAt_eq_map, PMF.bind_map, Function.comp_def, uniform_bind_map]
  rw [map_uniform_eq_map_prod_snd (A := S)]

variable (G : DHGroup S W)

/-- `completeStep` with the draw `r`. -/
def completeD (s : RSt S W K) (x : Inst) (r : Draw S K) : ROut S W K × RSt S W K :=
  match s.st.recs x, s.eph x with
  | some rc, some ek =>
    match opkOf s x.1 rc.peer with
    | some opk =>
      if rc.role = .initiator ∧ rc.key.isNone then
        (.ack, keyed (ltD (ltD s x.2 r.2.1).2 rc.peer r.2.2.1).2 x rc
          (roDet (ltD (ltD s x.2 r.2.1).2 rc.peer r.2.2.1).2.ro
            (aliceInp G x.1 x.2 rc.peer (ltD s x.2 r.2.1).1.1 ek
              (G.pub (ltD (ltD s x.2 r.2.1).2 rc.peer r.2.2.1).1.1)
              (G.pub (ltD (ltD s x.2 r.2.1).2 rc.peer r.2.2.1).1.2) (G.pub opk)) r.2.2.2).1
          (roDet (ltD (ltD s x.2 r.2.1).2 rc.peer r.2.2.1).2.ro
            (aliceInp G x.1 x.2 rc.peer (ltD s x.2 r.2.1).1.1 ek
              (G.pub (ltD (ltD s x.2 r.2.1).2 rc.peer r.2.2.1).1.1)
              (G.pub (ltD (ltD s x.2 r.2.1).2 rc.peer r.2.2.1).1.2) (G.pub opk)) r.2.2.2).2)
      else (.ack, s)
    | none => (.ack, s)
  | _, _ => (.ack, s)

/-- `sendStep` with the draw `r`. -/
def sendD (s : RSt S W K) (x : Inst) (e : W) (r : Draw S K) : ROut S W K × RSt S W K :=
  match s.st.recs x, s.eph x with
  | some rc, some opk =>
    if rc.role = .responder ∧ rc.key.isNone then
      (.ack, keyed (ltD (ltD s x.2 r.2.1).2 rc.peer r.2.2.1).2 x rc
        (roDet (ltD (ltD s x.2 r.2.1).2 rc.peer r.2.2.1).2.ro
          (bobInp G x.1 rc.peer x.2 (G.pub (ltD (ltD s x.2 r.2.1).2 rc.peer r.2.2.1).1.1) e
            (ltD s x.2 r.2.1).1.1 (ltD s x.2 r.2.1).1.2 opk) r.2.2.2).1
        (roDet (ltD (ltD s x.2 r.2.1).2 rc.peer r.2.2.1).2.ro
          (bobInp G x.1 rc.peer x.2 (G.pub (ltD (ltD s x.2 r.2.1).2 rc.peer r.2.2.1).1.1) e
            (ltD s x.2 r.2.1).1.1 (ltD s x.2 r.2.1).1.2 opk) r.2.2.2).2)
    else (.ack, s)
  | _, _ => (.ack, s)

/-- A step of the real protocol with the draw `r`. -/
def realD (s : RSt S W K) (e : OEv W) (r : Draw S K) : OOut S W K × RSt S W K :=
  match e with
  | .inl (.newSession sid pid peer role) =>
    if (s.st.recs (sid, pid)).isNone then
      (.inl .ok, { s with st := addSession s.st (sid, pid) peer role,
                          eph := Function.update s.eph (sid, pid) (some r.1) })
    else (.inl .ok, s)
  | .inl (.getKey sid pid) => (.inl (.key (keyOf s.st (sid, pid))), s)
  | .inr .idle => (.inr .ack, s)
  | .inr .poll => (.inr (.notice (pollStep s.st).2), { s with st := (pollStep s.st).1 })
  | .inr (.pub pid) =>
    (.inr (.pub (G.pub (ltD s pid r.2.1).1.1) (G.pub (ltD s pid r.2.1).1.2)), (ltD s pid r.2.1).2)
  | .inr (.ephPub sid pid) => (.inr (.eph (ephPubOf G s (sid, pid))), s)
  | .inr (.corrupt pid) =>
    if Named s.st pid then (.inr (.secret none), s) else
      (.inr (.secret (some (ltD s pid r.2.1).1)),
        { (ltD s pid r.2.1).2 with st := corruptStep (ltD s pid r.2.1).2.st pid })
  | .inr (.complete sid pid) => (.inr (completeD G s (sid, pid) r).1, (completeD G s (sid, pid) r).2)
  | .inr (.send sid pid e) => (.inr (sendD G s (sid, pid) e r).1, (sendD G s (sid, pid) e r).2)
  | .inr (.kdf x) => (.inr (.hash (roDet s.ro x r.2.2.2).1), { s with ro := (roDet s.ro x r.2.2.2).2 })

/-- `completeStep` is the image of a uniform draw under `completeD`. -/
theorem completeStep_eq_map (s : RSt S W K) (x : Inst) :
    completeStep G s x = (PMF.uniformFintype (Draw S K)).map (completeD G s x) := by
  have hP : ∀ b : ROut S W K × RSt S W K,
      PMF.pure b = (PMF.uniformFintype (Draw S K)).map fun _ => b := fun b =>
    (PMF.map_const _ _).symm
  change _ = (PMF.uniformFintype (Draw S K)).map fun r => completeD G s x r
  cases hr : s.st.recs x with
  | none => simp only [completeStep, completeD, hr, hP]
  | some rc =>
    cases he : s.eph x with
    | none => simp only [completeStep, completeD, hr, he, hP]
    | some ek =>
      cases ho : opkOf s x.1 rc.peer with
      | none => simp only [completeStep, completeD, hr, he, ho, hP]
      | some opk =>
        by_cases hc : rc.role = .initiator ∧ rc.key.isNone
        · simp only [completeStep, completeD, hr, he, ho, hc, and_self, ↓reduceIte, roAt_eq_map, PMF.map_comp]
          exact ltAt_bind_ltAt_eq s x.2 rc.peer _
        · simp only [completeStep, completeD, hr, he, ho, hc, ↓reduceIte, hP]

/-- `sendStep` is the image of a uniform draw under `sendD`. -/
theorem sendStep_eq_map (s : RSt S W K) (x : Inst) (e : W) :
    sendStep G s x e = (PMF.uniformFintype (Draw S K)).map (sendD G s x e) := by
  have hP : ∀ b : ROut S W K × RSt S W K,
      PMF.pure b = (PMF.uniformFintype (Draw S K)).map fun _ => b := fun b =>
    (PMF.map_const _ _).symm
  change _ = (PMF.uniformFintype (Draw S K)).map fun r => sendD G s x e r
  cases hr : s.st.recs x with
  | none => simp only [sendStep, sendD, hr, hP]
  | some rc =>
    cases he : s.eph x with
    | none => simp only [sendStep, sendD, hr, he, hP]
    | some opk =>
      by_cases hc : rc.role = .responder ∧ rc.key.isNone
      · simp only [sendStep, sendD, hr, he, hc, and_self, ↓reduceIte, roAt_eq_map, PMF.map_comp]
        exact ltAt_bind_ltAt_eq s x.2 rc.peer _
      · simp only [sendStep, sendD, hr, he, hc, ↓reduceIte, hP]

/-- **The oracle of the real game** is the image of a uniform draw under `realD`. -/
theorem realGame_oracle_eq (s : RSt S W K) (e : OEv W) :
    (realGame G).oracle () s e = (PMF.uniformFintype (Draw S K)).map (realD G s e) := by
  have hP : ∀ b : OOut S W K × RSt S W K,
      PMF.pure b = (PMF.uniformFintype (Draw S K)).map fun _ => b := fun b =>
    (PMF.map_const _ _).symm
  change _ = (PMF.uniformFintype (Draw S K)).map fun r => realD G s e r
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ | pid |
    ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | x)
  · simp only [realGame, realHon]
    split_ifs with h
    · rw [PMF.map_comp, map_uniform_eq_map_prod_fst (B := (S × S) × (S × S) × K)]
      congr 1
      funext r
      simp only [realD, h, ite_true, Function.comp_apply]
    · rw [PMF.pure_map, hP]
      congr 1
      funext r
      simp only [realD, h, Bool.false_eq_true, ite_false]
  · simp only [realGame, realHon, PMF.pure_map, hP]
    rfl
  · simp only [realGame, realAdv, PMF.pure_map, hP]
    rfl
  · simp only [realGame, realAdv, PMF.pure_map, hP]
    rfl
  · simp only [realGame, realAdv, PMF.map_comp]
    exact ltAt_map_eq s pid _
  · simp only [realGame, realAdv, PMF.pure_map, hP]
    rfl
  · simp only [realGame, realAdv, corruptRStep]
    by_cases h : Named s.st pid = true
    · simp only [h, ite_true, PMF.pure_map, hP]
      congr 1
      funext r
      simp only [realD, h, ite_true]
    · simp only [h, Bool.false_eq_true, ite_false, PMF.map_comp]
      refine (ltAt_map_eq s pid _).trans ?_
      congr 1
      funext r
      simp only [realD, h, Bool.false_eq_true, ite_false, Function.comp_apply]
  · simp only [realGame, realAdv, completeStep_eq_map, PMF.map_comp]
    rfl
  · simp only [realGame, realAdv, sendStep_eq_map, PMF.map_comp]
    rfl
  · simp only [realGame, realAdv, roAt_eq_map, PMF.map_comp]
    rw [map_uniform_eq_map_prod_snd (A := S × S), map_uniform_eq_map_prod_snd (A := S × S),
      map_uniform_eq_map_prod_snd (A := S)]
    rfl

end RealDraw

/-! ## The simulated world as a function of draws -/

section SimDraw

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] (G : DHGroup S W)

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- `ltStep` is the lift of `ltAt`. -/
theorem ltStep_eq (s : RSt S W K) (pid : PartyId) : ltStep s pid = liftPMF (ltAt s pid) := by
  unfold ltStep ltAt
  split <;> simp only [liftPMF_pure, sample_eq_liftPMF, map_liftPMF]

omit [Inhabited K] in
/-- `roStep` is the lift of `roAt`. -/
theorem roStep_eq {D : Type} [DecidableEq D] (tb : List (D × K)) (x : D) :
    roStep tb x = liftPMF (roAt tb x) := by
  cases h : tb.lookup x <;>
    simp only [roStep, roAt, h, liftPMF_pure, sample_eq_liftPMF, map_liftPMF]

/-- `deliver` with the value `k` of the key derivation. -/
def deliverD (rs : RSt S W K) (inp : Inst → Option (Inp W)) (x : Inst) (r : Rec K)
    (ip : Inp W) (k : K) : SimSt S W K × Dec S W K :=
  if Exposed rs.st x r then
    ((keyed rs x r (roDet rs.ro ip k).1 (roDet rs.ro ip k).2, Function.update inp x (some ip),
        .out .ack), .inl (.inr (.newKey x.1 x.2 (roDet rs.ro ip k).1)))
  else
    ((keyed rs x r default rs.ro, Function.update inp x (some ip), .out .ack),
      .inl (.inr (if (inp (x.1, r.peer)).all (· = ip) then .newKey x.1 x.2 default
        else .newKeyUnlinked x.1 x.2 default)))

omit [Field S] [Fintype S] in
/-- `deliver` is the lift of the image of a uniform value under `deliverD`. -/
theorem deliver_eq (rs : RSt S W K) (inp : Inst → Option (Inp W)) (x : Inst) (r : Rec K)
    (ip : Inp W) :
    deliver rs inp x r ip = liftPMF ((PMF.uniformFintype K).map (deliverD rs inp x r ip)) := by
  change _ = liftPMF ((PMF.uniformFintype K).map fun k => deliverD rs inp x r ip k)
  by_cases h : Exposed rs.st x r
  · simp only [deliver, h, ↓reduceIte, roStep_eq, map_liftPMF, roAt_eq_map, PMF.map_comp]
    congr 2
    funext k
    simp only [deliverD, h, ↓reduceIte, Function.comp_apply]
  · simp only [deliver, h, ↓reduceIte, liftPMF_pure]
    congr 1
    rw [← PMF.map_const (PMF.uniformFintype K)]
    congr 1
    funext k
    simp only [deliverD, h, ↓reduceIte, Function.const_apply]

/-- `simComplete` with the draw `r`. -/
def simCompleteD (s : SimSt S W K) (x : Inst) (r : Draw S K) : SimSt S W K × Dec S W K :=
  match s.1.st.recs x, s.1.eph x with
  | some rc, some ek =>
    match opkOf s.1 x.1 rc.peer with
    | some opk =>
      if rc.role = .initiator ∧ rc.key.isNone then
        deliverD (ltD (ltD s.1 x.2 r.2.1).2 rc.peer r.2.2.1).2 s.2.1 x rc
          (aliceInp G x.1 x.2 rc.peer (ltD s.1 x.2 r.2.1).1.1 ek
            (G.pub (ltD (ltD s.1 x.2 r.2.1).2 rc.peer r.2.2.1).1.1)
            (G.pub (ltD (ltD s.1 x.2 r.2.1).2 rc.peer r.2.2.1).1.2) (G.pub opk)) r.2.2.2
      else ((s.1, s.2.1, .fwd), .inr (.inr .ack))
    | none => ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | _, _ => ((s.1, s.2.1, .fwd), .inr (.inr .ack))

/-- `simSend` with the draw `r`. -/
def simSendD (s : SimSt S W K) (x : Inst) (e : W) (r : Draw S K) : SimSt S W K × Dec S W K :=
  match s.1.st.recs x, s.1.eph x with
  | some rc, some opk =>
    if rc.role = .responder ∧ rc.key.isNone then
      deliverD (ltD (ltD s.1 x.2 r.2.1).2 rc.peer r.2.2.1).2 s.2.1 x rc
        (bobInp G x.1 rc.peer x.2 (G.pub (ltD (ltD s.1 x.2 r.2.1).2 rc.peer r.2.2.1).1.1) e
          (ltD s.1 x.2 r.2.1).1.1 (ltD s.1 x.2 r.2.1).1.2 opk) r.2.2.2
    else ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | _, _ => ((s.1, s.2.1, .fwd), .inr (.inr .ack))

/-- `simStart` with the draw `r`. -/
def simStartD (s : SimSt S W K) (e : OEv W) (r : Draw S K) : SimSt S W K × Dec S W K :=
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
      .inr (.inr (.pub (G.pub (ltD s.1 pid r.2.1).1.1) (G.pub (ltD s.1 pid r.2.1).1.2))))
  | .inr (.ephPub sid pid) =>
    ((s.1, s.2.1, .fwd), .inr (.inr (.eph (ephPubOf G s.1 (sid, pid)))))
  | .inr (.corrupt pid) =>
    if Named s.1.st pid then ((s.1, s.2.1, .fwd), .inr (.inr (.secret none))) else
      (({ (ltD s.1 pid r.2.1).2 with st := corruptStep (ltD s.1 pid r.2.1).2.st pid }, s.2.1,
          .out (.secret (some (ltD s.1 pid r.2.1).1))), .inl (.inr (.corrupt pid)))
  | .inr (.complete sid pid) => simCompleteD G s (sid, pid) r
  | .inr (.send sid pid e) => simSendD G s (sid, pid) e r
  | .inr (.kdf x) =>
    (({ s.1 with ro := (roDet s.1.ro x r.2.2.2).2 }, s.2.1, .fwd),
      .inr (.inr (.hash (roDet s.1.ro x r.2.2.2).1)))

/-- **The start of the simulator as a function of a draw**: `simStart` is the lift of the image
of a uniform draw under `simStartD`. -/
theorem simStart_eq (s : SimSt S W K) (e : OEv W) :
    simStart G s e = liftPMF ((PMF.uniformFintype (Draw S K)).map (simStartD G s e)) := by
  have hP : ∀ b : SimSt S W K × Dec S W K,
      (SPComp.pure b : SPComp _) = liftPMF ((PMF.uniformFintype (Draw S K)).map fun _ => b) :=
    fun b => by rw [liftPMF_pure]; exact congrArg liftPMF (PMF.map_const _ _).symm
  change _ = liftPMF ((PMF.uniformFintype (Draw S K)).map fun r => simStartD G s e r)
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ | pid |
    ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | x)
  · by_cases h : (s.1.st.recs (sid, pid)).isNone = true
    · simp only [simStart, h, ↓reduceIte, sample_eq_liftPMF, map_liftPMF]
      rw [map_uniform_eq_map_prod_fst (B := (S × S) × (S × S) × K)]
      congr 2
      funext r
      simp only [simStartD, h, ↓reduceIte]
    · simp only [simStart, h, Bool.false_eq_true, ↓reduceIte, hP]
      congr 3
      funext r
      simp only [simStartD, h, Bool.false_eq_true, ↓reduceIte]
  · simp only [simStart, hP]
    rfl
  · simp only [simStart, hP]
    rfl
  · simp only [simStart, hP]
    rfl
  · simp only [simStart, ltStep_eq, map_liftPMF]
    exact congrArg liftPMF (ltAt_map_eq s.1 pid _)
  · simp only [simStart, hP]
    rfl
  · by_cases h : Named s.1.st pid = true
    · simp only [simStart, simCorrupt, h, ↓reduceIte, hP]
      congr 3
      funext r
      simp only [simStartD, h, ↓reduceIte]
    · simp only [simStart, simCorrupt, h, Bool.false_eq_true, ↓reduceIte, ltStep_eq,
        map_liftPMF]
      refine congrArg liftPMF ((ltAt_map_eq s.1 pid _).trans ?_)
      congr 1
      funext r
      simp only [simStartD, h, Bool.false_eq_true, ↓reduceIte]
  · simp only [simStart, simComplete, simStartD, simCompleteD]
    cases hr : s.1.st.recs (sid, pid) with
    | none => simp only [hP]
    | some rc =>
      cases he : s.1.eph (sid, pid) with
      | none => simp only [hP]
      | some ek =>
        cases ho : opkOf s.1 sid rc.peer with
        | none => simp only [ho, hP]
        | some opk =>
          by_cases hc : rc.role = .initiator ∧ rc.key.isNone
          · simp only [ho, hc, and_self, ↓reduceIte, ltStep_eq, deliver_eq, liftPMF_bind_liftPMF]
            exact congrArg liftPMF (ltAt_bind_ltAt_eq s.1 pid rc.peer _)
          · simp only [ho, hc, ↓reduceIte, hP]
  · simp only [simStart, simSend, simStartD, simSendD]
    cases hr : s.1.st.recs (sid, pid) with
    | none => simp only [hP]
    | some rc =>
      cases he : s.1.eph (sid, pid) with
      | none => simp only [hP]
      | some opk =>
        by_cases hc : rc.role = .responder ∧ rc.key.isNone
        · simp only [hc, and_self, ↓reduceIte, ltStep_eq, deliver_eq, liftPMF_bind_liftPMF]
          exact congrArg liftPMF (ltAt_bind_ltAt_eq s.1 pid rc.peer _)
        · simp only [hc, ↓reduceIte, hP]
  · simp only [simStart, roStep_eq, map_liftPMF, roAt_eq_map, PMF.map_comp]
    rw [map_uniform_eq_map_prod_snd (A := S × S), map_uniform_eq_map_prod_snd (A := S × S),
      map_uniform_eq_map_prod_snd (A := S)]
    rfl

/-- A step of the adversary port of `F_AKE` with uniform keys, with the fresh key `kf`. -/
def advD (t : St K) (a : AEv K) (kf : K) : St K × AOut :=
  match a with
  | .idle => (t, .ack)
  | .poll => ((pollStep t).1, .notice (pollStep t).2)
  | .corrupt pid => (corruptStep t pid, .ack)
  | .impersonate _ _ => (t, .ack)
  | .newKey sid pid k => (newKeyStep t (sid, pid) k kf, .ack)
  | .newKeyUnlinked sid pid k => (newKeyFreshStep t (sid, pid) k kf, .ack)

/-- A step of `F_AKE` with uniform keys, with the fresh key `kf`. -/
def fStepD (t : St K) (g : FEv K) (kf : K) : St K × FOut K :=
  match g with
  | .inl h => ((honStep t h).1, .inl (honStep t h).2)
  | .inr a => ((advD t a kf).1, .inr (advD t a kf).2)

omit [Inhabited K] in
/-- A step of `F_AKE` with uniform keys is the lift of the image of a uniform key under
`fStepD`. -/
theorem fStep_eq (t : St K) (g : FEv K) :
    (F_AKE (SPComp.sample K) true).step t g =
      liftPMF ((PMF.uniformFintype K).map (fStepD t g)) := by
  change _ = liftPMF ((PMF.uniformFintype K).map fun kf => fStepD t g kf)
  rcases g with h | a
  · simp only [F_AKE, Sys.ofPorts_step_inl, honSys, liftPMF_pure, map_liftPMF, PMF.pure_map]
    exact congrArg liftPMF (PMF.map_const _ _).symm
  · simp only [F_AKE, Sys.ofPorts_step_inr, advSys]
    cases a <;>
      simp only [liftPMF_pure, sample_eq_liftPMF, map_liftPMF, PMF.pure_map, PMF.map_comp,
        ↓reduceIte] <;>
      first
      | exact congrArg liftPMF (PMF.map_const _ _).symm
      | rfl

/-- The finish of the simulator. -/
def finV (s : SimSt S W K) (o : FOut K) : SimSt S W K × OOut S W K :=
  ((s.1, s.2.1, .fwd), simOut s.2.2 o)

/-- **A step of the simulated world** with the draw `r = (r₀, kf)`: the start of the simulator
reads `r₀` and the call to `F_AKE` reads `kf`. -/
def simWorldD (t : SimSt S W K × St K) (e : OEv W) (r : Draw S K × K) :
    (SimSt S W K × St K) × OOut S W K :=
  (((drive0D fStepD finV (simStartD G t.1 e r.1).1 (simStartD G t.1 e r.1).2 t.2 r.2).1,
    (drive0D fStepD finV (simStartD G t.1 e r.1).1 (simStartD G t.1 e r.1).2 t.2 r.2).2.1),
    (drive0D fStepD finV (simStartD G t.1 e r.1).1 (simStartD G t.1 e r.1).2 t.2 r.2).2.2)

/-- **The oracle of the simulated game** is the image of a uniform draw under `simWorldD`. -/
theorem simGame_oracle_eq (t : SimSt S W K × St K) (e : OEv W) :
    (simGame G).oracle () t e =
      (PMF.uniformFintype (Draw S K × K)).map fun r => (simWorldD G t e r).swap := by
  have hstep : ((simProt (K := K) G).withSub (F_AKE (SPComp.sample K) true)).step t e =
      liftPMF (withSubP (fun s e => (PMF.uniformFintype (Draw S K)).map (simStartD G s e))
        (fun t g => (PMF.uniformFintype K).map (fStepD t g))
        (fun s o => PMF.pure ((s.1, s.2.1, .fwd), .inr (simOut s.2.2 o)))
        (fun s o => PMF.pure (finV s o)) 0 t e) :=
    withSub_step_eq_liftPMF _ _ _ _ _ _ (simStart_eq G) fStep_eq (fun _ _ => liftPMF_pure _)
      (fun _ _ => liftPMF_pure _) t e
  change (simWorld_pureNF G t e).pmf.map Prod.swap = _
  rw [pmf_eq_of_eq_liftPMF (simWorld_pureNF G t e) hstep,
    withSubP_zero_eq _ _ _ _ (simStartD G) fStepD finV t e rfl (fun _ _ => rfl) (fun _ _ => rfl),
    PMF.map_comp]
  rfl

end SimDraw

/-! ## The joint world -/

section Joint

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- Whether the event `e` from the simulator state `s` lets the session it completes receive a
key of `F_AKE`: `e` completes the session `x` with record `r`, and `x` is not exposed. -/
def FKeyAt (s : SimSt S W K) : OEv W → Bool
  | .inr (.complete sid pid) | .inr (.send sid pid _) =>
    match s.1.st.recs (sid, pid) with
    | some r => !decide (Exposed s.1.st (sid, pid) r)
    | none => false
  | _ => false

/-- The draw of the real world from the draw `(r, kf)` of the simulated world: with `b`, the
value of the key derivation is `kf`, the key that `F_AKE` draws. -/
def cpl (b : Bool) (r : Draw S K × K) : Draw S K :=
  if b then (r.1.1, r.1.2.1, r.1.2.2.1, r.2) else r.1

omit [DecidableEq W] [Inhabited K] in
/-- The coupling takes a uniform draw of the simulated world to a uniform draw of the real
world. -/
theorem map_uniform_cpl (b : Bool) :
    (PMF.uniformFintype (Draw S K × K)).map (cpl b) = PMF.uniformFintype (Draw S K) := by
  cases b
  · exact PMF.map_uniform_fst
  · let e : (Draw S K × K) ≃ (Draw S K × K) :=
      { toFun := fun r => ((r.1.1, r.1.2.1, r.1.2.2.1, r.2), r.1.2.2.2)
        invFun := fun r => ((r.1.1, r.1.2.1, r.1.2.2.1, r.2), r.1.2.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have h : cpl (S := S) (K := K) true = Prod.fst ∘ e := rfl
    rw [h, ← PMF.map_comp, PMF.uniformFintype_map_equiv, PMF.map_uniform_fst]

/-- The state of the joint world: the simulated world, the real world, and whether the outputs
differed at the last step. -/
abbrev JSt (S W K : Type) [Field S] := ((SimSt S W K × St K) × RSt S W K) × Bool

/-- **A step of the joint world** with the draw `r`: the outputs of the real and of the
simulated world, and the next states. -/
def jointD (s : (SimSt S W K × St K) × RSt S W K) (e : OEv W) (r : Draw S K × K) :
    (OOut S W K × OOut S W K) × ((SimSt S W K × St K) × RSt S W K) :=
  (((realD G s.2 e (cpl (FKeyAt s.1.1 e) r)).1, (simWorldD G s.1 e r).2),
    ((simWorldD G s.1 e r).1, (realD G s.2 e (cpl (FKeyAt s.1.1 e) r)).2))

open Classical in
/-- The joint world answering with the output of the real world. -/
noncomputable def jointReal (s : JSt S W K) (e : OEv W) : PMF (OOut S W K × JSt S W K) :=
  (PMF.uniformFintype (Draw S K × K)).map fun r =>
    ((jointD G s.1 e r).1.1,
      ((jointD G s.1 e r).2, decide ((jointD G s.1 e r).1.1 ≠ (jointD G s.1 e r).1.2)))

open Classical in
/-- The joint world answering with the output of the simulated world. -/
noncomputable def jointSim (s : JSt S W K) (e : OEv W) : PMF (OOut S W K × JSt S W K) :=
  (PMF.uniformFintype (Draw S K × K)).map fun r =>
    ((jointD G s.1 e r).1.2,
      ((jointD G s.1 e r).2, decide ((jointD G s.1 e r).1.1 ≠ (jointD G s.1 e r).1.2)))

/-- The two answers of the joint world agree on every outcome whose outputs did not differ. -/
theorem jointReal_apply_eq (s : JSt S W K) (e : OEv W) (x : OOut S W K × JSt S W K)
    (hx : x.2.2 = false) : jointReal G s e x = jointSim G s e x := by
  simp only [jointReal, jointSim, PMF.map_apply]
  refine tsum_congr fun r => ?_
  by_cases h : (jointD G s.1 e r).1.1 = (jointD G s.1 e r).1.2
  · rw [h]
  · have h₁ : x ≠ ((jointD G s.1 e r).1.1, ((jointD G s.1 e r).2, true)) :=
      fun hc => by simp [hc] at hx
    have h₂ : x ≠ ((jointD G s.1 e r).1.2, ((jointD G s.1 e r).2, true)) :=
      fun hc => by simp [hc] at hx
    simp only [h, ne_eq, not_false_eq_true, decide_true, h₁, h₂, ite_false]

/-- The real part of `jointReal` is the real game. -/
theorem jointReal_map (s : JSt S W K) (e : OEv W) :
    (jointReal G s e).map (Prod.map id fun s' => s'.1.2) = (realGame G).oracle () s.1.2 e := by
  rw [realGame_oracle_eq, jointReal, PMF.map_comp, ← map_uniform_cpl (FKeyAt s.1.1.1 e),
    PMF.map_comp]
  rfl

/-- The simulated part of `jointSim` is the simulated game. -/
theorem jointSim_map (s : JSt S W K) (e : OEv W) :
    (jointSim G s e).map (Prod.map id fun s' => s'.1.1) = (simGame G).oracle () s.1.1 e := by
  rw [simGame_oracle_eq, jointSim, PMF.map_comp]
  rfl

/-- The bad transitions of the joint world: the outputs of the two worlds differed. -/
def JointBad (_ : JSt S W K) (_ : OEv W) (x : OOut S W K × JSt S W K) : Prop :=
  x.2.2 = true

instance (s : JSt S W K) (e : OEv W) (x : OOut S W K × JSt S W K) :
    Decidable (JointBad s e x) :=
  inferInstanceAs (Decidable (x.2.2 = true))

/-- The initial state of the joint world. -/
def jointInit : JSt S W K :=
  ((((rInit, fun _ => none, .fwd), initSt), rInit), false)

/-- **The bad-event experiment**: the adversary runs against the joint world answering with the
outputs of the simulated world, and the experiment outputs whether the outputs of the real and
of the simulated world differed at some step. -/
noncomputable def badGame (B : OracleAdv (OEv W) (OOut S W K) Bool) : PMF Bool :=
  (OracleAdv.run (OracleAdv.flagWhen JointBad (jointSim G)) B (jointInit, false)).map
    fun y => y.2.2

/-- **Real versus simulated X3DH, up to the bad event.** For every oracle adversary `B`, the
advantage of `B` between the real game and the simulated game is at most the probability of the
bad event of the joint world. -/
theorem x3dh_advantage_le_badGame (B : OracleAdv (OEv W) (OOut S W K) Bool) :
    KeyedGame.advantage (realGame G) (simGame G) B ≤ badGame G B true := by
  have hagree : ∀ (s : JSt S W K) (e : OEv W) (x : OOut S W K × JSt S W K), ¬ JointBad s e x →
      jointReal G s e x = jointSim G s e x :=
    fun s e x hx => jointReal_apply_eq G s e x (by simpa [JointBad] using hx)
  have hR : (OracleAdv.run ((realGame G).oracle ()) B (realGame G).init).map Prod.fst =
      (OracleAdv.run (jointReal G) B jointInit).map Prod.fst := by
    have h := OracleAdv.run_map_state (jointReal G) ((realGame G).oracle ())
      (fun s' => s'.1.2) (fun s e => jointReal_map G s e) B jointInit
    calc _ = ((OracleAdv.run (jointReal G) B jointInit).map
          (Prod.map id fun s' => s'.1.2)).map Prod.fst := (congrArg (PMF.map Prod.fst) h).symm
      _ = _ := by rw [PMF.map_comp]; rfl
  have hS : (OracleAdv.run ((simGame (K := K) G).oracle ()) B (simGame G).init).map Prod.fst =
      (OracleAdv.run (jointSim G) B jointInit).map Prod.fst := by
    have h := OracleAdv.run_map_state (jointSim G) ((simGame G).oracle ())
      (fun s' => s'.1.1) (fun s e => jointSim_map G s e) B jointInit
    calc _ = ((OracleAdv.run (jointSim G) B jointInit).map
          (Prod.map id fun s' => s'.1.1)).map Prod.fst := (congrArg (PMF.map Prod.fst) h).symm
      _ = _ := by rw [PMF.map_comp]; rfl
  have hF : ((OracleAdv.run (OracleAdv.flagWhen JointBad (jointSim G)) B
      (jointInit, false)).map fun y => y.2.2) true =
      (OracleAdv.run (OracleAdv.flagWhen JointBad (jointSim G)) B
        (jointInit, false)).toOuterMeasure {y | y.2.2 = true} := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    rfl
  have h₁ : ((OracleAdv.run (jointReal G) B jointInit).map Prod.fst) true ≤
      ((OracleAdv.run (jointSim G) B jointInit).map Prod.fst) true + badGame G B true := by
    rw [map_fst_apply_true, map_fst_apply_true, badGame, hF]
    exact OracleAdv.run_toOuterMeasure_le_add_flagWhen JointBad _ _ hagree B _ _
  have h₂ : ((OracleAdv.run (jointSim G) B jointInit).map Prod.fst) true ≤
      ((OracleAdv.run (jointReal G) B jointInit).map Prod.fst) true + badGame G B true := by
    rw [map_fst_apply_true, map_fst_apply_true, badGame, hF,
      ← OracleAdv.run_flagWhen_prob_eq JointBad _ _ hagree B]
    exact OracleAdv.run_toOuterMeasure_le_add_flagWhen JointBad _ _
      (fun s e x hx => (hagree s e x hx).symm) B _ _
  have hacc₁ : (realGame G).accept B =
      ((OracleAdv.run (jointReal G) B jointInit).map Prod.fst) true := by
    unfold KeyedGame.accept
    erw [PMF.pure_bind]
    rw [hR]
  have hacc₂ : (simGame (K := K) G).accept B =
      ((OracleAdv.run (jointSim G) B jointInit).map Prod.fst) true := by
    unfold KeyedGame.accept
    erw [PMF.pure_bind]
    rw [hS]
  rw [KeyedGame.advantage, hacc₁, hacc₂]
  exact max_le (tsub_le_iff_left.mpr h₁) (tsub_le_iff_left.mpr h₂)

end Joint

end CatCrypt.Crypto.AKE.X3DHSquareHops
