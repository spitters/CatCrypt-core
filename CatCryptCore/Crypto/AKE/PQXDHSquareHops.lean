/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDHSquare
public import CatCryptCore.Crypto.AKE.X3DHSquareHops

/-!
# The hops of the PQXDH square

Work in progress: the steps of the real and the simulated PQXDH worlds as images of draws.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.PQXDHSquareHops

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Crypto.PAKE.CPaceSquare (roAt PureNF pureGame sampleFrom_ofPMF_eq_liftPMF)
open CatCrypt.Crypto.AKE.X3DHSquare (Inp aliceInp bobInp RSt ROut ltAt Named keyed realHon
  ephPubOf opkOf corruptRStep realAdv rInit FEv FOut ltStep roStep subView)
open CatCrypt.Crypto.AKE.X3DHSquareHops (pmf_eq_of_eq_liftPMF drive0D driveP_zero_eq
  uniform_bind_map Draw ltD ltAt_eq_map ltAt_map_eq roAt_eq_map ltStep_eq roStep_eq advD fStepD fStep_eq cpl
  map_uniform_cpl Exp skRec InpShape DhOk DhOk.mono ltD_lt_mono ltD_lt_self ltD_st ltD_eph ltD_ro
  pollStep_fst addSession_of_isSome addSession_of_isNone sk_some sk_none exp_update lookup_cons
  roDet_of_some roDet_of_none exp_iff_of_shape shape_partner skRec_ext setRec_recs_ne
  keyOf_setRec_ne newKeyStep_of newKeyFreshStep_of)
open CatCrypt.Crypto.AKE.PQXDHSquare
open CatCrypt.Crypto.KEM.Games (Scheme)
open CatCrypt.Crypto.OracleGameUpToBad
open scoped ENNReal

/-! ## Activations with one call over a start given by any distribution -/

section Drive0

variable {σ τ E O EG OG Rs Rf : Type} [Fintype Rf] [Nonempty Rf]

/-- `withSubP` without resumption, over a start that is the image of a draw from any distribution
`μ` and a subroutine step that is the image of a uniform draw, is the image of the draw of the
start followed by an independent uniform draw for the call. -/
theorem withSubP_zero_eq_bind (start : σ → E → PMF (σ × (EG ⊕ O)))
    (step : τ → EG → PMF (τ × OG)) (res : σ → OG → PMF (σ × (EG ⊕ O)))
    (fin : σ → OG → PMF (σ × O)) (μ : PMF Rs) (startD : σ → E → Rs → σ × (EG ⊕ O))
    (stepD : τ → EG → Rf → τ × OG) (finV : σ → OG → σ × O) (t : σ × τ) (e : E)
    (hstart : start t.1 e = μ.map (startD t.1 e))
    (hstep : ∀ t g, step t g = (PMF.uniformFintype Rf).map (stepD t g))
    (hfin : ∀ s o, fin s o = PMF.pure (finV s o)) :
    withSubP start step res fin 0 t e =
      μ.bind fun a => (PMF.uniformFintype Rf).map fun b =>
        (((drive0D stepD finV (startD t.1 e a).1 (startD t.1 e a).2 t.2 b).1,
          (drive0D stepD finV (startD t.1 e a).1 (startD t.1 e a).2 t.2 b).2.1),
        (drive0D stepD finV (startD t.1 e a).1 (startD t.1 e a).2 t.2 b).2.2) := by
  simp only [withSubP, hstart, PMF.bind_map, Function.comp_def,
    driveP_zero_eq step res fin stepD finV hstep hfin, PMF.map_comp]

end Drive0

/-! ## Draws of a step -/

/-- A draw of a step of PQXDH: a draw of X3DH (a secret of a new session, the long-term secrets
of two parties and a value of the key derivation), a KEM key pair, and an encapsulation, absent
when the step has no public key to encapsulate to. -/
abbrev PDraw (S K PK SK SS C : Type) := Draw S K × (PK × SK) × Option (SS × C)

section Dist

variable {S K PK SK SS C : Type} [Fintype S] [Nonempty S] [Fintype K] [Nonempty K]
  (P : Scheme PK SK SS C)

/-- The distribution of the encapsulation of a step: an encapsulation to `pk` when the step has
the public key `pk`, and nothing otherwise. -/
noncomputable def encD : Option PK → PMF (Option (SS × C))
  | none => PMF.pure none
  | some pk => (P.encaps pk).map some

/-- The distribution of a draw of a step with the public key `o`: a uniform draw of X3DH, a key
pair of `P`, and the encapsulation to `o`, independent. -/
noncomputable def pDist (o : Option PK) : PMF (PDraw S K PK SK SS C) :=
  (PMF.uniformFintype (Draw S K)).bind fun r => P.keygen.bind fun kp =>
    (encD P o).map fun kc => (r, kp, kc)

omit [Fintype S] [Nonempty S] [Fintype K] [Nonempty K] in
/-- The image of a distribution under a constant map. -/
theorem map_fun_const {α β : Type} (p : PMF α) (b : β) : p.map (fun _ => b) = PMF.pure b :=
  PMF.map_const p b

/-- An image of a draw that reads the draw of X3DH only. -/
theorem pDist_map_fst {γ : Type} (o : Option PK) (F : PDraw S K PK SK SS C → γ)
    (g : Draw S K → γ) (hF : ∀ d, F d = g d.1) :
    (pDist P o).map F = (PMF.uniformFintype (Draw S K)).map g := by
  rw [funext hF]
  simp only [pDist, PMF.map_bind, PMF.map_comp, Function.comp_def, map_fun_const,
    PMF.bind_const]
  rfl

/-- An image of a draw that reads the draw of X3DH and the key pair. -/
theorem pDist_map_kp {γ : Type} (o : Option PK) (F : PDraw S K PK SK SS C → γ)
    (g : Draw S K → PK × SK → γ) (hF : ∀ d, F d = g d.1 d.2.1) :
    (pDist P o).map F = (PMF.uniformFintype (Draw S K)).bind fun r => P.keygen.map (g r) := by
  rw [funext hF]
  simp only [pDist, PMF.map_bind, PMF.map_comp, Function.comp_def, map_fun_const]
  rfl

/-- An image of a draw with a public key that reads the draw of X3DH and the encapsulation. -/
theorem pDist_map_enc {γ : Type} (pk : PK) (F : PDraw S K PK SK SS C → γ)
    (g : Draw S K → Option (SS × C) → γ) (hF : ∀ d, F d = g d.1 d.2.2) :
    (pDist P (some pk)).map F =
      (PMF.uniformFintype (Draw S K)).bind fun r => (P.encaps pk).map fun kc => g r (some kc) := by
  rw [funext hF]
  simp only [pDist, encD, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_const]

/-- A uniform draw of X3DH read at its first component is a uniform secret. -/
theorem uniform_draw_bind_fst {γ : Type} (H : S → PMF γ) :
    ((PMF.uniformFintype (Draw S K)).bind fun r => H r.1) = (PMF.uniformFintype S).bind H := by
  rw [PMF.uniform_prod_eq_bind (A := S)]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, PMF.bind_const]

end Dist

/-! ## The real world as a function of one draw -/

section RealDraw

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [DecidableEq SS] (P : Scheme PK SK SS C) (G : DHGroup S W)

/-- The public key to which the event `e` encapsulates from the state `s`: the KEM public key of
the peer's session, for the completion of a session with a record. -/
def encPk (s : PSt S W K PK SK SS C) : OEv W SS C → Option PK
  | .inr (.complete sid pid) =>
    match s.x.st.recs (sid, pid) with
    | some r => pkOf s sid r.peer
    | none => none
  | _ => none

/-- `pqComplete` with the draw `d` of X3DH and the encapsulation `kc`. -/
def pqCompleteD (s : PSt S W K PK SK SS C) (x : Inst) (d : Draw S K) (kc : Option (SS × C)) :
    POut S W K PK C × PSt S W K PK SK SS C :=
  match s.x.st.recs x, s.x.eph x with
  | some r, some ek =>
    match opkOf s.x x.1 r.peer, pkOf s x.1 r.peer, kc with
    | some opk, some _, some kc =>
      if r.role = .initiator ∧ r.key.isNone then
        (.inl .ack, pKeyed { s with x := (ltD (ltD s.x x.2 d.2.1).2 r.peer d.2.2.1).2,
                                    ct := Function.update s.ct x (some kc.2) } x r
          (roDet s.ro (aliceInp G x.1 x.2 r.peer (ltD s.x x.2 d.2.1).1.1 ek
            (G.pub (ltD (ltD s.x x.2 d.2.1).2 r.peer d.2.2.1).1.1)
            (G.pub (ltD (ltD s.x x.2 d.2.1).2 r.peer d.2.2.1).1.2) (G.pub opk), kc.1)
            d.2.2.2).1
          (roDet s.ro (aliceInp G x.1 x.2 r.peer (ltD s.x x.2 d.2.1).1.1 ek
            (G.pub (ltD (ltD s.x x.2 d.2.1).2 r.peer d.2.2.1).1.1)
            (G.pub (ltD (ltD s.x x.2 d.2.1).2 r.peer d.2.2.1).1.2) (G.pub opk), kc.1)
            d.2.2.2).2)
      else (.inl .ack, s)
    | _, _, _ => (.inl .ack, s)
  | _, _ => (.inl .ack, s)

/-- `pqSend` with the draw `d` of X3DH. -/
def pqSendD (s : PSt S W K PK SK SS C) (x : Inst) (e : W) (c : C) (d : Draw S K) :
    POut S W K PK C × PSt S W K PK SK SS C :=
  match s.x.st.recs x, s.x.eph x, s.kem x with
  | some r, some opk, some kp =>
    match P.decaps kp.2 c with
    | some ss =>
      if r.role = .responder ∧ r.key.isNone then
        (.inl .ack, pKeyed { s with x := (ltD (ltD s.x x.2 d.2.1).2 r.peer d.2.2.1).2 } x r
          (roDet s.ro (bobInp G x.1 r.peer x.2
            (G.pub (ltD (ltD s.x x.2 d.2.1).2 r.peer d.2.2.1).1.1) e
            (ltD s.x x.2 d.2.1).1.1 (ltD s.x x.2 d.2.1).1.2 opk, ss) d.2.2.2).1
          (roDet s.ro (bobInp G x.1 r.peer x.2
            (G.pub (ltD (ltD s.x x.2 d.2.1).2 r.peer d.2.2.1).1.1) e
            (ltD s.x x.2 d.2.1).1.1 (ltD s.x x.2 d.2.1).1.2 opk, ss) d.2.2.2).2)
      else (.inl .ack, s)
    | none => (.inl .ack, s)
  | _, _, _ => (.inl .ack, s)

/-- A step of the real protocol with the draw `d`. -/
def realD (s : PSt S W K PK SK SS C) (e : OEv W SS C) (d : PDraw S K PK SK SS C) :
    OOut S W K PK C × PSt S W K PK SK SS C :=
  match e with
  | .inl (.newSession sid pid peer role) =>
    if (s.x.st.recs (sid, pid)).isNone then
      if role = .responder then
        (.inl .ok, { s with x := { s.x with st := addSession s.x.st (sid, pid) peer role,
                                            eph := Function.update s.x.eph (sid, pid) (some d.1.1) },
                            kem := Function.update s.kem (sid, pid) (some d.2.1) })
      else
        (.inl .ok, { s with x := { s.x with st := addSession s.x.st (sid, pid) peer role,
                                            eph := Function.update s.x.eph (sid, pid) (some d.1.1) } })
    else (.inl .ok, s)
  | .inl (.getKey sid pid) => (.inl (.key (keyOf s.x.st (sid, pid))), s)
  | .inr .idle => (.inr (.inl .ack), s)
  | .inr .poll => (.inr (.inl (.notice (pollStep s.x.st).2)),
      { s with x := { s.x with st := (pollStep s.x.st).1 } })
  | .inr (.pub pid) =>
    (.inr (.inl (.pub (G.pub (ltD s.x pid d.1.2.1).1.1) (G.pub (ltD s.x pid d.1.2.1).1.2))),
      { s with x := (ltD s.x pid d.1.2.1).2 })
  | .inr (.ephPub sid pid) => (.inr (.inl (.eph (ephPubOf G s.x (sid, pid)))), s)
  | .inr (.pqPub sid pid) => (.inr (.inr (pkOf s sid pid, s.ct (sid, pid))), s)
  | .inr (.corrupt pid) =>
    if Named s.x.st pid then (.inr (.inl (.secret none)), s) else
      (.inr (.inl (.secret (some (ltD s.x pid d.1.2.1).1))),
        { s with x := { (ltD s.x pid d.1.2.1).2 with
                          st := corruptStep (ltD s.x pid d.1.2.1).2.st pid } })
  | .inr (.complete sid pid) =>
    (.inr (pqCompleteD G s (sid, pid) d.1 d.2.2).1, (pqCompleteD G s (sid, pid) d.1 d.2.2).2)
  | .inr (.send sid pid e c) =>
    (.inr (pqSendD P G s (sid, pid) e c d.1).1, (pqSendD P G s (sid, pid) e c d.1).2)
  | .inr (.kdf x) =>
    (.inr (.inl (.hash (roDet s.ro x d.1.2.2.2).1)), { s with ro := (roDet s.ro x d.1.2.2.2).2 })

omit [DecidableEq W] [DecidableEq SS] in
/-- Three uniform draws in sequence, the long-term secrets of two parties and a value of the
key derivation, followed by a draw from `ν`, are a uniform draw of X3DH followed by `ν` and a
uniform value of the key derivation read last. -/
theorem lt_lt_ro_bind {γ δ : Type} (ν : PMF δ) (g : S × S → S × S → δ → K → γ) :
    ((PMF.uniformFintype (S × S)).bind fun l₁ => (PMF.uniformFintype (S × S)).bind fun l₂ =>
      ν.bind fun a => (PMF.uniformFintype K).map (g l₁ l₂ a)) =
      (PMF.uniformFintype (Draw S K)).bind fun r => ν.map fun a => g r.2.1 r.2.2.1 a r.2.2.2 := by
  have hc : ∀ l₁ l₂, (ν.bind fun a => (PMF.uniformFintype K).map (g l₁ l₂ a)) =
      (PMF.uniformFintype K).bind fun k => ν.map fun a => g l₁ l₂ a k := by
    intro l₁ l₂
    change (ν.bind fun a => (PMF.uniformFintype K).bind fun k => PMF.pure (g l₁ l₂ a k)) =
      (PMF.uniformFintype K).bind fun k => ν.bind fun a => PMF.pure (g l₁ l₂ a k)
    exact PMF.bind_comm _ _ _
  simp only [hc]
  symm
  simp only [PMF.uniform_prod_eq_bind (A := S) (B := (S × S) × (S × S) × K),
    PMF.uniform_prod_eq_bind (A := S × S) (B := (S × S) × K),
    PMF.uniform_prod_eq_bind (A := S × S) (B := K), PMF.bind_bind, PMF.bind_map,
    Function.comp_def, PMF.bind_const]

omit [DecidableEq W] [DecidableEq SS] in
/-- The long-term secrets of two parties and a value of the key derivation, in sequence, are an
image of a uniform draw of X3DH. -/
theorem lt_lt_ro_map {γ : Type} (g : S × S → S × S → K → γ) :
    ((PMF.uniformFintype (S × S)).bind fun l₁ => (PMF.uniformFintype (S × S)).bind fun l₂ =>
      (PMF.uniformFintype K).map (g l₁ l₂)) =
      (PMF.uniformFintype (Draw S K)).map fun r => g r.2.1 r.2.2.1 r.2.2.2 := by
  have h := lt_lt_ro_bind (S := S) (K := K) (PMF.pure ()) (fun l₁ l₂ _ k => g l₁ l₂ k)
  simp only [PMF.pure_bind, PMF.pure_map] at h
  exact h

/-- `pqComplete` is the image of a draw under `pqCompleteD`. -/
theorem pqComplete_eq_map (s : PSt S W K PK SK SS C) (x : Inst) :
    pqComplete P G s x =
      (pDist P (encPk s (.inr (.complete x.1 x.2)))).map fun d => pqCompleteD G s x d.1 d.2.2 := by
  have hP : ∀ (o : Option PK) (b : POut S W K PK C × PSt S W K PK SK SS C),
      PMF.pure b = (pDist (S := S) (K := K) P o).map fun _ => b := fun o b => (map_fun_const _ _).symm
  cases hr : s.x.st.recs x with
  | none => simp only [pqComplete, pqCompleteD, hr, map_fun_const]
  | some rc =>
    cases he : s.x.eph x with
    | none => simp only [pqComplete, pqCompleteD, hr, he, map_fun_const]
    | some ek =>
      cases ho : opkOf s.x x.1 rc.peer with
      | none => simp only [pqComplete, pqCompleteD, hr, he, ho, map_fun_const]
      | some opk =>
        cases hk : pkOf s x.1 rc.peer with
        | none => simp only [pqComplete, pqCompleteD, hr, he, ho, hk, map_fun_const]
        | some pk =>
          have hpk : encPk s (.inr (.complete x.1 x.2)) = some pk := by
            simp only [encPk, hr, hk]
          rw [hpk, pDist_map_enc P pk _ (fun d kc => pqCompleteD G s x d kc) (fun _ => rfl)]
          by_cases hc : rc.role = .initiator ∧ rc.key.isNone
          · simp only [pqComplete, pqCompleteD, hr, he, ho, hk, hc, and_self, ↓reduceIte,
              ltAt_eq_map, roAt_eq_map, PMF.bind_map, PMF.map_comp, Function.comp_def]
            exact lt_lt_ro_bind _ _
          · simp only [pqComplete, pqCompleteD, hr, he, ho, hk, hc, ↓reduceIte, map_fun_const,
              PMF.bind_const]

/-- `pqSend` is the image of a draw under `pqSendD`. -/
theorem pqSend_eq_map (s : PSt S W K PK SK SS C) (x : Inst) (e : W) (c : C) :
    pqSend P G s x e c = (PMF.uniformFintype (Draw S K)).map (pqSendD P G s x e c) := by
  have hP : ∀ b : POut S W K PK C × PSt S W K PK SK SS C,
      PMF.pure b = (PMF.uniformFintype (Draw S K)).map fun _ => b := fun b =>
    (map_fun_const _ _).symm
  change _ = (PMF.uniformFintype (Draw S K)).map fun d => pqSendD P G s x e c d
  cases hr : s.x.st.recs x with
  | none => simp only [pqSend, pqSendD, hr, hP]
  | some rc =>
    cases he : s.x.eph x with
    | none => simp only [pqSend, pqSendD, hr, he, hP]
    | some opk =>
      cases hk : s.kem x with
      | none => simp only [pqSend, pqSendD, hr, he, hk, hP]
      | some kp =>
        cases hd : P.decaps kp.2 c with
        | none => simp only [pqSend, pqSendD, hr, he, hk, hd, hP]
        | some ss =>
          by_cases hc : rc.role = .responder ∧ rc.key.isNone
          · simp only [pqSend, pqSendD, hr, he, hk, hd, hc, and_self, ↓reduceIte, ltAt_eq_map,
              roAt_eq_map, PMF.bind_map, PMF.map_comp, Function.comp_def]
            exact lt_lt_ro_map _
          · simp only [pqSend, pqSendD, hr, he, hk, hd, hc, ↓reduceIte, hP]

/-- **The oracle of the real game** is the image of a draw under `realD`. -/
theorem realGame_oracle_eq (s : PSt S W K PK SK SS C) (e : OEv W SS C) :
    (realGame P G).oracle () s e = (pDist P (encPk s e)).map (realD P G s e) := by
  have hP : ∀ (o : Option PK) (b : OOut S W K PK C × PSt S W K PK SK SS C),
      PMF.pure b = (pDist (S := S) (K := K) P o).map fun _ => b := fun o b => (map_fun_const _ _).symm
  change _ = (pDist P _).map fun d => realD P G s e d
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e, c⟩ | x)
  · by_cases h : (s.x.st.recs (sid, pid)).isNone = true
    · by_cases hr : role = .responder
      · simp only [realGame, pqHon, realHon, realD, h, hr, and_self, ↓reduceIte, PMF.bind_map,
          PMF.map_bind, PMF.map_comp, Function.comp_def]
        rw [pDist_map_kp (γ := OOut S W K PK C × PSt S W K PK SK SS C) P _ _
          (fun r kp => ((Sum.inl HOut.ok : OOut S W K PK C), { s with
            x := { s.x with st := addSession s.x.st (sid, pid) peer .responder,
                            eph := Function.update s.x.eph (sid, pid) (some r.1) },
            kem := Function.update s.kem (sid, pid) (some kp) })) (fun _ => rfl)]
        exact (uniform_draw_bind_fst (γ := OOut S W K PK C × PSt S W K PK SK SS C) (K := K)
          (fun y => P.keygen.map fun kp => ((Sum.inl HOut.ok : OOut S W K PK C), { s with
            x := { s.x with st := addSession s.x.st (sid, pid) peer .responder,
                            eph := Function.update s.x.eph (sid, pid) (some y) },
            kem := Function.update s.kem (sid, pid) (some kp) }))).symm
      · simp only [realGame, pqHon, realHon, realD, h, hr, and_false, ↓reduceIte, PMF.bind_map,
          Function.comp_def]
        rw [pDist_map_fst (γ := OOut S W K PK C × PSt S W K PK SK SS C) P _ _
          (fun r => ((Sum.inl HOut.ok : OOut S W K PK C), { s with
            x := { s.x with st := addSession s.x.st (sid, pid) peer role,
                            eph := Function.update s.x.eph (sid, pid) (some r.1) } }))
          (fun _ => rfl)]
        change PMF.map _ ((PMF.uniformFintype S).map _) = _
        rw [PMF.map_comp, map_uniform_eq_map_prod_fst (A := S) (B := (S × S) × (S × S) × K)]
        rfl
    · simp only [realGame, pqHon, realHon, realD, h, Bool.false_eq_true, false_and, ↓reduceIte,
        PMF.pure_bind, PMF.pure_map, map_fun_const]
  · simp only [realGame, pqHon, realD, PMF.pure_map, map_fun_const]
  · simp only [realGame, pqAdv, onX, realAdv, realD, PMF.pure_map, map_fun_const]
  · simp only [realGame, pqAdv, onX, realAdv, realD, PMF.pure_map, map_fun_const]
  · simp only [realGame, pqAdv, onX, realAdv, realD, PMF.map_comp]
    rw [pDist_map_fst (γ := OOut S W K PK C × PSt S W K PK SK SS C) P _ _ (fun r => ((Sum.inr (Sum.inl (ROut.pub (G.pub (ltD s.x pid r.2.1).1.1)
      (G.pub (ltD s.x pid r.2.1).1.2))) : OOut S W K PK C), { s with x := (ltD s.x pid r.2.1).2 })) (fun _ => rfl)]
    exact ltAt_map_eq s.x pid _
  · simp only [realGame, pqAdv, onX, realAdv, realD, PMF.pure_map, map_fun_const]
  · simp only [realGame, pqAdv, realD, PMF.pure_map, map_fun_const]
  · simp only [realGame, pqAdv, onX, corruptRStep]
    by_cases h : Named s.x.st pid = true
    · simp only [realD, h, ↓reduceIte, PMF.pure_map, map_fun_const]
    · simp only [realD, h, Bool.false_eq_true, ↓reduceIte, PMF.map_comp]
      rw [pDist_map_fst (γ := OOut S W K PK C × PSt S W K PK SK SS C) P _ _ (fun r => ((Sum.inr (Sum.inl (ROut.secret
          (some (ltD s.x pid r.2.1).1))) : OOut S W K PK C),
        { s with x := { (ltD s.x pid r.2.1).2 with
                          st := corruptStep (ltD s.x pid r.2.1).2.st pid } })) (fun _ => rfl)]
      exact ltAt_map_eq s.x pid _
  · simp only [realGame, pqAdv, realD, pqComplete_eq_map, PMF.map_comp]
    rfl
  · simp only [realGame, pqAdv, realD, pqSend_eq_map, PMF.map_comp]
    rw [pDist_map_fst (γ := OOut S W K PK C × PSt S W K PK SK SS C) P _ _ (fun r => ((Sum.inr (pqSendD P G s (sid, pid) e c r).1 :
      OOut S W K PK C), (pqSendD P G s (sid, pid) e c r).2)) (fun _ => rfl)]
    rfl
  · simp only [realGame, pqAdv, realD, roAt_eq_map, PMF.map_comp]
    rw [pDist_map_fst (γ := OOut S W K PK C × PSt S W K PK SK SS C) P _ _ (fun r => ((Sum.inr (Sum.inl (ROut.hash (roDet s.ro x r.2.2.2).1)) :
      OOut S W K PK C), { s with ro := (roDet s.ro x r.2.2.2).2 })) (fun _ => rfl),
      map_uniform_eq_map_prod_snd (A := S × S), map_uniform_eq_map_prod_snd (A := S × S),
      map_uniform_eq_map_prod_snd (A := S)]
    rfl

end RealDraw

/-! ## The simulated world as a function of draws -/

section SimDraw

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (G : DHGroup S W)

/-- `deliver` with the value `k` of the key derivation. -/
def deliverD (s : PSt S W K PK SK SS C) (inp : Inst → Option (PInp W SS)) (x : Inst) (r : Rec K)
    (ip : PInp W SS) (k : K) : SimSt S W K PK SK SS C × Dec S W K PK C :=
  if Exposed s.x.st x r then
    ((pKeyed s x r (roDet s.ro ip k).1 (roDet s.ro ip k).2, Function.update inp x (some ip),
        .out (.inl .ack)), .inl (.inr (.newKey x.1 x.2 (roDet s.ro ip k).1)))
  else
    ((pKeyed s x r default s.ro, Function.update inp x (some ip), .out (.inl .ack)),
      .inl (.inr (if (inp (x.1, r.peer)).all (· = ip) then .newKey x.1 x.2 default
        else .newKeyUnlinked x.1 x.2 default)))

omit [Field S] [Fintype S] in
/-- `deliver` is the lift of the image of a uniform value under `deliverD`. -/
theorem deliver_eq (s : PSt S W K PK SK SS C) (inp : Inst → Option (PInp W SS)) (x : Inst)
    (r : Rec K) (ip : PInp W SS) :
    deliver s inp x r ip = liftPMF ((PMF.uniformFintype K).map (deliverD s inp x r ip)) := by
  change _ = liftPMF ((PMF.uniformFintype K).map fun k => deliverD s inp x r ip k)
  by_cases h : Exposed s.x.st x r
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

/-- `simComplete` with the draw `d` of X3DH and the encapsulation `kc`. -/
def simCompleteD (s : SimSt S W K PK SK SS C) (x : Inst) (d : Draw S K)
    (kc : Option (SS × C)) : SimSt S W K PK SK SS C × Dec S W K PK C :=
  match s.1.x.st.recs x, s.1.x.eph x with
  | some r, some ek =>
    match opkOf s.1.x x.1 r.peer, pkOf s.1 x.1 r.peer, kc with
    | some opk, some _, some kc =>
      if r.role = .initiator ∧ r.key.isNone then
        deliverD { s.1 with x := (ltD (ltD s.1.x x.2 d.2.1).2 r.peer d.2.2.1).2,
                            ct := Function.update s.1.ct x (some kc.2) } s.2.1 x r
          (aliceInp G x.1 x.2 r.peer (ltD s.1.x x.2 d.2.1).1.1 ek
            (G.pub (ltD (ltD s.1.x x.2 d.2.1).2 r.peer d.2.2.1).1.1)
            (G.pub (ltD (ltD s.1.x x.2 d.2.1).2 r.peer d.2.2.1).1.2) (G.pub opk), kc.1) d.2.2.2
      else ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
    | _, _, _ => ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
  | _, _ => ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))

/-- `simSend` with the draw `d` of X3DH. -/
def simSendD (s : SimSt S W K PK SK SS C) (x : Inst) (e : W) (c : C) (d : Draw S K) :
    SimSt S W K PK SK SS C × Dec S W K PK C :=
  match s.1.x.st.recs x, s.1.x.eph x, s.1.kem x with
  | some r, some opk, some kp =>
    match P.decaps kp.2 c with
    | some ss =>
      if r.role = .responder ∧ r.key.isNone then
        deliverD { s.1 with x := (ltD (ltD s.1.x x.2 d.2.1).2 r.peer d.2.2.1).2 } s.2.1 x r
          (bobInp G x.1 r.peer x.2 (G.pub (ltD (ltD s.1.x x.2 d.2.1).2 r.peer d.2.2.1).1.1) e
            (ltD s.1.x x.2 d.2.1).1.1 (ltD s.1.x x.2 d.2.1).1.2 opk, ss) d.2.2.2
      else ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
    | none => ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
  | _, _, _ => ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))

/-- `simStart` with the draw `d`. -/
def simStartD (s : SimSt S W K PK SK SS C) (e : OEv W SS C) (d : PDraw S K PK SK SS C) :
    SimSt S W K PK SK SS C × Dec S W K PK C :=
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
      .inr (.inr (.inl (.pub (G.pub (ltD s.1.x pid d.1.2.1).1.1)
        (G.pub (ltD s.1.x pid d.1.2.1).1.2)))))
  | .inr (.ephPub sid pid) =>
    ((s.1, s.2.1, .fwd), .inr (.inr (.inl (.eph (ephPubOf G s.1.x (sid, pid))))))
  | .inr (.pqPub sid pid) =>
    ((s.1, s.2.1, .fwd), .inr (.inr (.inr (pkOf s.1 sid pid, s.1.ct (sid, pid)))))
  | .inr (.corrupt pid) =>
    if Named s.1.x.st pid then ((s.1, s.2.1, .fwd), .inr (.inr (.inl (.secret none)))) else
      (({ s.1 with x := { (ltD s.1.x pid d.1.2.1).2 with
                            st := corruptStep (ltD s.1.x pid d.1.2.1).2.st pid } }, s.2.1,
          .out (.inl (.secret (some (ltD s.1.x pid d.1.2.1).1)))), .inl (.inr (.corrupt pid)))
  | .inr (.complete sid pid) => simCompleteD G s (sid, pid) d.1 d.2.2
  | .inr (.send sid pid e c) => simSendD P G s (sid, pid) e c d.1
  | .inr (.kdf x) =>
    (({ s.1 with ro := (roDet s.1.ro x d.1.2.2.2).2 }, s.2.1, .fwd),
      .inr (.inr (.inl (.hash (roDet s.1.ro x d.1.2.2.2).1))))

omit [DecidableEq W] [DecidableEq SS] in
/-- The key generation of `kemOps P` is the lift of `P.keygen`. -/
theorem kemOps_keygen : (kemOps P).keygen = liftPMF P.keygen :=
  sampleFrom_ofPMF_eq_liftPMF _

omit [DecidableEq W] [DecidableEq SS] in
/-- The encapsulation of `kemOps P` is the lift of `P.encaps`. -/
theorem kemOps_encaps (pk : PK) : (kemOps P).encaps pk = liftPMF (P.encaps pk) :=
  sampleFrom_ofPMF_eq_liftPMF _

/-- **The start of the simulator as a function of a draw**: `simStart` is the lift of the image
of a draw under `simStartD`. -/
theorem simStart_eq (s : SimSt S W K PK SK SS C) (e : OEv W SS C) :
    simStart (kemOps P) G s e =
      liftPMF ((pDist P (encPk s.1 e)).map (simStartD P G s e)) := by
  have hP : ∀ (o : Option PK) (b : SimSt S W K PK SK SS C × Dec S W K PK C),
      (SPComp.pure b : SPComp _) = liftPMF ((pDist (S := S) (K := K) P o).map fun _ => b) :=
    fun o b => by rw [liftPMF_pure]; exact congrArg liftPMF (map_fun_const _ _).symm
  change _ = liftPMF ((pDist P _).map fun d => simStartD P G s e d)
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e, c⟩ | x)
  · by_cases h : (s.1.x.st.recs (sid, pid)).isNone = true
    · by_cases hr : role = .responder
      · simp only [simStart, simStartD, h, hr, ↓reduceIte, sample_eq_liftPMF, kemOps_keygen,
          map_liftPMF, liftPMF_bind_liftPMF]
        rw [pDist_map_kp (γ := SimSt S W K PK SK SS C × Dec S W K PK C) P _ _ (fun r kp => (({ s.1 with
            x := { s.1.x with st := addSession s.1.x.st (sid, pid) peer .responder,
                              eph := Function.update s.1.x.eph (sid, pid) (some r.1) },
            kem := Function.update s.1.kem (sid, pid) (some kp) }, s.2.1, Phase.fwd),
          .inl (.inl (.newSession sid pid peer .responder)))) (fun _ => rfl)]
        exact congrArg liftPMF (uniform_draw_bind_fst
          (γ := SimSt S W K PK SK SS C × Dec S W K PK C) (K := K) (fun y => P.keygen.map fun kp =>
            (({ s.1 with
              x := { s.1.x with st := addSession s.1.x.st (sid, pid) peer .responder,
                                eph := Function.update s.1.x.eph (sid, pid) (some y) },
              kem := Function.update s.1.kem (sid, pid) (some kp) }, s.2.1, Phase.fwd),
            (.inl (.inl (.newSession sid pid peer .responder)) : Dec S W K PK C)))).symm
      · simp only [simStart, simStartD, h, hr, ↓reduceIte, sample_eq_liftPMF, liftPMF_bind_pure]
        rw [pDist_map_fst (γ := SimSt S W K PK SK SS C × Dec S W K PK C) P _ _ (fun r => (({ s.1 with
            x := { s.1.x with st := addSession s.1.x.st (sid, pid) peer role,
                              eph := Function.update s.1.x.eph (sid, pid) (some r.1) } },
            s.2.1, Phase.fwd), (.inl (.inl (.newSession sid pid peer role)) : Dec S W K PK C))) (fun _ => rfl),
          map_uniform_eq_map_prod_fst (B := (S × S) × (S × S) × K)]
    · simp only [simStart, simStartD, h, Bool.false_eq_true, ↓reduceIte, map_fun_const, liftPMF_pure]
  · simp only [simStart, simStartD, map_fun_const, liftPMF_pure]
  · simp only [simStart, simStartD, map_fun_const, liftPMF_pure]
  · simp only [simStart, simStartD, map_fun_const, liftPMF_pure]
  · simp only [simStart, simStartD, ltStep_eq, map_liftPMF]
    rw [pDist_map_fst (γ := SimSt S W K PK SK SS C × Dec S W K PK C) P _ _ (fun r => (({ s.1 with x := (ltD s.1.x pid r.2.1).2 }, s.2.1, Phase.fwd),
      (.inr (.inr (.inl (.pub (G.pub (ltD s.1.x pid r.2.1).1.1)
        (G.pub (ltD s.1.x pid r.2.1).1.2)))) : Dec S W K PK C))) (fun _ => rfl)]
    exact congrArg liftPMF (ltAt_map_eq s.1.x pid _)
  · simp only [simStart, simStartD, map_fun_const, liftPMF_pure]
  · simp only [simStart, simStartD, map_fun_const, liftPMF_pure]
  · by_cases h : Named s.1.x.st pid = true
    · simp only [simStart, simStartD, simCorrupt, h, ↓reduceIte, map_fun_const, liftPMF_pure]
    · simp only [simStart, simCorrupt, simStartD, h, Bool.false_eq_true, ↓reduceIte, ltStep_eq,
        map_liftPMF]
      rw [pDist_map_fst (γ := SimSt S W K PK SK SS C × Dec S W K PK C) P _ _ (fun r => (({ s.1 with x := { (ltD s.1.x pid r.2.1).2 with
                            st := corruptStep (ltD s.1.x pid r.2.1).2.st pid } }, s.2.1,
          .out (.inl (.secret (some (ltD s.1.x pid r.2.1).1)))),
          (.inl (.inr (.corrupt pid)) : Dec S W K PK C))) (fun _ => rfl)]
      exact congrArg liftPMF (ltAt_map_eq s.1.x pid _)
  · cases hr : s.1.x.st.recs (sid, pid) with
    | none => simp only [simStart, simComplete, simStartD, simCompleteD, hr, map_fun_const,
        liftPMF_pure]
    | some rc =>
      cases he : s.1.x.eph (sid, pid) with
      | none => simp only [simStart, simComplete, simStartD, simCompleteD, hr, he, map_fun_const,
          liftPMF_pure]
      | some ek =>
        cases ho : opkOf s.1.x sid rc.peer with
        | none => simp only [simStart, simComplete, simStartD, simCompleteD, hr, he, ho,
            map_fun_const, liftPMF_pure]
        | some opk =>
          cases hk : pkOf s.1 sid rc.peer with
          | none => simp only [simStart, simComplete, simStartD, simCompleteD, hr, he, ho, hk,
              map_fun_const, liftPMF_pure]
          | some pk =>
            have hpk : encPk s.1 (.inr (.complete sid pid)) = some pk := by
              simp only [encPk, hr, hk]
            simp only [simStartD]
            rw [hpk, pDist_map_enc P pk _ (fun d kc => simCompleteD G s (sid, pid) d kc)
              (fun _ => rfl)]
            by_cases hc : rc.role = .initiator ∧ rc.key.isNone
            · simp only [simStart, simComplete, simCompleteD, hr, he, ho, hk, hc, and_self,
                ↓reduceIte, ltStep_eq, kemOps_encaps, deliver_eq, liftPMF_bind_liftPMF,
                ltAt_eq_map, PMF.bind_map, Function.comp_def]
              exact congrArg liftPMF (lt_lt_ro_bind _ _)
            · simp only [simStart, simComplete, simCompleteD, hr, he, ho, hk, hc, ↓reduceIte,
                map_fun_const, PMF.bind_const, liftPMF_pure]
  · simp only [simStartD]
    rw [pDist_map_fst P _ _ (fun d => simSendD P G s (sid, pid) e c d) (fun _ => rfl)]
    cases hr : s.1.x.st.recs (sid, pid) with
    | none => simp only [simStart, simSend, simSendD, hr, map_fun_const, liftPMF_pure]
    | some rc =>
      cases he : s.1.x.eph (sid, pid) with
      | none => simp only [simStart, simSend, simSendD, hr, he, map_fun_const, liftPMF_pure]
      | some opk =>
        cases hk : s.1.kem (sid, pid) with
        | none => simp only [simStart, simSend, simSendD, hr, he, hk, map_fun_const,
            liftPMF_pure]
        | some kp =>
          cases hd : P.decaps kp.2 c with
          | none => simp only [simStart, simSend, simSendD, kemOps, hr, he, hk, hd,
              map_fun_const, liftPMF_pure]
          | some ss =>
            by_cases hc : rc.role = .responder ∧ rc.key.isNone
            · simp only [simStart, simSend, simSendD, kemOps, hr, he, hk, hd, hc, and_self,
                ↓reduceIte, ltStep_eq, deliver_eq, liftPMF_bind_liftPMF, ltAt_eq_map,
                PMF.bind_map, Function.comp_def]
              exact congrArg liftPMF (lt_lt_ro_map _)
            · simp only [simStart, simSend, simSendD, kemOps, hr, he, hk, hd, hc, ↓reduceIte,
                map_fun_const, liftPMF_pure]
  · simp only [simStart, simStartD, roStep_eq, map_liftPMF, roAt_eq_map, PMF.map_comp]
    rw [pDist_map_fst (γ := SimSt S W K PK SK SS C × Dec S W K PK C) P _ _ (fun r => (({ s.1 with ro := (roDet s.1.ro x r.2.2.2).2 }, s.2.1, Phase.fwd),
      (.inr (.inr (.inl (.hash (roDet s.1.ro x r.2.2.2).1))) : Dec S W K PK C))) (fun _ => rfl),
      map_uniform_eq_map_prod_snd (A := S × S), map_uniform_eq_map_prod_snd (A := S × S),
      map_uniform_eq_map_prod_snd (A := S)]
    rfl

end SimDraw


/-! ## The simulated game as an image of draws -/

section SimGame

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (G : DHGroup S W)

/-- The finish of the simulator. -/
def finV (s : SimSt S W K PK SK SS C) (o : FOut K) :
    SimSt S W K PK SK SS C × OOut S W K PK C :=
  ((s.1, s.2.1, .fwd), simOut s.2.2 o)

/-- **A step of the simulated world** with the draw `r = (d, kf)`: the start of the simulator
reads `d` and the call to `F_AKE` reads `kf`. -/
def simWorldD (t : SimSt S W K PK SK SS C × St K) (e : OEv W SS C)
    (r : PDraw S K PK SK SS C × K) :
    (SimSt S W K PK SK SS C × St K) × OOut S W K PK C :=
  (((drive0D fStepD finV (simStartD P G t.1 e r.1).1 (simStartD P G t.1 e r.1).2 t.2 r.2).1,
    (drive0D fStepD finV (simStartD P G t.1 e r.1).1 (simStartD P G t.1 e r.1).2 t.2 r.2).2.1),
    (drive0D fStepD finV (simStartD P G t.1 e r.1).1 (simStartD P G t.1 e r.1).2 t.2 r.2).2.2)

omit [Field S] [DecidableEq W] [Inhabited K] [DecidableEq SS] in
/-- The distribution of a draw of the simulated world with the public key `o`: a draw of a step
and an independent uniform key of `F_AKE`. -/
noncomputable def simDist [Nonempty S] (o : Option PK) : PMF (PDraw S K PK SK SS C × K) :=
  (pDist P o).bind fun d => (PMF.uniformFintype K).map fun kf => (d, kf)

/-- **The oracle of the simulated game** is the image of a draw under `simWorldD`. -/
theorem simGame_oracle_eq (t : SimSt S W K PK SK SS C × St K) (e : OEv W SS C) :
    (simGame P G).oracle () t e =
      (simDist P (encPk t.1.1 e)).map fun r => (simWorldD P G t e r).swap := by
  have hstep : ((simProt (K := K) P G).withSub (F_AKE (SPComp.sample K) true)).step t e =
      liftPMF (withSubP (fun s e => (pDist P (encPk s.1 e)).map (simStartD P G s e))
        (fun t g => (PMF.uniformFintype K).map (fStepD t g))
        (fun s o => PMF.pure ((s.1, s.2.1, .fwd), .inr (simOut s.2.2 o)))
        (fun s o => PMF.pure (finV s o)) 0 t e) :=
    withSub_step_eq_liftPMF _ _ _ _ _ _ (simStart_eq P G) fStep_eq (fun _ _ => liftPMF_pure _)
      (fun _ _ => liftPMF_pure _) t e
  change (simWorld_pureNF P G t e).pmf.map Prod.swap = _
  rw [pmf_eq_of_eq_liftPMF (simWorld_pureNF P G t e) hstep,
    withSubP_zero_eq_bind _ _ _ _ _ (simStartD P G) fStepD finV t e rfl (fun _ _ => rfl)
      (fun _ _ => rfl)]
  simp only [simDist, PMF.map_bind, PMF.map_comp]
  rfl

end SimGame

/-! ## The joint world -/

section Coupling

variable {S K PK SK SS C : Type} [Field S] [Fintype S] [Fintype K] [Nonempty K]
  (P : Scheme PK SK SS C)

/-- Two draws in either order. -/
theorem bind_map_comm {α β γ : Type} (p : PMF α) (q : PMF β) (f : α → β → γ) :
    (p.bind fun a => q.map (f a)) = q.bind fun b => p.map fun a => f a b :=
  PMF.bind_comm p q fun a b => PMF.pure (f a b)

open Classical in
/-- The coupling of the encapsulations of the two worlds, with the public keys `oR` and `oS`:
one encapsulation for both when the keys agree, independent encapsulations otherwise. -/
noncomputable def encPair (oR oS : Option PK) : PMF (Option (SS × C) × Option (SS × C)) :=
  if oR = oS then (encD P oR).map fun c => (c, c)
  else (encD P oR).bind fun a => (encD P oS).map fun b => (a, b)

/-- The encapsulation of the real world in the coupling. -/
theorem encPair_map_fst (oR oS : Option PK) : (encPair P oR oS).map Prod.fst = encD P oR := by
  unfold encPair
  split_ifs
  · rw [PMF.map_comp]
    exact PMF.map_id _
  · simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, map_fun_const]
    exact PMF.bind_pure _

/-- The encapsulation of the simulated world in the coupling. -/
theorem encPair_map_snd (oR oS : Option PK) : (encPair P oR oS).map Prod.snd = encD P oS := by
  unfold encPair
  split_ifs with h
  · rw [PMF.map_comp, h]
    exact PMF.map_id _
  · simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_const]
    exact PMF.map_id _

/-- A draw of the joint world: the draw of X3DH and the key of `F_AKE`, a KEM key pair, and the
coupled encapsulations of the two worlds. -/
abbrev JDraw (S K PK SK SS C : Type) :=
  (Draw S K × K) × (PK × SK) × (Option (SS × C) × Option (SS × C))

/-- The distribution of a draw of the joint world with the public keys `oR` and `oS`. -/
noncomputable def jDist (oR oS : Option PK) : PMF (JDraw S K PK SK SS C) :=
  (PMF.uniformFintype (Draw S K × K)).bind fun rk => P.keygen.bind fun kp =>
    (encPair P oR oS).map fun kc => (rk, kp, kc)

/-- The draw of the real world from a draw of the joint world. -/
def realOf (b : Bool) (j : JDraw S K PK SK SS C) : PDraw S K PK SK SS C :=
  (cpl b j.1, j.2.1, j.2.2.1)

/-- The draw of the simulated world from a draw of the joint world. -/
def simOf (j : JDraw S K PK SK SS C) : PDraw S K PK SK SS C × K :=
  ((j.1.1, j.2.1, j.2.2.2), j.1.2)

/-- The real part of a draw of the joint world is a draw of the real world. -/
theorem jDist_map_realOf (b : Bool) (oR oS : Option PK) :
    (jDist (S := S) (K := K) P oR oS).map (realOf b) = pDist P oR := by
  have h1 : ∀ (rk : Draw S K × K) (kp : PK × SK),
      ((encPair P oR oS).map fun kc => (rk, kp, kc)).map (realOf b) =
      (encD P oR).map fun c => (cpl b rk, kp, c) := by
    intro rk kp
    rw [PMF.map_comp, ← encPair_map_fst P oR oS, PMF.map_comp]
    rfl
  simp only [jDist, PMF.map_bind, h1]
  rw [pDist, ← map_uniform_cpl (S := S) (K := K) b, PMF.bind_map]
  rfl

/-- The simulated part of a draw of the joint world is a draw of the simulated world. -/
theorem jDist_map_simOf (oR oS : Option PK) :
    (jDist (S := S) (K := K) P oR oS).map simOf = simDist P oS := by
  have h1 : ∀ (rk : Draw S K × K) (kp : PK × SK),
      ((encPair P oR oS).map fun kc => (rk, kp, kc)).map simOf =
      (encD P oS).map fun c => ((rk.1, kp, c), rk.2) := by
    intro rk kp
    rw [PMF.map_comp, ← encPair_map_snd P oR oS, PMF.map_comp]
    rfl
  simp only [jDist, PMF.map_bind, h1, simDist, pDist, PMF.bind_bind, PMF.bind_map,
    Function.comp_def]
  rw [PMF.uniform_prod_eq_bind (A := Draw S K) (B := K), PMF.bind_bind]
  refine congrArg _ (funext fun r => ?_)
  simp only [PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun kp => ?_)
  exact (bind_map_comm _ _ _).symm

end Coupling

section Joint

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (G : DHGroup S W)

/-- Whether the event `e` from the simulator state `s` lets the session it completes receive a
key of `F_AKE`: `e` completes the session `x` with record `r`, and `x` is not exposed. -/
def FKeyAt (s : SimSt S W K PK SK SS C) : OEv W SS C → Bool
  | .inr (.complete sid pid) | .inr (.send sid pid _ _) =>
    match s.1.x.st.recs (sid, pid) with
    | some r => !decide (Exposed s.1.x.st (sid, pid) r)
    | none => false
  | _ => false

/-- The record of delivered encapsulations: the event `send sid pid e c` to a session without a
key records `c` for it. -/
def dlvStep (s : SimSt S W K PK SK SS C) (e : OEv W SS C) (g : Inst → Option C) :
    Inst → Option C :=
  match e with
  | .inr (.send sid pid _ c) =>
    if (keyOf s.1.x.st (sid, pid)).isNone then Function.update g (sid, pid) (some c) else g
  | _ => g

/-- The state of the joint world without its flag: the simulated world, the real world, and the
record of the encapsulations delivered to sessions without a key. -/
abbrev JS (S W K PK SK SS C : Type) :=
  (SimSt S W K PK SK SS C × St K) × PSt S W K PK SK SS C × (Inst → Option C)

/-- The state of the joint world: its state and whether the outputs differed at the last
step. -/
abbrev JSt (S W K PK SK SS C : Type) := JS S W K PK SK SS C × Bool

/-- **A step of the joint world** with the draw `j`: the outputs of the real and of the
simulated world, and the next state. When the simulator completes a session that is not exposed,
the real world reads the value of the key derivation from the key that `F_AKE` draws. -/
def jointD (s : JS S W K PK SK SS C) (e : OEv W SS C) (j : JDraw S K PK SK SS C) :
    (OOut S W K PK C × OOut S W K PK C) × JS S W K PK SK SS C :=
  (((realD P G s.2.1 e (realOf (FKeyAt s.1.1 e) j)).1, (simWorldD P G s.1 e (simOf j)).2),
    ((simWorldD P G s.1 e (simOf j)).1, (realD P G s.2.1 e (realOf (FKeyAt s.1.1 e) j)).2,
      dlvStep s.1.1 e s.2.2))

omit [DecidableEq W] [Inhabited K] [DecidableEq SS] in
/-- The distribution of the draw of the joint world at the state `s` and the event `e`: the
encapsulations are to the public keys of the two worlds. -/
noncomputable def jDistAt (s : JS S W K PK SK SS C) (e : OEv W SS C) :
    PMF (JDraw S K PK SK SS C) :=
  jDist P (encPk s.2.1 e) (encPk s.1.1.1 e)

open Classical in
/-- The joint world answering with the output of the real world. -/
noncomputable def jointReal (s : JSt S W K PK SK SS C) (e : OEv W SS C) :
    PMF (OOut S W K PK C × JSt S W K PK SK SS C) :=
  (jDistAt P s.1 e).map fun j =>
    ((jointD P G s.1 e j).1.1,
      ((jointD P G s.1 e j).2, decide ((jointD P G s.1 e j).1.1 ≠ (jointD P G s.1 e j).1.2)))

open Classical in
/-- The joint world answering with the output of the simulated world. -/
noncomputable def jointSim (s : JSt S W K PK SK SS C) (e : OEv W SS C) :
    PMF (OOut S W K PK C × JSt S W K PK SK SS C) :=
  (jDistAt P s.1 e).map fun j =>
    ((jointD P G s.1 e j).1.2,
      ((jointD P G s.1 e j).2, decide ((jointD P G s.1 e j).1.1 ≠ (jointD P G s.1 e j).1.2)))

/-- The two answers of the joint world agree on every outcome whose outputs did not differ. -/
theorem jointReal_apply_eq (s : JSt S W K PK SK SS C) (e : OEv W SS C)
    (x : OOut S W K PK C × JSt S W K PK SK SS C) (hx : x.2.2 = false) :
    jointReal P G s e x = jointSim P G s e x := by
  simp only [jointReal, jointSim, PMF.map_apply]
  refine tsum_congr fun r => ?_
  by_cases h : (jointD P G s.1 e r).1.1 = (jointD P G s.1 e r).1.2
  · rw [h]
  · have h₁ : x ≠ ((jointD P G s.1 e r).1.1, ((jointD P G s.1 e r).2, true)) :=
      fun hc => by simp [hc] at hx
    have h₂ : x ≠ ((jointD P G s.1 e r).1.2, ((jointD P G s.1 e r).2, true)) :=
      fun hc => by simp [hc] at hx
    simp only [h, ne_eq, not_false_eq_true, decide_true, h₁, h₂, ite_false]

/-- The real part of `jointReal` is the real game. -/
theorem jointReal_map (s : JSt S W K PK SK SS C) (e : OEv W SS C) :
    (jointReal P G s e).map (Prod.map id fun s' => s'.1.2.1) =
      (realGame P G).oracle () s.1.2.1 e := by
  rw [realGame_oracle_eq, jointReal, PMF.map_comp,
    ← jDist_map_realOf P (FKeyAt s.1.1.1 e) (encPk s.1.2.1 e) (encPk s.1.1.1.1 e), PMF.map_comp]
  rfl

/-- The simulated part of `jointSim` is the simulated game. -/
theorem jointSim_map (s : JSt S W K PK SK SS C) (e : OEv W SS C) :
    (jointSim P G s e).map (Prod.map id fun s' => s'.1.1) = (simGame P G).oracle () s.1.1 e := by
  rw [simGame_oracle_eq, jointSim, PMF.map_comp,
    ← jDist_map_simOf P (encPk s.1.2.1 e) (encPk s.1.1.1.1 e), PMF.map_comp]
  rfl

/-- The bad transitions of the joint world: the outputs of the two worlds differed. -/
def JointBad (_ : JSt S W K PK SK SS C) (_ : OEv W SS C)
    (x : OOut S W K PK C × JSt S W K PK SK SS C) : Prop :=
  x.2.2 = true

instance (s : JSt S W K PK SK SS C) (e : OEv W SS C)
    (x : OOut S W K PK C × JSt S W K PK SK SS C) : Decidable (JointBad s e x) :=
  inferInstanceAs (Decidable (x.2.2 = true))

/-- The initial state of the joint world. -/
def jointInit : JSt S W K PK SK SS C :=
  ((((pInit, fun _ => none, .fwd), initSt), pInit, fun _ => none), false)

/-- **The experiment of differing outputs**: the adversary runs against the joint world
answering with the outputs of the simulated world, and the experiment outputs whether the outputs
of the real and of the simulated world differed at some step. -/
noncomputable def diffGame (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) : PMF Bool :=
  (OracleAdv.run (OracleAdv.flagWhen JointBad (jointSim P G)) B (jointInit, false)).map
    fun y => y.2.2

/-- **Real versus simulated PQXDH, up to differing outputs.** For every oracle adversary `B`,
the advantage of `B` between the real game and the simulated game is at most the probability
that the outputs of the two worlds differ at some step of the joint world. -/
theorem pqxdh_advantage_le_diffGame (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) :
    KeyedGame.advantage (realGame P G) (simGame P G) B ≤ diffGame P G B true := by
  have hagree : ∀ (s : JSt S W K PK SK SS C) (e : OEv W SS C)
      (x : OOut S W K PK C × JSt S W K PK SK SS C), ¬ JointBad s e x →
      jointReal P G s e x = jointSim P G s e x :=
    fun s e x hx => jointReal_apply_eq P G s e x (by simpa [JointBad] using hx)
  have hR : (OracleAdv.run ((realGame P G).oracle ()) B (realGame P G).init).map Prod.fst =
      (OracleAdv.run (jointReal P G) B jointInit).map Prod.fst := by
    have h := OracleAdv.run_map_state (jointReal P G) ((realGame P G).oracle ())
      (fun s' => s'.1.2.1) (fun s e => jointReal_map P G s e) B jointInit
    calc _ = ((OracleAdv.run (jointReal P G) B jointInit).map
          (Prod.map id fun s' => s'.1.2.1)).map Prod.fst :=
            (congrArg (PMF.map Prod.fst) h).symm
      _ = _ := by rw [PMF.map_comp]; rfl
  have hS : (OracleAdv.run ((simGame (K := K) P G).oracle ()) B (simGame P G).init).map
      Prod.fst = (OracleAdv.run (jointSim P G) B jointInit).map Prod.fst := by
    have h := OracleAdv.run_map_state (jointSim P G) ((simGame P G).oracle ())
      (fun s' => s'.1.1) (fun s e => jointSim_map P G s e) B jointInit
    calc _ = ((OracleAdv.run (jointSim P G) B jointInit).map
          (Prod.map id fun s' => s'.1.1)).map Prod.fst := (congrArg (PMF.map Prod.fst) h).symm
      _ = _ := by rw [PMF.map_comp]; rfl
  have hF : ((OracleAdv.run (OracleAdv.flagWhen JointBad (jointSim P G)) B
      (jointInit, false)).map fun y => y.2.2) true =
      (OracleAdv.run (OracleAdv.flagWhen JointBad (jointSim P G)) B
        (jointInit, false)).toOuterMeasure {y | y.2.2 = true} := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    rfl
  have h₁ : ((OracleAdv.run (jointReal P G) B jointInit).map Prod.fst) true ≤
      ((OracleAdv.run (jointSim P G) B jointInit).map Prod.fst) true + diffGame P G B true := by
    rw [map_fst_apply_true, map_fst_apply_true, diffGame, hF]
    exact OracleAdv.run_toOuterMeasure_le_add_flagWhen JointBad _ _ hagree B _ _
  have h₂ : ((OracleAdv.run (jointSim P G) B jointInit).map Prod.fst) true ≤
      ((OracleAdv.run (jointReal P G) B jointInit).map Prod.fst) true + diffGame P G B true := by
    rw [map_fst_apply_true, map_fst_apply_true, diffGame, hF,
      ← OracleAdv.run_flagWhen_prob_eq JointBad _ _ hagree B]
    exact OracleAdv.run_toOuterMeasure_le_add_flagWhen JointBad _ _
      (fun s e x hx => (hagree s e x hx).symm) B _ _
  have hacc₁ : (realGame P G).accept B =
      ((OracleAdv.run (jointReal P G) B jointInit).map Prod.fst) true := by
    unfold KeyedGame.accept
    erw [PMF.pure_bind]
    rw [hR]
  have hacc₂ : (simGame (K := K) P G).accept B =
      ((OracleAdv.run (jointSim P G) B jointInit).map Prod.fst) true := by
    unfold KeyedGame.accept
    erw [PMF.pure_bind]
    rw [hS]
  rw [KeyedGame.advantage, hacc₁, hacc₂]
  exact max_le (tsub_le_iff_left.mpr h₁) (tsub_le_iff_left.mpr h₂)

end Joint

/-! ## The bad event of a query at the input of a session with a key of `F_AKE`

The bad event `PQHit` is a predicate of the simulated world and of the record of delivered
encapsulations: the table of the key derivation holds the recorded input `ip` of a session `y`
whose party and peer are uncorrupt, that is of a session that received a key of `F_AKE`. The
simulator writes to that table only on a query of the adversary and on the completion of an
exposed session, so the event is a query of the adversary at the input of such a session. The
event states the two routes to its bound:
* the route of Diffie–Hellman: `ip` has the shape of the session (`InpShape`), and its `DH1` is
  the Diffie–Hellman value `g^{ik_a · spk_b}` of the identity key of the initiator `a` and the
  signed prekey of the responder `b` of `ip`, both uncorrupt (`DhOk`);
* the route of the KEM (`KemOk`): for an initiator, the shared secret of `ip` and the
  encapsulation `c` that the session sent form an encapsulation, by `P.encaps`, to the public key
  of the KEM key pair of the responder's session, a key pair of `P.keygen`; for a responder, the
  shared secret of `ip` is the decapsulation of the encapsulation `c` delivered to it under the
  secret key of its own KEM key pair, a key pair of `P.keygen`. When `c` is the encapsulation that
  the initiator of the session sent, the shared secret is hidden under IND-CCA; otherwise the
  adversary made `c`, and the route of Diffie–Hellman applies.

The invariant `PInv` relates the simulator's copy `rs` of the real state with its recorded
inputs `inp`, the record `dlv` of delivered encapsulations, the state `f` of `F_AKE` and the real
state `rl`. It is the invariant of X3DH (`CatCryptCore.Crypto.AKE.X3DHSquareHops`) with the KEM
key pairs and the encapsulations of the two copies equal, every KEM key pair a key pair of
`P.keygen` at a session with a record, and every recorded input satisfying `KemOk`. -/

section Bad

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (G : DHGroup S W)

/-- **The route of the KEM** at the session `y` with record `r` and recorded input `ip`: for an
initiator, its encapsulation `c` with the shared secret of `ip` is an encapsulation to the
public key of the responder's KEM key pair; for a responder, the shared secret of `ip` is the
decapsulation of the encapsulation `c` delivered to it, under its KEM key pair. Both key pairs
are key pairs of `P.keygen`. -/
def KemOk (rs : PSt S W K PK SK SS C) (dlv : Inst → Option C) (y : Inst) (r : Rec K)
    (ip : PInp W SS) : Prop :=
  (r.role = .initiator ∧ ∃ c pk sk, rs.ct y = some c ∧ rs.kem (y.1, r.peer) = some (pk, sk) ∧
      (pk, sk) ∈ P.keygen.support ∧ (ip.2, c) ∈ (P.encaps pk).support) ∨
    (r.role = .responder ∧ ∃ c pk sk, dlv y = some c ∧ rs.kem y = some (pk, sk) ∧
      (pk, sk) ∈ P.keygen.support ∧ P.decaps sk c = some ip.2)

/-- **The bad event**: the table of the key derivation of the simulated world holds the recorded
input `ip` of a session `y` whose party and peer are uncorrupt; `ip` has the shape of `y`, its
`DH1` is the Diffie–Hellman value of the long-term keys of its initiator and responder, and its
shared secret satisfies the route of the KEM. -/
def PQHit (t : SimSt S W K PK SK SS C) (dlv : Inst → Option C) : Prop :=
  ∃ y r ip v, t.1.x.st.recs y = some r ∧ t.2.1 y = some ip ∧ t.1.ro.lookup ip = some v ∧
    t.1.x.st.corrupt y.2 = false ∧ t.1.x.st.corrupt r.peer = false ∧ InpShape y r ip.1 ∧
    DhOk G t.1.x.lt ip.1 ∧ KemOk P t.1 dlv y r ip

/-- **The invariant of the joint world** between the simulator's copy `rs`, its recorded
inputs `inp`, the record `dlv` of delivered encapsulations, the state `f` of `F_AKE` and the real
state `rl`. -/
structure PInv (rs : PSt S W K PK SK SS C) (inp : Inst → Option (PInp W SS))
    (dlv : Inst → Option C) (f : St K) (rl : PSt S W K PK SK SS C) : Prop where
  lt : rl.x.lt = rs.x.lt
  eph : rl.x.eph = rs.x.eph
  corrupt : rl.x.st.corrupt = rs.x.st.corrupt
  notices : rl.x.st.notices = rs.x.st.notices
  cursor : rl.x.st.cursor = rs.x.st.cursor
  recs : ∀ y, (rl.x.st.recs y).map skRec = (rs.x.st.recs y).map skRec
  fcorrupt : f.corrupt = rs.x.st.corrupt
  frecs : ∀ y, (f.recs y).map skRec = (rs.x.st.recs y).map skRec
  key : ∀ y, keyOf rl.x.st y = keyOf f y
  fresh : ∀ y r, rs.x.st.recs y = some r → r.status = .fresh
  fstatus : ∀ y r, f.recs y = some r →
    r.status = if r.key.isSome then (if Exp rs.x.st.corrupt y r.peer then .compromised
      else .completed) else .fresh
  inpSome : ∀ y, (inp y).isSome = (keyOf rs.x.st y).isSome
  inpShape : ∀ y ip r, inp y = some ip → rs.x.st.recs y = some r → InpShape y r ip.1
  inpDh : ∀ y ip, inp y = some ip → DhOk G rs.x.lt ip.1
  named : ∀ y r, rs.x.st.recs y = some r →
    Named rs.x.st y.2 = true ∧ Named rs.x.st r.peer = true
  roSim : ∀ ip v, rs.ro.lookup ip = some v → rl.ro.lookup ip = some v
  roSess : ∀ y ip r, inp y = some ip → rs.x.st.recs y = some r →
    ¬ Exp rs.x.st.corrupt y r.peer → rl.ro.lookup ip = keyOf rl.x.st y
  roReal : ∀ ip v, rl.ro.lookup ip = some v → rs.ro.lookup ip = some v ∨
    ∃ y r, inp y = some ip ∧ rs.x.st.recs y = some r ∧ ¬ Exp rs.x.st.corrupt y r.peer
  kem : rl.kem = rs.kem
  ct : rl.ct = rs.ct
  kemRec : ∀ y kp, rs.kem y = some kp → (rs.x.st.recs y).isSome = true
  kemSupp : ∀ y kp, rs.kem y = some kp → kp ∈ P.keygen.support
  inpKem : ∀ y ip r, inp y = some ip → rs.x.st.recs y = some r → KemOk P rs dlv y r ip

/-- The invariant on a joint state. -/
def InvJ (s : JS S W K PK SK SS C) : Prop :=
  PInv P G s.1.1.1 s.1.1.2.1 s.2.2 s.1.2 s.2.1

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- The invariant holds at the start. -/
theorem inv_init :
    PInv P G (pInit : PSt S W K PK SK SS C) (fun _ => none) (fun _ => none) initSt pInit := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, fun _ => rfl, fun _ => rfl, ?_, ?_,
    fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩ <;>
    simp [pInit, rInit, initSt]

omit [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- `KemOk` depends on the encapsulations, the KEM key pairs and the record of delivered
encapsulations at the sessions that it names. -/
theorem KemOk.of_eq {rs rs' : PSt S W K PK SK SS C} {dlv dlv' : Inst → Option C} {y : Inst}
    {r : Rec K} {ip : PInp W SS} (h : KemOk P rs dlv y r ip) (hct : rs'.ct y = rs.ct y)
    (hkem : ∀ z, rs.kem z ≠ none → rs'.kem z = rs.kem z) (hdlv : dlv' y = dlv y) :
    KemOk P rs' dlv' y r ip := by
  rcases h with ⟨hr, c, pk, sk, h₁, h₂, h₃, h₄⟩ | ⟨hr, c, pk, sk, h₁, h₂, h₃, h₄⟩
  · exact Or.inl ⟨hr, c, pk, sk, by rw [hct, h₁], by rw [hkem _ (by rw [h₂]; simp), h₂], h₃, h₄⟩
  · exact Or.inr ⟨hr, c, pk, sk, by rw [hdlv, h₁], by rw [hkem _ (by rw [h₂]; simp), h₂], h₃, h₄⟩

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- The invariant depends on the components of the states that it names. -/
theorem PInv.of_eq {rs rs' rl rl' : PSt S W K PK SK SS C} {inp : Inst → Option (PInp W SS)}
    {dlv : Inst → Option C} {f : St K} (hI : PInv P G rs inp dlv f rl)
    (h₁ : ∀ q v, rs.x.lt q = some v → rs'.x.lt q = some v)
    (h₂ : rs'.x.eph = rs.x.eph) (h₃ : rs'.ro = rs.ro)
    (h₄ : rs'.x.st.recs = rs.x.st.recs) (h₅ : rs'.x.st.corrupt = rs.x.st.corrupt)
    (h₆ : rs'.x.st.notices = rs.x.st.notices) (h₈ : rs'.kem = rs.kem) (h₉ : rs'.ct = rs.ct)
    (h₁' : rl'.x.lt = rs'.x.lt) (h₂' : rl'.x.eph = rl.x.eph)
    (h₃' : rl'.ro = rl.ro) (h₄' : rl'.x.st.recs = rl.x.st.recs)
    (h₅' : rl'.x.st.corrupt = rl.x.st.corrupt) (h₆' : rl'.x.st.notices = rl.x.st.notices)
    (h₇ : rl'.x.st.cursor = rs'.x.st.cursor) (h₈' : rl'.kem = rl.kem) (h₉' : rl'.ct = rl.ct) :
    PInv P G rs' inp dlv f rl' := by
  have hk : ∀ y, keyOf rs'.x.st y = keyOf rs.x.st y := fun y => by simp only [keyOf, h₄]
  have hk' : ∀ y, keyOf rl'.x.st y = keyOf rl.x.st y := fun y => by simp only [keyOf, h₄']
  have hn : ∀ p, Named rs'.x.st p = Named rs.x.st p := fun p => by simp only [Named, h₆]
  refine ⟨?_, ?_, ?_, ?_, h₇, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact h₁'
  · rw [h₂, h₂', hI.eph]
  · rw [h₅, h₅', hI.corrupt]
  · rw [h₆, h₆', hI.notices]
  · intro y; rw [h₄, h₄', hI.recs]
  · rw [h₅, hI.fcorrupt]
  · intro y; rw [h₄, hI.frecs]
  · intro y; rw [hk', hI.key]
  · intro y r hr; rw [h₄] at hr; exact hI.fresh y r hr
  · intro y r hr; rw [h₅]; exact hI.fstatus y r hr
  · intro y; rw [hk, hI.inpSome]
  · intro y ip r hy hr; rw [h₄] at hr; exact hI.inpShape y ip r hy hr
  · intro y ip hy; exact (hI.inpDh y ip hy).mono G h₁
  · intro y r hr; rw [h₄] at hr; rw [hn, hn]; exact hI.named y r hr
  · intro ip v h; rw [h₃] at h; rw [h₃']; exact hI.roSim ip v h
  · intro y ip r hy hr hx; rw [h₄] at hr; rw [h₅] at hx; rw [h₃', hk']
    exact hI.roSess y ip r hy hr hx
  · intro ip v h; rw [h₃'] at h; rw [h₃, h₄, h₅]; exact hI.roReal ip v h
  · rw [h₈, h₈', hI.kem]
  · rw [h₉, h₉', hI.ct]
  · intro y kp h; rw [h₈] at h; rw [h₄]; exact hI.kemRec y kp h
  · intro y kp h; rw [h₈] at h; exact hI.kemSupp y kp h
  · intro y ip r hy hr; rw [h₄] at hr
    exact (hI.inpKem y ip r hy hr).of_eq P (by rw [h₉]) (fun z _ => by rw [h₈]) rfl

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- `ltD` on both copies keeps the invariant, and outputs the same secrets. -/
theorem PInv.lt_step {rs rl : PSt S W K PK SK SS C} {inp : Inst → Option (PInp W SS)}
    {dlv : Inst → Option C} {f : St K} (hI : PInv P G rs inp dlv f rl) (pid : PartyId)
    (l : S × S) :
    (ltD rl.x pid l).1 = (ltD rs.x pid l).1 ∧
      PInv P G { rs with x := (ltD rs.x pid l).2 } inp dlv f { rl with x := (ltD rl.x pid l).2 } := by
  have hlt : (ltD rl.x pid l).2.lt = (ltD rs.x pid l).2.lt ∧
      (ltD rl.x pid l).1 = (ltD rs.x pid l).1 := by
    unfold ltD
    cases h : rs.x.lt pid <;> simp [hI.lt, h]
  refine ⟨hlt.2, hI.of_eq P G (ltD_lt_mono rs.x pid l) ?_ ?_ ?_ ?_ ?_ rfl rfl hlt.1 ?_ ?_ ?_ ?_ ?_
    ?_ rfl rfl⟩ <;>
    simp only [ltD_st, ltD_eph, hI.cursor]

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- `poll` on both copies keeps the invariant and gives the same notice. -/
theorem PInv.poll {rs rl : PSt S W K PK SK SS C} {inp : Inst → Option (PInp W SS)}
    {dlv : Inst → Option C} {f : St K} (hI : PInv P G rs inp dlv f rl) :
    (pollStep rl.x.st).2 = (pollStep rs.x.st).2 ∧
      PInv P G { rs with x := { rs.x with st := (pollStep rs.x.st).1 } } inp dlv f
        { rl with x := { rl.x with st := (pollStep rl.x.st).1 } } := by
  have hc : (pollStep rl.x.st).1.cursor = (pollStep rs.x.st).1.cursor ∧
      (pollStep rl.x.st).2 = (pollStep rs.x.st).2 := by
    unfold pollStep
    rw [hI.notices, hI.cursor]
    split <;> first | exact ⟨rfl, rfl⟩ | exact ⟨hI.cursor, rfl⟩
  refine ⟨hc.2, hI.of_eq P G (fun _ _ h => h) rfl rfl (pollStep_fst _).1 (pollStep_fst _).2.1
    (pollStep_fst _).2.2 rfl rfl hI.lt rfl rfl (pollStep_fst _).1 (pollStep_fst _).2.1
    (pollStep_fst _).2.2 hc.1 rfl rfl⟩

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- A new session on both copies and in `F_AKE` keeps the invariant, with KEM key pairs `kmS`
and `kmR` equal to the previous ones elsewhere and a key pair of `P.keygen`, if any, at the new
session. -/
theorem PInv.newSession {rs rl : PSt S W K PK SK SS C} {inp : Inst → Option (PInp W SS)}
    {dlv : Inst → Option C} {f : St K} (hI : PInv P G rs inp dlv f rl) (x : Inst)
    (hx : rs.x.st.recs x = none) (peer : PartyId) (role : Role) (y : S)
    (kmS kmR : Inst → Option (PK × SK)) (hR : kmR = kmS) (hkm : ∀ z, z ≠ x → kmS z = rs.kem z)
    (hkx : ∀ kp, kmS x = some kp → kp ∈ P.keygen.support) :
    PInv P G { rs with x := { rs.x with st := addSession rs.x.st x peer role,
                                        eph := Function.update rs.x.eph x (some y) }, kem := kmS }
      inp dlv (addSession f x peer role)
      { rl with x := { rl.x with st := addSession rl.x.st x peer role,
                                 eph := Function.update rl.x.eph x (some y) }, kem := kmR } := by
  have hxl : rl.x.st.recs x = none := by
    have h := hI.recs x
    rw [hx] at h
    cases h' : rl.x.st.recs x <;> simp_all
  have hxf : f.recs x = none := by
    have h := hI.frecs x
    rw [hx] at h
    cases h' : f.recs x <;> simp_all
  have hix : inp x = none := by
    have h := hI.inpSome x
    simp only [keyOf, hx, Option.bind_none, Option.isSome_none] at h
    exact Option.not_isSome_iff_eq_none.mp (by simp [h])
  rw [addSession_of_isNone hx, addSession_of_isNone hxl, addSession_of_isNone hxf]
  have hrec : ∀ (t : St K) y', y' ≠ x →
      (Function.update t.recs x (some (⟨peer, role, .fresh, none⟩ : Rec K))) y' = t.recs y' :=
    fun t y' h => Function.update_of_ne h _ _
  have hny : ∀ y' ip, inp y' = some ip → y' ≠ x := fun y' ip h hc => by
    subst hc; rw [hix] at h; cases h
  constructor
  · exact hI.lt
  · simp only [hI.eph]
  · exact hI.corrupt
  · simp only [hI.notices]
  · exact hI.cursor
  · intro y'
    by_cases h : y' = x
    · subst h; simp only [Function.update_self]
    · simp only [hrec _ _ h, hI.recs y']
  · exact hI.fcorrupt
  · intro y'
    by_cases h : y' = x
    · subst h; simp only [Function.update_self]
    · simp only [hrec _ _ h, hI.frecs y']
  · intro y'
    by_cases h : y' = x
    · subst h; simp [keyOf]
    · simpa [keyOf, hrec _ _ h] using hI.key y'
  · intro y' r hr
    by_cases h : y' = x
    · subst h; simp only [Function.update_self, Option.some.injEq] at hr; subst hr; rfl
    · simp only [hrec _ _ h] at hr; exact hI.fresh y' r hr
  · intro y' r hr
    by_cases h : y' = x
    · subst h; simp only [Function.update_self, Option.some.injEq] at hr; subst hr; simp
    · simp only [hrec _ _ h] at hr; exact hI.fstatus y' r hr
  · intro y'
    by_cases h : y' = x
    · subst h; simp [keyOf, hix]
    · simpa [keyOf, hrec _ _ h] using hI.inpSome y'
  · intro y' ip r hy hr
    simp only [hrec _ _ (hny y' ip hy)] at hr
    exact hI.inpShape y' ip r hy hr
  · exact hI.inpDh
  · intro y' r hr
    have hn : ∀ p, Named rs.x.st p = true → Named { rs.x.st with
        recs := Function.update rs.x.st.recs x (some ⟨peer, role, .fresh, none⟩),
        notices := rs.x.st.notices ++ [⟨x.1, x.2, peer, role⟩] } p = true := fun p hp => by
      simp only [Named] at hp ⊢
      simp [List.any_append, hp]
    by_cases h : y' = x
    · subst h
      simp only [Function.update_self, Option.some.injEq] at hr
      subst hr
      simp [Named]
    · simp only [hrec _ _ h] at hr
      exact ⟨hn _ (hI.named y' r hr).1, hn _ (hI.named y' r hr).2⟩
  · exact hI.roSim
  · intro y' ip r hy hr he
    have h := hny y' ip hy
    simp only [hrec _ _ h] at hr
    simpa [keyOf, hrec _ _ h] using hI.roSess y' ip r hy hr he
  · intro ip v hv
    rcases hI.roReal ip v hv with h | ⟨y', r, hy, hr, he⟩
    · exact Or.inl h
    · exact Or.inr ⟨y', r, hy, by simpa [hrec _ _ (hny y' ip hy)] using hr, he⟩
  · exact hR
  · exact hI.ct
  · intro z kp hz
    change kmS z = some kp at hz
    by_cases h : z = x
    · subst h; simp
    · rw [hkm z h] at hz
      simpa [hrec _ _ h] using hI.kemRec z kp hz
  · intro z kp hz
    change kmS z = some kp at hz
    by_cases h : z = x
    · subst h; exact hkx kp hz
    · rw [hkm z h] at hz; exact hI.kemSupp z kp hz
  · intro y' ip r hy hr
    simp only [hrec _ _ (hny y' ip hy)] at hr
    refine (hI.inpKem y' ip r hy hr).of_eq P rfl (fun z hz => hkm z fun hc => ?_) rfl
    subst hc
    obtain ⟨kp, hkp⟩ := Option.ne_none_iff_exists'.mp hz
    have := hI.kemRec z kp hkp
    rw [hx] at this
    cases this

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- A party that no session names is neither the party nor the peer of a session. -/
theorem PInv.not_named {rs rl : PSt S W K PK SK SS C} {inp : Inst → Option (PInp W SS)}
    {dlv : Inst → Option C} {f : St K} (hI : PInv P G rs inp dlv f rl) {pid : PartyId}
    (hn : Named rs.x.st pid = false) {y : Inst} {r : Rec K} (hr : rs.x.st.recs y = some r) :
    y.2 ≠ pid ∧ r.peer ≠ pid := by
  constructor
  · intro hc; have := (hI.named y r hr).1; rw [hc, hn] at this; cases this
  · intro hc; have := (hI.named y r hr).2; rw [hc, hn] at this; cases this

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- Corrupting a party that no session names, on both copies and in `F_AKE`, keeps the
invariant. -/
theorem PInv.corrupt_step {rs rl : PSt S W K PK SK SS C} {inp : Inst → Option (PInp W SS)}
    {dlv : Inst → Option C} {f : St K} (hI : PInv P G rs inp dlv f rl) {pid : PartyId}
    (hn : Named rs.x.st pid = false) :
    PInv P G { rs with x := { rs.x with st := corruptStep rs.x.st pid } } inp dlv
      (corruptStep f pid) { rl with x := { rl.x with st := corruptStep rl.x.st pid } } := by
  have hE : ∀ y r, rs.x.st.recs y = some r →
      (Exp (Function.update rs.x.st.corrupt pid true) y r.peer ↔ Exp rs.x.st.corrupt y r.peer) :=
    fun y r hr => exp_update (hI.not_named P G hn hr).1 (hI.not_named P G hn hr).2
  refine ⟨hI.lt, hI.eph, ?_, hI.notices, hI.cursor, hI.recs, ?_, hI.frecs, hI.key, hI.fresh,
    ?_, hI.inpSome, hI.inpShape, hI.inpDh, hI.named, hI.roSim, ?_, ?_, hI.kem, hI.ct, hI.kemRec,
    hI.kemSupp, hI.inpKem⟩
  · simp only [corruptStep, hI.corrupt]
  · simp only [corruptStep, hI.fcorrupt]
  · intro y r hr
    obtain ⟨r0, hr0, hp, -, -⟩ := sk_some (hI.frecs y).symm hr
    have h := hI.fstatus y r hr
    have hEx : Exp (Function.update rs.x.st.corrupt pid true) y r.peer ↔
        Exp rs.x.st.corrupt y r.peer := by rw [← hp]; exact hE y r0 hr0
    simpa only [corruptStep, hEx] using h
  · intro y ip r hy hr he
    exact hI.roSess y ip r hy hr (fun h => he ((hE y r hr).mpr h))
  · intro ip v hv
    rcases hI.roReal ip v hv with h | ⟨y, r, hy, hr, he⟩
    · exact Or.inl h
    · exact Or.inr ⟨y, r, hy, hr, fun h => he ((hE y r hr).mp h)⟩

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- Recording the encapsulation of a session without a recorded input, on both copies, keeps the
invariant. -/
theorem PInv.ct_step {rs rl : PSt S W K PK SK SS C} {inp : Inst → Option (PInp W SS)}
    {dlv : Inst → Option C} {f : St K} (hI : PInv P G rs inp dlv f rl) {x : Inst}
    (hx : inp x = none) (c : C) :
    PInv P G { rs with ct := Function.update rs.ct x (some c) } inp dlv f
      { rl with ct := Function.update rl.ct x (some c) } :=
  { hI with
    ct := by simp only [hI.ct]
    inpKem := fun y ip r hy hr => (hI.inpKem y ip r hy hr).of_eq P
      (Function.update_of_ne (fun hc => by subst hc; rw [hx] at hy; cases hy) _ _)
      (fun _ _ => rfl) rfl }

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- Recording a delivered encapsulation for a session without a key keeps the invariant. -/
theorem PInv.dlv_step {rs rl : PSt S W K PK SK SS C} {inp : Inst → Option (PInp W SS)}
    {dlv : Inst → Option C} {f : St K} (hI : PInv P G rs inp dlv f rl) {x : Inst}
    (hx : (keyOf rs.x.st x).isNone = true) (c : C) :
    PInv P G rs inp (Function.update dlv x (some c)) f rl :=
  { hI with
    inpKem := fun y ip r hy hr => (hI.inpKem y ip r hy hr).of_eq P rfl (fun _ _ => rfl)
      (Function.update_of_ne (fun hc => by
        subst hc
        have h := hI.inpSome y
        rw [hy, Option.isSome_some, ← Option.not_isNone, hx] at h
        cases h) _ _) }

omit [Fintype S] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The bad event holds when the table holds the recorded input of a session of uncorrupt
parties with its routes. -/
theorem pqHit_intro {t : SimSt S W K PK SK SS C} {dlv : Inst → Option C} {y : Inst} {r : Rec K}
    {ip : PInp W SS} (hr : t.1.x.st.recs y = some r) (hy : t.2.1 y = some ip)
    (hl : (t.1.ro.lookup ip).isSome = true) (he : ¬ Exp t.1.x.st.corrupt y r.peer)
    (hsh : InpShape y r ip.1) (hd : DhOk G t.1.x.lt ip.1) (hk : KemOk P t.1 dlv y r ip) :
    PQHit P G t dlv := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
  simp only [Exp, not_or, Bool.not_eq_true] at he
  exact ⟨y, r, ip, v, hr, hy, hv, he.1, he.2, hsh, hd, hk⟩

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- A session with a recorded input has a key in the real world. -/
theorem PInv.key_isSome {rs rl : PSt S W K PK SK SS C} {inp : Inst → Option (PInp W SS)}
    {dlv : Inst → Option C} {f : St K} (hI : PInv P G rs inp dlv f rl) {y : Inst}
    {ip : PInp W SS} (hy : inp y = some ip) : (keyOf rl.x.st y).isSome = true := by
  have h := hI.inpSome y
  rw [hy, Option.isSome_some] at h
  cases hr : rs.x.st.recs y with
  | none => simp [keyOf, hr] at h
  | some r =>
    obtain ⟨rl', hrl, -, -, hk⟩ := sk_some (hI.recs y) hr
    simp only [keyOf, hr, Option.bind_some] at h
    simp only [keyOf, hrl, Option.bind_some, hk, h]

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- **A query of the key derivation** on both copies either is the bad event or gives the same
answer and keeps the invariant. -/
theorem PInv.kdf {rs rl : PSt S W K PK SK SS C} {inp : Inst → Option (PInp W SS)}
    {dlv : Inst → Option C} {f : St K} (hI : PInv P G rs inp dlv f rl) (x : PInp W SS) (k : K)
    (ph : Phase S W K PK C) :
    PQHit P G ({ rs with ro := (roDet rs.ro x k).2 }, inp, ph) dlv ∨
      ((roDet rl.ro x k).1 = (roDet rs.ro x k).1 ∧
        PInv P G { rs with ro := (roDet rs.ro x k).2 } inp dlv f
          { rl with ro := (roDet rl.ro x k).2 }) := by
  cases hs : rs.ro.lookup x with
  | some v =>
    rw [roDet_of_some hs, roDet_of_some (hI.roSim x v hs)]
    exact Or.inr ⟨rfl, hI⟩
  | none =>
    cases hl : rl.ro.lookup x with
    | some v =>
      rcases hI.roReal x v hl with h | ⟨y, r, hy, hr, he⟩
      · rw [hs] at h; cases h
      · refine Or.inl (pqHit_intro P G (t := ({ rs with ro := (roDet rs.ro x k).2 }, inp, ph))
          hr hy ?_ he (hI.inpShape y x r hy hr) (hI.inpDh y x hy) (hI.inpKem y x r hy hr))
        simp [roDet_of_none hs]
    | none =>
      rw [roDet_of_none hs, roDet_of_none hl]
      refine Or.inr ⟨rfl, ?_⟩
      have hne : ∀ y ip r, inp y = some ip → rs.x.st.recs y = some r →
          ¬ Exp rs.x.st.corrupt y r.peer → ip ≠ x := fun y ip r hy hr he hc => by
        have h := hI.roSess y ip r hy hr he
        have h' := hI.key_isSome P G hy
        rw [← h, hc, hl] at h'
        cases h'
      exact { hI with
        roSim := fun ip v h => by
          simp only [lookup_cons] at h ⊢
          split_ifs at h ⊢ with hc
          · exact h
          · exact hI.roSim ip v h
        roSess := fun y ip r hy hr he => by
          simp only [lookup_cons, hne y ip r hy hr he, ite_false]
          exact hI.roSess y ip r hy hr he
        roReal := fun ip v h => by
          simp only [lookup_cons] at h ⊢
          split_ifs at h ⊢ with hc
          · exact Or.inl h
          · exact hI.roReal ip v h }

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- The fields that a completion of the session `x` changes: its key on both copies and in
`F_AKE`, and its recorded input. Given the clauses on the tables of the key derivation, the
invariant holds after the completion. -/
theorem PInv.keyed_step {rs rl : PSt S W K PK SK SS C} {inp : Inst → Option (PInp W SS)}
    {dlv : Inst → Option C} {f : St K}
    (hI : PInv P G rs inp dlv f rl) {x : Inst} {rcs rcl rcf : Rec K} (hs : rs.x.st.recs x = some rcs)
    (hl : rl.x.st.recs x = some rcl) (hf : f.recs x = some rcf) {ip : PInp W SS}
    (hsh : InpShape x rcs ip.1) (hd : DhOk G rs.x.lt ip.1) (hkem : KemOk P rs dlv x rcs ip)
    (ks kr : K) (ros rol : List (PInp W SS × K))
    (stf : Status) (hstf : stf = if Exp rs.x.st.corrupt x rcs.peer then .compromised else .completed)
    (hroSim : ∀ ip' v, ros.lookup ip' = some v → rol.lookup ip' = some v)
    (hroSess : ∀ y ip' r, Function.update inp x (some ip) y = some ip' →
      (setRec rs.x.st x { rcs with key := some ks }).recs y = some r →
      ¬ Exp rs.x.st.corrupt y r.peer →
        rol.lookup ip' = keyOf (setRec rl.x.st x { rcl with key := some kr }) y)
    (hroReal : ∀ ip' v, rol.lookup ip' = some v → ros.lookup ip' = some v ∨
      ∃ y r, Function.update inp x (some ip) y = some ip' ∧
        (setRec rs.x.st x { rcs with key := some ks }).recs y = some r ∧
        ¬ Exp rs.x.st.corrupt y r.peer) :
    PInv P G (pKeyed rs x rcs ks ros) (Function.update inp x (some ip)) dlv
      (setRec f x { rcf with key := some kr, status := stf }) (pKeyed rl x rcl kr rol) := by
  obtain ⟨rl₀, hl₀, hpl, hrl, -⟩ := sk_some (hI.recs x) hs
  obtain ⟨rf₀, hf₀, hpf, hrf, -⟩ := sk_some (hI.frecs x) hs
  rw [hl] at hl₀; cases hl₀
  rw [hf] at hf₀; cases hf₀
  have hu : ∀ {α : Type} (g : Inst → α) (a : α) (y : Inst), y ≠ x → Function.update g x a y = g y :=
    fun g a y h => Function.update_of_ne h _ _
  refine ⟨hI.lt, hI.eph, hI.corrupt, hI.notices, hI.cursor, ?_, hI.fcorrupt, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, hroSim, hroSess, hroReal, hI.kem, hI.ct, ?_, hI.kemSupp, ?_⟩
  · intro y
    by_cases h : y = x
    · subst h
      simp only [pKeyed, keyed, setRec, Function.update_self, Option.map_some]
      exact congrArg some (skRec_ext hpl hrl rfl)
    · simp only [pKeyed, keyed, setRec, hu _ _ _ h]
      exact hI.recs y
  · intro y
    by_cases h : y = x
    · subst h
      simp only [setRec, pKeyed, keyed, Function.update_self, Option.map_some]
      exact congrArg some (skRec_ext hpf hrf rfl)
    · simp only [pKeyed, keyed, setRec, hu _ _ _ h]
      exact hI.frecs y
  · intro y
    by_cases h : y = x
    · subst h; simp [keyOf, pKeyed, keyed, setRec]
    · simp only [keyOf, pKeyed, keyed, setRec, hu _ _ _ h]
      exact hI.key y
  · intro y r hr
    by_cases h : y = x
    · subst h
      simp only [pKeyed, keyed, setRec, Function.update_self, Option.some.injEq] at hr
      subst hr
      exact (hI.fresh _ _ hs : rcs.status = _)
    · simp only [pKeyed, keyed, setRec, hu _ _ _ h] at hr
      exact hI.fresh y r hr
  · intro y r hr
    by_cases h : y = x
    · subst h
      simp only [setRec, Function.update_self, Option.some.injEq] at hr
      subst hr
      simp only [Option.isSome_some, ite_true, pKeyed, keyed, setRec, hstf, hpf]
    · simp only [setRec, hu _ _ _ h] at hr
      exact hI.fstatus y r hr
  · intro y
    by_cases h : y = x
    · subst h; simp [keyOf, pKeyed, keyed, setRec]
    · simp only [keyOf, pKeyed, keyed, setRec, hu _ _ _ h]
      exact hI.inpSome y
  · intro y ip' r hy hr
    by_cases h : y = x
    · subst h
      simp only [pKeyed, keyed, setRec, Function.update_self, Option.some.injEq] at hy hr
      subst hy hr
      exact hsh
    · simp only [pKeyed, keyed, setRec, hu _ _ _ h] at hy hr
      exact hI.inpShape y ip' r hy hr
  · intro y ip' hy
    by_cases h : y = x
    · subst h
      simp only [Function.update_self, Option.some.injEq] at hy
      subst hy
      exact hd
    · simp only [hu _ _ _ h] at hy
      exact hI.inpDh y ip' hy
  · intro y r hr
    by_cases h : y = x
    · subst h
      simp only [pKeyed, keyed, setRec, Function.update_self, Option.some.injEq] at hr
      subst hr
      exact (hI.named _ _ hs : Named rs.x.st y.2 = true ∧ Named rs.x.st rcs.peer = true)
    · simp only [pKeyed, keyed, setRec, hu _ _ _ h] at hr
      exact hI.named y r hr
  · intro y kp hy
    by_cases h : y = x
    · subst h; simp [pKeyed, keyed, setRec]
    · simp only [pKeyed, keyed, setRec, hu _ _ _ h]
      exact hI.kemRec y kp hy
  · intro y ip' r hy hr
    by_cases h : y = x
    · subst h
      simp only [pKeyed, keyed, setRec, Function.update_self, Option.some.injEq] at hy hr
      subst hy hr
      exact hkem
    · simp only [pKeyed, keyed, setRec, hu _ _ _ h] at hy hr
      exact hI.inpKem y ip' r hy hr

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- The record of `x` in each component, for a session `x` of the simulator's copy without a
key: the same peer and role, no key, and a fresh record in `F_AKE` whose exposure is that of the
copy. -/
theorem PInv.recs_of {rs rl : PSt S W K PK SK SS C} {inp : Inst → Option (PInp W SS)}
    {dlv : Inst → Option C} {f : St K}
    (hI : PInv P G rs inp dlv f rl) {x : Inst} {rcs : Rec K} (hs : rs.x.st.recs x = some rcs)
    (hk : rcs.key = none) :
    inp x = none ∧ (∃ rcl, rl.x.st.recs x = some rcl ∧ rcl.peer = rcs.peer ∧ rcl.role = rcs.role ∧
      rcl.key = none) ∧ ∃ rcf, f.recs x = some rcf ∧ rcf.peer = rcs.peer ∧
      rcf.role = rcs.role ∧ rcf.key = none ∧ (Exposed f x rcf ↔ Exp rs.x.st.corrupt x rcs.peer) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := hI.inpSome x
    simp only [keyOf, hs, Option.bind_some, hk, Option.isSome_none] at h
    exact Option.not_isSome_iff_eq_none.mp (by simp [h])
  · obtain ⟨rcl, hl, hp, hr, hkk⟩ := sk_some (hI.recs x) hs
    exact ⟨rcl, hl, hp, hr, by simpa [hk] using hkk⟩
  · obtain ⟨rcf, hf, hp, hr, hkk⟩ := sk_some (hI.frecs x) hs
    have hkf : rcf.key = none := by simpa [hk] using hkk
    have hst := hI.fstatus x rcf hf
    simp only [hkf, Option.isSome_none, Bool.false_eq_true, ite_false] at hst
    refine ⟨rcf, hf, hp, hr, hkf, ?_⟩
    simp only [Exposed, Exp, hI.fcorrupt, hp, hst, reduceCtorEq, or_false]

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- **The completion of an exposed session** keeps the invariant: the simulator samples the key
derivation on its table, and the real world reads the same value. -/
theorem PInv.deliver_exp {rs rl : PSt S W K PK SK SS C} {inp : Inst → Option (PInp W SS)}
    {dlv : Inst → Option C} {f : St K}
    (hI : PInv P G rs inp dlv f rl) {x : Inst} {rcs rcl : Rec K} (hs : rs.x.st.recs x = some rcs)
    (hk : rcs.key = none) (hl : rl.x.st.recs x = some rcl) {ip : PInp W SS}
    (hsh : InpShape x rcs ip.1) (hd : DhOk G rs.x.lt ip.1) (hkem : KemOk P rs dlv x rcs ip) (he : Exp rs.x.st.corrupt x rcs.peer)
    (k kf : K) :
    PInv P G (pKeyed rs x rcs (roDet rs.ro ip k).1 (roDet rs.ro ip k).2)
      (Function.update inp x (some ip)) dlv (newKeyStep f x (roDet rs.ro ip k).1 kf)
      (pKeyed rl x rcl (roDet rl.ro ip k).1 (roDet rl.ro ip k).2) := by
  obtain ⟨hix, ⟨rcl', hl', -⟩, rcf, hf, hpf, -, hkf, hexf⟩ := hI.recs_of P G hs hk
  rw [hl] at hl'; cases hl'
  have hnoun : ∀ y r, inp y = some ip → rs.x.st.recs y = some r → ¬ Exp rs.x.st.corrupt y r.peer →
      False := fun y r hy hr hey =>
    hey ((exp_iff_of_shape (hI.inpShape y ip r hy hr)).mpr ((exp_iff_of_shape hsh).mp he))
  have hux : ∀ y ip', Function.update inp x (some ip) y = some ip' → y ≠ x →
      inp y = some ip' := fun y ip' h hne => by rwa [Function.update_of_ne hne] at h
  have hexp : ∀ (kk : K) y r, (setRec rs.x.st x { rcs with key := some kk }).recs y =
      some r → ¬ Exp rs.x.st.corrupt y r.peer → y ≠ x := fun kk y r hr hey hc => by
    subst hc
    simp only [setRec, Function.update_self, Option.some.injEq] at hr
    subst hr
    exact hey he
  rw [newKeyStep_of hf hkf]
  simp only [hexf.mpr he, ↓reduceIte]
  have hval : newKeyVal f x rcf (roDet rs.ro ip k).1 kf = (roDet rs.ro ip k).1 := by
    simp [newKeyVal, hexf.mpr he]
  rw [hval]
  cases hls : rs.ro.lookup ip with
  | some v =>
    have hll := hI.roSim ip v hls
    rw [roDet_of_some hls, roDet_of_some hll]
    refine hI.keyed_step P G hs hl hf hsh hd hkem v v rs.ro rl.ro _ (by simp only [he, ↓reduceIte])
      hI.roSim ?_ ?_
    · intro y ip' r hy hr hey
      have hne := hexp _ y r hr hey
      rw [setRec_recs_ne hne] at hr
      rw [keyOf_setRec_ne hne]
      exact hI.roSess y ip' r (hux y ip' hy hne) hr hey
    · intro ip' v' hv
      rcases hI.roReal ip' v' hv with h | ⟨y, r, hy, hr, hey⟩
      · exact Or.inl h
      · have hne : y ≠ x := fun hc => by subst hc; rw [hix] at hy; cases hy
        exact Or.inr ⟨y, r, by rw [Function.update_of_ne hne]; exact hy,
          by rw [setRec_recs_ne hne]; exact hr, hey⟩
  | none =>
    have hll : rl.ro.lookup ip = none := by
      cases h : rl.ro.lookup ip with
      | none => rfl
      | some v =>
        rcases hI.roReal ip v h with h' | ⟨y, r, hy, hr, hey⟩
        · rw [hls] at h'; cases h'
        · exact (hnoun y r hy hr hey).elim
    rw [roDet_of_none hls, roDet_of_none hll]
    refine hI.keyed_step P G hs hl hf hsh hd hkem k k _ _ _ (by simp only [he, ↓reduceIte]) ?_ ?_ ?_
    · intro ip' v h
      simp only [lookup_cons] at h ⊢
      split_ifs at h ⊢
      · exact h
      · exact hI.roSim ip' v h
    · intro y ip' r hy hr hey
      have hne := hexp _ y r hr hey
      rw [setRec_recs_ne hne] at hr
      rw [keyOf_setRec_ne hne]
      have hy' := hux y ip' hy hne
      have hip : ip' ≠ ip := fun hc => by subst hc; exact hnoun y r hy' hr hey
      simp only [lookup_cons, hip, ite_false]
      exact hI.roSess y ip' r hy' hr hey
    · intro ip' v h
      simp only [lookup_cons] at h ⊢
      split_ifs at h ⊢
      · exact Or.inl h
      · rcases hI.roReal ip' v h with h' | ⟨y, r, hy, hr, hey⟩
        · exact Or.inl h'
        · have hne : y ≠ x := fun hc => by subst hc; rw [hix] at hy; cases hy
          exact Or.inr ⟨y, r, by rw [Function.update_of_ne hne]; exact hy,
            by rw [setRec_recs_ne hne]; exact hr, hey⟩

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- **The completion of an unexposed session** either is the bad event, when the simulator's
table holds its input, or keeps the invariant: the real world reads the key of `F_AKE`, which
is the key of the partner with the same input or the fresh value `kf`. -/
theorem PInv.deliver_unexp {rs rl : PSt S W K PK SK SS C} {inp : Inst → Option (PInp W SS)}
    {dlv : Inst → Option C} {f : St K}
    (hI : PInv P G rs inp dlv f rl) {x : Inst} {rcs rcl : Rec K} (hs : rs.x.st.recs x = some rcs)
    (hk : rcs.key = none) (hl : rl.x.st.recs x = some rcl) {ip : PInp W SS}
    (hsh : InpShape x rcs ip.1) (hd : DhOk G rs.x.lt ip.1) (hkem : KemOk P rs dlv x rcs ip) (he : ¬ Exp rs.x.st.corrupt x rcs.peer)
    (kf : K) (ph : Phase S W K PK C) :
    PQHit P G (pKeyed rs x rcs default rs.ro, Function.update inp x (some ip), ph) dlv ∨
      PInv P G (pKeyed rs x rcs default rs.ro) (Function.update inp x (some ip)) dlv
        (advD f (if (inp (x.1, rcs.peer)).all (· = ip) then .newKey x.1 x.2 default
          else .newKeyUnlinked x.1 x.2 default) kf).1
        (pKeyed rl x rcl (roDet rl.ro ip kf).1 (roDet rl.ro ip kf).2) := by
  obtain ⟨hix, ⟨rcl', hl', -⟩, rcf, hf, hpf, hrf, hkf, hexf⟩ := hI.recs_of P G hs hk
  rw [hl] at hl'; cases hl'
  have hunc := (exp_iff_of_shape (c := rs.x.st.corrupt) hsh).not.mp he
  simp only [not_or, Bool.not_eq_true] at hunc
  cases hls : rs.ro.lookup ip with
  | some v =>
    exact Or.inl (pqHit_intro P G
      (t := (pKeyed rs x rcs default rs.ro, Function.update inp x (some ip), ph))
      (r := { rcs with key := some default }) (by simp [pKeyed, keyed, setRec])
      (Function.update_self _ _ _) (by simp [pKeyed, hls]) he hsh hd hkem)
  | none =>
  refine Or.inr ?_
  have hnf : ¬ Exposed f x rcf := fun h => he (hexf.mp h)
  have hux : ∀ y ip', Function.update inp x (some ip) y = some ip' → y ≠ x →
      inp y = some ip' := fun y ip' h hne => by rwa [Function.update_of_ne hne] at h
  -- a session with the input `ip` is the partner `(x.1, rcs.peer)`, unexposed
  have hpart : ∀ y r, inp y = some ip → rs.x.st.recs y = some r →
      y = (x.1, rcs.peer) ∧ r.peer = x.2 ∧ r.role ≠ rcs.role ∧ ¬ Exp rs.x.st.corrupt y r.peer := by
    intro y r hy hr
    have hne : y ≠ x := fun hc => by subst hc; rw [hix] at hy; cases hy
    have hsy := hI.inpShape y ip r hy hr
    obtain ⟨h₁, h₂, h₃⟩ := shape_partner hsh hsy hne
    exact ⟨h₁, h₂, h₃, fun h => he ((exp_iff_of_shape hsh).mpr ((exp_iff_of_shape hsy).mp h))⟩
  have hrec : ∀ y, inp y = some ip → ∃ r, rs.x.st.recs y = some r := by
    intro y hy
    have h := hI.inpSome y
    rw [hy, Option.isSome_some] at h
    cases hr : rs.x.st.recs y with
    | none => simp [keyOf, hr] at h
    | some r => exact ⟨r, rfl⟩
  have hexp : ∀ (kk : K) y r, (setRec rs.x.st x { rcs with key := some kk }).recs y = some r →
      y ≠ x → rs.x.st.recs y = some r := fun kk y r hr hne => by
    rwa [setRec_recs_ne hne] at hr
  have hcomp : (if Exposed f x rcf then Status.compromised else Status.completed) =
      (if Exp rs.x.st.corrupt x rcs.peer then .compromised else .completed) := by
    simp only [hnf, he, ↓reduceIte]
  cases hll : rl.ro.lookup ip with
  | some v =>
    obtain ⟨y, r, hy, hr, hey⟩ := (hI.roReal ip v hll).resolve_left (by rw [hls]; simp)
    obtain ⟨rfl, hpe, hro, -⟩ := hpart y r hy hr
    have hc : (inp (x.1, rcs.peer)).all (· = ip) = true := by simp [hy]
    obtain ⟨p, hp, hpp, hpr, hpk⟩ := sk_some (hI.frecs (x.1, rcs.peer)) hr
    have hkr : (keyOf rl.x.st (x.1, rcs.peer)) = some v := by rw [← hI.roSess _ ip r hy hr hey, hll]
    have hkp : p.key = some v := by
      have := hI.key (x.1, rcs.peer)
      rw [hkr] at this
      simpa [keyOf, hp] using this.symm
    have hps : p.status = .completed := by
      have h := hI.fstatus _ p hp
      rw [hkp, hpp] at h
      simpa [hey] using h
    have hval : newKeyVal f x rcf default kf = v := by
      simp only [newKeyVal, hnf, ↓reduceIte, hpf, hp]
      have hP : Partner x rcf p := ⟨hpp.trans hpe, by rw [hpr, hrf]; exact hro, hps⟩
      simp [hP, hkp]
    simp only [hc, ↓reduceIte, advD]
    rw [show ((x.1, x.2) : Inst) = x from rfl, newKeyStep_of hf hkf, hval, roDet_of_some hll,
      hcomp]
    refine hI.keyed_step P G hs hl hf hsh hd hkem default v rs.ro rl.ro _ rfl hI.roSim ?_ ?_
    · intro y' ip' r' hy' hr' hey'
      by_cases hne : y' = x
      · subst hne
        simp only [Function.update_self, Option.some.injEq] at hy'
        subst hy'
        simp [hll, keyOf, setRec]
      · rw [keyOf_setRec_ne hne]
        exact hI.roSess y' ip' r' (hux y' ip' hy' hne) (hexp _ y' r' hr' hne) hey'
    · intro ip' v' hv
      rcases hI.roReal ip' v' hv with h | ⟨y', r', hy', hr', hey'⟩
      · exact Or.inl h
      · have hne : y' ≠ x := fun hc => by subst hc; rw [hix] at hy'; cases hy'
        exact Or.inr ⟨y', r', by rw [Function.update_of_ne hne]; exact hy',
          by rw [setRec_recs_ne hne]; exact hr', hey'⟩
  | none =>
    -- no session has the input `ip`
    have hnone : ∀ y, inp y ≠ some ip := by
      intro y hy
      obtain ⟨r, hr⟩ := hrec y hy
      obtain ⟨-, -, -, hey⟩ := hpart y r hy hr
      have h := hI.key_isSome P G hy
      rw [← hI.roSess y ip r hy hr hey, hll] at h
      cases h
    have hfx : (advD f (if (inp (x.1, rcs.peer)).all (· = ip) then .newKey x.1 x.2 default
        else .newKeyUnlinked x.1 x.2 default) kf).1 =
        setRec f x
          { rcf with
            key := some kf
            status := if Exp rs.x.st.corrupt x rcs.peer then .compromised else .completed } := by
      split_ifs with hc
      · have hin : inp (x.1, rcs.peer) = none := by
          cases h : inp (x.1, rcs.peer) with
          | none => rfl
          | some ip' =>
            rw [h] at hc
            simp only [Option.all_some, decide_eq_true_eq] at hc
            subst hc
            exact absurd h (hnone _)
        have hval : newKeyVal f x rcf default kf = kf := by
          simp only [newKeyVal, hnf, ↓reduceIte, hpf]
          cases hp : f.recs (x.1, rcs.peer) with
          | none => rfl
          | some p =>
            simp only
            split_ifs with hP
            · exfalso
              obtain ⟨r0, hr0, -, -, hk0⟩ := sk_some (hI.frecs (x.1, rcs.peer)).symm hp
              have h := hI.fstatus _ p hp
              rw [hP.2.2] at h
              have hpk : p.key.isSome = true := by
                cases hpk : p.key.isSome
                · rw [hpk] at h; simp at h
                · rfl
              have h1 := hI.inpSome (x.1, rcs.peer)
              rw [hin] at h1
              simp [keyOf, hr0, hk0, hpk] at h1
            · rfl
        simp only [advD]
        rw [show ((x.1, x.2) : Inst) = x from rfl, newKeyStep_of hf hkf, hval, hcomp]
        simp only [he, ↓reduceIte]
      · simp only [advD]
        rw [show ((x.1, x.2) : Inst) = x from rfl, newKeyFreshStep_of hf hkf]
        simp only [hnf, ↓reduceIte]
    rw [hfx, roDet_of_none hll]
    refine hI.keyed_step P G hs hl hf hsh hd hkem default kf rs.ro _ _ rfl ?_ ?_ ?_
    · intro ip' v h
      have hne : ip' ≠ ip := fun hc => by subst hc; rw [hls] at h; cases h
      simp only [lookup_cons, hne, ite_false]
      exact hI.roSim ip' v h
    · intro y' ip' r' hy' hr' hey'
      by_cases hne : y' = x
      · subst hne
        simp only [Function.update_self, Option.some.injEq] at hy'
        subst hy'
        simp [keyOf, setRec]
      · rw [keyOf_setRec_ne hne]
        have hy'' := hux y' ip' hy' hne
        have hip : ip' ≠ ip := fun hc => by subst hc; exact hnone y' hy''
        simp only [lookup_cons, hip, ite_false]
        exact hI.roSess y' ip' r' hy'' (hexp _ y' r' hr' hne) hey'
    · intro ip' v h
      simp only [lookup_cons] at h
      split_ifs at h with hc
      · subst hc
        exact Or.inr ⟨x, { rcs with key := some default }, Function.update_self _ _ _,
          by simp [setRec], he⟩
      · rcases hI.roReal ip' v h with h' | ⟨y', r', hy', hr', hey'⟩
        · exact Or.inl h'
        · have hne : y' ≠ x := fun hc => by subst hc; rw [hix] at hy'; cases hy'
          exact Or.inr ⟨y', r', by rw [Function.update_of_ne hne]; exact hy',
            by rw [setRec_recs_ne hne]; exact hr', hey'⟩

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- The one-time prekeys agree on both copies. -/
theorem PInv.opkOf_eq {rs rl : PSt S W K PK SK SS C} {inp : Inst → Option (PInp W SS)}
    {dlv : Inst → Option C} {f : St K}
    (hI : PInv P G rs inp dlv f rl) (sid : SessionId) (b : PartyId) :
    opkOf rl.x sid b = opkOf rs.x sid b := by
  unfold opkOf
  rw [hI.eph]
  cases h : rs.x.st.recs (sid, b) with
  | none => rw [sk_none (hI.recs (sid, b)) h]
  | some p =>
    obtain ⟨q, hq, -, hr, -⟩ := sk_some (hI.recs (sid, b)) h
    rw [hq]
    simp only [hr]

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- The KEM public keys agree on both copies. -/
theorem PInv.pkOf_eq {rs rl : PSt S W K PK SK SS C} {inp : Inst → Option (PInp W SS)}
    {dlv : Inst → Option C} {f : St K} (hI : PInv P G rs inp dlv f rl) (sid : SessionId)
    (b : PartyId) : pkOf rl sid b = pkOf rs sid b := by
  simp only [pkOf, hI.kem]

end Bad

end CatCrypt.Crypto.AKE.PQXDHSquareHops
