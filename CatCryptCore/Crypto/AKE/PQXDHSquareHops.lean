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

end CatCrypt.Crypto.AKE.PQXDHSquareHops
