/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PAKE.CPaceHops
public import CatCryptCore.Crypto.PAKE.CPaceH1
public import CatCryptCore.Crypto.PAKE.DHExtractKit
public import CatCryptCore.Crypto.OracleLazyMulti

/-!
# The bad event of the CPace square

`advantage_le_badGame` (`CatCryptCore.Crypto.PAKE.CPaceHops`) bounds the advantage between the
real and the simulated CPace world by the probability `badGame G B true` that the outputs of the
two worlds differ at some step of the joint world. This file splits that event.

## The invariant

`GoodM td M s` relates the simulated world (the simulator core, its programmed inputs and the
state of `F_lePAKE`) and the real world of the joint state `s`, for the table `td` of `H1` and the
message `M pid` received by each keyed party:

* the session records agree up to the bookkeeping of `F_lePAKE` (`stripSt`);
* the secret of a protocol party in the simulated world is `td pw` times its real secret;
* a keyed party of the session `0` has its key in the real table of `H2` at its honest input
  `hin`, and a session is completed in `F_lePAKE` iff it received its partner's message;
* every other input of the real table of `H2` has the value of the simulator's tables;
* the simulator's tables hold no double match, no match for an unqueried password and no query
  at the honest input of a passive session.

## The bad events

* `DMst`: two inputs of the simulator's tables with one transcript match distinct passwords;
* `UQst`: an input of the simulator's tables matches a password not queried at `H1`;
* `PSst`: an input of the simulator's tables is the honest input of a party that received its
  partner's message;
* `CollStep`, `TdColl`: a new party's message occurs in an earlier input of `H2`, or two
  passwords have the same value of `H1`.

## Main results

* `step_good`: from `Good`, a step of the joint world either is bad or gives equal outputs and
  reaches a state satisfying `Good`.
* `run_flagWhen_or_le`: the union bound for bad flags.
* `badGame_le`: `badGame G B true` is at most the sum of the probabilities of the experiments
  `dmExp`, `uqExp`, `psExp` and `collExp`, each the probability that the run of the joint world
  makes a transition of the named kind.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PAKE.CPaceBad

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FPAKE
open CatCrypt.Crypto.PAKE.DHExtract CatCrypt.Crypto.PAKE.CPaceSquare
open CatCrypt.Crypto.PAKE.CPaceHops CatCrypt.NonUniform
open scoped ENNReal

/-- The state of the joint world without its flag. -/
abbrev JS (S W Pw K : Type) [Field S] := (SimSt S W Pw K × St Pw K) × RSt S W Pw K

/-! ## Records up to the bookkeeping of `F_lePAKE` -/

section Strip

variable {Pw K : Type}

/-- A record without the status, the test outcome and the late-test flag. -/
def strip (r : Rec Pw K) : Rec Pw K :=
  { r with status := .fresh, tested := none, registered := false }

/-- The state with every record stripped. -/
def stripSt (t : St Pw K) : St Pw K := { t with recs := fun x => (t.recs x).map strip }

/-- `pollStep` commutes with `stripSt`. -/
theorem pollStep_stripSt (t : St Pw K) :
    pollStep (stripSt t) = (stripSt (pollStep t).1, (pollStep t).2) := by
  unfold pollStep stripSt
  split <;> rename_i h <;> simp_all

/-- `keyOf` is invariant under `stripSt`. -/
theorem keyOf_stripSt (t : St Pw K) (x : Inst) : keyOf (stripSt t) x = keyOf t x := by
  unfold keyOf stripSt strip
  cases h : t.recs x <;> simp [h]

end Strip

/-! ## Inputs of `H2` -/

section Inputs

variable {S W Pw K : Type} [Field S] [DecidableEq W] [DecidableEq Pw] (G : DHGroup S W)

/-- The value of `H2` at `x` in the simulator's tables: the programmed value, else the sampled
one. -/
def simLk (s : SimSt S W Pw K) (x : Inp W) : Option K :=
  match s.2.lookup x with
  | some k => some k
  | none => s.1.h2.lookup x

/-- The received message of the party `pid` in the input `x` of `H2`. -/
def peerMsg (pid : PartyId) (x : Inp W) : W := if pid = 0 then x.2.2.1 else x.2.1

/-- The honest input of `H2` of the real party `pid` on the received message `m`. -/
def hin (td : Pw → Sˣ) (rs : RSt S W Pw K) (pid : PartyId) (m : W) : Option (Inp W) :=
  match rs.ys pid, rs.st.recs (0, pid) with
  | some y, some rc => some (h2Inp pid rc.role (G.exp (G.pub (td rc.pw)) y) m (G.exp m y))
  | _, _ => none

/-- The input `x` of `H2` matches the password `pw` for the simulated party `pid`: its transcript
is a transcript of the party, and it passes the CPace match test for `pw`. -/
def Matches (td : Pw → Sˣ) (c : SimCore S W Pw K) (pid : PartyId) (pw : Pw) (x : Inp W) :
    Prop :=
  ∃ z peer role, c.zs pid = some z ∧ c.info pid = some (peer, role) ∧
    x.tr = (h2Inp pid role (G.pub z) (peerMsg pid x) (peerMsg pid x)).tr ∧
    (kit G td).matchTest z (peerMsg pid x) x.2.2.2 pw = true

/-- The input `x` has a value in the simulator's tables. -/
def InDom (s : SimSt S W Pw K) (x : Inp W) : Prop := (simLk s x).isSome

/-- **Double match**: two inputs of the simulator's tables with one transcript match distinct
passwords for one party. -/
def DMst (td : Pw → Sˣ) (s : SimSt S W Pw K) : Prop :=
  ∃ pid x₁ x₂ pw₁ pw₂, InDom s x₁ ∧ InDom s x₂ ∧ x₁.tr = x₂.tr ∧ pw₁ ≠ pw₂ ∧
    Matches G td s.1 pid pw₁ x₁ ∧ Matches G td s.1 pid pw₂ x₂

/-- **Unqueried match**: an input of the simulator's tables matches a password whose point of
`H1` was not queried. -/
def UQst (td : Pw → Sˣ) (s : SimSt S W Pw K) : Prop :=
  ∃ pid x pw, InDom s x ∧ pw ∉ s.1.cands ∧ Matches G td s.1 pid pw x

/-- **Passive-session query**: an input of the simulator's tables is the input of the party
`pid` on its partner's message, matching the party's password. -/
def PSst (td : Pw → Sˣ) (s : SimSt S W Pw K × St Pw K) : Prop :=
  ∃ pid x z' r, InDom s.1 x ∧ s.1.1.zs (1 - pid) = some z' ∧ peerMsg pid x = G.pub z' ∧
    s.2.recs (0, pid) = some r ∧ Matches G td s.1.1 pid r.pw x

/-- The value `w` occurs as a message in an input of `H2` of the real or the simulated tables. -/
def InMsgs (s : JS S W Pw K) (w : W) : Prop :=
  ∃ x, ((s.2.h2.lookup x).isSome ∨ InDom s.1.1 x) ∧ (x.2.1 = w ∨ x.2.2.1 = w)

/-- **Collision of `H1`**: two passwords with the same value of `H1`. -/
def TdColl (td : Pw → Sˣ) : Prop := ¬ Function.Injective td

/-- **Collision of a new message**: a party draws a secret whose message occurs in an earlier
input of `H2`. -/
def CollStep (s s' : JS S W Pw K) : Prop :=
  ∃ pid z, s.1.1.1.zs pid = none ∧ s'.1.1.1.zs pid = some z ∧ InMsgs s (G.pub z)

/-- **The bad transitions** of the joint world from `s` to `s'`. -/
def Bad (td : Pw → Sˣ) (s s' : JS S W Pw K) : Prop :=
  TdColl td ∨ CollStep G s s' ∨ DMst G td s'.1.1 ∨ UQst G td s'.1.1 ∨ PSst G td s'.1

end Inputs

/-! ## The invariant -/

section Good

variable {S W Pw K : Type} [Field S] [DecidableEq W] [DecidableEq Pw] (G : DHGroup S W)

/-- **The invariant of the joint world** for the table `td` of `H1` and the message `M pid`
received by each keyed party. -/
structure GoodM (td : Pw → Sˣ) (M : PartyId → W) (s : JS S W Pw K) : Prop where
  st : s.2.st = stripSt s.1.2
  info : ∀ pid, s.1.1.1.info pid =
    if pid ≤ 1 then (s.1.2.recs (0, pid)).map fun r => (r.peer, r.role) else none
  zs : ∀ pid, s.1.1.1.zs pid =
    (s.2.ys pid).bind fun y => (s.1.2.recs (0, pid)).map fun r => (td r.pw : S) * y
  act : ∀ pid y, s.2.ys pid = some y →
    pid ≤ 1 ∧ ∃ r, s.1.2.recs (0, pid) = some r ∧ r.peer = 1 - pid
  fresh : ∀ x r, s.1.2.recs x = some r → r.key = none →
    r.status = .fresh ∧ r.tested = none ∧ r.registered = false
  reg : ∀ x r, s.1.2.recs x = some r → r.registered = true → r.status = .interrupted
  keyed : ∀ pid, s.1.1.1.keyed pid = (keyOf s.1.2 (0, pid)).isSome
  keyAt : ∀ x r, s.1.2.recs x = some r → r.key.isSome → x.1 = 0
  key : ∀ pid r k, s.1.2.recs (0, pid) = some r → r.key = some k → ∃ hx,
    hin G td s.2 pid (M pid) = some hx ∧ s.2.h2.lookup hx = some k ∧
    (simLk s.1.1 hx = none ∨ simLk s.1.1 hx = some k) ∧ M pid ≠ G.pub 0 ∧
    (r.status = .completed ↔ (s.1.1.1.zs (1 - pid)).map G.pub = some (M pid))
  pend : ∀ pid T, s.1.1.1.pend pid = some T → ∃ r hx, s.1.2.recs (0, pid) = some r ∧
    r.key.isSome ∧ r.registered = true ∧ hin G td s.2 pid (M pid) = some hx ∧ hx.tr = T
  tab : ∀ x, s.2.h2.lookup x = simLk s.1.1 x ∨
    ∃ pid, (keyOf s.1.2 (0, pid)).isSome ∧ hin G td s.2 pid (M pid) = some x
  prog : ∀ x k, s.1.1.2.lookup x = some k → ∃ pid r hx, s.1.2.recs (0, pid) = some r ∧
    r.key.isSome ∧ r.status = .interrupted ∧ hin G td s.2 pid (M pid) = some hx ∧ hx.tr = x.tr
  disj : ∀ x, s.1.1.2.lookup x = none ∨ s.1.1.1.h2.lookup x = none
  nodup : ∀ e ∈ s.1.1.1.h2, s.1.1.1.h2.lookup e.1 = some e.2
  dm : ¬ DMst G td s.1.1
  uq : ¬ UQst G td s.1.1
  ps : ¬ PSst G td s.1
  wit : ∀ pid r hx, s.1.2.recs (0, pid) = some r → r.key.isSome → r.status ≠ .completed →
    s.1.1.1.pend pid = none → hin G td s.2 pid (M pid) = some hx → simLk s.1.1 hx = none →
    ∃ e pw₁, InDom s.1.1 e ∧ e.tr = hx.tr ∧ pw₁ ≠ r.pw ∧ Matches G td s.1.1.1 pid pw₁ e

/-- The invariant for some received messages. -/
def Good (td : Pw → Sˣ) (s : JS S W Pw K) : Prop := ∃ M, GoodM G td M s

end Good

/-! ## Steps of the joint world -/

section Step

variable {S W Pw K : Type} [Field S] [DecidableEq W] [DecidableEq Pw] [Inhabited K]
  (G : DHGroup S W)

omit [DecidableEq Pw] [Inhabited K] in
/-- The invariant survives a change of the state of `F_lePAKE` and of the real records that
keeps the records. -/
theorem GoodM.congr {td : Pw → Sˣ} {M : PartyId → W} {c c' : SimCore S W Pw K}
    {p : List (Inp W × K)} {t t' : St Pw K} {rs rs' : RSt S W Pw K}
    (hG : GoodM G td M (((c, p), t), rs)) (hca : ∀ pw, pw ∈ c.cands → pw ∈ c'.cands)
    (hi : c'.info = c.info)
    (hz : c'.zs = c.zs) (hke : c'.keyed = c.keyed) (hpe : c'.pend = c.pend) (hh : c'.h2 = c.h2)
    (h : t'.recs = t.recs) (hst : rs'.st = stripSt t')
    (hys : rs'.ys = rs.ys) (hh2 : rs'.h2 = rs.h2) : GoodM G td M (((c', p), t'), rs') := by
  have hst₀ : rs.st = stripSt t := hG.st
  have hhin : hin G td rs' = hin G td rs := by
    funext pid m
    simp only [hin, hys, hst, hst₀, stripSt, h]
  have hk : keyOf t' = keyOf t := by
    funext x
    simp only [keyOf, h]
  have hlk : simLk (c', p) = simLk (c, p) := by
    funext x
    simp only [simLk, hh]
  have hma : Matches G td c' = Matches G td c := by
    funext pid pw x
    simp only [Matches, hz, hi]
  obtain ⟨-, info, zs, act, fresh, reg, keyed, keyAt, key, pend, tab, prog, disj, nodup, dm, uq,
    ps, wit⟩ := hG
  refine ⟨hst, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [h, hi] using info
  · simpa only [h, hys, hz] using zs
  · simpa only [h, hys] using act
  · simpa only [h] using fresh
  · simpa only [h] using reg
  · simpa only [hk, hke] using keyed
  · simpa only [h] using keyAt
  · simpa only [h, hhin, hh2, hlk, hz] using key
  · simpa only [h, hhin, hpe] using pend
  · simpa only [hk, hhin, hh2, hlk] using tab
  · simpa only [h, hhin] using prog
  · simpa only [hh] using disj
  · simpa only [hh] using nodup
  · simpa only [DMst, InDom, hlk, hma] using dm
  · rintro ⟨pid, x, pw, h₁, h₂, h₃⟩
    refine uq ⟨pid, x, pw, ?_, fun h => h₂ (hca pw h), ?_⟩
    · simpa only [InDom, hlk] using h₁
    · simpa only [hma] using h₃
  · simpa only [PSst, InDom, hlk, hma, hz, h] using ps
  · simpa only [h, hhin, hpe, hlk, hma, InDom] using wit

omit [DecidableEq Pw] [Inhabited K] in
/-- The invariant depends on the simulator core only through its fields other than the table of
`H1` and the phase. -/
theorem GoodM.phase {td : Pw → Sˣ} {M : PartyId → W} {c : SimCore S W Pw K}
    {p : List (Inp W × K)} {t : St Pw K} {rs : RSt S W Pw K}
    (hG : GoodM G td M (((c, p), t), rs)) (o : Option (Pw → Sˣ)) (ph : Phase W K) :
    GoodM G td M ((({ c with td := o, phase := ph }, p), t), rs) :=
  GoodM.congr G hG (fun _ h => h) rfl rfl rfl rfl rfl rfl hG.st rfl rfl

/-- `h1` keeps the invariant and gives equal outputs. -/
theorem step_h1 (td : Pw → Sˣ) (M : PartyId → W) (s : JS S W Pw K) (hG : GoodM G td M s)
    (r : (S × K) × K × K) (pw : Pw) :
    (jointD G td s (.inr (.h1 pw)) r).1.1 = (jointD G td s (.inr (.h1 pw)) r).1.2 ∧
      GoodM G td M (jointD G td s (.inr (.h1 pw)) r).2 := by
  obtain ⟨⟨⟨c, p⟩, t⟩, rs⟩ := s
  simp only [jointD, simWorldD, simStartD, simCoreD, advCoreD, drive1D, realDet, setTd]
  refine ⟨trivial, GoodM.congr G hG ?_ rfl rfl rfl rfl rfl rfl hG.st rfl rfl⟩
  intro q hq
  split_ifs
  · grind
  · grind

/-- `idle` keeps the invariant and gives equal outputs. -/
theorem step_idle (td : Pw → Sˣ) (M : PartyId → W) (s : JS S W Pw K) (hG : GoodM G td M s)
    (r : (S × K) × K × K) :
    (jointD G td s (.inr .idle) r).1.1 = (jointD G td s (.inr .idle) r).1.2 ∧
      GoodM G td M (jointD G td s (.inr .idle) r).2 := by
  obtain ⟨⟨⟨c, p⟩, t⟩, rs⟩ := s
  simp only [jointD, simWorldD, simStartD, simCoreD, advCoreD, drive1D, realDet, setTd]
  exact ⟨trivial, GoodM.phase G hG _ _⟩

/-- `poll` keeps the invariant and gives equal outputs. -/
theorem step_poll (td : Pw → Sˣ) (M : PartyId → W) (s : JS S W Pw K) (hG : GoodM G td M s)
    (r : (S × K) × K × K) :
    (jointD G td s (.inr .poll) r).1.1 = (jointD G td s (.inr .poll) r).1.2 ∧
      GoodM G td M (jointD G td s (.inr .poll) r).2 := by
  obtain ⟨⟨⟨c, p⟩, t⟩, rs⟩ := s
  have hst : rs.st = stripSt t := hG.st
  simp only [jointD, simWorldD, simStartD, simCoreD, advCoreD, drive1D, realDet, fStepD, leAdvD,
    simResumeV, simAnswer, convert, setTd, hst, pollStep_stripSt]
  refine ⟨trivial, GoodM.congr G hG (fun _ h => h) rfl rfl rfl rfl rfl ?_ rfl rfl rfl⟩
  unfold pollStep
  split <;> rfl

/-- `msg` keeps the invariant and gives equal outputs. -/
theorem step_msg (td : Pw → Sˣ) (M : PartyId → W) (s : JS S W Pw K) (hG : GoodM G td M s)
    (r : (S × K) × K × K) (pid : PartyId) :
    (jointD G td s (.inr (.msg pid)) r).1.1 = (jointD G td s (.inr (.msg pid)) r).1.2 ∧
      GoodM G td M (jointD G td s (.inr (.msg pid)) r).2 := by
  obtain ⟨⟨⟨c, p⟩, t⟩, rs⟩ := s
  have hst : rs.st = stripSt t := hG.st
  have hz := hG.zs pid
  simp only [jointD, simWorldD, simStartD, simCoreD, advCoreD, drive1D, realDet, setTd]
  refine ⟨?_, GoodM.phase G hG _ _⟩
  simp only at hz
  rcases hy : rs.ys pid with _ | y <;> rcases hr : t.recs (0, pid) with _ | rc <;>
    simp [realMsg, hst, stripSt, strip, hy, hr, hz, G.exp_pub]

/-- `getKey` keeps the invariant and gives equal outputs. -/
theorem step_getKey (td : Pw → Sˣ) (M : PartyId → W) (s : JS S W Pw K) (hG : GoodM G td M s)
    (r : (S × K) × K × K) (sid pid : PartyId) :
    (jointD G td s (.inl (.getKey sid pid)) r).1.1 =
        (jointD G td s (.inl (.getKey sid pid)) r).1.2 ∧
      GoodM G td M (jointD G td s (.inl (.getKey sid pid)) r).2 := by
  obtain ⟨⟨⟨c, p⟩, t⟩, rs⟩ := s
  have hst : rs.st = stripSt t := hG.st
  simp only [jointD, simWorldD, simStartD, simCoreD, honStepD, honPub, drive1D, realDet, fStepD,
    leHonStep, simResumeV, simAnswer, convert, setTd, hst, keyOf_stripSt]
  exact ⟨trivial, GoodM.phase G hG _ _⟩

omit [DecidableEq Pw] [Inhabited K] in
/-- `addSession` at an instance without a record commutes with `stripSt`. -/
theorem stripSt_addSession {t : St Pw K} {x : Inst} (peer : PartyId) (role : Role) (pw : Pw) :
    addSession (stripSt t) x peer role pw = stripSt (addSession t x peer role pw) := by
  unfold addSession stripSt
  by_cases h : (t.recs x).isSome
  · simp [h]
  · simp only [Option.isSome_map, h, Bool.false_eq_true, ite_false, St.mk.injEq, and_true]
    funext y
    by_cases hy : y = x
    · subst hy
      simp [strip]
    · simp [Function.update_of_ne hy]

omit [DecidableEq W] [DecidableEq Pw] [Inhabited K] in
/-- The received message occurs among the messages of an honest input. -/
theorem hin_msg {td : Pw → Sˣ} {rs : RSt S W Pw K} {q : PartyId} {m : W} {x : Inp W}
    (h : hin G td rs q m = some x) : x.2.1 = m ∨ x.2.2.1 = m := by
  unfold hin at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp only [h2Inp]
    split_ifs <;> simp
  · simp at h

omit [DecidableEq Pw] [Inhabited K] in
/-- `Matches` for the party `q` reads only the secret and the role of `q`. -/
theorem Matches_congr {td : Pw → Sˣ} {c c' : SimCore S W Pw K} {q : PartyId} {pw : Pw}
    {x : Inp W} (hz : c'.zs q = c.zs q) (hi : c'.info q = c.info q) :
    Matches G td c' q pw x ↔ Matches G td c q pw x := by
  simp only [Matches, hz, hi]

omit [DecidableEq W] in
/-- The received message of an input of `H2` of a party is its received message. -/
@[simp] theorem peerMsg_h2Inp (q : PartyId) (role : Role) (own m d : W) :
    peerMsg q (h2Inp q role own m d) = m := by
  unfold peerMsg h2Inp
  split_ifs <;> rfl

omit [DecidableEq W] in
/-- The received message is determined by the transcript. -/
theorem peerMsg_eq_of_tr {q : PartyId} {x x' : Inp W} (h : x.tr = x'.tr) :
    peerMsg q x = peerMsg q x' := by
  simp only [Inp.tr, Prod.mk.injEq] at h
  unfold peerMsg
  rw [h.2.1, h.2.2]

omit [DecidableEq Pw] [Inhabited K] in
/-- `Matches` as a Diffie–Hellman relation. -/
theorem matches_iff {td : Pw → Sˣ} {c : SimCore S W Pw K} {q : PartyId} {pw : Pw} {x : Inp W} :
    Matches G td c q pw x ↔ ∃ z peer role, c.zs q = some z ∧ c.info q = some (peer, role) ∧
      x.tr = (h2Inp q role (G.pub z) (peerMsg q x) (peerMsg q x)).tr ∧
      peerMsg q x ≠ G.pub 0 ∧ x.2.2.2 = G.exp (peerMsg q x) (z * ((td pw : S))⁻¹) := by
  simp only [Matches, kit, cpaceKit, DHExtractKit.matchTest, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨z, peer, role, h1, h2, h3, h4, h5⟩
    grind
  · rintro ⟨z, peer, role, h1, h2, h3, h4, h5⟩
    grind

omit [DecidableEq Pw] [Inhabited K] in
/-- **Honest inputs in simulator terms**: under the invariant, the honest input of a started
party `q` on `m` is `h2Inp q role (g^z) m (m^(z / td pw))`. -/
theorem GoodM.hin_eq {td : Pw → Sˣ} {M : PartyId → W} {c : SimCore S W Pw K}
    {p : List (Inp W × K)} {t : St Pw K} {rs : RSt S W Pw K}
    (hG : GoodM G td M (((c, p), t), rs)) {q : PartyId} {m : W} {hx : Inp W}
    (h : hin G td rs q m = some hx) : ∃ z rc, c.zs q = some z ∧ t.recs (0, q) = some rc ∧
      c.info q = some (rc.peer, rc.role) ∧
      hx = h2Inp q rc.role (G.pub z) m (G.exp m (z * ((td rc.pw : S))⁻¹)) := by
  have hst : rs.st = stripSt t := hG.st
  unfold hin at h
  cases hy : rs.ys q with
  | none => simp [hy] at h
  | some y =>
    cases hr : t.recs (0, q) with
    | none => simp [hy, hst, stripSt, hr] at h
    | some rc =>
      simp only [hy, hst, stripSt, hr, Option.map_some, Option.some.injEq] at h
      have hq := (hG.act q y hy).1
      have hz := hG.zs q
      have hi := hG.info q
      simp only [hy, hr, Option.bind_some, Option.map_some] at hz hi
      rw [ite_eq_left hq] at hi
      refine ⟨_, rc, hz, rfl, hi, ?_⟩
      rw [← h]
      simp only [strip, G.exp_pub]
      congr 2
      field_simp

omit [DecidableEq Pw] [Inhabited K] in
/-- **An honest input matches the party's password** when its received message is not the
identity. -/
theorem GoodM.hin_matches {td : Pw → Sˣ} {M : PartyId → W} {c : SimCore S W Pw K}
    {p : List (Inp W × K)} {t : St Pw K} {rs : RSt S W Pw K}
    (hG : GoodM G td M (((c, p), t), rs)) {q : PartyId} {m : W} {hx : Inp W}
    (h : hin G td rs q m = some hx) (hm : m ≠ G.pub 0) {rc : Rec Pw K}
    (hr : t.recs (0, q) = some rc) : Matches G td c q rc.pw hx := by
  obtain ⟨z, rc', hz, hr', hi, rfl⟩ := hG.hin_eq G h
  rw [hr] at hr'
  cases hr'
  rw [matches_iff]
  refine ⟨z, rc.peer, rc.role, hz, hi, ?_, ?_, ?_⟩
  · rw [peerMsg_h2Inp]
    rfl
  · rwa [peerMsg_h2Inp]
  · rw [peerMsg_h2Inp]
    rfl

omit [DecidableEq Pw] [Inhabited K] in
/-- **A matching input with an honest transcript is the honest input.** -/
theorem GoodM.eq_hin_of_matches {td : Pw → Sˣ} {M : PartyId → W} {c : SimCore S W Pw K}
    {p : List (Inp W × K)} {t : St Pw K} {rs : RSt S W Pw K}
    (hG : GoodM G td M (((c, p), t), rs)) {q : PartyId} {m : W} {hx x : Inp W}
    (h : hin G td rs q m = some hx) {rc : Rec Pw K} (hr : t.recs (0, q) = some rc)
    (hxm : Matches G td c q rc.pw x) (htr : x.tr = hx.tr) : x = hx := by
  obtain ⟨z, rc', hz, hr', hi, rfl⟩ := hG.hin_eq G h
  rw [hr] at hr'
  cases hr'
  rw [matches_iff] at hxm
  obtain ⟨z', -, -, hz', -, -, -, hd⟩ := hxm
  rw [hz] at hz'
  cases hz'
  have hpm : peerMsg q x = m := by rw [peerMsg_eq_of_tr htr, peerMsg_h2Inp]
  obtain ⟨x1, x2, x3, x4⟩ := x
  simp only [Inp.tr, h2Inp, Prod.mk.injEq] at htr ⊢
  refine ⟨htr.1, htr.2.1, htr.2.2, ?_⟩
  simpa only [hpm] using hd

/-- The simulator core after a new record: the peer and role of a party of the session `0`, and
`td pw` times the real secret `oy` of a protocol party. -/
def newCore (td : Pw → Sˣ) (c : SimCore S W Pw K) (sid pid peer : PartyId) (role : Role) (pw : Pw)
    (oy : Option S) : SimCore S W Pw K :=
  { c with
    info := if sid = 0 ∧ pid ≤ 1 then Function.update c.info pid (some (peer, role)) else c.info,
    zs := oy.elim c.zs fun y => Function.update c.zs pid (some ((td pw : S) * y)) }

/-- The real state after a new record with the secret `oy`. -/
def newRs (rs : RSt S W Pw K) (t : St Pw K) (pid : PartyId) (oy : Option S) : RSt S W Pw K :=
  { rs with st := stripSt t, ys := oy.elim rs.ys fun y => Function.update rs.ys pid (some y) }

omit [DecidableEq Pw] [Inhabited K] in
/-- **A new record keeps the invariant**: a record at an instance without one, the peer and role
of a party of the session `0`, and, for a protocol party, the secret `oy` in the real world and
`td pw` times it in the simulated world, whose message occurs in no earlier input of `H2`. -/
theorem GoodM.addSess {td : Pw → Sˣ} {M : PartyId → W} {c : SimCore S W Pw K}
    {p : List (Inp W × K)} {t : St Pw K} {rs : RSt S W Pw K} {sid pid peer : PartyId}
    {role : Role} {pw : Pw} (oy : Option S) (hG : GoodM G td M (((c, p), t), rs))
    (hn : t.recs (sid, pid) = none)
    (hoy : oy.isSome → sid = 0 ∧ pid ≤ 1 ∧ peer = 1 - pid)
    (hcoll : ∀ y, oy = some y → ¬ InMsgs (((c, p), t), rs) (G.pub ((td pw : S) * y)))
    (hdm : ¬ DMst G td (newCore td c sid pid peer role pw oy, p))
    (huq : ¬ UQst G td (newCore td c sid pid peer role pw oy, p))
    (hps : ¬ PSst G td ((newCore td c sid pid peer role pw oy, p),
      addSession t (sid, pid) peer role pw)) :
    GoodM G td M (((newCore td c sid pid peer role pw oy, p), addSession t (sid, pid) peer role pw),
      newRs rs (addSession t (sid, pid) peer role pw) pid oy) := by
  have hst : rs.st = stripSt t := hG.st
  have hrecs : (addSession t (sid, pid) peer role pw).recs =
      Function.update t.recs (sid, pid) (some ⟨peer, role, pw, .fresh, none, none, false⟩) := by
    simp [addSession, hn]
  have hold : ∀ q r, t.recs (0, q) = some r →
      (addSession t (sid, pid) peer role pw).recs (0, q) = some r ∧
        (newRs rs (addSession t (sid, pid) peer role pw) pid oy).ys q = rs.ys q := by
    intro q r hr
    have hne : (0, q) ≠ (sid, pid) := fun h => by rw [h, hn] at hr; simp at hr
    refine ⟨by rw [hrecs, Function.update_of_ne hne, hr], ?_⟩
    rcases oy with _ | y
    · rfl
    · have hq : q ≠ pid := fun h => hne (by rw [h, (hoy rfl).1])
      simp [newRs, Function.update_of_ne hq]
  have hinq : ∀ q m r, t.recs (0, q) = some r →
      hin G td (newRs rs (addSession t (sid, pid) peer role pw) pid oy) q m = hin G td rs q m := by
    intro q m r hr
    obtain ⟨h₁, h₂⟩ := hold q r hr
    simp only [hin, h₂, hst]
    simp only [newRs, stripSt, h₁, hr]
  have hkey : ∀ q, keyOf (addSession t (sid, pid) peer role pw) (0, q) = keyOf t (0, q) := by
    intro q
    unfold keyOf
    rw [hrecs]
    by_cases hq : (0, q) = (sid, pid)
    · rw [hq, Function.update_self, hn]
      rfl
    · rw [Function.update_of_ne hq]
  have hlk : simLk (newCore td c sid pid peer role pw oy, p) = simLk (c, p) := rfl
  have hys0 : ∀ y, oy = some y → rs.ys pid = none ∧ c.zs pid = none := by
    intro y hy
    have hs := (hoy (by simp [hy])).1
    have hy0 : rs.ys pid = none := by
      cases h : rs.ys pid with
      | none => rfl
      | some y' =>
        obtain ⟨-, r, hr, -⟩ := hG.act pid y' h
        rw [hs] at hn
        rw [hn] at hr
        simp at hr
    refine ⟨hy0, ?_⟩
    rw [hG.zs pid]
    simp [hy0]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hG.disj, hG.nodup, hdm, huq, hps, ?_⟩
  rotate_right
  · -- wit
    intro q r hx hr hk hc hp hh hl
    have hne : (0, q) ≠ (sid, pid) := by
      intro h
      rw [hrecs, h, Function.update_self, Option.some.injEq] at hr
      subst hr
      simp at hk
    rw [hrecs, Function.update_of_ne hne] at hr
    rw [hinq q _ r hr] at hh
    obtain ⟨e, pw₁, h1, h2, h3, h4⟩ := hG.wit q r hx hr hk hc hp hh hl
    refine ⟨e, pw₁, h1, h2, h3, ?_⟩
    have hcz : (newCore td c sid pid peer role pw oy).zs q = c.zs q ∧
        (newCore td c sid pid peer role pw oy).info q = c.info q := by
      by_cases hs : sid = 0
      · have hq : q ≠ pid := fun h => hne (by rw [h, hs])
        constructor
        · rcases oy with _ | y
          · rfl
          · simp [newCore, Function.update_of_ne hq]
        · simp only [newCore]
          split_ifs
          · exact Function.update_of_ne hq _ _
          · rfl
      · have hoy' : oy = none := by
          rcases oy with _ | y
          · rfl
          · exact absurd (hoy rfl).1 hs
        subst hoy'
        simp [newCore, hs]
    rwa [Matches_congr G hcz.1 hcz.2]
  · -- info
    intro q
    have h := hG.info q
    simp only [newCore, hrecs]
    grind
  · -- zs
    intro q
    have hz := hG.zs q
    simp only at hz
    rw [hrecs]
    by_cases hq : (0, q) = (sid, pid)
    · obtain ⟨h1, h2⟩ := Prod.mk.inj hq
      subst h1 h2
      have hyq : rs.ys q = none := by
        cases h : rs.ys q with
        | none => rfl
        | some y' =>
          obtain ⟨-, r, hr, -⟩ := hG.act q y' h
          rw [hn] at hr
          simp at hr
      rw [Function.update_self]
      rcases oy with _ | y
      · simp [newCore, newRs, hz, hyq]
      · simp [newCore, newRs]
    · rw [Function.update_of_ne hq]
      rcases oy with _ | y
      · simpa [newCore, newRs] using hz
      · have hqp : q ≠ pid := fun h => hq (by rw [h, (hoy rfl).1])
        simpa [newCore, newRs, Function.update_of_ne hqp] using hz
  · -- act
    intro q y hy
    rcases oy with _ | y₀
    · obtain ⟨h1, r, hr, hp⟩ := hG.act q y hy
      exact ⟨h1, r, (hold q r hr).1, hp⟩
    · by_cases hq : q = pid
      · subst hq
        obtain ⟨h0, h1, h2⟩ := hoy rfl
        refine ⟨h1, ⟨peer, role, pw, .fresh, none, none, false⟩, ?_, h2⟩
        rw [hrecs, h0, Function.update_self]
      · simp only [newRs, Option.elim, Function.update_of_ne hq] at hy
        obtain ⟨h1, r, hr, hp⟩ := hG.act q y hy
        exact ⟨h1, r, (hold q r hr).1, hp⟩
  · -- fresh
    intro x r hr hk
    rw [hrecs] at hr
    by_cases hx : x = (sid, pid)
    · subst hx
      simp only [Function.update_self, Option.some.injEq] at hr
      subst hr
      simp
    · rw [Function.update_of_ne hx] at hr
      exact hG.fresh x r hr hk
  · -- reg
    intro x r hr hk
    rw [hrecs] at hr
    by_cases hx : x = (sid, pid)
    · subst hx
      simp only [Function.update_self, Option.some.injEq] at hr
      subst hr
      simp at hk
    · rw [Function.update_of_ne hx] at hr
      exact hG.reg x r hr hk
  · -- keyed
    intro q
    rw [hkey]
    exact hG.keyed q
  · -- keyAt
    intro x r hr hk
    rw [hrecs] at hr
    by_cases hx : x = (sid, pid)
    · subst hx
      simp only [Function.update_self, Option.some.injEq] at hr
      subst hr
      simp at hk
    · rw [Function.update_of_ne hx] at hr
      exact hG.keyAt x r hr hk
  · -- key
    intro q r k hr hk
    have hne : (0, q) ≠ (sid, pid) := by
      intro h
      rw [hrecs, h, Function.update_self, Option.some.injEq] at hr
      subst hr
      simp at hk
    rw [hrecs, Function.update_of_ne hne] at hr
    obtain ⟨hx, h1, h2, h3, h4, h5⟩ := hG.key q r k hr hk
    refine ⟨hx, by rw [hinq q _ r hr]; exact h1, h2, h3, h4, ?_⟩
    rcases oy with _ | y
    · exact h5
    · by_cases hq : 1 - q = pid
      · have hne' : G.pub ((td pw : S) * y) ≠ M q := by
          intro he
          refine hcoll y rfl ⟨hx, Or.inl (by simp [h2]), ?_⟩
          rw [he]
          exact hin_msg G h1
        have hz0 := (hys0 y rfl).2
        simp only at h5
        rw [hq, hz0] at h5
        simp only [newCore, Option.elim, hq, Function.update_self, Option.map_some,
          Option.some.injEq, hne', iff_false]
        intro hc
        exact absurd (h5.mp hc) (by simp)
      · simpa only [newCore, Option.elim, Function.update_of_ne hq] using h5
  · -- pend
    intro q T hT
    obtain ⟨r, hx, hr, h₁, h₂, h₃, h₄⟩ := hG.pend q T hT
    exact ⟨r, hx, (hold q r hr).1, h₁, h₂, by rw [hinq q _ r hr]; exact h₃, h₄⟩
  · -- tab
    intro x
    rcases hG.tab x with h | ⟨q, hq, hx⟩
    · exact Or.inl h
    · refine Or.inr ⟨q, by rw [hkey]; exact hq, ?_⟩
      obtain ⟨r, hr⟩ : ∃ r, t.recs (0, q) = some r := by
        unfold keyOf at hq
        cases h : t.recs (0, q) with
        | none => simp [h] at hq
        | some r => exact ⟨r, rfl⟩
      rw [hinq q _ r hr]
      exact hx
  · -- prog
    intro x k hx
    obtain ⟨q, r, x, hr, h₁, h₂, h₃, h₄⟩ := hG.prog x k hx
    exact ⟨q, r, x, (hold q r hr).1, h₁, h₂, by rw [hinq q _ r hr]; exact h₃, h₄⟩

omit [DecidableEq Pw] [Inhabited K] in
/-- Under the invariant, a value of the simulator's tables is the value of the real table. -/
theorem GoodM.lookup_of_simLk {td : Pw → Sˣ} {M : PartyId → W} {c : SimCore S W Pw K}
    {p : List (Inp W × K)} {t : St Pw K} {rs : RSt S W Pw K}
    (hG : GoodM G td M (((c, p), t), rs)) {x : Inp W} {k : K} (h : simLk (c, p) x = some k) :
    rs.h2.lookup x = some k := by
  rcases hG.tab x with h' | ⟨q, hq, hx⟩
  · rw [h', h]
  · obtain ⟨rc, hr⟩ : ∃ rc, t.recs (0, q) = some rc := by
      unfold keyOf at hq
      cases h0 : t.recs (0, q) with
      | none => simp [h0] at hq
      | some rc => exact ⟨rc, rfl⟩
    obtain ⟨kq, hkq⟩ : ∃ kq, rc.key = some kq := by
      unfold keyOf at hq
      rw [hr] at hq
      cases h0 : rc.key with
      | none => simp [h0] at hq
      | some kq => exact ⟨kq, rfl⟩
    obtain ⟨x, h1, h2, h3, -⟩ := hG.key q rc kq hr hkq
    rw [hx] at h1
    obtain rfl := Option.some.inj h1
    rcases h3 with h3 | h3 <;> rw [h3] at h
    · simp at h
    · rw [h2, h]

/-- A lookup past an entry for another key. -/
theorem lookup_cons_ne {α β : Type} [DecidableEq α] {x y : α} {k : β} {l : List (α × β)}
    (h : y ≠ x) : ((x, k) :: l).lookup y = l.lookup y := by
  have hb : (y == x) = false := by simpa using h
  simp only [List.lookup, hb]

/-- A lookup at the key of the first entry. -/
theorem lookup_cons_self {α β : Type} [DecidableEq α] {x : α} {k : β} {l : List (α × β)} :
    ((x, k) :: l).lookup x = some k := by
  simp [List.lookup]

omit [DecidableEq Pw] [Inhabited K] in
/-- An input with a value in the simulator's tables keeps it after a sampled value is added. -/
theorem inDom_cons {c : SimCore S W Pw K} {p : List (Inp W × K)} {x e : Inp W} {k : K}
    (h : InDom (c, p) e) : InDom ({ c with h2 := (x, k) :: c.h2 }, p) e := by
  unfold InDom simLk at h ⊢
  cases hp : p.lookup e with
  | some v => simp
  | none =>
    simp only [hp] at h ⊢
    by_cases hx : e = x
    · subst hx
      simp
    · rwa [lookup_cons_ne hx]

omit [DecidableEq Pw] [Inhabited K] in
/-- **A fresh sampled value of `H2` keeps the invariant**: the value `k` at an input `x` without
a value in either world is added to the simulator's and the real table. -/
theorem GoodM.insertH2 {td : Pw → Sˣ} {M : PartyId → W} {c : SimCore S W Pw K}
    {p : List (Inp W × K)} {t : St Pw K} {rs : RSt S W Pw K}
    (hG : GoodM G td M (((c, p), t), rs)) {x : Inp W} (k : K) (hp : p.lookup x = none)
    (hc : c.h2.lookup x = none) (hr : rs.h2.lookup x = none)
    (hdm : ¬ DMst G td ({ c with h2 := (x, k) :: c.h2 }, p))
    (huq : ¬ UQst G td ({ c with h2 := (x, k) :: c.h2 }, p))
    (hps : ¬ PSst G td (({ c with h2 := (x, k) :: c.h2 }, p), t)) :
    GoodM G td M ((({ c with h2 := (x, k) :: c.h2 }, p), t),
      { rs with h2 := (x, k) :: rs.h2 }) := by
  have hlk : ∀ y, y ≠ x → simLk ({ c with h2 := (x, k) :: c.h2 }, p) y = simLk (c, p) y := by
    intro y hy
    simp only [simLk, lookup_cons_ne hy]
  have hrl : ∀ y, y ≠ x → ((x, k) :: rs.h2).lookup y = rs.h2.lookup y :=
    fun y hy => lookup_cons_ne hy
  have hhin : hin G td { rs with h2 := (x, k) :: rs.h2 } = hin G td rs := rfl
  refine ⟨hG.st, hG.info, hG.zs, hG.act, hG.fresh, hG.reg, hG.keyed, hG.keyAt, ?_, hG.pend, ?_,
    hG.prog, ?_, ?_, hdm, huq, hps, ?_⟩
  · -- key
    intro q rc kq hrc hk
    obtain ⟨hx, h1, h2, h3, h4, h5⟩ := hG.key q rc kq hrc hk
    have hne : hx ≠ x := fun h => by rw [h, hr] at h2; simp at h2
    exact ⟨hx, h1, by rw [hrl hx hne]; exact h2, by rw [hlk hx hne]; exact h3, h4, h5⟩
  · -- tab
    intro y
    by_cases hy : y = x
    · subst hy
      left
      simp only [simLk, hp, lookup_cons_self]
    · rw [hrl y hy, hlk y hy]
      exact hG.tab y
  · -- disj
    intro y
    by_cases hy : y = x
    · subst hy
      exact Or.inl hp
    · rcases hG.disj y with h | h
      · exact Or.inl h
      · right
        simpa only [lookup_cons_ne hy] using h
  · -- nodup
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact lookup_cons_self
    · have h0 := hG.nodup e he
      have hne : e.1 ≠ x := fun h => by rw [h, hc] at h0; simp at h0
      simpa only [lookup_cons_ne hne] using h0
  · -- wit
    intro q rc hx hrc hk hcomp hpend hh hl
    have hne : hx ≠ x := by
      intro h
      subst h
      simp only [simLk, hp, lookup_cons_self, reduceCtorEq] at hl
    rw [hlk hx hne] at hl
    obtain ⟨e, pw₁, h1, h2, h3, h4⟩ := hG.wit q rc hx hrc hk hcomp hpend hh hl
    exact ⟨e, pw₁, inDom_cons h1, h2, h3, h4⟩

omit [DecidableEq Pw] [Inhabited K] in
/-- Without a late-test target, neither party of the session `0` has a late test at `x`. -/
theorem lateAt_of_lateTarget {td : Pw → Sˣ} {c : SimCore S W Pw K} {x : Inp W}
    (h : lateTarget G td c x = none) {q : PartyId} (hq : q ≤ 1) : lateAt G td c x q = none := by
  unfold lateTarget at h
  cases h0 : lateAt G td c x 0 with
  | some pw => simp [h0] at h
  | none =>
    rw [h0] at h
    interval_cases q
    · exact h0
    · simpa using h

omit [DecidableEq Pw] [Inhabited K] in
/-- A registered transcript with a candidate password that matches has a late test. -/
theorem lateAt_isSome {td : Pw → Sˣ} {c : SimCore S W Pw K} {x : Inp W} {q : PartyId}
    {T : Role × W × W} (hT : c.pend q = some T) (htr : x.tr = T) {pw : Pw}
    (hm : Matches G td c q pw x) (hc : pw ∈ c.cands) : (lateAt G td c x q).isSome := by
  obtain ⟨z, peer, role, hz, -, -, hmt⟩ := hm
  unfold lateAt
  rw [hT, hz]
  simp only [htr, ite_true, extractAt, DHExtractKit.extract]
  rw [List.find?_isSome]
  exact ⟨pw, hc, hmt⟩

omit [DecidableEq Pw] [Inhabited K] in
/-- **A fresh query at a keyed party's honest input is bad**: the honest input of a keyed party
that has no value in the simulator's tables and triggers no late test matches an unqueried
password, is a passive-session query, or forms a double match. -/
theorem GoodM.bad_fresh {td : Pw → Sˣ} {M : PartyId → W} {c : SimCore S W Pw K}
    {p : List (Inp W × K)} {t : St Pw K} {rs : RSt S W Pw K}
    (hG : GoodM G td M (((c, p), t), rs)) {x : Inp W} (hl : simLk (c, p) x = none)
    (hlt : lateTarget G td c x = none) {q : PartyId} (hq : (keyOf t (0, q)).isSome)
    (hx : hin G td rs q (M q) = some x) (k : K) :
    DMst G td ({ c with h2 := (x, k) :: c.h2 }, p) ∨
      UQst G td ({ c with h2 := (x, k) :: c.h2 }, p) ∨
        PSst G td (({ c with h2 := (x, k) :: c.h2 }, p), t) := by
  obtain ⟨rc, hr⟩ : ∃ rc, t.recs (0, q) = some rc := by
    unfold keyOf at hq
    cases h0 : t.recs (0, q) with
    | none => simp [h0] at hq
    | some rc => exact ⟨rc, rfl⟩
  obtain ⟨kq, hkq⟩ : ∃ kq, rc.key = some kq := by
    unfold keyOf at hq
    rw [hr] at hq
    cases h0 : rc.key with
    | none => simp [h0] at hq
    | some kq => exact ⟨kq, rfl⟩
  obtain ⟨hx0, h1, -, -, hM, hiff⟩ := hG.key q rc kq hr hkq
  rw [hx] at h1
  obtain rfl := Option.some.inj h1
  have hmatch : Matches G td c q rc.pw x := hG.hin_matches G hx hM hr
  have hpx : p.lookup x = none := by
    unfold simLk at hl
    cases h0 : p.lookup x with
    | none => rfl
    | some v => simp [h0] at hl
  have hdom : InDom ({ c with h2 := (x, k) :: c.h2 }, p) x := by
    simp [InDom, simLk, hpx]
  obtain ⟨z, rc', hz, hr', -, hxe⟩ := hG.hin_eq G hx
  rw [hr] at hr'
  cases hr'
  by_cases hcand : rc.pw ∈ c.cands
  · by_cases hcomp : rc.status = .completed
    · right; right
      obtain ⟨z', hz', hpz⟩ : ∃ z', c.zs (1 - q) = some z' ∧ G.pub z' = M q := by
        have := hiff.mp hcomp
        simp only at this
        cases h0 : c.zs (1 - q) with
        | none => simp [h0] at this
        | some z' => exact ⟨z', rfl, by simpa [h0] using this⟩
      refine ⟨q, x, z', rc, hdom, hz', ?_, hr, hmatch⟩
      rw [hxe, peerMsg_h2Inp, hpz]
    · by_cases hpend : c.pend q = none
      · left
        obtain ⟨e, pw₁, h1, h2, h3, h4⟩ :=
          hG.wit q rc x hr (by simp [hkq]) hcomp hpend hx hl
        exact ⟨q, e, x, pw₁, rc.pw, inDom_cons h1, hdom, h2, h3, h4, hmatch⟩
      · exfalso
        obtain ⟨T, hT⟩ : ∃ T, c.pend q = some T := Option.ne_none_iff_exists'.mp hpend
        obtain ⟨r', hxp, hr'', -, -, h3, h4⟩ := hG.pend q T hT
        rw [hx] at h3
        obtain rfl := Option.some.inj h3
        have hq1 : q ≤ 1 := by
          unfold hin at hx
          cases hy : rs.ys q with
          | none => simp [hy] at hx
          | some y => exact (hG.act q y hy).1
        have h5 := lateAt_isSome G hT h4 hmatch hcand
        rw [lateAt_of_lateTarget G hlt hq1] at h5
        simp at h5
  · right; left
    exact ⟨q, x, rc.pw, hdom, hcand, hmatch⟩

omit [DecidableEq Pw] [Inhabited K] in
/-- **A late test keeps the invariant**: the party `q` with the registered transcript of `x` has
its late test spent, and `x` gets the value `k` in the simulator's programmed inputs and in the
real table (where it is the party's key at its honest input, or a fresh value at an input that
matches another password). -/
theorem GoodM.late {td : Pw → Sˣ} {M : PartyId → W} {c : SimCore S W Pw K}
    {p : List (Inp W × K)} {t : St Pw K} {rs : RSt S W Pw K}
    (hG : GoodM G td M (((c, p), t), rs)) {x : Inp W} (k : K) (hp : p.lookup x = none)
    (hc : c.h2.lookup x = none) {q : PartyId} {T : Role × W × W} (hT : c.pend q = some T)
    (htr : x.tr = T) {rc : Rec Pw K} (hr : t.recs (0, q) = some rc) (h2' : List (Inp W × K))
    (hreal : (h2' = rs.h2 ∧ rs.h2.lookup x = some k ∧ hin G td rs q (M q) = some x) ∨
      (h2' = (x, k) :: rs.h2 ∧ rs.h2.lookup x = none ∧
        ∃ pw₁, pw₁ ≠ rc.pw ∧ Matches G td c q pw₁ x))
    (hdm : ¬ DMst G td ({ c with pend := Function.update c.pend q none }, (x, k) :: p))
    (huq : ¬ UQst G td ({ c with pend := Function.update c.pend q none }, (x, k) :: p))
    (hps : ¬ PSst G td (({ c with pend := Function.update c.pend q none }, (x, k) :: p),
      setRec t (0, q) { rc with registered := false })) :
    GoodM G td M ((({ c with pend := Function.update c.pend q none }, (x, k) :: p),
      setRec t (0, q) { rc with registered := false }), { rs with h2 := h2' }) := by
  have hst : rs.st = stripSt t := hG.st
  obtain ⟨rc₀, hx, hr₀, hkey, hreg, hhin, htrT⟩ := hG.pend q T hT
  rw [hr] at hr₀
  cases hr₀
  have hint : rc.status = .interrupted := hG.reg (0, q) rc hr hreg
  have hrecs : ∀ y, (setRec t (0, q) { rc with registered := false }).recs y =
      if y = (0, q) then some { rc with registered := false } else t.recs y := by
    intro y
    by_cases hy : y = (0, q)
    · subst hy
      simp [setRec]
    · simp [setRec, hy]
  have hbwd : ∀ y r, (setRec t (0, q) { rc with registered := false }).recs y = some r →
      ∃ r₀, t.recs y = some r₀ ∧ r.key = r₀.key ∧ r.status = r₀.status ∧ r.peer = r₀.peer ∧
        r.role = r₀.role ∧ r.pw = r₀.pw ∧ (r.registered = true → r₀.registered = true) := by
    intro y r hy
    rw [hrecs] at hy
    split_ifs at hy with h
    · subst h
      cases hy
      exact ⟨rc, hr, rfl, rfl, rfl, rfl, rfl, by simp⟩
    · exact ⟨r, hy, rfl, rfl, rfl, rfl, rfl, id⟩
  have hfwd : ∀ y r₀, t.recs y = some r₀ → ∃ r,
      (setRec t (0, q) { rc with registered := false }).recs y = some r ∧ r.key = r₀.key ∧
        r.status = r₀.status ∧ r.peer = r₀.peer ∧ r.role = r₀.role ∧ r.pw = r₀.pw := by
    intro y r₀ hy
    rw [hrecs]
    split_ifs with h
    · subst h
      rw [hr] at hy
      cases hy
      exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨r₀, hy, rfl, rfl, rfl, rfl, rfl⟩
  have hmap : ∀ {α : Type} (y : Inst) (g : Rec Pw K → α),
      (∀ r : Rec Pw K, g { r with registered := false } = g r) →
      ((setRec t (0, q) { rc with registered := false }).recs y).map g = (t.recs y).map g := by
    intro α y g hg
    rw [hrecs]
    split_ifs with h
    · subst h
      simp [hr, hg]
    · rfl
  have hstrip : stripSt (setRec t (0, q) { rc with registered := false }) = stripSt t := by
    unfold stripSt
    congr 1
    funext y
    exact hmap y strip (fun _ => rfl)
  have hkeyOf : ∀ y, keyOf (setRec t (0, q) { rc with registered := false }) y = keyOf t y := by
    intro y
    unfold keyOf
    rw [hrecs]
    split_ifs with h
    · subst h
      simp [hr]
    · rfl
  have hlk : ∀ y, simLk ({ c with pend := Function.update c.pend q none }, (x, k) :: p) y =
      if y = x then some k else simLk (c, p) y := by
    intro y
    split_ifs with h
    · subst h
      simp [simLk]
    · simp only [simLk, lookup_cons_ne h]
  have hrl : ∀ y, y ≠ x →
      (({ rs with h2 := h2' } : RSt S W Pw K).h2).lookup y = rs.h2.lookup y := by
    intro y hy
    rcases hreal with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rfl
    · exact lookup_cons_ne hy
  have hrlx : (({ rs with h2 := h2' } : RSt S W Pw K).h2).lookup x = some k := by
    rcases hreal with ⟨rfl, h, -⟩ | ⟨rfl, -⟩
    · exact h
    · exact lookup_cons_self
  refine ⟨by rw [hstrip]; exact hst, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hG.nodup,
    hdm, huq, hps, ?_⟩
  · -- info
    intro pid
    rw [hmap _ _ (fun _ => rfl)]
    exact hG.info pid
  · -- zs
    intro pid
    rw [hG.zs pid]
    congr 1
    funext y
    exact (hmap _ _ (fun _ => rfl)).symm
  · -- act
    intro pid y hy
    obtain ⟨h1, r₀, h2, h3⟩ := hG.act pid y hy
    obtain ⟨r, h4, -, -, h5, -⟩ := hfwd _ r₀ h2
    exact ⟨h1, r, h4, h5.trans h3⟩
  · -- fresh
    intro y r hy hk
    obtain ⟨r₀, h1, h2, h3, -, -, -, h4⟩ := hbwd y r hy
    obtain ⟨h5, h6, h7⟩ := hG.fresh y r₀ h1 (h2 ▸ hk)
    refine ⟨h3.trans h5, ?_, ?_⟩
    · rw [hrecs] at hy
      split_ifs at hy with h
      · cases hy
        grind
      · rw [hy] at h1
        cases h1
        exact h6
    · cases hb : r.registered
      · rfl
      · rw [h4 hb] at h7
        exact h7
  · -- reg
    intro y r hy hk
    obtain ⟨r₀, h1, -, h3, -, -, -, h4⟩ := hbwd y r hy
    rw [h3]
    exact hG.reg y r₀ h1 (h4 hk)
  · -- keyed
    intro pid
    rw [hkeyOf]
    exact hG.keyed pid
  · -- keyAt
    intro y r hy hk
    obtain ⟨r₀, h1, h2, -⟩ := hbwd y r hy
    exact hG.keyAt y r₀ h1 (h2 ▸ hk)
  · -- key
    intro pid r k₀ hy hk
    obtain ⟨r₀, h1, h2, h3, -⟩ := hbwd _ r hy
    obtain ⟨hx₀, e1, e2, e3, e4, e5⟩ := hG.key pid r₀ k₀ h1 (h2 ▸ hk)
    refine ⟨hx₀, e1, ?_, ?_, e4, by rw [h3]; exact e5⟩
    · by_cases hxx : hx₀ = x
      · subst hxx
        rw [hrlx]
        rcases hreal with ⟨-, h, -⟩ | ⟨-, h, -⟩
        · rw [h] at e2
          exact e2
        · rw [h] at e2
          simp at e2
      · rw [hrl _ hxx]
        exact e2
    · rw [hlk]
      split_ifs with hxx
      · subst hxx
        right
        rcases hreal with ⟨-, h, -⟩ | ⟨-, h, -⟩
        · rw [h] at e2
          exact e2
        · rw [h] at e2
          simp at e2
      · exact e3
  · -- pend
    intro pid T' hT'
    have hpq : pid ≠ q := by
      intro h
      subst h
      simp at hT'
    simp only [Function.update_of_ne hpq] at hT'
    obtain ⟨r₀, hx₀, h1, h2, h3, h4, h5⟩ := hG.pend pid T' hT'
    have hne : (0, pid) ≠ (0, q) := fun h => hpq (Prod.mk.inj h).2
    refine ⟨r₀, hx₀, ?_, h2, h3, h4, h5⟩
    rw [hrecs, ite_eq_right hne, h1]
  · -- tab
    intro y
    by_cases hxx : y = x
    · subst hxx
      left
      rw [hrlx, hlk, ite_eq_left rfl]
    · rw [hrl _ hxx, hlk, ite_eq_right hxx]
      rcases hG.tab y with h | ⟨q', h1, h2⟩
      · exact Or.inl h
      · refine Or.inr ⟨q', ?_, h2⟩
        dsimp only
        rw [hkeyOf]
        exact h1
  · -- prog
    intro y k' hy
    by_cases hxx : y = x
    · subst hxx
      obtain ⟨r, h1, h2, h3, -⟩ := hfwd _ rc hr
      exact ⟨q, r, hx, h1, by rw [h2]; exact hkey, by rw [h3]; exact hint, hhin,
        by rw [htrT, htr]⟩
    · rw [lookup_cons_ne hxx] at hy
      obtain ⟨pid, r₀, hx₀, h1, h2, h3, h4, h5⟩ := hG.prog y k' hy
      obtain ⟨r, h6, h7, h8, -⟩ := hfwd _ r₀ h1
      exact ⟨pid, r, hx₀, h6, by rw [h7]; exact h2, by rw [h8]; exact h3, h4, h5⟩
  · -- disj
    intro y
    by_cases hxx : y = x
    · subst hxx
      exact Or.inr hc
    · rw [lookup_cons_ne hxx]
      exact hG.disj y
  · -- wit
    intro pid r hx₀ hy hk hcomp hpend hh hl
    rw [hlk] at hl
    split_ifs at hl with hxx
    obtain ⟨r₀, h1, h2, h3, -, -, h6, -⟩ := hbwd _ r hy
    by_cases hpq : pid = q
    · subst hpq
      rw [hr] at h1
      cases h1
      have hh' : hin G td rs pid (M pid) = some hx₀ := hh
      have hhin' : hin G td rs pid (M pid) = some hx := hhin
      rw [hhin'] at hh'
      cases hh'
      rcases hreal with ⟨-, -, h⟩ | ⟨-, -, pw₁, hne, hm⟩
      · rw [hhin'] at h
        exact absurd (Option.some.inj h) hxx
      · refine ⟨x, pw₁, ?_, by rw [htr, htrT], by rw [h6]; exact hne, hm⟩
        simp [InDom, simLk]
    · simp only [Function.update_of_ne hpq] at hpend
      obtain ⟨e, pw₁, e1, e2, e3, e4⟩ :=
        hG.wit pid r₀ hx₀ h1 (h2 ▸ hk) (h3 ▸ hcomp) hpend hh hl
      refine ⟨e, pw₁, ?_, e2, by rw [h6]; exact e3, e4⟩
      unfold InDom at e1 ⊢
      rw [hlk]
      split_ifs <;> simp_all

omit [DecidableEq Pw] [Inhabited K] in
/-- A match found by the simulator is an entry of its table with the transcript that extracts
the password. -/
theorem findMatch_some {td : Pw → Sˣ} {c : SimCore S W Pw K} {z : S} {pid : PartyId}
    {T : Role × W × W} {pw : Pw} {k : K} (h : findMatch G td c z pid T = some (pw, k)) :
    ∃ e ∈ c.h2, e.1.tr = T ∧ extractAt G td c.cands z pid e.1 = some pw ∧ e.2 = k := by
  unfold findMatch at h
  obtain ⟨e, he, hfe⟩ := List.exists_of_findSome?_eq_some h
  refine ⟨e, he, ?_⟩
  split_ifs at hfe with htr
  cases hex : extractAt G td c.cands z pid e.1 with
  | none => simp [hex] at hfe
  | some pw' =>
    simp only [hex, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hfe
    exact ⟨htr, by rw [hfe.1], hfe.2⟩

omit [DecidableEq Pw] [Inhabited K] in
/-- Without a match, no entry of the simulator's table with the transcript extracts a
password. -/
theorem findMatch_none {td : Pw → Sˣ} {c : SimCore S W Pw K} {z : S} {pid : PartyId}
    {T : Role × W × W} (h : findMatch G td c z pid T = none) :
    ∀ e ∈ c.h2, e.1.tr = T → extractAt G td c.cands z pid e.1 = none := by
  unfold findMatch at h
  intro e he htr
  have := List.findSome?_eq_none_iff.mp h e he
  simp only [htr, ite_true, Option.map_eq_none_iff] at this
  exact this

omit [DecidableEq Pw] [Inhabited K] in
/-- An extraction finds a candidate that matches. -/
theorem extractAt_isSome {td : Pw → Sˣ} {c : SimCore S W Pw K} {pid : PartyId} {pw : Pw}
    {x : Inp W} (hm : Matches G td c pid pw x) (hc : pw ∈ c.cands) {z : S}
    (hz : c.zs pid = some z) : (extractAt G td c.cands z pid x).isSome := by
  obtain ⟨z', -, -, hz', -, -, hmt⟩ := hm
  rw [hz] at hz'
  cases hz'
  unfold extractAt DHExtractKit.extract
  rw [List.find?_isSome]
  exact ⟨pw, hc, hmt⟩

omit [DecidableEq Pw] [Inhabited K] in
/-- An extracted password matches, for an input with the party's transcript. -/
theorem matches_of_extractAt {td : Pw → Sˣ} {c : SimCore S W Pw K} {pid : PartyId} {pw : Pw}
    {x : Inp W} {z : S} (hz : c.zs pid = some z) {peer : PartyId} {role : Role}
    (hi : c.info pid = some (peer, role))
    (htr : x.tr = (h2Inp pid role (G.pub z) (peerMsg pid x) (peerMsg pid x)).tr)
    (h : extractAt G td c.cands z pid x = some pw) : Matches G td c pid pw x :=
  ⟨z, peer, role, hz, hi, htr, List.find?_some h⟩

omit [DecidableEq Pw] [Inhabited K] in
/-- **A key delivery keeps the invariant**: the party `pid` with secret `z`, no key and the
received message `m ≠ 1` gets the record `rc'` with the key `K` in `F_lePAKE` and in the real
world, where `K` is the value of its honest input `hx` in the real table, either recorded or
fresh; a registered test records the transcript of `hx`. -/
theorem GoodM.send {td : Pw → Sˣ} {M : PartyId → W} {c : SimCore S W Pw K}
    {p : List (Inp W × K)} {t : St Pw K} {rs : RSt S W Pw K}
    (hG : GoodM G td M (((c, p), t), rs)) {pid : PartyId} {m : W} {rc : Rec Pw K}
    (hr : t.recs (0, pid) = some rc) (hkey0 : rc.key = none) (hm : m ≠ G.pub 0) {hx : Inp W}
    (hhx : hin G td rs pid m = some hx) (k : K) (rc' : Rec Pw K)
    (hrc : rc'.peer = rc.peer ∧ rc'.role = rc.role ∧ rc'.pw = rc.pw ∧ rc'.key = some k)
    (hst' : rc'.registered = true → rc'.status = .interrupted)
    (hcomp : rc'.status = .completed ↔ (c.zs (1 - pid)).map G.pub = some m)
    (pend' : PartyId → Option (Role × W × W))
    (hpend : (pend' = c.pend ∧ rc'.registered = false) ∨
      (pend' = Function.update c.pend pid (some hx.tr) ∧ rc'.registered = true))
    (h2' : List (Inp W × K))
    (hreal : (h2' = rs.h2 ∧ rs.h2.lookup hx = some k ∧
        (simLk (c, p) hx = none ∨ simLk (c, p) hx = some k)) ∨
      (h2' = (hx, k) :: rs.h2 ∧ rs.h2.lookup hx = none ∧ simLk (c, p) hx = none))
    (hwit : rc'.status ≠ .completed → pend' pid = none → simLk (c, p) hx = none →
      ∃ e pw₁, InDom (c, p) e ∧ e.tr = hx.tr ∧ pw₁ ≠ rc.pw ∧ Matches G td c pid pw₁ e) :
    GoodM G td (Function.update M pid m)
      ((({ c with keyed := Function.update c.keyed pid true, pend := pend' }, p),
        setRec t (0, pid) rc'), { rs with st := stripSt (setRec t (0, pid) rc'), h2 := h2' }) := by
  have hst : rs.st = stripSt t := hG.st
  have hrecs : ∀ y, (setRec t (0, pid) rc').recs y =
      if y = (0, pid) then some rc' else t.recs y := by
    intro y
    by_cases hy : y = (0, pid)
    · subst hy
      simp [setRec]
    · simp [setRec, hy]
  have hhin : hin G td { rs with st := stripSt (setRec t (0, pid) rc'), h2 := h2' } =
      hin G td rs := by
    funext q m'
    unfold hin
    simp only [hst, stripSt, hrecs]
    split_ifs with h
    · rw [h, hr]
      simp only [Option.map_some, strip, hrc.2.1, hrc.2.2.1]
      cases rs.ys q <;> rfl
    · rfl
  have hMq : ∀ q, q ≠ pid → Function.update M pid m q = M q :=
    fun q hq => Function.update_of_ne hq _ _
  have hkeyOf : ∀ q, q ≠ pid → keyOf (setRec t (0, pid) rc') (0, q) = keyOf t (0, q) := by
    intro q hq
    unfold keyOf
    rw [hrecs, ite_eq_right (fun h => hq (Prod.mk.inj h).2)]
  have hkeyOfp : keyOf (setRec t (0, pid) rc') (0, pid) = some k := by
    unfold keyOf
    rw [hrecs, ite_eq_left rfl]
    simp [hrc.2.2.2]
  have hkeyOf0 : keyOf t (0, pid) = none := by
    simp [keyOf, hr, hkey0]
  have hmap : ∀ {α : Type} (y : Inst) (g : Rec Pw K → α),
      (∀ r r' : Rec Pw K, r.peer = r'.peer → r.role = r'.role → r.pw = r'.pw → g r = g r') →
      ((setRec t (0, pid) rc').recs y).map g = (t.recs y).map g := by
    intro α y g hg
    rw [hrecs]
    split_ifs with h
    · subst h
      simp [hr, hg rc' rc hrc.1 hrc.2.1 hrc.2.2.1]
    · rfl
  have hlk2 : ∀ y, y ≠ hx → (h2' : List (Inp W × K)).lookup y = rs.h2.lookup y := by
    intro y hy
    rcases hreal with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rfl
    · exact lookup_cons_ne hy
  have hlkx : (h2' : List (Inp W × K)).lookup hx = some k := by
    rcases hreal with ⟨rfl, h, -⟩ | ⟨rfl, -⟩
    · exact h
    · exact lookup_cons_self
  have hslk : simLk ({ c with keyed := Function.update c.keyed pid true, pend := pend' }, p) =
      simLk (c, p) := rfl
  have hma : Matches G td { c with keyed := Function.update c.keyed pid true, pend := pend' } =
      Matches G td c := rfl
  have hold : ∀ q r, q ≠ pid → (setRec t (0, pid) rc').recs (0, q) = some r →
      t.recs (0, q) = some r := by
    intro q r hq hy
    rwa [hrecs, ite_eq_right (fun h => hq (Prod.mk.inj h).2)] at hy
  have hnew : ∀ r, (setRec t (0, pid) rc').recs (0, pid) = some r → r = rc' := by
    intro r hy
    rw [hrecs, ite_eq_left rfl] at hy
    exact (Option.some.inj hy).symm
  have hpq : ∀ q r, t.recs (0, q) = some r → r.key.isSome → q ≠ pid := by
    intro q r h1 h2 h
    subst h
    rw [hr] at h1
    cases h1
    simp [hkey0] at h2
  have hpend' : ∀ q, q ≠ pid → pend' q = c.pend q := by
    intro q hq
    rcases hpend with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rfl
    · exact Function.update_of_ne hq _ _
  have hhx' : hin G td { rs with st := stripSt (setRec t (0, pid) rc'), h2 := h2' } pid
      (Function.update M pid m pid) = some hx := by
    rw [hhin, Function.update_self]
    exact hhx
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hG.disj, hG.nodup, hG.dm, hG.uq,
    ?_, ?_⟩
  · -- info
    intro q
    rw [hmap _ _ (fun r r' h1 h2 _ => by rw [h1, h2])]
    exact hG.info q
  · -- zs
    intro q
    rw [hG.zs q]
    congr 1
    funext y
    exact (hmap _ _ (fun r r' _ _ h3 => by rw [h3])).symm
  · -- act
    intro q y hy
    obtain ⟨h1, r₀, h2, h3⟩ := hG.act q y hy
    by_cases hq : q = pid
    · subst hq
      rw [hr] at h2
      cases h2
      exact ⟨h1, rc', by rw [hrecs, ite_eq_left rfl], by rw [hrc.1]; exact h3⟩
    · exact ⟨h1, r₀, by rw [hrecs, ite_eq_right (fun h => hq (Prod.mk.inj h).2), h2], h3⟩
  · -- fresh
    intro y r hy hk
    rw [hrecs] at hy
    split_ifs at hy with h
    · cases hy
      rw [hrc.2.2.2] at hk
      simp at hk
    · exact hG.fresh y r hy hk
  · -- reg
    intro y r hy hk
    rw [hrecs] at hy
    split_ifs at hy with h
    · cases hy
      exact hst' hk
    · exact hG.reg y r hy hk
  · -- keyed
    intro q
    by_cases hq : q = pid
    · subst hq
      simp [Function.update_self, hkeyOfp]
    · simp only [Function.update_of_ne hq]
      rw [hkeyOf q hq]
      exact hG.keyed q
  · -- keyAt
    intro y r hy hk
    rw [hrecs] at hy
    split_ifs at hy with h
    · rw [h]
    · exact hG.keyAt y r hy hk
  · -- key
    intro q r k₀ hy hk
    by_cases hq : q = pid
    · subst hq
      obtain rfl := hnew r hy
      rw [hrc.2.2.2] at hk
      cases hk
      refine ⟨hx, hhx', hlkx, ?_, by rw [Function.update_self]; exact hm, ?_⟩
      · rcases hreal with ⟨-, -, h⟩ | ⟨-, -, h⟩
        · exact h
        · exact Or.inl h
      · rw [Function.update_self]
        exact hcomp
    · have hy' := hold q r hq hy
      obtain ⟨hq', e1, e2, e3, e4, e5⟩ := hG.key q r k₀ hy' hk
      refine ⟨hq', by rw [hhin, hMq q hq]; exact e1, ?_, e3, by rw [hMq q hq]; exact e4,
        by rw [hMq q hq]; exact e5⟩
      by_cases hxx : hq' = hx
      · subst hxx
        rcases hreal with ⟨rfl, -⟩ | ⟨-, hn, -⟩
        · exact e2
        · rw [hn] at e2
          simp at e2
      · rw [hlk2 _ hxx]
        exact e2
  · -- pend
    intro q T hT
    by_cases hq : q = pid
    · subst hq
      rcases hpend with ⟨rfl, -⟩ | ⟨rfl, hreg'⟩
      · obtain ⟨r, -, h1, h2, -⟩ := hG.pend q T hT
        exact absurd rfl (hpq q r h1 h2)
      · simp only [Function.update_self, Option.some.injEq] at hT
        subst hT
        exact ⟨rc', hx, by rw [hrecs, ite_eq_left rfl], by simp [hrc.2.2.2], hreg', hhx', rfl⟩
    · dsimp only at hT
      rw [hpend' q hq] at hT
      obtain ⟨r, hq', h1, h2, h3, h4, h5⟩ := hG.pend q T hT
      exact ⟨r, hq', by rw [hrecs, ite_eq_right (fun h => hq (Prod.mk.inj h).2), h1], h2, h3,
        by rw [hhin, hMq q hq]; exact h4, h5⟩
  · -- tab
    intro y
    by_cases hy : y = hx
    · subst hy
      right
      exact ⟨pid, by dsimp only; rw [hkeyOfp]; rfl, hhx'⟩
    · rw [hlk2 y hy]
      rcases hG.tab y with h | ⟨q, hq, hh⟩
      · exact Or.inl h
      · have hne : q ≠ pid := by
          intro h
          subst h
          rw [hkeyOf0] at hq
          simp at hq
        right
        exact ⟨q, by dsimp only; rw [hkeyOf q hne]; exact hq, by rw [hhin, hMq q hne]; exact hh⟩
  · -- prog
    intro y k' hy
    obtain ⟨q, r, hq', h1, h2, h3, h4, h5⟩ := hG.prog y k' hy
    have hne := hpq q r h1 h2
    exact ⟨q, r, hq', by rw [hrecs, ite_eq_right (fun h => hne (Prod.mk.inj h).2), h1], h2, h3,
      by rw [hhin, hMq q hne]; exact h4, h5⟩
  · -- ps
    rintro ⟨q, x, z', r, h1, h2, h3, h4, h5⟩
    apply hG.ps
    by_cases hq : q = pid
    · subst hq
      obtain rfl := hnew r h4
      exact ⟨q, x, z', rc, h1, h2, h3, hr, by rw [← hrc.2.2.1]; exact h5⟩
    · exact ⟨q, x, z', r, h1, h2, h3, hold q r hq h4, h5⟩
  · -- wit
    intro q r hx₀ hy hk hc hpe hh hl
    by_cases hq : q = pid
    · subst hq
      obtain rfl := hnew r hy
      rw [hhx'] at hh
      obtain rfl := Option.some.inj hh
      obtain ⟨e, pw₁, e1, e2, e3, e4⟩ := hwit hc hpe hl
      exact ⟨e, pw₁, e1, e2, by rw [hrc.2.2.1]; exact e3, e4⟩
    · dsimp only at hpe hh
      rw [hpend' q hq] at hpe
      rw [hhin, hMq q hq] at hh
      obtain ⟨e, pw₁, e1, e2, e3, e4⟩ := hG.wit q r hx₀ (hold q r hq hy) hk hc hpe hh hl
      exact ⟨e, pw₁, e1, e2, e3, e4⟩

/-- `newSession` gives equal outputs, and keeps the invariant unless the step is bad. -/
theorem step_newSession (td : Pw → Sˣ) (M : PartyId → W) (s : JS S W Pw K)
    (hG : GoodM G td M s) (r : (S × K) × K × K) (sid pid peer : PartyId) (role : Role) (pw : Pw) :
    Bad G td s (jointD G td s (.inl (.newSession sid pid peer role pw)) r).2 ∨
      ((jointD G td s (.inl (.newSession sid pid peer role pw)) r).1.1 =
          (jointD G td s (.inl (.newSession sid pid peer role pw)) r).1.2 ∧
        GoodM G td M (jointD G td s (.inl (.newSession sid pid peer role pw)) r).2) := by
  obtain ⟨⟨⟨c, p⟩, t⟩, rs⟩ := s
  have hst : rs.st = stripSt t := hG.st
  have hrs : (rs.st.recs (sid, pid)).isNone = (t.recs (sid, pid)).isNone := by
    simp [hst, stripSt]
  cases hn : t.recs (sid, pid) with
  | some rr =>
    have hinfo : sid = 0 ∧ pid ≤ 1 → c.info pid ≠ none := by
      rintro ⟨rfl, hp⟩
      rw [hG.info pid, ite_eq_left hp, hn]
      simp
    have hadd : addSession t (sid, pid) peer role pw = t := by simp [addSession, hn]
    have haddr : addSession rs.st (sid, pid) peer role pw = rs.st := by
      simp [addSession, hst, stripSt, hn]
    have hj : jointD G td (((c, p), t), rs) (.inl (.newSession sid pid peer role pw)) r =
        ((.inl .ok, .inl .ok), ((({ c with td := some td, phase := .rest }, p), t), rs)) := by
      simp only [jointD, simWorldD, simStartD, simCoreD, honStepD, honPub, drive1D, realDet,
        fStepD, leHonStep, simResumeV, simAnswer, convert, setTd, cpl, cplScale, honCoreD, hadd,
        haddr, hrs, hn]
      have hc : ¬ (sid = 0 ∧ pid ≤ 1 ∧ c.info pid = none) := fun h => hinfo ⟨h.1, h.2.1⟩ h.2.2
      simp only [hc, Option.isNone_some, Bool.false_eq_true, false_and, ite_false]
    rw [hj]
    exact Or.inr ⟨rfl, GoodM.phase G hG _ _⟩
  | none =>
    have hinfo : sid = 0 ∧ pid ≤ 1 → c.info pid = none := by
      rintro ⟨rfl, hp⟩
      rw [hG.info pid, ite_eq_left hp, hn]
      rfl
    have hAct : Active sid pid peer = true → sid = 0 ∧ pid ≤ 1 ∧ peer = 1 - pid := by
      intro hA
      simpa [Active] using hA
    let oy : Option S :=
      if Active sid pid peer = true then some (((td pw)⁻¹ : Sˣ) * r.1.1) else none
    have hj : jointD G td (((c, p), t), rs) (.inl (.newSession sid pid peer role pw)) r =
        ((.inl .ok, .inl .ok), ((({ newCore td c sid pid peer role pw oy with
          td := some td, phase := .rest }, p), addSession t (sid, pid) peer role pw),
          newRs rs (addSession t (sid, pid) peer role pw) pid oy)) := by
      simp only [jointD, simWorldD, simStartD, simCoreD, honStepD, honPub, drive1D, realDet,
        fStepD, leHonStep, simResumeV, simAnswer, convert, setTd, cpl, cplScale, honCoreD,
        hst, stripSt_addSession]
      by_cases hA : Active sid pid peer = true
      · obtain ⟨rfl, h1, -⟩ := hAct hA
        simp [hA, hinfo ⟨rfl, h1⟩, h1, oy, newCore, newRs, stripSt, hn]
      · by_cases h0 : sid = 0 ∧ pid ≤ 1
        · obtain ⟨rfl, h1⟩ := h0
          simp [hA, hinfo ⟨rfl, h1⟩, h1, oy, newCore, newRs]
        · have h0' : ¬ (sid = 0 ∧ pid ≤ 1 ∧ c.info pid = none) := fun h => h0 ⟨h.1, h.2.1⟩
          simp [hA, h0, h0', oy, newCore, newRs]
    rw [hj]
    by_cases hb : Bad G td (((c, p), t), rs) ((({ newCore td c sid pid peer role pw oy with
        td := some td, phase := .rest }, p), addSession t (sid, pid) peer role pw),
          newRs rs (addSession t (sid, pid) peer role pw) pid oy)
    · exact Or.inl hb
    refine Or.inr ⟨rfl, GoodM.phase G (GoodM.addSess G oy hG hn ?_ ?_ ?_ ?_ ?_) _ _⟩
    · intro h
      by_cases hA : Active sid pid peer = true
      · exact hAct hA
      · simp [oy, hA] at h
    · intro y hy hm
      refine hb (Or.inr (Or.inl ⟨pid, (td pw : S) * y, ?_, ?_, hm⟩))
      · have hz := hG.zs pid
        simp only at hz
        have hs : sid = 0 := by
          by_cases hA : Active sid pid peer = true
          · exact (hAct hA).1
          · simp [oy, hA] at hy
        rw [hz, ← hs, hn]
        cases rs.ys pid <;> rfl
      · simp [newCore, hy]
    · exact fun h => hb (Or.inr (Or.inr (Or.inl h)))
    · exact fun h => hb (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact fun h => hb (Or.inr (Or.inr (Or.inr (Or.inr h))))

omit [DecidableEq Pw] [Inhabited K] in
/-- A late-test target is a late test of a party of the session `0`. -/
theorem lateAt_of_lateTarget_some {td : Pw → Sˣ} {c : SimCore S W Pw K} {x : Inp W}
    {q : PartyId} {pw : Pw} (h : lateTarget G td c x = some (q, pw)) :
    lateAt G td c x q = some pw := by
  unfold lateTarget at h
  cases h0 : lateAt G td c x 0 with
  | some pw₀ =>
    rw [h0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact h0
  | none =>
    rw [h0] at h
    cases h1 : lateAt G td c x 1 with
    | none => simp [h1] at h
    | some pw₁ =>
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact h1

omit [DecidableEq Pw] [Inhabited K] in
/-- A party with an honest input is a party of the session `0`. -/
theorem GoodM.le_one_of_hin {td : Pw → Sˣ} {M : PartyId → W} {c : SimCore S W Pw K}
    {p : List (Inp W × K)} {t : St Pw K} {rs : RSt S W Pw K}
    (hG : GoodM G td M (((c, p), t), rs)) {q : PartyId} {m : W} {x : Inp W}
    (h : hin G td rs q m = some x) : q ≤ 1 := by
  unfold hin at h
  cases hy : rs.ys q with
  | none => simp [hy] at h
  | some y => exact (hG.act q y hy).1

omit [DecidableEq Pw] [Inhabited K] in
/-- **The other party's honest input on this party's transcript**: if the honest input of the
party `q'` has the transcript of the keyed party `q ≠ q'`, then `q` received the message of `q'`,
and its session is completed. -/
theorem GoodM.completed_of_tr {td : Pw → Sˣ} {M : PartyId → W} {c : SimCore S W Pw K}
    {p : List (Inp W × K)} {t : St Pw K} {rs : RSt S W Pw K}
    (hG : GoodM G td M (((c, p), t), rs)) {q q' : PartyId} (hne : q ≠ q') {x hx : Inp W}
    (hx' : hin G td rs q' (M q') = some x) (hhx : hin G td rs q (M q) = some hx)
    (htr : x.tr = hx.tr) {rc : Rec Pw K} (hr : t.recs (0, q) = some rc) {kq : K}
    (hk : rc.key = some kq) : rc.status = .completed := by
  have hq := hG.le_one_of_hin G hhx
  have hq' := hG.le_one_of_hin G hx'
  obtain ⟨-, h1, -, -, -, hiff⟩ := hG.key q rc kq hr hk
  obtain ⟨z', rc', hz', -, -, hxe'⟩ := hG.hin_eq G hx'
  obtain ⟨z, rc'', -, -, -, hxe⟩ := hG.hin_eq G hhx
  have h1q : 1 - q = q' := by grind
  simp only at hiff
  rw [hiff, h1q, hz']
  simp only [Option.map_some, Option.some.injEq]
  rw [hxe', hxe] at htr
  interval_cases q <;> interval_cases q' <;> simp_all [Inp.tr, h2Inp]

omit [DecidableEq Pw] [Inhabited K] in
/-- `lateTarget` does not read the table of `H1` of the core. -/
@[simp] theorem lateTarget_td (td : Pw → Sˣ) (c : SimCore S W Pw K) (o : Option (Pw → Sˣ))
    (x : Inp W) : lateTarget G td { c with td := o } x = lateTarget G td c x := rfl

/-- `h2` gives equal outputs, and keeps the invariant unless the step is bad. -/
theorem step_h2 (td : Pw → Sˣ) (M : PartyId → W) (s : JS S W Pw K)
    (hG : GoodM G td M s) (r : (S × K) × K × K) (x : Inp W) :
    Bad G td s (jointD G td s (.inr (.h2 x)) r).2 ∨
      ((jointD G td s (.inr (.h2 x)) r).1.1 = (jointD G td s (.inr (.h2 x)) r).1.2 ∧
        ∃ M', GoodM G td M' (jointD G td s (.inr (.h2 x)) r).2) := by
  obtain ⟨⟨⟨c, p⟩, t⟩, rs⟩ := s
  cases hp : p.lookup x with
  | some k =>
    have hrl : rs.h2.lookup x = some k := hG.lookup_of_simLk G (by simp [simLk, hp])
    right
    simp only [jointD, simWorldD, simStartD, drive1D, realDet, setTd, roDet, hp, hrl]
    exact ⟨trivial, M, GoodM.phase G hG _ _⟩
  | none =>
    cases hc : c.h2.lookup x with
    | some k =>
      have hrl : rs.h2.lookup x = some k := hG.lookup_of_simLk G (by simp [simLk, hp, hc])
      right
      simp only [jointD, simWorldD, simStartD, simCoreD, advCoreD, drive1D, realDet, setTd,
        roDet, hp, hc, hrl]
      exact ⟨trivial, M, GoodM.phase G hG _ _⟩
    | none =>
      cases hlt : lateTarget G td c x with
      | none =>
        have hj : jointD G td (((c, p), t), rs) (.inr (.h2 x)) r =
            ((.inr (.hash (roDet rs.h2 x r.1.2).1), .inr (.hash r.1.2)),
              ((({ c with td := some td, h2 := (x, r.1.2) :: c.h2, phase := .rest }, p), t),
                { rs with h2 := (roDet rs.h2 x r.1.2).2 })) := by
          simp only [jointD, simWorldD, simStartD, simCoreD, advCoreD, h2CoreD, drive1D,
            realDet, setTd, cpl, cplSlot, Slot.get, hp, hc, hlt]
          simp [hlt]
        rw [hj]
        cases hrl : rs.h2.lookup x with
        | none =>
          simp only [roDet, hrl]
          by_cases hb : DMst G td ({ c with h2 := (x, r.1.2) :: c.h2 }, p) ∨
              UQst G td ({ c with h2 := (x, r.1.2) :: c.h2 }, p) ∨
              PSst G td (({ c with h2 := (x, r.1.2) :: c.h2 }, p), t)
          · left
            exact Or.inr (Or.inr hb)
          · right
            push Not at hb
            exact ⟨trivial, M, GoodM.phase G (hG.insertH2 G r.1.2 hp hc hrl hb.1 hb.2.1 hb.2.2) _ _⟩
        | some kr =>
          left
          have hl : simLk (c, p) x = none := by simp [simLk, hp, hc]
          rcases hG.tab x with h | ⟨q, hq, hx⟩
          · rw [hrl, hl] at h
            simp at h
          · exact Or.inr (Or.inr (hG.bad_fresh G hl hlt hq hx r.1.2))
      | some qp =>
        obtain ⟨q, pw'⟩ := qp
        have hla := lateAt_of_lateTarget_some G hlt
        obtain ⟨T, hT, z, hz, htr, hex⟩ : ∃ T, c.pend q = some T ∧ ∃ z, c.zs q = some z ∧
            x.tr = T ∧ extractAt G td c.cands z q x = some pw' := by
          unfold lateAt at hla
          cases hT : c.pend q with
          | none => simp [hT] at hla
          | some T =>
            cases hz : c.zs q with
            | none => simp [hT, hz] at hla
            | some z =>
              simp only [hT, hz] at hla
              split_ifs at hla with h
              exact ⟨T, rfl, z, rfl, h, hla⟩
        obtain ⟨rc, hx, hr, hkey, hreg, hhin, htrT⟩ := hG.pend q T hT
        obtain ⟨kq, hkq⟩ : ∃ kq, rc.key = some kq := Option.isSome_iff_exists.mp hkey
        obtain ⟨hx1, h1, h2, h3, hM, hiff⟩ := hG.key q rc kq hr hkq
        rw [hhin] at h1
        obtain rfl := Option.some.inj h1
        obtain ⟨z₀, rc₀, hz₀, hr₀, hi₀, hxe⟩ := hG.hin_eq G hhin
        rw [hr] at hr₀
        cases hr₀
        rw [hz] at hz₀
        cases hz₀
        have hmx : Matches G td c q pw' x := by
          refine ⟨z, rc.peer, rc.role, hz, hi₀, ?_, ?_⟩
          · rw [htr, ← htrT, peerMsg_eq_of_tr (htr.trans htrT.symm), hxe, peerMsg_h2Inp]
            rfl
          · exact List.find?_some hex
        simp only at hr h2 h3 hiff hhin
        let v : K := if rc.pw = pw' then kq else r.2.1
        have hlr : lateReveal t (0, q) pw' r.2.1 = some v := by
          simp [lateReveal, hr, LateTestable, hkq, hreg, v]
        have hls : lateStep t (0, q) = setRec t (0, q) { rc with registered := false } := by
          simp [lateStep, hr, LateTestable, hkq, hreg]
        have hj : jointD G td (((c, p), t), rs) (.inr (.h2 x)) r =
            ((.inr (.hash (roDet rs.h2 x r.2.1).1), .inr (.hash v)),
              ((({ { c with pend := Function.update c.pend q none } with
                  td := some td, phase := .rest }, (x, v) :: p),
                setRec t (0, q) { rc with registered := false }),
                { rs with h2 := (roDet rs.h2 x r.2.1).2 })) := by
          simp only [jointD, simWorldD, simStartD, simCoreD, advCoreD, h2CoreD, drive1D,
            realDet, setTd, cpl, cplSlot, Slot.get, hp, hc, lateTarget_td, hlt, fStepD, leAdvD,
            simResumeV, simAnswer, revealVal, hlr, hls]
          simp
        rw [hj]
        by_cases hb : DMst G td ({ c with pend := Function.update c.pend q none }, (x, v) :: p) ∨
            UQst G td ({ c with pend := Function.update c.pend q none }, (x, v) :: p) ∨
            PSst G td (({ c with pend := Function.update c.pend q none }, (x, v) :: p),
              setRec t (0, q) { rc with registered := false })
        · exact Or.inl (Or.inr (Or.inr hb))
        push Not at hb
        have hdomx : InDom ({ c with pend := Function.update c.pend q none }, (x, v) :: p) x := by
          simp [InDom, simLk]
        by_cases heq : rc.pw = pw'
        · have hxx : x = hx :=
            hG.eq_hin_of_matches G hhin hr (heq ▸ hmx) (htr.trans htrT.symm)
          have h2x : rs.h2.lookup x = some kq := hxx ▸ h2
          have hv : v = kq := ite_eq_left heq
          right
          simp only [roDet, h2x]
          rw [hv]
          rw [hv] at hb
          exact ⟨rfl, M, GoodM.phase G
            (hG.late G kq hp hc hT htr hr rs.h2 (Or.inl ⟨rfl, h2x, by rw [hxx]; exact hhin⟩)
              hb.1 hb.2.1 hb.2.2) _ _⟩
        · have hv : v = r.2.1 := ite_eq_right heq
          cases hrl : rs.h2.lookup x with
          | none =>
            right
            simp only [roDet, hrl]
            rw [hv]
            rw [hv] at hb
            exact ⟨rfl, M, GoodM.phase G (hG.late G r.2.1 hp hc hT htr hr _
              (Or.inr ⟨rfl, hrl, pw', fun h => heq h.symm, hmx⟩) hb.1 hb.2.1 hb.2.2) _ _⟩
          | some kr =>
            exfalso
            rcases hG.tab x with h | ⟨q', hq', hx'⟩
            · simp [hrl, simLk, hp, hc] at h
            · by_cases hqq : q' = q
              · subst hqq
                rw [hhin] at hx'
                have hxx : hx = x := Option.some.inj hx'
                have hmr : Matches G td c q' rc.pw x := hxx ▸ hG.hin_matches G hhin hM hr
                exact hb.1 ⟨q', x, x, pw', rc.pw, hdomx, hdomx, rfl, fun h => heq h.symm, hmx,
                  hmr⟩
              · have hcomp := hG.completed_of_tr G (Ne.symm hqq) hx' hhin (htr.trans htrT.symm)
                  hr hkq
                have hint := hG.reg (0, q) rc hr hreg
                rw [hcomp] at hint
                exact absurd hint (by decide)

omit [DecidableEq Pw] [Inhabited K] in
/-- **Two parties' inputs on one transcript**: if the honest inputs of the parties `q ≠ q'` on the
messages `m` and `m'` have one transcript, then `m` is the message of `q'`. -/
theorem GoodM.cross_of_tr {td : Pw → Sˣ} {M : PartyId → W} {c : SimCore S W Pw K}
    {p : List (Inp W × K)} {t : St Pw K} {rs : RSt S W Pw K}
    (hG : GoodM G td M (((c, p), t), rs)) {q q' : PartyId} (hne : q ≠ q') {m m' : W}
    {x x' : Inp W} (hx : hin G td rs q m = some x) (hx' : hin G td rs q' m' = some x')
    (htr : x.tr = x'.tr) : (c.zs q').map G.pub = some m := by
  have hq := hG.le_one_of_hin G hx
  have hq' := hG.le_one_of_hin G hx'
  obtain ⟨z, rc, hz, -, -, hxe⟩ := hG.hin_eq G hx
  obtain ⟨z', rc', hz', -, -, hxe'⟩ := hG.hin_eq G hx'
  rw [hz']
  simp only [Option.map_some, Option.some.injEq]
  rw [hxe, hxe'] at htr
  interval_cases q <;> interval_cases q' <;> simp_all [Inp.tr, h2Inp]

/-- `z' · z / a = z · z' / b` iff `a = b`, for nonzero values. -/
theorem dh_eq_iff {z z' a b : S} (hz : z ≠ 0) (hz' : z' ≠ 0) :
    z' * (z * a⁻¹) = z * (z' * b⁻¹) ↔ a = b := by
  constructor
  · intro h
    have h' : z * z' * a⁻¹ = z * z' * b⁻¹ := by linear_combination h
    exact inv_injective (mul_left_cancel₀ (mul_ne_zero hz hz') h')
  · rintro rfl
    ring

omit [DecidableEq W] in
/-- **The two parties' inputs of a passive session coincide** iff their roles differ and their
generators have the same exponent. -/
theorem h2Inp_partner_iff {pid q : PartyId} (hp : pid ≤ 1) (hq : q ≤ 1) (hne : pid ≠ q)
    {r r' : Role} {z z' a b : S} (hz : z ≠ 0) (hz' : z' ≠ 0) :
    h2Inp pid r (G.pub z) (G.pub z') (G.exp (G.pub z') (z * a⁻¹)) =
        h2Inp q r' (G.pub z') (G.pub z) (G.exp (G.pub z) (z' * b⁻¹)) ↔ r ≠ r' ∧ a = b := by
  have hd := dh_eq_iff (a := a) (b := b) hz hz'
  interval_cases pid <;> interval_cases q <;> simp at hne <;>
    cases r <;> cases r' <;>
    simp [h2Inp, role0, otherRole, G.exp_pub, G.pub.injective.eq_iff, hd, eq_comm]

omit [DecidableEq Pw] [Inhabited K] in
/-- `findMatch` does not read the table of `H1` of the core. -/
@[simp] theorem findMatch_td (td : Pw → Sˣ) (c : SimCore S W Pw K) (o : Option (Pw → Sˣ))
    (z : S) (pid : PartyId) (T : Role × W × W) :
    findMatch G td { c with td := o } z pid T = findMatch G td c z pid T := rfl

/-- An entry found by a lookup is a member of the list. -/
theorem mem_of_lookup {α β : Type} [DecidableEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, l.lookup a = some b → (a, b) ∈ l
  | [], h => by simp at h
  | (a', b') :: l, h => by
    by_cases ha : a = a'
    · subst ha
      rw [lookup_cons_self] at h
      cases h
      exact List.mem_cons_self
    · rw [lookup_cons_ne ha] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)

omit [DecidableEq Pw] [Inhabited K] in
/-- Two records at one instance: the second one stays. -/
theorem setRec_setRec (t : St Pw K) (x : Inst) (r₁ r₂ : Rec Pw K) :
    setRec (setRec t x r₁) x r₂ = setRec t x r₂ := by
  simp [setRec]

omit [DecidableEq Pw] [Inhabited K] in
/-- A record with a key in the real world is the stripped record of `F_lePAKE` with the same
key. -/
theorem setRec_stripSt {t : St Pw K} {x : Inst} {rc : Rec Pw K} (rc' : Rec Pw K)
    (hrc : rc'.peer = rc.peer ∧ rc'.role = rc.role ∧ rc'.pw = rc.pw) :
    setRec (stripSt t) x { strip rc with key := rc'.key } = stripSt (setRec t x rc') := by
  unfold stripSt setRec
  congr 1
  funext y
  by_cases hy : y = x
  · subst hy
    simp [strip, hrc.1, hrc.2.1, hrc.2.2]
  · simp [Function.update_of_ne hy]

/-- `send` gives equal outputs, and keeps the invariant unless the step is bad. -/
theorem step_send (td : Pw → Sˣ) (M : PartyId → W) (s : JS S W Pw K)
    (hG : GoodM G td M s) (r : (S × K) × K × K) (pid : PartyId) (m : W) :
    Bad G td s (jointD G td s (.inr (.send pid m)) r).2 ∨
      ((jointD G td s (.inr (.send pid m)) r).1.1 =
          (jointD G td s (.inr (.send pid m)) r).1.2 ∧
        ∃ M', GoodM G td M' (jointD G td s (.inr (.send pid m)) r).2) := by
  obtain ⟨⟨⟨c, p⟩, t⟩, rs⟩ := s
  have hst : rs.st = stripSt t := hG.st
  have hz := hG.zs pid
  simp only at hz
  cases hy : rs.ys pid with
  | none =>
    have hz0 : c.zs pid = none := by rw [hz, hy]; rfl
    right
    simp only [jointD, simWorldD, simStartD, simCoreD, advCoreD, sendCore, drive1D, realDet,
      setTd, hz0, hy]
    exact ⟨trivial, M, GoodM.phase G hG _ _⟩
  | some y =>
    obtain ⟨hp1, rc, hr, hpeer⟩ := hG.act pid y hy
    simp only at hr
    have hzs : c.zs pid = some ((td rc.pw : S) * y) := by rw [hz, hy]; simp [hr]
    have hinfo : c.info pid = some (rc.peer, rc.role) := by
      rw [hG.info pid, ite_eq_left hp1, hr]
      rfl
    have hrr : rs.st.recs (0, pid) = some (strip rc) := by simp [hst, stripSt, hr]
    have hkeyed : c.keyed pid = rc.key.isSome := by
      rw [hG.keyed pid]
      simp [keyOf, hr]
    by_cases hcond : rc.key = none ∧ m ≠ G.pub 0
    · obtain ⟨hk0, hm⟩ := hcond
      obtain ⟨hfr, htst, hreg0⟩ := hG.fresh (0, pid) rc hr hk0
      have hkc : c.keyed pid = false := by rw [hkeyed, hk0]; rfl
      have hcr : (strip rc).key = none ∧ m ≠ G.pub 0 := ⟨by simp [strip, hk0], hm⟩
      have hhx : hin G td rs pid m = some (h2Inp pid rc.role (G.exp (G.pub (td rc.pw)) y) m
          (G.exp m y)) := by
        simp [hin, hy, hrr, strip]
      by_cases ha : (c.zs (1 - pid)).map G.pub = some m
      · simp only [jointD, simWorldD, simStartD, simCoreD, advCoreD, sendCore, drive1D, realDet,
          setTd, hzs, hinfo, hkc, hm, ha, hy, hrr, hcr, cpl, cplSlot, Slot.get, fStepD, leAdvD,
          simResumeV, simAnswer, ne_eq, not_false_eq_true, and_self, ite_true]
        -- the partner
        obtain ⟨z', hz', hpz'⟩ : ∃ z', c.zs (1 - pid) = some z' ∧ G.pub z' = m := by
          cases h0 : c.zs (1 - pid) with
          | none => simp [h0] at ha
          | some z' => exact ⟨z', rfl, by simpa [h0] using ha⟩
        have hzq := hG.zs (1 - pid)
        simp only at hzq
        obtain ⟨y', hy', pr, hpr, hz'e⟩ : ∃ y', rs.ys (1 - pid) = some y' ∧ ∃ pr,
            t.recs (0, 1 - pid) = some pr ∧ z' = (td pr.pw : S) * y' := by
          rw [hz'] at hzq
          cases h1 : rs.ys (1 - pid) with
          | none => simp [h1] at hzq
          | some y' =>
            cases h2 : t.recs (0, 1 - pid) with
            | none => simp [h1, h2] at hzq
            | some pr =>
              simp only [h1, h2, Option.bind_some, Option.map_some, Option.some.injEq] at hzq
              exact ⟨y', rfl, pr, rfl, hzq⟩
        obtain ⟨-, pr', hpr', hprp⟩ := hG.act (1 - pid) y' hy'
        simp only at hpr'
        rw [hpr] at hpr'
        cases hpr'
        have hprpeer : pr.peer = pid := by rw [hprp]; grind
        have hne : pid ≠ 1 - pid := by grind
        have h11 : 1 - (1 - pid) = pid := by grind
        have hKF : newKeyVal t (0, pid) rc default r.2.1 =
            if pr.role ≠ rc.role ∧ pr.status = .completed ∧ pr.pw = rc.pw then
              pr.key.getD r.2.1 else r.2.1 := by
          simp [newKeyVal, hfr, hpeer, hpr, hprpeer]
        have hF : newKeyStep t (0, pid) default r.2.1 = setRec t (0, pid)
            { rc with key := some (newKeyVal t (0, pid) rc default r.2.1),
                      status := .completed } := by
          simp [newKeyStep, hr, hk0, hfr]
        rw [hF]
        have hhx' : hin G td rs pid m = some (h2Inp pid (strip rc).role
            (G.exp (G.pub (td (strip rc).pw)) y) m (G.exp m y)) := hhx
        generalize h2Inp pid (strip rc).role (G.exp (G.pub (td (strip rc).pw)) y) m
          (G.exp m y) = hxv at hhx' ⊢
        have hmatch : Matches G td c pid rc.pw hxv := hG.hin_matches G hhx' hm hr
        obtain ⟨z₁, rc₁, hz₁, hr₁, -, hxe⟩ := hG.hin_eq G hhx'
        rw [hr] at hr₁
        cases hr₁
        rw [hzs] at hz₁
        cases hz₁
        by_cases hA1 : pr.role ≠ rc.role ∧ pr.status = .completed ∧ pr.pw = rc.pw
        · obtain ⟨kp, hkp⟩ : ∃ kp, pr.key = some kp := by
            cases h0 : pr.key with
            | none =>
              have := (hG.fresh _ pr hpr h0).1
              rw [hA1.2.1] at this
              cases this
            | some kp => exact ⟨kp, rfl⟩
          obtain ⟨hxp, e1, e2, e3, e4, e5⟩ := hG.key (1 - pid) pr kp hpr hkp
          simp only [h11, hzs, Option.map_some, Option.some.injEq] at e5
          have hMq : G.pub ((td rc.pw : S) * y) = M (1 - pid) := e5.mp hA1.2.1
          obtain ⟨z₂, rc₂, hz₂, hr₂, -, hxe₂⟩ := hG.hin_eq G e1
          rw [hpr] at hr₂
          cases hr₂
          rw [hz'] at hz₂
          cases hz₂
          have hzz : (td rc.pw : S) * y ≠ 0 := fun h => e4 (by rw [← hMq, h])
          have hzz' : z' ≠ 0 := fun h => hm (by rw [← hpz', h])
          have hxx : hxv = hxp := by
            rw [hxe, hxe₂, ← hMq, ← hpz']
            exact (h2Inp_partner_iff G hp1 (by grind) hne hzz hzz').mpr
              ⟨fun h => hA1.1 h.symm, by rw [hA1.2.2]⟩
          rw [← hxx] at e2 e3
          rw [hKF, ite_eq_left hA1, hkp, Option.getD_some]
          simp only [roDet, e2]
          have hR : setRec rs.st (0, pid) { strip rc with key := some kp } =
              stripSt (setRec t (0, pid) { rc with key := some kp, status := .completed }) := by
            rw [hst]
            exact setRec_stripSt ({ rc with key := some kp, status := .completed } : Rec Pw K)
              ⟨rfl, rfl, rfl⟩
          rw [hR]
          right
          refine ⟨trivial, _, GoodM.phase G (hG.send G hr hk0 hm hhx' kp
            { rc with key := some kp, status := .completed } ⟨rfl, rfl, rfl, rfl⟩
            (by simp [hreg0]) (by simp [ha]) c.pend (Or.inl ⟨rfl, hreg0⟩) rs.h2
            (Or.inl ⟨rfl, e2, e3⟩) (by simp)) _ _⟩
        · rw [hKF, ite_eq_right hA1]
          cases hl : rs.h2.lookup hxv with
          | none =>
            have hsl : simLk (c, p) hxv = none := by
              cases h0 : simLk (c, p) hxv with
              | none => rfl
              | some v => rw [hG.lookup_of_simLk G h0] at hl; simp at hl
            simp only [roDet, hl]
            let rcn : Rec Pw K := { rc with key := some r.2.1, status := .completed }
            have hR : setRec rs.st (0, pid) { strip rc with key := some r.2.1 } =
                stripSt (setRec t (0, pid) rcn) := by
              rw [hst]
              exact setRec_stripSt rcn ⟨rfl, rfl, rfl⟩
            rw [hR]
            right
            refine ⟨trivial, _, GoodM.phase G (hG.send G hr hk0 hm hhx' r.2.1 rcn
              ⟨rfl, rfl, rfl, rfl⟩ (by simp [rcn, hreg0]) (by simp [rcn, ha]) c.pend
              (Or.inl ⟨rfl, hreg0⟩) _ (Or.inr ⟨rfl, hl, hsl⟩) (by simp [rcn])) _ _⟩
          | some kr =>
            rcases hG.tab hxv with h | ⟨q, hq, hxq⟩
            · exfalso
              rw [hl] at h
              apply hG.ps
              refine ⟨pid, hxv, z', rc, ?_, hz', ?_, hr, hmatch⟩
              · simp [InDom, ← h]
              · rw [hxe, peerMsg_h2Inp, hpz']
            · have hqp : q ≠ pid := by
                intro h
                subst h
                simp [keyOf, hr, hk0] at hq
              have hq1 : q = 1 - pid := by
                have := hG.le_one_of_hin G hxq
                grind
              subst hq1
              have hcr := hG.cross_of_tr G hqp hxq hhx' rfl
              rw [hzs] at hcr
              simp only [Option.map_some, Option.some.injEq] at hcr
              obtain ⟨kp, hkp⟩ : ∃ kp, pr.key = some kp := by
                unfold keyOf at hq
                rw [hpr] at hq
                exact Option.isSome_iff_exists.mp hq
              obtain ⟨hxp, e1, -, -, e4, e5⟩ := hG.key (1 - pid) pr kp hpr hkp
              rw [hxq] at e1
              obtain rfl := Option.some.inj e1
              simp only [h11, hzs, Option.map_some, Option.some.injEq] at e5
              have hcomp : pr.status = .completed := e5.mpr hcr
              obtain ⟨z₂, rc₂, hz₂, hr₂, -, hxe₂⟩ := hG.hin_eq G hxq
              rw [hpr] at hr₂
              cases hr₂
              rw [hz'] at hz₂
              cases hz₂
              have hzz : (td rc.pw : S) * y ≠ 0 := fun h => e4 (by rw [← hcr, h])
              have hzz' : z' ≠ 0 := fun h => hm (by rw [← hpz', h])
              have hiff := h2Inp_partner_iff G (r := rc.role) (r' := pr.role)
                (a := (td rc.pw : S)) (b := (td pr.pw : S)) hp1 (by grind) hne
                hzz hzz'
              rw [← hpz'] at hxe
              rw [← hcr] at hxe₂
              obtain ⟨hrole, htd⟩ := hiff.mp (hxe.symm.trans hxe₂)
              by_cases hpw : pr.pw = rc.pw
              · exact absurd ⟨fun h => hrole h.symm, hcomp, hpw⟩ hA1
              · left
                exact Or.inl fun hinj => hpw (hinj (Units.ext htd.symm))
      · have hhx' : hin G td rs pid m = some (h2Inp pid (strip rc).role
            (G.exp (G.pub (td (strip rc).pw)) y) m (G.exp m y)) := hhx
        obtain ⟨z₁, rc₁, hz₁, hr₁, -, hxe⟩ := hG.hin_eq G hhx'
        rw [hr] at hr₁
        cases hr₁
        rw [hzs] at hz₁
        cases hz₁
        have hmatch := hG.hin_matches G hhx' hm hr
        have hTx : (h2Inp pid (strip rc).role (G.exp (G.pub (td (strip rc).pw)) y) m
            (G.exp m y)).tr = (h2Inp pid rc.role (G.pub ((td rc.pw : S) * y)) m m).tr := by
          rw [hxe]
          rfl
        -- the other party's honest input on this transcript would make `m` its message
        have hcross : ∀ q x', (keyOf t (0, q)).isSome → hin G td rs q (M q) = some x' →
            x'.tr = (h2Inp pid (strip rc).role (G.exp (G.pub (td (strip rc).pw)) y) m
              (G.exp m y)).tr → False := by
          intro q x' hq hx' htr
          have hqp : q ≠ pid := by
            intro h
            subst h
            simp [keyOf, hr, hk0] at hq
          have hq1 : q = 1 - pid := by
            have := hG.le_one_of_hin G hx'
            grind
          subst hq1
          exact ha (hG.cross_of_tr G (Ne.symm hqp) hhx' hx' htr.symm)
        cases hf : findMatch G td c ((td rc.pw : S) * y) pid
            (h2Inp pid rc.role (G.pub ((td rc.pw : S) * y)) m m).tr with
        | some pk =>
          obtain ⟨pw, k⟩ := pk
          obtain ⟨e, he, het, hex, hek⟩ := findMatch_some G hf
          have hpe : peerMsg pid e.1 = m := by rw [peerMsg_eq_of_tr het, peerMsg_h2Inp]
          have hme : Matches G td c pid pw e.1 :=
            matches_of_extractAt G hzs hinfo (by rw [hpe]; exact het) hex
          have hce : c.h2.lookup e.1 = some k := by rw [← hek]; exact hG.nodup e he
          have hpe0 : p.lookup e.1 = none := by
            rcases hG.disj e.1 with h | h
            · exact h
            · rw [hce] at h
              simp at h
          have hsle : simLk (c, p) e.1 = some k := by simp [simLk, hpe0, hce]
          simp only [jointD, simWorldD, simStartD, simCoreD, advCoreD, sendCore, drive1D,
            realDet, setTd, hzs, hinfo, hkc, hm, ha, hy, hrr, hcr, cpl, cplSlot, Slot.get,
            fStepD, leAdvD, simResumeV, simAnswer, ne_eq, not_false_eq_true, and_self, ite_true,
            ite_false, findMatch_td, hf]
          generalize h2Inp pid (strip rc).role (G.exp (G.pub (td (strip rc).pw)) y) m
            (G.exp m y) = hxv at hhx' hxe hmatch hTx hcross ⊢
          have htest : testStep t (0, pid) pw =
              setRec t (0, pid) (guessed rc (decide (rc.pw = pw))) := by
            simp [testStep, hr, Testable, hfr, htst]
          by_cases hb : rc.pw = pw
          · let rcb : Rec Pw K :=
              { rc with status := .compromised, tested := some true, key := some k }
            have hF : newKeyStep (testStep t (0, pid) pw) (0, pid) k r.2.2 =
                setRec t (0, pid) rcb := by
              rw [htest]
              simp [newKeyStep, setRec, guessed, newKeyVal, hk0, rcb, hb]
            have hxx : e.1 = hxv := hG.eq_hin_of_matches G hhx' hr (hb ▸ hme) (het.trans hTx.symm)
            rw [hxx] at hsle
            have hlk : rs.h2.lookup hxv = some k := hG.lookup_of_simLk G hsle
            simp only [roDet, hlk]
            have hR : setRec rs.st (0, pid) { strip rc with key := some k } =
                stripSt (setRec t (0, pid) rcb) := by
              rw [hst]
              exact setRec_stripSt rcb ⟨rfl, rfl, rfl⟩
            rw [hF, hR]
            right
            refine ⟨trivial, _, GoodM.phase G (hG.send G hr hk0 hm hhx' k rcb
              ⟨rfl, rfl, rfl, rfl⟩ (by simp [rcb, hreg0]) (by simp [rcb, ha]) c.pend
              (Or.inl ⟨rfl, hreg0⟩) rs.h2 (Or.inl ⟨rfl, hlk, Or.inr hsle⟩)
              (fun _ _ h => by rw [hsle] at h; simp at h)) _ _⟩
          · let rcb : Rec Pw K :=
              { rc with status := .interrupted, tested := some false, key := some r.2.2 }
            have hF : newKeyStep (testStep t (0, pid) pw) (0, pid) k r.2.2 =
                setRec t (0, pid) rcb := by
              rw [htest]
              simp [newKeyStep, setRec, guessed, newKeyVal, hk0, rcb, hb]
            rw [hF]
            cases hl : rs.h2.lookup hxv with
            | none =>
              have hsl : simLk (c, p) hxv = none := by
                cases h0 : simLk (c, p) hxv with
                | none => rfl
                | some v => rw [hG.lookup_of_simLk G h0] at hl; simp at hl
              simp only [roDet, hl]
              have hR : setRec rs.st (0, pid) { strip rc with key := some r.2.2 } =
                  stripSt (setRec t (0, pid) rcb) := by
                rw [hst]
                exact setRec_stripSt rcb ⟨rfl, rfl, rfl⟩
              rw [hR]
              right
              refine ⟨trivial, _, GoodM.phase G (hG.send G hr hk0 hm hhx' r.2.2 rcb
                ⟨rfl, rfl, rfl, rfl⟩ (by simp [rcb, hreg0]) (by simp [rcb, ha]) c.pend
                (Or.inl ⟨rfl, hreg0⟩) _ (Or.inr ⟨rfl, hl, hsl⟩)
                (fun _ _ _ => ⟨e.1, pw, by simp [InDom, hsle], het.trans hTx.symm,
                  fun h => hb h.symm, hme⟩)) _ _⟩
            | some kr =>
              exfalso
              rcases hG.tab hxv with h | ⟨q, hq, hxq⟩
              · rw [hl] at h
                exact hG.dm ⟨pid, e.1, hxv, pw, rc.pw, by simp [InDom, hsle],
                  by simp [InDom, ← h], het.trans hTx.symm, fun h => hb h.symm, hme, hmatch⟩
              · exact hcross q hxv hq hxq rfl
        | none =>
          simp only [jointD, simWorldD, simStartD, simCoreD, advCoreD, sendCore, drive1D,
            realDet, setTd, hzs, hinfo, hkc, hm, ha, hy, hrr, hcr, cpl, cplSlot, Slot.get,
            fStepD, leAdvD, simResumeV, simAnswer, ne_eq, not_false_eq_true, and_self, ite_true,
            ite_false, findMatch_td, hf]
          generalize h2Inp pid (strip rc).role (G.exp (G.pub (td (strip rc).pw)) y) m
            (G.exp m y) = hxv at hhx' hxe hmatch hTx hcross ⊢
          let rcb : Rec Pw K :=
            { rc with status := .interrupted, registered := true, key := some r.2.2 }
          have hF : newKeyStep (registerStep t (0, pid)) (0, pid) default r.2.2 =
              setRec t (0, pid) rcb := by
            simp [registerStep, hr, Testable, hfr, htst, newKeyStep, setRec, newKeyVal, hk0,
              rcb]
          rw [hF]
          cases hl : rs.h2.lookup hxv with
          | none =>
            have hsl : simLk (c, p) hxv = none := by
              cases h0 : simLk (c, p) hxv with
              | none => rfl
              | some v => rw [hG.lookup_of_simLk G h0] at hl; simp at hl
            simp only [roDet, hl]
            have hR : setRec rs.st (0, pid) { strip rc with key := some r.2.2 } =
                stripSt (setRec t (0, pid) rcb) := by
              rw [hst]
              exact setRec_stripSt rcb ⟨rfl, rfl, rfl⟩
            rw [hR, ← hTx]
            right
            refine ⟨trivial, _, GoodM.phase G (hG.send G hr hk0 hm hhx' r.2.2 rcb
              ⟨rfl, rfl, rfl, rfl⟩ (by simp [rcb]) (by simp [rcb, ha]) _
              (Or.inr ⟨rfl, rfl⟩) _ (Or.inr ⟨rfl, hl, hsl⟩)
              (fun _ h _ => by simp at h)) _ _⟩
          | some kr =>
            exfalso
            rcases hG.tab hxv with h | ⟨q, hq, hxq⟩
            · rw [hl] at h
              cases hpx : p.lookup hxv with
              | some v =>
                obtain ⟨q, rq, hx'', hrq, hkq, -, hxq, htq⟩ := hG.prog hxv v hpx
                simp only at hrq
                exact hcross q hx'' (by simp [keyOf, hrq, hkq]) hxq htq
              | none =>
                have hcx : c.h2.lookup hxv = some kr := by simpa [simLk, hpx] using h.symm
                have hnone := findMatch_none G hf (hxv, kr) (mem_of_lookup hcx) hTx
                by_cases hcand : rc.pw ∈ c.cands
                · have := extractAt_isSome G hmatch hcand hzs
                  rw [hnone] at this
                  simp at this
                · exact hG.uq ⟨pid, hxv, rc.pw, by simp [InDom, ← h], hcand, hmatch⟩
            · exact hcross q hxv hq hxq rfl
    · right
      have hc' : ¬ (c.keyed pid = false ∧ m ≠ G.pub 0) := by
        rw [hkeyed]
        intro h
        apply hcond
        refine ⟨?_, h.2⟩
        cases hk : rc.key with
        | none => rfl
        | some _ => simp [hk] at h
      have hr' : ¬ ((strip rc).key = none ∧ m ≠ G.pub 0) := by simpa [strip] using hcond
      simp only [jointD, simWorldD, simStartD, simCoreD, advCoreD, sendCore, drive1D, realDet,
        setTd, hzs, hinfo, hc', hy, hrr, hr', ite_false]
      exact ⟨trivial, M, GoodM.phase G hG _ _⟩

/-- **The one-step lemma.** From a state satisfying the invariant, a step of the joint world is
bad, or its two outputs are equal and it reaches a state satisfying the invariant. -/
theorem step_good (td : Pw → Sˣ) (s : JS S W Pw K) (hG : Good G td s) (e : OEv Pw W)
    (r : (S × K) × K × K) :
    Bad G td s (jointD G td s e r).2 ∨
      ((jointD G td s e r).1.1 = (jointD G td s e r).1.2 ∧ Good G td (jointD G td s e r).2) := by
  obtain ⟨M, hG⟩ := hG
  rcases e with (⟨sid, pid, peer, role, pw⟩ | ⟨sid, pid⟩) | (_ | _ | pid | pw | x | ⟨pid, m⟩)
  · rcases step_newSession G td M s hG r sid pid peer role pw with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, M, h2⟩
  · exact Or.inr ⟨(step_getKey G td M s hG r sid pid).1, M, (step_getKey G td M s hG r sid pid).2⟩
  · exact Or.inr ⟨(step_idle G td M s hG r).1, M, (step_idle G td M s hG r).2⟩
  · exact Or.inr ⟨(step_poll G td M s hG r).1, M, (step_poll G td M s hG r).2⟩
  · exact Or.inr ⟨(step_msg G td M s hG r pid).1, M, (step_msg G td M s hG r pid).2⟩
  · exact Or.inr ⟨(step_h1 G td M s hG r pw).1, M, (step_h1 G td M s hG r pw).2⟩
  · exact step_h2 G td M s hG r x
  · exact step_send G td M s hG r pid m

end Step

/-! ## Unions of bad flags

This section belongs upstream, in `CatCryptCore.Crypto.OracleLazyMulti` beside `flagWhen`. -/

section FlagUnion

variable {D R α σ : Type}

/-- **A weaker bad event sets its flag at most as often.** -/
theorem run_flagWhen_mono (O : σ → D → PMF (R × σ)) (bad₁ bad₂ : σ → D → R × σ → Prop)
    [∀ s d x, Decidable (bad₁ s d x)] [∀ s d x, Decidable (bad₂ s d x)]
    (h : ∀ s d x, bad₁ s d x → bad₂ s d x) (A : OracleAdv D R α) (s : σ) :
    (OracleAdv.run (OracleAdv.flagWhen bad₁ O) A (s, false)).toOuterMeasure
        {y | y.2.2 = true} ≤
      (OracleAdv.run (OracleAdv.flagWhen bad₂ O) A (s, false)).toOuterMeasure
        {y | y.2.2 = true} :=
  run_flagWhen_le_of_inv O bad₁ bad₂ (fun _ => True)
    (fun s d _ x _ => (em (bad₁ s d x)).elim (fun hb => Or.inl (h s d x hb))
      (fun hb => Or.inr ⟨hb, trivial⟩)) A s trivial

/-- **The union bound for bad flags**: the flag of `bad₁ ∨ bad₂` is set with at most the sum
of the probabilities that the flags of `bad₁` and of `bad₂` are set. -/
theorem run_flagWhen_or_le (O : σ → D → PMF (R × σ)) (bad₁ bad₂ : σ → D → R × σ → Prop)
    [∀ s d x, Decidable (bad₁ s d x)] [∀ s d x, Decidable (bad₂ s d x)]
    (A : OracleAdv D R α) (s : σ) :
    (OracleAdv.run (OracleAdv.flagWhen (fun s d x => bad₁ s d x ∨ bad₂ s d x) O) A
        (s, false)).toOuterMeasure {y | y.2.2 = true} ≤
      (OracleAdv.run (OracleAdv.flagWhen bad₁ O) A (s, false)).toOuterMeasure
          {y | y.2.2 = true} +
        (OracleAdv.run (OracleAdv.flagWhen bad₂ O) A (s, false)).toOuterMeasure
          {y | y.2.2 = true} := by
  let bad₂' : σ × Bool → D → R × (σ × Bool) → Prop := fun st d x => bad₂ st.1 d (x.1, x.2.1)
  let O₂ := OracleAdv.flagWhen bad₂' (OracleAdv.flagWhen bad₁ O)
  have h₁ : (OracleAdv.run O₂ A ((s, false), false)).map (Prod.map id Prod.fst) =
      OracleAdv.run (OracleAdv.flagWhen bad₁ O) A (s, false) :=
    OracleAdv.run_flagWhen_map bad₂' _ A _ false
  have h₂ : (OracleAdv.run O₂ A ((s, false), false)).map
      (Prod.map id fun st => (st.1.1, st.2)) =
        OracleAdv.run (OracleAdv.flagWhen bad₂ O) A (s, false) :=
    OracleAdv.run_map_state _ _ _ (fun st d => by
      simp only [O₂, bad₂', OracleAdv.flagWhen, PMF.map_comp]
      rfl) A _
  have h₃ : (OracleAdv.run O₂ A ((s, false), false)).map
      (Prod.map id fun st => (st.1.1, st.1.2 || st.2)) =
        OracleAdv.run (OracleAdv.flagWhen (fun s d x => bad₁ s d x ∨ bad₂ s d x) O) A
          (s, false) :=
    OracleAdv.run_map_state _ _ _ (fun st d => by
      simp only [O₂, bad₂', OracleAdv.flagWhen, PMF.map_comp]
      congr 1
      funext x
      simp only [Function.comp_apply, Prod.map_apply, id_eq, Bool.decide_or]
      cases st.1.2 <;> cases st.2 <;> simp) A _
  rw [← h₁, ← h₂, ← h₃, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_map_apply]
  refine (MeasureTheory.measure_mono ?_).trans (MeasureTheory.measure_union_le _ _)
  intro y hy
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy ⊢
  simp only [Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq]
  grind

/-- A flagged run does not depend on the decision procedure of the bad event. -/
theorem run_flagWhen_inst (O : σ → D → PMF (R × σ)) (bad : σ → D → R × σ → Prop)
    (i j : ∀ s d x, Decidable (bad s d x)) (A : OracleAdv D R α) (s : σ × Bool) :
    OracleAdv.run (@OracleAdv.flagWhen D R σ bad i O) A s =
      OracleAdv.run (@OracleAdv.flagWhen D R σ bad j O) A s := by
  rw [Subsingleton.elim i j]

/-- The output flag of a flagged run, at `true`, as an outer measure. -/
theorem map_flag_apply {β : Type} (p : PMF (β × (σ × Bool))) :
    (p.map fun y => y.2.2) true = p.toOuterMeasure {y | y.2.2 = true} := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl

end FlagUnion

/-! ## The bad-event experiments -/

section Experiments

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]
  [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- The invariant holds at the initial state of the joint world. -/
theorem good_init (td : Pw → Sˣ) :
    Good G td (jointInit G (S := S) (W := W) (Pw := Pw) (K := K)).1 := by
  refine ⟨fun _ => G.pub 0, ?_⟩
  refine ⟨by simp [jointInit, simProt, stripSt, initSt], fun q => by
    simp [jointInit, simProt, initSt], fun q => by simp [jointInit, simProt],
    fun q y h => by simp [jointInit] at h, fun x r h => by simp [jointInit, initSt] at h,
    fun x r h => by simp [jointInit, initSt] at h,
    fun q => by simp [jointInit, simProt, keyOf, initSt],
    fun x r h => by simp [jointInit, initSt] at h,
    fun q r k h => by simp [jointInit, initSt] at h,
    fun q T h => by simp [jointInit, simProt] at h,
    fun x => Or.inl (by simp [jointInit, simProt, simLk]),
    fun x k h => by simp [jointInit, simProt] at h,
    fun x => Or.inl (by simp [jointInit, simProt]),
    fun e he => by simp [jointInit, simProt] at he,
    ?_, ?_, ?_, fun q r hx h => by simp [jointInit, initSt] at h⟩
  · rintro ⟨_, x, _, _, _, h, -⟩
    simp [InDom, simLk, jointInit, simProt] at h
  · rintro ⟨_, x, _, h, -⟩
    simp [InDom, simLk, jointInit, simProt] at h
  · rintro ⟨_, x, _, _, h, -⟩
    simp [InDom, simLk, jointInit, simProt] at h

open Classical in
/-- **The experiment of a bad event of the joint world**: the table of `H1` is sampled, the
adversary runs against the joint world answering with the outputs of the simulated world, and
the experiment outputs whether a transition from `s` to `s'` with `bad td s s'` occurred. -/
noncomputable def flagExp (bad : (Pw → Sˣ) → JS S W Pw K → JS S W Pw K → Prop)
    (B : OracleAdv (OEv Pw W) (OOut W K) Bool) : PMF Bool :=
  (PMF.uniformFintype (Pw → Sˣ)).bind fun td =>
    (OracleAdv.run (OracleAdv.flagWhen (fun s _ x => bad td s.1 x.2.1) (jointSim G td)) B
      (jointInit G, false)).map fun y => y.2.2

/-- **The double-match experiment.** -/
noncomputable def dmExp (B : OracleAdv (OEv Pw W) (OOut W K) Bool) : PMF Bool :=
  flagExp G (fun td _ s' => DMst G td s'.1.1) B

/-- **The unqueried-match experiment.** -/
noncomputable def uqExp (B : OracleAdv (OEv Pw W) (OOut W K) Bool) : PMF Bool :=
  flagExp G (fun td _ s' => UQst G td s'.1.1) B

/-- **The passive-session experiment.** -/
noncomputable def psExp (B : OracleAdv (OEv Pw W) (OOut W K) Bool) : PMF Bool :=
  flagExp G (fun td _ s' => PSst G td s'.1) B

/-- **The collision experiment.** -/
noncomputable def collExp (B : OracleAdv (OEv Pw W) (OOut W K) Bool) : PMF Bool :=
  flagExp G (fun td s s' => TdColl td ∨ CollStep G s s') B

open Classical in
/-- The output of a flagged run, at `true`, as an outer measure. -/
theorem flagExp_inner_apply (td : Pw → Sˣ) (bad : (Pw → Sˣ) → JS S W Pw K → JS S W Pw K → Prop)
    (B : OracleAdv (OEv Pw W) (OOut W K) Bool) :
    ((OracleAdv.run (OracleAdv.flagWhen (fun s _ x => bad td s.1 x.2.1) (jointSim G td)) B
      (jointInit G, false)).map fun y => y.2.2) true =
    (OracleAdv.run (OracleAdv.flagWhen (fun s _ x => bad td s.1 x.2.1) (jointSim G td)) B
      (jointInit G, false)).toOuterMeasure {y | y.2.2 = true} := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl

open Classical in
/-- **The bad event of the CPace square is split.** For every oracle adversary `B`, the
probability that the outputs of the real and of the simulated world differ at some step is at
most the sum of the probabilities of a double match, an unqueried match, a passive-session query
and a collision. -/
theorem badGame_le (B : OracleAdv (OEv Pw W) (OOut W K) Bool) :
    badGame G B true ≤ dmExp G B true + uqExp G B true + psExp G B true + collExp G B true := by
  have hstep : ∀ td : Pw → Sˣ, ∀ s e, Good G td (s : JS S W Pw K × Bool).1 →
      ∀ x ∈ (jointSim G td s e).support,
        Bad G td s.1 x.2.1 ∨ (¬ JointBad s e x ∧ Good G td x.2.1) := by
    intro td s e hs x hx
    simp only [jointSim, PMF.support_map, Set.mem_image] at hx
    obtain ⟨r, -, rfl⟩ := hx
    rcases step_good G td s.1 hs e r with h | ⟨h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨?_, h2⟩
      simp [JointBad, h1]
  unfold badGame dmExp uqExp psExp collExp flagExp
  simp only [PMF.bind_apply]
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun td => ?_
  simp only [← mul_add]
  gcongr
  simp only [map_flag_apply]
  have h1 := run_flagWhen_le_of_inv (jointSim G td) JointBad
    (fun s _ x => Bad G td s.1 x.2.1) (fun s => Good G td s.1) (hstep td) B _ (good_init G td)
  have h2 := run_flagWhen_mono (jointSim G td) (fun s _ x => Bad G td s.1 x.2.1)
    (fun s _ x => (TdColl td ∨ CollStep G s.1 x.2.1) ∨ (DMst G td x.2.1.1.1 ∨
      (UQst G td x.2.1.1.1 ∨ PSst G td x.2.1.1)))
    (fun _ _ _ h => or_assoc.mpr h) B (jointInit G)
  have h3 := run_flagWhen_or_le (jointSim G td)
    (fun s _ x => TdColl td ∨ CollStep G s.1 x.2.1)
    (fun _ _ x => DMst G td x.2.1.1.1 ∨ (UQst G td x.2.1.1.1 ∨ PSst G td x.2.1.1)) B
    (jointInit G)
  have h4 := run_flagWhen_or_le (jointSim G td) (fun _ _ x => DMst G td x.2.1.1.1)
    (fun _ _ x => UQst G td x.2.1.1.1 ∨ PSst G td x.2.1.1) B (jointInit G)
  have h5 := run_flagWhen_or_le (jointSim G td) (fun _ _ x => UQst G td x.2.1.1.1)
    (fun _ _ x => PSst G td x.2.1.1) B (jointInit G)
  refine h1.trans (h2.trans (h3.trans ((add_le_add_right (h4.trans (add_le_add_right h5 _))
    _).trans (le_of_eq ?_))))
  rw [add_comm]
  simp only [add_assoc]
  congr 3
  exact congrArg (fun p => PMF.toOuterMeasure p _) (run_flagWhen_inst _ _ _ _ _ _)

end Experiments

end CatCrypt.Crypto.PAKE.CPaceBad
