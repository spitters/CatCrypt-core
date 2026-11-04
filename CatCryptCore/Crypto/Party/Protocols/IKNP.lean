/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Derived
public import CatCryptCore.Crypto.Party.Refinement
public import CatCryptCore.Crypto.Party.UnwindingTransfer
public import CatCryptCore.Crypto.Party.Timed
public import CatCryptCore.Tactics.PartyDerive
public import CatCryptCore.Crypto.OTExtension.IKNPWakeShape

/-!
# IKNP OT extension in the party language

**Ideal functionality.** `FOTSched otChoose` (both parties honest) and
`FOTSchedSH otChoose leak` (a semi-honest corrupt sender, `leak = leakSend`, or receiver,
`leak = leakRecv otChoose`): the scheduled oblivious transfer of `m` message pairs of
`OT/FOTSched.lean`, whose adversary delivers the receiver's output and, for a corrupt party,
reads that party's view on the adversary port.

**Real protocol.** The IKNP parties written as one program of the party language,
`IKNPProg.partyBody`, one iteration per activation, as the multi-call hybrid
`IKNPProg.partyLoop` over the `κ` scheduled base OTs beside the secure channel. The program
draws the randomness `(T, s)` at the first input of a party; the receiver's input gives the
column pairs of `T` and `T + r` to the base OTs by the loop `rLoop`, the sender's input gives the
bits of `s` as choices by `sLoop`; the wake `wakeS i` fetches the column of base OT `i` and, once
every column is present, sends the masked message pairs (`fetchP`); the wake `wakeR` reads the
message and outputs the unmasked messages (`recvP`). Adversary events of the base OTs and of the
channel are forwarded. The protocol is `IKNPProg.realP`.

**Simulator.** The IKNP simulator `IKNPWake.simW` written as a program, `IKNPProg.simBody`, as
the multi-call hybrid `IKNPProg.simLoop` over the ideal functionality: it forwards the inputs,
simulates the base OTs from the input status the functionality reports and the channel with
every message replaced by a fixed value, and draws the corrupt party's view by `simS` or
`simR`. Its opacity is information flow of the program (`Prog.loopSys_unwinding`,
`MultiHybrid.unwinding_ofSys`), and its time certificate is the bound of the program
(`ProgE.LoopBoundGraded`).

**Proof.** A multi-call hybrid whose answers are typed by the calls (`Ans`) embeds into a
program up to a bound on the remaining calls of each activation
(`MultiHybrid.EmbedsUpTo`, `Prog.loopMulti_embedsUpTo`): the residual program at a pending call
is the continuation determined by the hand-written state, and the fuel is never exhausted. The
program parties embed the hand-written parties with their own draw (`IKNPWake.partyLazy`) beside
the forwarding of the adversary port, and the simulator program embeds `simW`; the realizations
of `OTExtension/IKNPWake.lean` transfer through these step equivalences
(`IKNPProg.realizesSim_prog`). The refinement of the parties onto the abstract system is the
hand-written `IKNPWake.view_realW_eq`, used through `IKNPWake.view_iknpW_eq_lazy`.

Search words: party language, IKNP, OT extension, oblivious transfer, refinement, simulator,
embedding, multi-call hybrid, opacity, time certificate.

## Main definitions

* `MultiHybrid.EmbedsUpTo`: an embedding of multi-call hybrids up to typed answers and a bound
  on the remaining calls.
* `IKNPProg.partyBody`, `IKNPProg.partyLoop`, `IKNPProg.realP`: the IKNP parties as a program
  and the protocol over them.
* `IKNPProg.simBody`, `IKNPProg.simLoop`, `IKNPProg.simP`: the simulator as a program.

## Main results

* `MultiHybrid.EmbedsUpTo.stepEq`, `Prog.loopMulti_embedsUpTo`: step equivalence from an
  embedding up to a call bound.
* `IKNPProg.partyLoop_stepEq`: the program parties are step-equivalent to `partyLazy`.
* `IKNPProg.view_realP_eq`: the program protocol has the view of `iknpW`.
* `IKNPProg.simLoop_stepEq`, `IKNPProg.simLoop_opaque`, `IKNPProg.simLoop_time`: the simulator
  program, its opacity and its time certificate.
* `IKNPProg.iknpH_realizesSim_prog`, `IKNPProg.iknpS_realizesSim_prog`,
  `IKNPProg.iknpR_realizesSim_prog`: IKNP realizes the scheduled transfer behind the program
  simulator, with the bounds of `iknpH_realizesSim`, `iknpS_realizesSim`, `iknpR_realizesSim`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent.MultiHybrid

open CatCrypt.Core

variable {σ σ' τ E O Q A : Type}

/-! ## Embeddings up to a bound on the remaining calls -/

/-- The image of a decision: a pending call `q` at the state `s` is mapped to `c s q`, an outer
output at `s` to `b s`. -/
def liftDecQ (b : σ → σ') (c : σ → Q → σ') (r : σ × (Q ⊕ O)) : σ' × (Q ⊕ O) :=
  (match r.2 with
    | .inl q => c r.1 q
    | .inr _ => b r.1, r.2)

/-- Unfolding lemma of `liftDecQ` at a call. -/
@[simp] theorem liftDecQ_inl (b : σ → σ') (c : σ → Q → σ') (s : σ) (q : Q) :
    liftDecQ (O := O) b c (s, .inl q) = (c s q, .inl q) := rfl

/-- Unfolding lemma of `liftDecQ` at an output. -/
@[simp] theorem liftDecQ_inr (b : σ → σ') (c : σ → Q → σ') (s : σ) (o : O) :
    liftDecQ (Q := Q) b c (s, .inr o) = (b s, .inr o) := rfl

/-- `π'` embeds `π` up to the answers `Ans` and the call bound `D`: boundary states are mapped by
`b`, a state with the call `q` pending by `c · q`; `start`, and `resume` at the answers `Ans`
allows, commute with the embedding; and `D s q` bounds the calls that follow the pending call
`q` at `s`, below the fuel at a `start` and decreasing at each `resume`. `finish` is not
compared: under the bound the fuel is never exhausted. -/
structure EmbedsUpTo (π : MultiHybrid σ E O Q A) (π' : MultiHybrid σ' E O Q A) (b : σ → σ')
    (c : σ → Q → σ') (Ans : Q → A → Prop) (D : σ → Q → ℕ) : Prop where
  /-- The initial state of `π'` is the image of that of `π`. -/
  init : π'.init = b π.init
  /-- The fuels agree. -/
  fuel : π'.fuel = π.fuel
  /-- `start` commutes with the embedding. -/
  start : ∀ s e, π'.start (b s) e = SPComp.map (liftDecQ b c) (π.start s e)
  /-- `resume` commutes with the embedding at the answers `Ans` allows. -/
  resume : ∀ s q a, Ans q a → π'.resume (c s q) a = SPComp.map (liftDecQ b c) (π.resume s a)
  /-- A call issued by `start` is followed by fewer calls than the fuel. -/
  start_depth : ∀ s e r q, IsOutcome (π.start s e) r → r.2 = .inl q → D r.1 q < π.fuel
  /-- A call issued by `resume` is followed by fewer calls than the pending one. -/
  resume_depth : ∀ s q a r q', Ans q a → IsOutcome (π.resume s a) r → r.2 = .inl q' →
    D r.1 q' < D s q

namespace EmbedsUpTo

variable {π : MultiHybrid σ E O Q A} {π' : MultiHybrid σ' E O Q A} {b : σ → σ'}
  {c : σ → Q → σ'} {Ans : Q → A → Prop} {D : σ → Q → ℕ}

/-- The rest of an activation from an output is the output. -/
theorem drive_inr (ρ : MultiHybrid σ E O Q A) (X : Sys τ Q A) (n : ℕ) (s : σ) (o : O) (t : τ) :
    ρ.drive X n s (.inr o) t = SPComp.pure (s, t, o) := by
  cases n <;> rfl

/-- **The interaction with a subroutine commutes with an embedding up to a call bound**, for a
subroutine whose answers are typed by `Ans`. -/
theorem drive (h : EmbedsUpTo π π' b c Ans D) (X : Sys τ Q A)
    (hX : ∀ t q r, IsOutcome (X.step t q) r → Ans q r.2) :
    ∀ n s q t, D s q < n → π'.drive X n (c s q) (.inl q) t =
      SPComp.map (fun p => (b p.1, p.2)) (π.drive X n s (.inl q) t) := by
  intro n
  induction n with
  | zero => intro s q t hd; exact absurd hd (Nat.not_lt_zero _)
  | succ n ih =>
    intro s q t hd
    simp only [MultiHybrid.drive, SPComp.map, SPComp.bind_assoc]
    refine bind_congr_isOutcome fun x hx => ?_
    rw [h.resume s q x.2 (hX t q x hx)]
    simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    refine bind_congr_isOutcome fun r hr => ?_
    rcases r with ⟨s', q' | o⟩
    · have hd' := h.resume_depth s q x.2 _ q' (hX t q x hx) hr rfl
      simp only [liftDecQ_inl]
      rw [ih s' q' x.1 (by grind)]
      simp only [SPComp.map]
    · simp only [liftDecQ_inr, drive_inr, SPComp.pure_bind]

/-- **A step of the composite with a subroutine commutes with an embedding up to a call
bound.** -/
theorem withSub_step (h : EmbedsUpTo π π' b c Ans D) (X : Sys τ Q A)
    (hX : ∀ t q r, IsOutcome (X.step t q) r → Ans q r.2) (s : σ) (t : τ) (e : E) :
    (π'.withSub X).step (b s, t) e =
      SPComp.map (fun p => ((b p.1.1, p.1.2), p.2)) ((π.withSub X).step (s, t) e) := by
  simp only [withSub, h.start, h.fuel, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  refine bind_congr_isOutcome fun r hr => ?_
  rcases r with ⟨s', q | o⟩
  · simp only [liftDecQ_inl]
    rw [h.drive X hX _ s' q t (h.start_depth s e _ q hr rfl)]
    simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · simp only [liftDecQ_inr, drive_inr, SPComp.pure_bind]

/-- **An embedding up to a call bound gives step equivalence** over every subroutine whose
answers are typed by `Ans`. -/
theorem stepEq (h : EmbedsUpTo π π' b c Ans D) (X : Sys τ Q A)
    (hX : ∀ t q r, IsOutcome (X.step t q) r → Ans q r.2) :
    Sys.StepEq ⟨σ × τ, π.withSub X⟩ ⟨σ' × τ, π'.withSub X⟩ :=
  (Sys.StepMapOn.of_step (fun p => (b p.1, p.2)) (by simp [withSub, h.init])
    fun t e => (h.withSub_step X hX t.1 t.2 e).symm).stepEq

end EmbedsUpTo

end CatCrypt.Crypto.UCTransparent.MultiHybrid

namespace CatCrypt.Crypto.Party.Prog

open CatCrypt.Core CatCrypt.Crypto.UCTransparent MultiHybrid

variable {σ E O Q A : Type}

/-- **Loops with calls, up to a call bound.** When the activation of `body s` on an outer event
is the image of `π.start s e`, and the continuation `k s q` of the call `q` pending at `s` on an
answer typed by `Ans` is the image of `π.resume s a`, the loop of `body` from `π.init` embeds
`π` up to the call bound `D`. -/
theorem loopMulti_embedsUpTo [Inhabited O] (π : MultiHybrid σ E O Q A)
    (body : σ → Prog (E ⊕ A) (Q ⊕ O) σ) (k : σ → Q → A → Prog (E ⊕ A) (Q ⊕ O) σ)
    (Ans : Q → A → Prop) (D : σ → Q → ℕ)
    (hs : ∀ s e, act (body s) (.inl e) =
      SPComp.map (liftDecQ (fun s => .ret s) fun s q => callK (k s q)) (π.start s e))
    (hr : ∀ s q a, Ans q a → act (callK (k s q)) (.inr a) =
      SPComp.map (liftDecQ (fun s => .ret s) fun s q => callK (k s q)) (π.resume s a))
    (hsd : ∀ s e r q, IsOutcome (π.start s e) r → r.2 = .inl q → D r.1 q < π.fuel)
    (hrd : ∀ s q a r q', Ans q a → IsOutcome (π.resume s a) r → r.2 = .inl q' →
      D r.1 q' < D s q) :
    EmbedsUpTo π (loopMulti body π.init π.fuel) (fun s => .ret s) (fun s q => callK (k s q))
      Ans D where
  init := rfl
  fuel := rfl
  start s e := by
    change guardNF (act (body s) (.inl e)) _ = _
    rw [hs]
    exact guardNF_of_noFail _ (noFail_map _ (π.start_noFail s e))
  resume s q a ha := by
    change guardNF (act (callK (k s q)) (.inr a)) _ = _
    rw [hr s q a ha]
    exact guardNF_of_noFail _ (noFail_map _ (π.resume_noFail s a))
  start_depth := hsd
  resume_depth := hrd

end CatCrypt.Crypto.Party.Prog

namespace CatCrypt.Crypto.Party.IKNPProg

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.NonUniform CatCrypt.Relational
open CatCrypt.Crypto.OT CatCrypt.Crypto.OT.IKNPSquare CatCrypt.Crypto.OT.IKNPWake
open CatCrypt.Crypto.Choreography (ChannelCap)
open Prog (call callK outE recvO act emitK)
open MultiHybrid (EmbedsUpTo liftDecQ)
open scoped ENNReal

variable {κ m : ℕ} {M P L : Type}

/-! ## The parties as a program -/

/-- The events of the parties: inputs, wakes and corruption events, and the adversary events of
the base OTs and of the channel, which are forwarded. -/
abbrev PEv (κ m : ℕ) (M P : Type) := ((InEv m M ⊕ WakeEv κ) ⊕ P) ⊕ AEv κ m M

/-- The answers to the calls of the parties. -/
abbrev PAns (m : ℕ) (M : Type) := (HOut m ⊕ ChanHOut (Msg m M)) ⊕ AOut m M

/-- The calls of the parties: the honest port of the base OTs and the channel, and the
forwarded adversary events. -/
abbrev PCall (κ m : ℕ) (M : Type) := (HEv κ m ⊕ ChanHEv (Msg m M)) ⊕ AEv κ m M

/-- The outputs of the parties. -/
abbrev POut (m : ℕ) (M L : Type) := (InOut m M ⊕ L) ⊕ AOut m M

/-- The state of the parties: the randomness once drawn, the parties' record, and the unit
state of the forwarding of the adversary port. -/
abbrev PS (κ m : ℕ) (M : Type) := (Option (IKNPKey κ m) × PSt κ m M) × Unit

/-- Programs of the parties. -/
abbrev PP (κ m : ℕ) (M P L α : Type) :=
  Prog (PEv κ m M P ⊕ PAns m M) (PCall κ m M ⊕ POut m M L) α

/-- The default output of the parties: the sender's completion bit `false`. -/
instance : Inhabited (POut m M L) := ⟨.inl (.inl (.inl false))⟩

/-- The continuation of a call on the honest port: an adversary answer fails. -/
def lK {α : Type} (k : HOut m ⊕ ChanHOut (Msg m M) → PP κ m M P L α) :
    PAns m M → PP κ m M P L α
  | .inl a => k a
  | .inr _ => .fail

/-- Call the honest port of the base OTs and the channel with `q`, continuing with `k`. -/
def callL {α : Type} (q : HEv κ m ⊕ ChanHEv (Msg m M))
    (k : HOut m ⊕ ChanHOut (Msg m M) → PP κ m M P L α) : PP κ m M P L α :=
  call (.inl q) (lK k)

/-- Emit the output `o` of the parties and return the state `((ko, st), ())`. -/
def fin (ko : Option (IKNPKey κ m)) (st : PSt κ m M) (o : InOut m M ⊕ L) :
    PP κ m M P L (PS κ m M) :=
  ProgE.bind (outE (.inl o)) fun _ => .ret ((ko, st), ())

/-- The sender's choice bits `k.2 j, k.2 (j + 1), …` to the base OTs `j, j + 1, …`, then its
completion bit. -/
def sLoop (k : IKNPKey κ m) (ko : Option (IKNPKey κ m)) (st : PSt κ m M) (j : ℕ) :
    PP κ m M P L (PS κ m M) :=
  if h : j < κ then callL (sCall k j h) fun _ => sLoop k ko st (j + 1)
  else fin ko { st with ph := .idle } (.inl (.inl false))
termination_by κ - j

/-- The receiver's column pairs of `T` and `T + r` to the base OTs `j, j + 1, …`, then its
empty output. -/
def rLoop (k : IKNPKey κ m) (ko : Option (IKNPKey κ m)) (st : PSt κ m M) (j : ℕ) :
    PP κ m M P L (PS κ m M) :=
  if h : j < κ then callL (rCall k (st.ro.getD fun _ => false) j h) fun _ => rLoop k ko st (j + 1)
  else fin ko { st with ph := .idle } (.inl (.inr none))
termination_by κ - j

section Parties

variable [AddCommGroup M] (H : Fin m → (Fin κ → Bool) → M)
  {LS LR : Type} (φS : IKNPSenderView κ m Unit → LS)
  (φR : IKNPReceiverView κ m M Unit × (Fin m → M) → LR) (ans : Option LS → Option LR → P → L)

/-- The sender's step on the column fetched from the base OT `i`: keep it, and once every
column is present send the masked message pairs on the channel. -/
def fetchP (k : IKNPKey κ m) (ko : Option (IKNPKey κ m)) (st : PSt κ m M) (i : Fin κ) :
    HOut m ⊕ ChanHOut (Msg m M) → PP κ m M P L (PS κ m M)
  | .inl (.inr (some q)) =>
    let c := Function.update st.cols i (some q)
    match st.xo with
    | some x =>
      if allCols c && !st.ysent then
        callL (.inr (.send (iknpSenderMsg H x k.2 (colsVal c)))) fun _ =>
          fin ko { st with cols := c, ysent := true, ph := .idle } (.inl (.inl false))
      else fin ko { st with cols := c, ph := .idle } (.inl (.inl false))
    | none => fin ko { st with cols := c, ph := .idle } (.inl (.inl false))
  | _ => fin ko { st with ph := .idle } (.inl (.inl false))

/-- The receiver's step on the message read from the channel: output the unmasked messages. -/
def recvP (k : IKNPKey κ m) (ko : Option (IKNPKey κ m)) (st : PSt κ m M) :
    HOut m ⊕ ChanHOut (Msg m M) → PP κ m M P L (PS κ m M)
  | .inr (.got (some y)) => fin ko { st with yrecv := some y, ph := .idle }
      (.inl (.inr (some (iknpRecvOut H (st.ro.getD fun _ => false) k.1 y))))
  | _ => fin ko { st with ph := .idle } (.inl (.inr none))

/-- **One activation of the parties with randomness `k`** on an input, a wake or a corruption
event. -/
def partyStep (k : IKNPKey κ m) (ko : Option (IKNPKey κ m)) (st : PSt κ m M) :
    (InEv m M ⊕ WakeEv κ) ⊕ P → PP κ m M P L (PS κ m M)
  | .inl (.inl (.inl x)) => match st.xo with
    | some _ => fin ko st (.inl (.inl false))
    | none => sLoop k ko { st with xo := some x, ph := .idle } 0
  | .inl (.inl (.inr r)) => match st.ro with
    | some _ => fin ko st (.inl (.inr none))
    | none => rLoop k ko { st with ro := some r, ph := .idle } 0
  | .inl (.inr (.wakeS i)) => match st.xo with
    | some _ => callL (.inl (.inr (i, k.2 i))) (fetchP H k ko { st with ph := .idle } i)
    | none => fin ko st (.inl (.inl false))
  | .inl (.inr .wakeR) => match st.ro with
    | some _ => callL (.inr .recv) (recvP H k ko { st with ph := .idle })
    | none => fin ko st (.inl (.inr none))
  | .inr p => fin ko st (.inr (peekAns H φS φR ans k st p))

/-- An activation of the parties at the state `s`: the randomness is drawn uniformly at the
first activation that reads it (`partyUses`). -/
noncomputable def partyAct (s : PS κ m M) (e : (InEv m M ⊕ WakeEv κ) ⊕ P) :
    PP κ m M P L (PS κ m M) :=
  if s.1.1.isNone && partyUses s.1.2 e then
    Prog.sample (sampleFrom (ofPMF (PMF.uniformFintype (IKNPKey κ m)))) fun k =>
      partyStep H φS φR ans k (some k) s.1.2 e
  else partyStep H φS φR ans (s.1.1.getD default) s.1.1 s.1.2 e

/-- The forwarding of an adversary answer: output it and return the state. -/
def advK (s : PS κ m M) : PAns m M → PP κ m M P L (PS κ m M)
  | .inr o => ProgE.bind (outE (.inr o)) fun _ => .ret s
  | .inl _ => .fail

/-- **The IKNP parties as a program**: one iteration per activation. An event of a party is
answered by `partyAct`; an adversary event of the base OTs or of the channel is forwarded. -/
noncomputable def partyBody (s : PS κ m M) : PP κ m M P L (PS κ m M) :=
  ProgE.bind recvO fun
    | .inl e => partyAct H φS φR ans s e
    | .inr a => call (.inr a) (advK s)

/-- The hand-written parties with their own draw beside the forwarding of the adversary port. -/
noncomputable abbrev partyHW [NeZero κ] :=
  (partyLazy H φS φR ans).tensor (MultiHybrid.idSim (AEv κ m M) (AOut m M))

/-- The loop of `partyBody` as a multi-call hybrid over the base OTs beside the channel. -/
noncomputable def partyLoop [NeZero κ] :=
  Prog.loopMulti (partyBody H φS φR ans) (partyHW H φS φR ans).init (partyHW H φS φR ans).fuel

/-- **The IKNP protocol over the program parties**: the loop of `partyBody` over the `κ` base
OTs beside the channel, the corruption events on the adversary port. -/
noncomputable def realP [NeZero κ] :=
  ((partyLoop H φS φR ans).withSub ((baseG κ m).withChan (chanC m M))).mapPorts peekEv peekOut

/-! ## The embedding of the hand-written parties -/

/-- The continuation of the honest call pending at the hand-written state `s`, by its phase. -/
def contP (s : PS κ m M) : HOut m ⊕ ChanHOut (Msg m M) → PP κ m M P L (PS κ m M) :=
  match s.1.2.ph with
  | .sIn j => fun _ => sLoop (s.1.1.getD default) s.1.1 { s.1.2 with ph := .idle } (j + 1)
  | .rIn j => fun _ => rLoop (s.1.1.getD default) s.1.1 { s.1.2 with ph := .idle } (j + 1)
  | .fetch i => fetchP H (s.1.1.getD default) s.1.1 { s.1.2 with ph := .idle } i
  | .sendY => fun _ => fin s.1.1 { s.1.2 with ph := .idle } (.inl (.inl false))
  | .recvY => recvP H (s.1.1.getD default) s.1.1 { s.1.2 with ph := .idle }
  | .idle => fun _ => fin s.1.1 s.1.2 (.inl (.inl false))

/-- The continuation of the call `q` pending at the hand-written state `s`. -/
def partyK (s : PS κ m M) : PCall κ m M → PAns m M → PP κ m M P L (PS κ m M)
  | .inl _ => lK (contP H s)
  | .inr _ => advK s

/-- The answers typed by the calls: an honest call is answered on the honest port, a forwarded
adversary event on the adversary port. -/
def AnsT : PCall κ m M → PAns m M → Prop
  | .inl _, .inl _ => True
  | .inr _, .inr _ => True
  | _, _ => False

/-- The number of calls after the honest call pending in the phase of `st`. -/
def phD (st : PSt κ m M) : ℕ :=
  match st.ph with
  | .sIn j => κ - 1 - j
  | .rIn j => κ - 1 - j
  | .fetch _ => 1
  | _ => 0

/-- The call bound of the parties: `phD` for an honest call, `0` for a forwarded one. -/
def partyD (s : PS κ m M) : PCall κ m M → ℕ
  | .inl _ => phD s.1.2
  | .inr _ => 0

/-- The decision map of the embedding. -/
abbrev liftP : PS κ m M × (PCall κ m M ⊕ POut m M L) →
    PP κ m M P L (PS κ m M) × (PCall κ m M ⊕ POut m M L) :=
  liftDecQ (fun s => .ret s) fun s q => callK (partyK H s q)

/-- The emit phase of an activation of the parties with randomness `ko.getD default` is the
embedded first step `pStart`. -/
theorem emitK_partyStep [NeZero κ] (ko : Option (IKNPKey κ m)) (st : PSt κ m M)
    (e : (InEv m M ⊕ WakeEv κ) ⊕ P) :
    emitK (fun o p => SPComp.pure (p, o)) (fun _ => SPComp.fail)
        (partyStep H φS φR ans (ko.getD default) ko st e) =
      SPComp.pure (liftP H (((ko, (pStart H φS φR ans (ko.getD default) st e).1), ()),
        Sum.map Sum.inl Sum.inl (pStart H φS φR ans (ko.getD default) st e).2)) := by
  rcases e with ((x | r) | (i | _)) | p
  · cases hx : st.xo
    · simp only [partyStep, hx, pStart]
      rw [sLoop]
      simp only [show 0 < κ from NeZero.pos κ, ↓reduceDIte]
      rfl
    · simp only [partyStep, hx, pStart]
      rfl
  · cases hr : st.ro
    · simp only [partyStep, hr, pStart]
      rw [rLoop]
      simp only [show 0 < κ from NeZero.pos κ, ↓reduceDIte]
      rfl
    · simp only [partyStep, hr, pStart]
      rfl
  · cases hx : st.xo <;> simp only [partyStep, hx, pStart] <;> rfl
  · cases hr : st.ro <;> simp only [partyStep, hr, pStart] <;> rfl
  · rfl

/-- The emit phase of the continuation of a pending honest call is the embedded step
`pResume`. -/
theorem emitK_contP [NeZero κ] (s : PS κ m M) (o : HOut m ⊕ ChanHOut (Msg m M)) :
    emitK (fun o p => SPComp.pure (p, o)) (fun _ => SPComp.fail) (contP (P := P) H s o) =
      SPComp.pure (liftP H (((s.1.1, (pResume (L := L) H (s.1.1.getD default) s.1.2 o).1), ()),
        Sum.map Sum.inl Sum.inl (pResume (L := L) H (s.1.1.getD default) s.1.2 o).2)) := by
  obtain ⟨⟨ko, ⟨xo, ro, cols, ys, yr, ph⟩⟩, ⟨⟩⟩ := s
  cases ph with
  | idle => rfl
  | sIn j =>
    simp only [contP, pResume]
    rw [sLoop]
    by_cases h : j + 1 < κ <;> simp only [h, ↓reduceDIte] <;> rfl
  | rIn j =>
    simp only [contP, pResume]
    rw [rLoop]
    by_cases h : j + 1 < κ <;> simp only [h, ↓reduceDIte] <;> rfl
  | fetch i =>
    rcases o with (_ | (_ | q)) | (_ | (_ | y)) <;> try rfl
    simp only [contP, pResume, fetchP, pFetch]
    cases xo
    · rfl
    · simp only
      split <;> rfl
  | sendY => rfl
  | recvY => rcases o with (_ | (_ | q)) | (_ | (_ | y)) <;> rfl

/-- `emitK_partyStep` after the draw of the randomness `k`. -/
theorem emitK_partyStep_some [NeZero κ] (k : IKNPKey κ m) (st : PSt κ m M)
    (e : (InEv m M ⊕ WakeEv κ) ⊕ P) :
    emitK (fun o p => SPComp.pure (p, o)) (fun _ => SPComp.fail)
        (partyStep H φS φR ans k (some k) st e) =
      SPComp.pure (liftP H (((some k, (pStart H φS φR ans k st e).1), ()),
        Sum.map Sum.inl Sum.inl (pStart H φS φR ans k st e).2)) :=
  emitK_partyStep H φS φR ans (some k) st e

/-- **The start of the program parties** is the embedded start of the hand-written parties. -/
theorem act_partyBody [NeZero κ] (s : PS κ m M) (e : PEv κ m M P) :
    act (partyBody H φS φR ans s) (.inl e) =
      SPComp.map (liftP H) ((partyHW H φS φR ans).start s e) := by
  obtain ⟨⟨ko, st⟩, ⟨⟩⟩ := s
  rcases e with e | a
  · simp only [partyBody, Prog.act_def, Prog.stepWith_def, Prog.awaitK_recvO_bind, partyAct]
    by_cases hu : (ko.isNone && partyUses st e) = true
    · obtain ⟨rfl, hu2⟩ : ko = none ∧ partyUses st e = true := by simpa using hu
      simp [hu2, Prog.emitK_sample, emitK_partyStep_some, partyHW, partyLazy,
        MultiHybrid.lazyKey, MultiHybrid.tensor, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    · have hu' : ¬(ko = none ∧ partyUses st e = true) := by simpa using hu
      simp [hu, hu', emitK_partyStep, partyHW, partyLazy, MultiHybrid.lazyKey,
        MultiHybrid.tensor, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · simp only [partyHW, MultiHybrid.tensor, MultiHybrid.idSim, Sum.elim_inr, SPComp.map,
      SPComp.pure_bind]
    rfl

/-- **The resumption of the program parties** at an answer typed by the pending call is the
embedded resumption of the hand-written parties. -/
theorem act_partyK [NeZero κ] (s : PS κ m M) (q : PCall κ m M) (a : PAns m M)
    (ha : AnsT q a) :
    act (callK (partyK (P := P) (L := L) H s q)) (.inr a) =
      SPComp.map (liftP H) ((partyHW H φS φR ans).resume s a) := by
  obtain ⟨⟨ko, st⟩, ⟨⟩⟩ := s
  rcases q with q | q <;> rcases a with a | a <;> simp only [AnsT] at ha
  · refine (emitK_contP (P := P) (L := L) H _ a).trans ?_
    simp [partyHW, partyLazy, MultiHybrid.lazyKey, MultiHybrid.tensor, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]
  · simp only [partyHW, MultiHybrid.tensor, MultiHybrid.idSim, Sum.elim_inr, SPComp.map,
      SPComp.pure_bind]
    rfl

omit [AddCommGroup M] in
/-- A call of the first step is followed by fewer calls than the fuel `κ + 1`. -/
theorem pStart_depth [AddCommGroup M] [NeZero κ] (k : IKNPKey κ m) (st : PSt κ m M)
    (e : (InEv m M ⊕ WakeEv κ) ⊕ P) (q : HEv κ m ⊕ ChanHEv (Msg m M))
    (h : (pStart H φS φR ans k st e).2 = .inl q) :
    phD (pStart H φS φR ans k st e).1 < κ + 1 := by
  have hκ := NeZero.pos κ
  rcases e with ((x | r) | (i | _)) | p
  · cases hx : st.xo <;> simp_all [pStart, phD]
  · cases hr : st.ro <;> simp_all [pStart, phD]
  · cases hx : st.xo <;> simp_all [pStart, phD]
  · cases hr : st.ro <;> simp_all [pStart, phD]
  · simp [pStart] at h

/-- A call of a resumption is followed by fewer calls than the pending one. -/
theorem pResume_depth (k : IKNPKey κ m) (st : PSt κ m M) (o : HOut m ⊕ ChanHOut (Msg m M))
    (q : HEv κ m ⊕ ChanHEv (Msg m M)) (h : (pResume (L := L) H k st o).2 = .inl q) :
    phD (pResume (L := L) H k st o).1 < phD st := by
  obtain ⟨xo, ro, cols, ys, yr, ph⟩ := st
  cases ph with
  | sIn j =>
    by_cases hj : j + 1 < κ <;> simp_all [pResume, phD]
    omega
  | rIn j =>
    by_cases hj : j + 1 < κ <;> simp_all [pResume, phD]
    omega
  | fetch i =>
    rcases o with (_ | (_ | q')) | (_ | (_ | y)) <;> simp_all [pResume, phD]
    simp only [pFetch] at h ⊢
    cases xo <;> simp_all
    grind
  | idle => simp [pResume] at h
  | sendY => simp [pResume] at h
  | recvY => rcases o with (_ | (_ | q')) | (_ | (_ | y)) <;> simp_all [pResume]

omit [AddCommGroup M] in
/-- The base OTs beside the channel answer each call on the port of the call. -/
theorem sub_ans (t : SubSt κ m M) (q : PCall κ m M) (r : SubSt κ m M × PAns m M)
    (hr : IsOutcome (((baseG κ m).withChan (chanC m M)).step t q) r) : AnsT q r.2 := by
  rcases q with q | q
  · rw [sub_step_inl] at hr
    obtain ⟨_, _, rfl⟩ := exists_of_isOutcome_map hr
    trivial
  · rw [sub_step_inr] at hr
    obtain ⟨_, _, rfl⟩ := exists_of_isOutcome_map hr
    trivial

/-- The fuel of the hand-written parties. -/
theorem partyHW_fuel [NeZero κ] : (partyHW (P := P) (L := L) H φS φR ans).fuel = κ + 1 := by
  simp [partyHW, MultiHybrid.tensor, MultiHybrid.lazyKey, partyLazy, partyW, MultiHybrid.idSim]

/-- An image under `Sum.map Sum.inl Sum.inl` that is a call is the image of a call. -/
theorem sumMap_eq_inl {α β γ δ : Type} {x : α ⊕ β} {q : α ⊕ γ}
    (h : Sum.map Sum.inl (Sum.inl : β → β ⊕ δ) x = .inl q) : ∃ q', x = .inl q' ∧ q = .inl q' := by
  rcases x with q' | o
  · exact ⟨q', rfl, (Sum.inl.inj h).symm⟩
  · simp at h

/-- **The program parties embed the hand-written parties** up to the typed answers and the call
bound `partyD`. -/
theorem partyLoop_embeds [NeZero κ] :
    EmbedsUpTo (partyHW H φS φR ans) (partyLoop H φS φR ans) (fun s => .ret s)
      (fun s q => callK (partyK H s q)) AnsT partyD := by
  refine Prog.loopMulti_embedsUpTo _ _ _ _ _ (act_partyBody H φS φR ans)
    (act_partyK H φS φR ans) ?_ ?_
  · rintro ⟨⟨ko, st⟩, ⟨⟩⟩ (e | a) r q hr hq
    · rw [partyHW_fuel]
      simp only [partyHW, MultiHybrid.tensor, Sum.elim_inl, partyLazy, MultiHybrid.lazyKey,
        partyW_start] at hr
      obtain ⟨r', hr', rfl⟩ := exists_of_isOutcome_map hr
      obtain ⟨k, ko', rfl⟩ : ∃ k ko', r' =
          ((ko', (pStart H φS φR ans k st e).1), (pStart H φS φR ans k st e).2) := by
        split at hr'
        · obtain ⟨k, -, hk⟩ := isOutcome_bind hr'
          obtain ⟨r'', h1, rfl⟩ := exists_of_isOutcome_map hk
          exact ⟨k, some k, by rw [← isOutcome_pure h1]⟩
        · obtain ⟨r'', h1, rfl⟩ := exists_of_isOutcome_map hr'
          exact ⟨_, ko, by rw [← isOutcome_pure h1]⟩
      obtain ⟨q', hq', rfl⟩ := sumMap_eq_inl hq
      exact pStart_depth H φS φR ans k st e q' hq'
    · simp only [partyHW, MultiHybrid.tensor, MultiHybrid.idSim, Sum.elim_inr, SPComp.map,
        SPComp.pure_bind] at hr
      obtain rfl := (isOutcome_pure hr).symm
      simp only [Sum.map_inl, Sum.inl.injEq] at hq
      subst hq
      simp [partyD, partyHW_fuel]
  · rintro ⟨⟨ko, st⟩, ⟨⟩⟩ (q | q) (a | a) r q' ha hr hq <;> simp only [AnsT] at ha
    · simp only [partyHW, MultiHybrid.tensor, Sum.elim_inl, partyLazy, MultiHybrid.lazyKey,
        partyW_resume, SPComp.map, SPComp.pure_bind] at hr
      obtain rfl := (isOutcome_pure hr).symm
      obtain ⟨q'', hq'', rfl⟩ := sumMap_eq_inl hq
      exact pResume_depth H _ st a q'' hq''
    · simp only [partyHW, MultiHybrid.tensor, MultiHybrid.idSim, Sum.elim_inr, SPComp.map,
        SPComp.pure_bind] at hr
      obtain rfl := (isOutcome_pure hr).symm
      simp at hq

/-- **The program parties are step-equivalent to the hand-written parties** with their own
draw, over the base OTs beside the channel. -/
theorem partyLoop_stepEq [NeZero κ] :
    Sys.StepEq ⟨_, (partyHW H φS φR ans).withSub ((baseG κ m).withChan (chanC m M))⟩
      ⟨_, (partyLoop H φS φR ans).withSub ((baseG κ m).withChan (chanC m M))⟩ :=
  (partyLoop_embeds H φS φR ans).stepEq _ sub_ans

/-- **The program protocol has the view of the IKNP protocol** `iknpW`. -/
theorem view_realP_eq [NeZero κ] {ζ : Type}
    (Z : Strat ζ ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P)) (InOut m M ⊕ (AOut m M ⊕ L))) :
    view (realP H φS φR ans) Z = view (iknpW H φS φR ans) Z := by
  rw [view_iknpW_eq_lazy]
  refine (view_eq_of_stepMap (realLazyW H φS φR ans) (realP H φS φR ans)
    (fun t => (.ret t.1, t.2)) rfl (fun t e => ?_) Z).symm
  exact Sys.mapPorts_stepMap
    (fun t : PS κ m M × SubSt κ m M => ((ProgE.ret t.1 : PP κ m M P L (PS κ m M)), t.2))
    (fun t g => ((partyLoop_embeds H φS φR ans).withSub_step _ sub_ans t.1 t.2 g).symm)
    peekEv peekOut t e

end Parties

/-! ## The simulator as a program -/

section Simulator

variable [Zero M] {LS LR EGA OGA : Type} [Countable LS] [Countable LR]
  (ans : Option LS → Option LR → P → L) (sch : SchedEv → EGA) (stat : OGA → Bool × Bool)
  (pkEv : EGA) (simS : OGA → SPComp LS) (simR : OGA → SPComp LR)

/-- Programs of the simulator: the interface of the protocol outside, calls to the ideal
functionality. -/
abbrev SP (κ m : ℕ) (M P L EGA OGA α : Type) :=
  Prog (((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P)) ⊕ (InOut m M ⊕ OGA))
    ((InEv m M ⊕ EGA) ⊕ (InOut m M ⊕ (AOut m M ⊕ L))) α

/-- The default output of the simulator: the sender's completion bit `false`. -/
instance : Inhabited (InOut m M ⊕ (AOut m M ⊕ L)) := ⟨outS⟩

/-- Emit the output `o` of the simulator and return the state `s`. -/
def sfin (s : SSt κ m M LS LR) (o : InOut m M ⊕ (AOut m M ⊕ L)) :
    SP κ m M P L EGA OGA (SSt κ m M LS LR) :=
  ProgE.bind (outE o) fun _ => .ret s

/-- The answer to a forwarded input, or to the receiver's choice: passed on. -/
def honK (s : SSt κ m M LS LR) : InOut m M ⊕ OGA → SP κ m M P L EGA OGA (SSt κ m M LS LR)
  | .inl o => sfin s (.inl o)
  | .inr _ => sfin s outS

/-- The input status, for a poll of a base OT. -/
def cpollK (s : SSt κ m M LS LR) : InOut m M ⊕ OGA → SP κ m M P L EGA OGA (SSt κ m M LS LR)
  | .inl _ => sfin s (outA .ack)
  | .inr a => sfin s (outA (.status (stat a).2 (stat a).1))

/-- The input status, for a delivery of the base OT `i`. -/
def cdelK (s : SSt κ m M LS LR) (i : Fin κ) :
    InOut m M ⊕ OGA → SP κ m M P L EGA OGA (SSt κ m M LS LR)
  | .inl _ => sfin s (outA .ack)
  | .inr a => if (stat a).1 && (stat a).2 && !s.dR i then
      sfin { s with dR := Function.update s.dR i true } (outA .ack)
    else sfin s (outA .ack)

/-- The corrupt sender's view, drawn by `simS`. -/
noncomputable def revK (s : SSt κ m M LS LR) :
    InOut m M ⊕ OGA → SP κ m M P L EGA OGA (SSt κ m M LS LR)
  | .inr a => Prog.sample (simS a) fun v => sfin { s with lvS := some v } outS
  | .inl _ => sfin s outS

/-- The corrupt receiver's view, drawn by `simR`, then the receiver's choice. -/
noncomputable def wR2K (s : SSt κ m M LS LR) :
    InOut m M ⊕ OGA → SP κ m M P L EGA OGA (SSt κ m M LS LR)
  | .inr a => Prog.sample (simR a) fun v =>
      call (.inl (.inr dummyC)) (honK { s with lvR := some v })
  | .inl _ => call (.inl (.inr dummyC)) (honK s)

/-- After the delivery to the receiver: the corrupt receiver's view, if not yet drawn, then the
receiver's choice. -/
noncomputable def wR1K (s : SSt κ m M LS LR) :
    InOut m M ⊕ OGA → SP κ m M P L EGA OGA (SSt κ m M LS LR) :=
  fun _ => if s.lvR.isNone then call (.inr pkEv) (wR2K simR s)
    else call (.inl (.inr dummyC)) (honK s)

/-- **One activation of the simulator** on an event of the interface of the protocol. -/
noncomputable def simAct (s : SSt κ m M LS LR) :
    (InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P) → SP κ m M P L EGA OGA (SSt κ m M LS LR)
  | .inl (.inl e) => call (.inl e) (honK { s with ph := .idle })
  | .inl (.inr (.wakeS i)) =>
    if s.dR i && !s.col i then
      if allB (Function.update s.col i true) && !s.ysent then
        call (.inr pkEv) (revK simS
          { s with
            col := Function.update s.col i true, ysent := true,
            ch := (FChan.honStep s.ch (.send y0)).1, ph := .idle })
      else sfin { s with col := Function.update s.col i true } outS
    else sfin s outS
  | .inl (.inr .wakeR) => match s.ch.inbox with
    | [] => sfin s (.inl (.inr none))
    | _ :: rest => call (.inr (sch .deliverRecv))
        (wR1K pkEv simR { s with ch := ⟨s.ch.queue, s.ch.cursor, rest⟩, ph := .idle })
  | .inr (.inl (.inl (i, ev))) => match ev with
    | .idle => sfin s (outA .ack)
    | .poll => call (.inr (sch .poll)) (cpollK stat { s with ph := .idle })
    | .deliverRecv => call (.inr (sch .poll)) (cdelK stat { s with ph := .idle } i)
    | .deliverSend => sfin s (outA .ack)
  | .inr (.inl (.inr d)) =>
    sfin { s with ch := (FChan.advStep ChannelCap.secure msgLeak s.ch d).1 }
      (.inr (.inl (.inr (FChan.advStep ChannelCap.secure msgLeak s.ch d).2)))
  | .inr (.inr p) => sfin s (.inr (.inr (ans s.lvS s.lvR p)))

/-- **The IKNP simulator as a program**: one iteration per activation. -/
noncomputable def simBody (s : SSt κ m M LS LR) : SP κ m M P L EGA OGA (SSt κ m M LS LR) :=
  ProgE.bind recvO (simAct ans sch stat pkEv simS simR s)

/-- The loop of `simBody` as a multi-call hybrid over the ideal functionality, with fuel `3`. -/
noncomputable def simLoop :
    MultiHybrid (SP κ m M P L EGA OGA (SSt κ m M LS LR)) ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P))
      (InOut m M ⊕ (AOut m M ⊕ L)) (InEv m M ⊕ EGA) (InOut m M ⊕ OGA) :=
  Prog.loopMulti (simBody ans sch stat pkEv simS simR) SSt.init 3

/-- The continuation of the call pending at the hand-written state `s`, by its phase. -/
noncomputable def contS (s : SSt κ m M LS LR) :
    InOut m M ⊕ OGA → SP κ m M P L EGA OGA (SSt κ m M LS LR) :=
  match s.ph with
  | .idle => fun _ => sfin { s with ph := .idle } outS
  | .fwd => honK { s with ph := .idle }
  | .cpoll _ => cpollK stat { s with ph := .idle }
  | .cdel i => cdelK stat { s with ph := .idle } i
  | .revS => revK simS { s with ph := .idle }
  | .wR1 => wR1K pkEv simR { s with ph := .idle }
  | .wR2 => wR2K simR { s with ph := .idle }
  | .wR3 => honK { s with ph := .idle }

/-- The call bound of the simulator: the calls after the delivery to the receiver. -/
def simD (s : SSt κ m M LS LR) (_ : InEv m M ⊕ EGA) : ℕ :=
  match s.ph with
  | .wR1 => 2
  | .wR2 => 1
  | _ => 0

/-- **The simulator program embeds `simW`** up to the call bound `simD`. -/
theorem simLoop_embeds (hS : ∀ a, SPComp.NoFail (simS a)) (hR : ∀ a, SPComp.NoFail (simR a)) :
    EmbedsUpTo (simW ans sch stat pkEv simS simR hS hR (κ := κ) (m := m) (M := M))
      (simLoop ans sch stat pkEv simS simR) (fun s => .ret s)
      (fun s _ => callK (contS stat pkEv simS simR s)) (fun _ _ => True) simD := by
  refine Prog.loopMulti_embedsUpTo _ _ (fun s _ => contS stat pkEv simS simR s) _ _ ?_ ?_ ?_ ?_
  · intro s e
    simp only [simW, SPComp.map, SPComp.pure_bind]
    rcases e with (e | (i | _)) | ((⟨i, ev⟩ | d) | p) <;> try rfl
    · simp only [simBody, simAct, simStart, Prog.act_def, Prog.stepWith_def,
        Prog.awaitK_recvO_bind]
      by_cases h1 : (s.dR i && !s.col i) = true <;>
        by_cases h2 : (allB (Function.update s.col i true) && !s.ysent) = true <;>
        simp only [h1, h2, ↓reduceIte, Bool.false_eq_true] <;> rfl
    · simp only [simBody, simAct, simStart, Prog.act_def, Prog.stepWith_def,
        Prog.awaitK_recvO_bind]
      cases s.ch.inbox <;> rfl
    · cases ev <;> rfl
  · intro s q a _
    obtain ⟨dR, col, ys, ch, lvS, lvR, ph⟩ := s
    cases ph <;> rcases a with o | a <;>
      simp only [simW, simResume, simResA, SPh.isHon, Bool.false_eq_true, ↓reduceIte,
        SPComp.map, SPComp.pure_bind] <;> try rfl
    all_goals simp only [contS, Prog.act_def, Prog.stepWith_def, Prog.emitK_callK, cdelK, revK,
      wR1K, wR2K, Prog.emitK_sample, SPComp.bind_assoc, SPComp.pure_bind]
    all_goals (try split_ifs) <;> (try simp only [SPComp.pure_bind]) <;> rfl
  · intro s e r q _ _
    change simD r.1 q < 3
    unfold simD
    split <;> omega
  · intro s q a r q' _ hr hq
    obtain ⟨dR, col, ys, ch, lvS, lvR, ph⟩ := s
    change IsOutcome (simResume stat pkEv simS simR _ a) r at hr
    cases ph <;> rcases a with o | a <;>
      simp only [simResume, simResA, SPh.isHon, Bool.false_eq_true, ↓reduceIte] at hr
    all_goals (try split_ifs at hr)
    all_goals first
      | obtain rfl := isOutcome_pure hr; simp_all [simD]
      | obtain ⟨v, -, rfl⟩ := exists_of_isOutcome_map hr; simp_all [simD]

/-- **The simulator program is step-equivalent to `simW`** over every ideal functionality. -/
theorem simLoop_stepEq (hS : ∀ a, SPComp.NoFail (simS a)) (hR : ∀ a, SPComp.NoFail (simR a))
    {υ : Type} (X : Sys υ (InEv m M ⊕ EGA) (InOut m M ⊕ OGA)) :
    Sys.StepEq ⟨_, (simW ans sch stat pkEv simS simR hS hR (κ := κ)).withSub X⟩
      ⟨_, (simLoop ans sch stat pkEv simS simR).withSub X⟩ :=
  (simLoop_embeds ans sch stat pkEv simS simR hS hR).stepEq X fun _ _ _ _ => trivial

/-! ## Opacity of the simulator program, by information flow -/

/-- The view of the sum interface of the simulator. -/
abbrev simView (κ m : ℕ) (M P L EGA OGA : Type) :=
  PubView.callView (outerV κ m M P L) (innerV m M EGA OGA)

omit [Zero M] [Countable LS] [Countable LR] in
/-- Every decision of the simulator is related to itself. -/
theorem simView_out_refl (d : (InEv m M ⊕ EGA) ⊕ (InOut m M ⊕ (AOut m M ⊕ L))) :
    (simView κ m M P L EGA OGA).out d d := by
  rcases d with (g | g) | (o | o)
  · exact Sum.LiftRel.inl trivial
  · exact Sum.LiftRel.inr rfl
  · exact Sum.LiftRel.inl trivial
  · exact Sum.LiftRel.inr rfl

omit [Zero M] [Countable LS] [Countable LR] in
/-- The continuation of a call is related to itself when its branches at related answers are. -/
theorem callK_viewRel {k : InOut m M ⊕ OGA → SP κ m M P L EGA OGA (SSt κ m M LS LR)}
    (h : ∀ a a', (innerV m M EGA OGA).out a a' →
      ProgE.ViewRel (simView κ m M P L EGA OGA) Eq (k a) (k a')) :
    ProgE.ViewRel (simView κ m M P L EGA OGA) Eq (callK k) (callK k) :=
  ProgE.ViewRel.recv fun x x' hx => by
    cases hx with
    | inl _ => exact ProgE.ViewRel.fail
    | inr ha => exact h _ _ ha

omit [Zero M] [Countable LS] [Countable LR] in
/-- A call is related to itself when its continuation is. -/
theorem call_viewRel (q : InEv m M ⊕ EGA)
    {k : InOut m M ⊕ OGA → SP κ m M P L EGA OGA (SSt κ m M LS LR)}
    (h : ∀ a a', (innerV m M EGA OGA).out a a' →
      ProgE.ViewRel (simView κ m M P L EGA OGA) Eq (k a) (k a')) :
    ProgE.ViewRel (simView κ m M P L EGA OGA) Eq (call q k) (call q k) :=
  ProgE.ViewRel.send (simView_out_refl (.inl q)) (callK_viewRel h)

omit [Zero M] [Countable LS] [Countable LR] in
/-- An output and return is related to itself. -/
theorem sfin_viewRel (s : SSt κ m M LS LR) (o : InOut m M ⊕ (AOut m M ⊕ L)) :
    ProgE.ViewRel (simView κ m M P L EGA OGA) Eq
      (sfin (EGA := EGA) (OGA := OGA) s o) (sfin s o) :=
  ProgE.ViewRel.send (simView_out_refl (.inr o)) (ProgE.ViewRel.ret rfl)

omit [Zero M] [Countable LS] [Countable LR] in
/-- A draw is related to itself when its continuations are. -/
theorem sample_viewRel {β : Type} [Countable β] (μ : SPComp β)
    {k : β → SP κ m M P L EGA OGA (SSt κ m M LS LR)}
    (h : ∀ b, ProgE.ViewRel (simView κ m M P L EGA OGA) Eq (k b) (k b)) :
    ProgE.ViewRel (simView κ m M P L EGA OGA) Eq (Prog.sample μ k) (Prog.sample μ k) := by
  unfold Prog.sample
  refine ProgE.ViewRel.opN _ fun n => ?_
  split
  · exact h _
  · exact ProgE.ViewRel.fail

omit [Zero M] [Countable LS] [Countable LR] in
/-- The answer to a forwarded input is related at related answers. -/
theorem honK_viewRel (s : SSt κ m M LS LR) (a a' : InOut m M ⊕ OGA)
    (h : (innerV m M EGA OGA).out a a') :
    ProgE.ViewRel (simView κ m M P L EGA OGA) Eq (honK (P := P) (L := L) s a) (honK s a') := by
  cases h with
  | inl _ =>
    exact ProgE.ViewRel.send
      (show (outerV κ m M P L).out (.inl _) (.inl _) from Sum.LiftRel.inl trivial)
      (ProgE.ViewRel.ret rfl)
  | inr h => subst h; exact sfin_viewRel s _

/-- **The simulator program is related to itself** for the view of its sum interface: it reads
no input value and no output on the honest port of the ideal functionality. -/
theorem simBody_viewRel (s : SSt κ m M LS LR) :
    ProgE.ViewRel (simView κ m M P L EGA OGA) Eq (simBody ans sch stat pkEv simS simR s)
      (simBody ans sch stat pkEv simS simR s) := by
  have hign : ∀ (k : SP κ m M P L EGA OGA (SSt κ m M LS LR)),
      ProgE.ViewRel (simView κ m M P L EGA OGA) Eq k k →
      ∀ (f : InOut m M ⊕ OGA → SP κ m M P L EGA OGA (SSt κ m M LS LR)),
      (∀ o, f (.inl o) = k) → (∀ a, ProgE.ViewRel (simView κ m M P L EGA OGA) Eq
        (f (.inr a)) (f (.inr a))) →
      ∀ a a', (innerV m M EGA OGA).out a a' →
        ProgE.ViewRel (simView κ m M P L EGA OGA) Eq (f a) (f a') := by
    intro k hk f hf hr a a' h
    cases h with
    | inl _ => rw [hf, hf]; exact hk
    | inr h => subst h; exact hr _
  have hwR2 : ∀ s' : SSt κ m M LS LR, ∀ a a', (innerV m M EGA OGA).out a a' →
      ProgE.ViewRel (simView κ m M P L EGA OGA) Eq (wR2K (P := P) (L := L) simR s' a)
        (wR2K simR s' a') := fun s' =>
    hign _ (call_viewRel _ (honK_viewRel s')) _ (fun _ => rfl)
      fun _ => sample_viewRel _ fun _ => call_viewRel _ (honK_viewRel _)
  unfold simBody
  refine ProgE.ViewRel.bind (RA := (outerV κ m M P L).ev) ?_ fun e e' he => ?_
  · refine ProgE.ViewRel.recv fun x x' hx => ?_
    cases hx with
    | inl h => exact ProgE.ViewRel.ret h
    | inr _ => exact ProgE.ViewRel.fail
  · rcases he with ((h | h) | h) | h
    · exact ProgE.ViewRel.send
        (show (innerV m M EGA OGA).ev (.inl _) (.inl _) from Sum.LiftRel.inl trivial)
        (callK_viewRel (honK_viewRel _))
    · subst h
      rename_i w
      rcases w with i | _
      · simp only [simAct]
        split
        · split
          · exact call_viewRel _ (hign _ (sfin_viewRel _ _) _ (fun _ => rfl)
              fun _ => sample_viewRel _ fun _ => sfin_viewRel _ _)
          · exact sfin_viewRel _ _
        · exact sfin_viewRel _ _
      · simp only [simAct]
        split
        · exact sfin_viewRel _ _
        · refine call_viewRel _ fun a a' _ => ?_
          simp only [wR1K]
          split
          · exact call_viewRel _ (hwR2 _)
          · exact call_viewRel _ (honK_viewRel _)
    · subst h
      rename_i a
      rcases a with (⟨i, ev⟩ | d) | p
      · cases ev
        · exact sfin_viewRel _ _
        · exact call_viewRel _ (hign _ (sfin_viewRel _ _) _ (fun _ => rfl)
            fun _ => sfin_viewRel _ _)
        · refine call_viewRel _ (hign _ (sfin_viewRel _ _) _ (fun _ => rfl) fun _ => ?_)
          simp only [cdelK]
          split
          · exact sfin_viewRel _ _
          · exact sfin_viewRel _ _
        · exact sfin_viewRel _ _
      · exact sfin_viewRel _ _
      · exact sfin_viewRel _ _

/-- **Opacity of the simulator program**, derived from information flow of its loop
(`Prog.loopSys_opaque`) and transferred to the multi-call hybrid (`MultiHybrid.opaque_ofSys`). -/
theorem simLoop_opaque :
    (simLoop ans sch stat pkEv simS simR (κ := κ) (m := m) (M := M)).Opaque
      (outerV κ m M P L) (innerV m M EGA OGA) :=
  MultiHybrid.opaque_ofSys
    (Prog.loopSys_opaque _ _ rfl fun s _ hs => hs ▸ simBody_viewRel ans sch stat pkEv simS simR s)
    (Sum.LiftRel.inl trivial) 3

/-- **The IKNP simulator program** as a bundled opaque simulator. -/
noncomputable def simP :
    Simulator ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P)) (InOut m M ⊕ (AOut m M ⊕ L))
      (InEv m M ⊕ EGA) (InOut m M ⊕ OGA) (outerV κ m M P L) (innerV m M EGA OGA) :=
  Simulator.ofMultiHybrid (simLoop ans sch stat pkEv simS simR)
    (simLoop_opaque ans sch stat pkEv simS simR)

/-- The time of one iteration of the simulator program at unit weight. -/
theorem simBody_bound (s : SSt κ m M LS LR) :
    ProgE.Bound (fun _ => 1) (simBody ans sch stat pkEv simS simR s) 10 (fun _ => True) := by
  party_derive

/-- **Time certificate of the simulator program**: its first `q` iterations cost at most
`10 q` at unit weight, every receive, send and draw one unit. -/
theorem simLoop_time (q : ℕ) :
    ProgE.Bound (fun _ => 1) (ProgE.iterate (simBody ans sch stat pkEv simS simR) q
      (SSt.init : SSt κ m M LS LR))
      (q * 10 + 0 * (q * (q - 1) / 2)) (fun _ => True) :=
  (ProgE.LoopBoundGraded.of_bound (Inv := fun _ => True) trivial
    fun s _ => simBody_bound ans sch stat pkEv simS simR s).iterate_time_le q

end Simulator

/-! ## Realization through the program forms -/

section Realize

variable [AddCommGroup M] (H : Fin m → (Fin κ → Bool) → M) [NeZero κ]

/-- **Realization transfers to the program forms.** A realization of `I` by the IKNP protocol
`iknpW` behind the simulator `simW` with bound `b` is a realization of `I` by the program
protocol `realP` behind the simulator program `simP`, with the same bound. -/
theorem realizesSim_prog {LS LR EGA OGA : Type} [Countable LS] [Countable LR]
    (φS : IKNPSenderView κ m Unit → LS) (φR : IKNPReceiverView κ m M Unit × (Fin m → M) → LR)
    (ans : Option LS → Option LR → P → L) (sch : SchedEv → EGA) (stat : OGA → Bool × Bool)
    (pkEv : EGA) (simS : OGA → SPComp LS) (simR : OGA → SPComp LR)
    (hS : ∀ a, SPComp.NoFail (simS a)) (hR : ∀ a, SPComp.NoFail (simR a)) {υ : Type}
    {I : Sys υ (InEv m M ⊕ EGA) (InOut m M ⊕ OGA)}
    {b : (ζ : Type) → Env (Strat ζ ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P))
      (InOut m M ⊕ (AOut m M ⊕ L))) ζ → ℝ≥0∞}
    (h : RealizesSim (iknpW H φS φR ans) I
      (Simulator.ofMultiHybrid (simW ans sch stat pkEv simS simR hS hR)
        (simW_opaque ans sch stat pkEv simS simR hS hR)) b) :
    RealizesSim (realP H φS φR ans) I (simP ans sch stat pkEv simS simR) b := by
  refine (Sys.traceEq_iff_view_eq.mpr fun ζ Z =>
    view_realP_eq H φS φR ans Z).symm.realizes_left ?_
  exact fun ζ Z => le_of_le_of_eq ((Realizes.trans h
    (Sys.StepEq.realizes (simLoop_stepEq ans sch stat pkEv simS simR hS hR I)).1) ζ Z)
    (add_zero _)

/-- **IKNP with both parties honest, in the party language.** Ideal functionality:
`FOTSched otChoose`. Real protocol: the program parties `realP` over `κ` scheduled base OTs
beside the secure channel, with no corruption event. Simulator: the program `simP` of the
honest simulator. Distance `0`, as `iknpH_realizesSim`. -/
theorem iknpH_realizesSim_prog :
    RealizesSim (realP H (fun _ : IKNPSenderView κ m Unit => ())
        (fun _ : IKNPReceiverView κ m M Unit × (Fin m → M) => ()) ansH)
      (FOTSched otChoose)
      (simP ansH id statSched .poll (fun _ => SPComp.pure ()) (fun _ => SPComp.pure ()))
      (fun _ _ => 0) :=
  realizesSim_prog H _ _ _ _ _ _ _ _ _ _ (iknpH_realizesSim H)

/-- **IKNP against a semi-honest corrupt sender, in the party language.** Ideal functionality:
`FOTSchedSH otChoose leakSend`. Real protocol: the program parties `realP`, the corruption event
showing the sender's secret and columns once it has sent. Simulator: the program `simP` of the
simulator that draws the sender's view by `iknpSimS`. Distance `0`, as `iknpS_realizesSim`. -/
theorem iknpS_realizesSim_prog :
    RealizesSim (realP H (fun v : IKNPSenderView κ m Unit => v)
        (fun _ : IKNPReceiverView κ m M Unit × (Fin m → M) => ()) ansS)
      (FOTSchedSH otChoose leakSend)
      (simP ansS .inl statSH (.inr ())
        (fun _ => iknpSimS (fun _ _ => SPComp.pure ()) (fun _ => ((0 : M), (0 : M))))
        (fun _ => SPComp.pure ()))
      (fun _ _ => 0) :=
  realizesSim_prog H _ _ _ _ _ _ _ _ _ _ (iknpS_realizesSim H)

/-- **IKNP against a semi-honest corrupt receiver, in the party language.** Ideal functionality:
`FOTSchedSH otChoose (leakRecv otChoose)`. Real protocol: the program parties `realP`, the
corruption event showing the receiver's matrix, the masked message pairs and its output.
Simulator: the program `simP` of the simulator that completes the receiver's view by
`iknpSimR`. Bound: the correlation-robust hash advantage of `iknpWakeCRRed H Z`, as
`iknpR_realizesSim`. -/
theorem iknpR_realizesSim_prog [Fintype M] [Nonempty M] :
    RealizesSim (realP H (fun _ : IKNPSenderView κ m Unit => ()) (fun v : RView κ m M => v) ansR)
      (FOTSchedSH otChoose (leakRecv otChoose))
      (simP ansR .inl statSH (.inr ()) (fun _ => SPComp.pure ()) (simRR H))
      (fun _ Z => CRHash_Advantage H (iknpWakeCRRed H Z)) :=
  realizesSim_prog H _ _ _ _ _ _ _ _ _ _ (iknpR_realizesSim H)

end Realize

end CatCrypt.Crypto.Party.IKNPProg
