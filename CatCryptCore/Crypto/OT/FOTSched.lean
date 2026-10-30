/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCChannel

/-!
# Oblivious transfer with adversarially scheduled delivery

**Ideal functionality.** `FOTSched out` is the oblivious-transfer functionality of Canetti,
Lindell, Ostrovsky and Sahai (STOC 2002) with delayed outputs, generic in the sender's input `X`,
the receiver's choice `C` and the receiver's output `Y`, with the output map `out : X → C → Y`.
The 1-out-of-2 transfer of messages in `M` is `out = otSel` with `X = M × M` and `C = Bool`; the
batched transfer of `m` message pairs with a choice vector is `out = otChoose`. The functionality
has three ports, all on one shared state (`Sys.ofPorts`):

* the sender port: the first input `x` is recorded; every sender activation outputs whether the
  completion notice has been delivered;
* the receiver port: the first choice `c` is recorded; a receiver activation outputs the delivered
  value `out x c` once, and nothing otherwise;
* the adversary port (`SchedEv`): `poll` reports which inputs have arrived; `deliverRecv` makes
  `out x c` available to the receiver and `deliverSend` delivers the completion notice to the
  sender, each only when both inputs have arrived; `idle` changes nothing.

The adversary learns that an input arrived and nothing about its value, and no output reaches a
party before the adversary delivers it. Every activation answers on the port of its event
(`FOTSched_portTyped` and the forms with a corrupt party), and the adversary event `idle` is idle
(`FOTSched_idleAt`).

The corruption forms move the corrupt party's port to the adversary side: `FOTSchedR` (corrupt
receiver) has the sender on the honest port and the receiver beside the scheduler on the adversary
port; `FOTSchedS` (corrupt sender) has the receiver on the honest port. For a semi-honest
corrupt party, `FOTSchedSH out leak` keeps both parties on the honest port and adds to the
adversary port an event that shows the corrupt party's view (`leakSend`, `leakRecv`); the
adversary cannot choose that party's input.

**Parallel form.** `FOTSchedPar ι out` runs one independent copy of `FOTSched out` for each index
`i : ι`; each event carries the index of its copy (`Sys.indexed`), so the adversary schedules each
copy separately. The `κ`-fold form is `ι = Fin κ`.

## Main definitions

* `SchedSt`, `SchedEv`, `SchedOut`: the state and the adversary port.
* `FOTSched.sendSys`, `FOTSched.recvSys`, `FOTSched.schedSys`: the three ports.
* `FOTSched`, `FOTSchedR`, `FOTSchedS`: the functionality, honest and with a corrupt party.
* `FOTSchedSH`, `leakSend`, `leakRecv`: the functionality with a semi-honest corrupt party.
* `Sys.indexed`: independent copies of a system indexed by `ι`.
* `FOTSchedPar`, `FOTSchedParR`, `FOTSchedParS`: the parallel form.

## Main results

* `FOTSched_portTyped`, `FOTSchedR_portTyped`, `FOTSchedS_portTyped`,
  `FOTSchedPar_portTyped`: each event is answered on its port.
* `FOTSched_idleAt`, `FOTSchedPar_idleAt`: the idle adversary event.
* `FOTSched.recvSys_step_delivered`: after `deliverRecv`, the receiver obtains `out x c`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core

/-! ## Independent indexed copies of a system

Upstream target: `CatCryptCore/Crypto/UCParallel.lean`. -/

namespace Sys

variable {ι τ E O : Type} [DecidableEq ι]

/-- Independent copies of `X`, one for each index: the event `(i, e)` is the event `e` of the
copy `i`, which alone changes its state. -/
noncomputable def indexed (X : Sys τ E O) : Sys (ι → τ) (ι × E) O where
  init _ := X.init
  step t e := SPComp.map (fun q => (Function.update t e.1 q.1, q.2)) (X.step (t e.1) e.2)

/-- Unfolding lemma of `Sys.indexed`: a step on the event `(i, e)`. -/
@[simp] theorem indexed_step (X : Sys τ E O) (t : ι → τ) (i : ι) (e : E) :
    (X.indexed (ι := ι)).step t (i, e) =
      SPComp.map (fun q => (Function.update t i q.1, q.2)) (X.step (t i) e) := rfl

/-- Copies of a system idle at `g` with output `o` are idle at every `(i, g)`. -/
theorem indexed_idleAt {X : Sys τ E O} {g : E} {o : O}
    (h : MultiHybrid.IdleAt X g o) (i : ι) :
    MultiHybrid.IdleAt (X.indexed (ι := ι)) (i, g) o := fun t => by
  simp only [indexed_step, h (t i), SPComp.map, SPComp.pure_bind, Function.update_eq_self]

end Sys

end CatCrypt.Crypto.UCTransparent

namespace CatCrypt.Crypto.OT

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCTransparent

/-! ## The state and the adversary port -/

/-- The state of the scheduled oblivious transfer. -/
structure SchedSt (X C Y : Type) where
  /-- The sender's first input. -/
  sent : Option X
  /-- The receiver's first choice. -/
  chosen : Option C
  /-- The value delivered to the receiver and not yet obtained. -/
  inbox : Option Y
  /-- Whether the receiver's output has been delivered. -/
  dRecv : Bool
  /-- Whether the completion notice has been delivered to the sender. -/
  dSend : Bool

/-- Events of the adversary port. -/
inductive SchedEv where
  /-- No action. -/
  | idle
  /-- Ask which inputs have arrived. -/
  | poll
  /-- Deliver the receiver's output. -/
  | deliverRecv
  /-- Deliver the completion notice to the sender. -/
  | deliverSend

/-- Outputs of the adversary port. -/
inductive SchedOut where
  /-- Acknowledgement. -/
  | ack
  /-- Whether the sender's input and the receiver's choice have arrived. -/
  | status (sent chosen : Bool)

namespace FOTSched

variable {X C Y : Type}

/-- The initial state: no input, nothing delivered. -/
def initSt : SchedSt X C Y := ⟨none, none, none, false, false⟩

/-- A sender activation with input `x`: the first input is kept, and the sender learns whether
the completion notice has been delivered. -/
def sendStep (t : SchedSt X C Y) (x : X) : SchedSt X C Y × Bool :=
  ({ t with sent := t.sent.or (some x) }, t.dSend)

/-- A receiver activation with choice `c`: the first choice is kept, and the delivered value,
if any, is output once. -/
def recvStep (t : SchedSt X C Y) (c : C) : SchedSt X C Y × Option Y :=
  ({ t with chosen := t.chosen.or (some c), inbox := none }, t.inbox)

/-- An adversary activation. -/
def schedStep (out : X → C → Y) (t : SchedSt X C Y) : SchedEv → SchedSt X C Y × SchedOut
  | .idle => (t, .ack)
  | .poll => (t, .status t.sent.isSome t.chosen.isSome)
  | .deliverRecv =>
    match t.sent, t.chosen, t.dRecv with
    | some x, some c, false => ({ t with inbox := some (out x c), dRecv := true }, .ack)
    | _, _, _ => (t, .ack)
  | .deliverSend =>
    match t.sent, t.chosen with
    | some _, some _ => ({ t with dSend := true }, .ack)
    | _, _ => (t, .ack)

/-- The sender port. -/
noncomputable def sendSys : Sys (SchedSt X C Y) X Bool where
  init := initSt
  step t x := SPComp.pure (sendStep t x)

/-- The receiver port. -/
noncomputable def recvSys : Sys (SchedSt X C Y) C (Option Y) where
  init := initSt
  step t c := SPComp.pure (recvStep t c)

/-- The adversary port. -/
noncomputable def schedSys (out : X → C → Y) : Sys (SchedSt X C Y) SchedEv SchedOut where
  init := initSt
  step t e := SPComp.pure (schedStep out t e)

/-- After the adversary delivers the receiver's output for the inputs `x` and `c`, the next
receiver activation outputs `out x c`. -/
theorem recvSys_step_delivered (out : X → C → Y) (t : SchedSt X C Y) (x : X) (c c' : C)
    (hx : t.sent = some x) (hc : t.chosen = some c) (hd : t.dRecv = false) :
    (recvStep (schedStep out t .deliverRecv).1 c').2 = some (out x c) := by
  simp [schedStep, recvStep, hx, hc, hd]

end FOTSched

open FOTSched

/-! ## The functionality and its corruption forms -/

section Single

variable {X C Y : Type}

/-- **Scheduled oblivious transfer**, both parties honest: the sender and the receiver on the
honest port, the scheduler on the adversary port. -/
noncomputable def FOTSched (out : X → C → Y) :
    Sys (SchedSt X C Y) ((X ⊕ C) ⊕ SchedEv) ((Bool ⊕ Option Y) ⊕ SchedOut) :=
  Sys.ofPorts (Sys.ofPorts sendSys recvSys) (schedSys out)

/-- **Scheduled oblivious transfer against a corrupt receiver**: the sender on the honest port,
the receiver beside the scheduler on the adversary port. -/
noncomputable def FOTSchedR (out : X → C → Y) :
    Sys (SchedSt X C Y) (X ⊕ (C ⊕ SchedEv)) (Bool ⊕ (Option Y ⊕ SchedOut)) :=
  Sys.ofPorts sendSys (Sys.ofPorts recvSys (schedSys out))

/-- **Scheduled oblivious transfer against a corrupt sender**: the receiver on the honest port,
the sender beside the scheduler on the adversary port. -/
noncomputable def FOTSchedS (out : X → C → Y) :
    Sys (SchedSt X C Y) (C ⊕ (X ⊕ SchedEv)) (Option Y ⊕ (Bool ⊕ SchedOut)) :=
  Sys.ofPorts recvSys (Sys.ofPorts sendSys (schedSys out))

/-- `FOTSched` answers each event on the port of the event. -/
theorem FOTSched_portTyped (out : X → C → Y) : (FOTSched out).PortTyped :=
  Sys.ofPorts_portTyped _ _

/-- `FOTSchedR` answers each event on the port of the event. -/
theorem FOTSchedR_portTyped (out : X → C → Y) : (FOTSchedR out).PortTyped :=
  Sys.ofPorts_portTyped _ _

/-- `FOTSchedS` answers each event on the port of the event. -/
theorem FOTSchedS_portTyped (out : X → C → Y) : (FOTSchedS out).PortTyped :=
  Sys.ofPorts_portTyped _ _

/-- The adversary port of the scheduled transfer is idle at `idle`. -/
theorem schedSys_idleAt (out : X → C → Y) :
    MultiHybrid.IdleAt (schedSys out) .idle .ack := fun _ => rfl

/-- `FOTSched` is idle at the adversary event `idle`. -/
theorem FOTSched_idleAt (out : X → C → Y) :
    MultiHybrid.IdleAt (FOTSched out) (.inr .idle) (.inr .ack) := fun t => by
  simp [FOTSched, schedSys, schedStep, SPComp.map, SPComp.pure_bind]

/-- `FOTSchedR` is idle at the adversary event `idle`. -/
theorem FOTSchedR_idleAt (out : X → C → Y) :
    MultiHybrid.IdleAt (FOTSchedR out) (.inr (.inr .idle)) (.inr (.inr .ack)) := fun t => by
  simp [FOTSchedR, schedSys, schedStep, SPComp.map, SPComp.pure_bind]

/-- `FOTSchedS` is idle at the adversary event `idle`. -/
theorem FOTSchedS_idleAt (out : X → C → Y) :
    MultiHybrid.IdleAt (FOTSchedS out) (.inr (.inr .idle)) (.inr (.inr .ack)) := fun t => by
  simp [FOTSchedS, schedSys, schedStep, SPComp.map, SPComp.pure_bind]

/-- The view of a semi-honest corrupt sender: its input and whether the completion notice has
been delivered to it. -/
def leakSend (t : SchedSt X C Y) : Option X × Bool := (t.sent, t.dSend)

/-- The view of a semi-honest corrupt receiver: its choice and the output delivered to it. -/
def leakRecv (out : X → C → Y) (t : SchedSt X C Y) : Option C × Option Y :=
  (t.chosen, match t.sent, t.chosen, t.dRecv with
    | some x, some c, true => some (out x c)
    | _, _, _ => none)

/-- The port that shows the view `leak` of the state. -/
noncomputable def peekSys {L : Type} (leak : SchedSt X C Y → L) : Sys (SchedSt X C Y) Unit L where
  init := initSt
  step t _ := SPComp.pure (t, leak t)

/-- **Scheduled oblivious transfer with a semi-honest corrupt party**: both parties run on the
honest port; the adversary port carries the scheduler and the event that shows the corrupt
party's view `leak` (`leakSend` or `leakRecv`). -/
noncomputable def FOTSchedSH {L : Type} (out : X → C → Y) (leak : SchedSt X C Y → L) :
    Sys (SchedSt X C Y) ((X ⊕ C) ⊕ (SchedEv ⊕ Unit)) ((Bool ⊕ Option Y) ⊕ (SchedOut ⊕ L)) :=
  Sys.ofPorts (Sys.ofPorts sendSys recvSys) (Sys.ofPorts (schedSys out) (peekSys leak))

/-- `FOTSchedSH` answers each event on the port of the event. -/
theorem FOTSchedSH_portTyped {L : Type} (out : X → C → Y) (leak : SchedSt X C Y → L) :
    (FOTSchedSH out leak).PortTyped :=
  Sys.ofPorts_portTyped _ _

/-- `FOTSchedSH` is idle at the adversary event `idle`. -/
theorem FOTSchedSH_idleAt {L : Type} (out : X → C → Y) (leak : SchedSt X C Y → L) :
    MultiHybrid.IdleAt (FOTSchedSH out leak) (.inr (.inl .idle)) (.inr (.inl .ack)) :=
  fun t => by simp [FOTSchedSH, schedSys, schedStep, SPComp.map, SPComp.pure_bind]

end Single

/-! ## The parallel form -/

section Par

variable {ι X C Y : Type} [DecidableEq ι]

/-- **Independent copies of the scheduled transfer**, both parties honest: one copy for each
index; each event names its copy. -/
noncomputable def FOTSchedPar (ι : Type) [DecidableEq ι] (out : X → C → Y) :
    Sys (ι → SchedSt X C Y) (((ι × X) ⊕ (ι × C)) ⊕ (ι × SchedEv))
      ((Bool ⊕ Option Y) ⊕ SchedOut) :=
  Sys.ofPorts (Sys.ofPorts sendSys.indexed recvSys.indexed) (schedSys out).indexed

/-- Independent copies of the scheduled transfer against a corrupt receiver. -/
noncomputable def FOTSchedParR (ι : Type) [DecidableEq ι] (out : X → C → Y) :
    Sys (ι → SchedSt X C Y) ((ι × X) ⊕ ((ι × C) ⊕ (ι × SchedEv)))
      (Bool ⊕ (Option Y ⊕ SchedOut)) :=
  Sys.ofPorts sendSys.indexed (Sys.ofPorts recvSys.indexed (schedSys out).indexed)

/-- Independent copies of the scheduled transfer against a corrupt sender. -/
noncomputable def FOTSchedParS (ι : Type) [DecidableEq ι] (out : X → C → Y) :
    Sys (ι → SchedSt X C Y) ((ι × C) ⊕ ((ι × X) ⊕ (ι × SchedEv)))
      (Option Y ⊕ (Bool ⊕ SchedOut)) :=
  Sys.ofPorts recvSys.indexed (Sys.ofPorts sendSys.indexed (schedSys out).indexed)

/-- `FOTSchedPar` answers each event on the port of the event. -/
theorem FOTSchedPar_portTyped (out : X → C → Y) : (FOTSchedPar ι out).PortTyped :=
  Sys.ofPorts_portTyped _ _

/-- `FOTSchedParR` answers each event on the port of the event. -/
theorem FOTSchedParR_portTyped (out : X → C → Y) : (FOTSchedParR ι out).PortTyped :=
  Sys.ofPorts_portTyped _ _

/-- `FOTSchedParS` answers each event on the port of the event. -/
theorem FOTSchedParS_portTyped (out : X → C → Y) : (FOTSchedParS ι out).PortTyped :=
  Sys.ofPorts_portTyped _ _

/-- `FOTSchedPar` is idle at the adversary event `idle` of every copy. -/
theorem FOTSchedPar_idleAt (out : X → C → Y) (i : ι) :
    MultiHybrid.IdleAt (FOTSchedPar ι out) (.inr (i, .idle)) (.inr .ack) := fun t => by
  simp [FOTSchedPar, schedSys, schedStep, SPComp.map, SPComp.pure_bind]

end Par

end CatCrypt.Crypto.OT
