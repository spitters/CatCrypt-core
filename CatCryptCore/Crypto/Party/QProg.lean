/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Prog
public import CatCryptCore.Quantum.QSysCat
public import CatCryptCore.Quantum.OpenSystem
public import CatCryptCore.Quantum.QOTPReactive

/-!
# Quantum party programs and their denotation as quantum reactive systems

The party language is one generic program tree `Party.ProgE Op E O α` with two effect handlers,
the classical one of `Party.Prog` and the quantum one of this module. A quantum party on the
register `R` (a finite type of basis states) with input events `E` and outputs `O` is a program
`Party.QProg R E O α`, the abbreviation of `ProgE (SubInstrument R R ℕ) E O α`. Its classical
ports are those of every party program: it returns, waits for the next activation (`recv`),
emits the output of the current activation (`send`) or fails. Its effect operation `opN q k`
applies the subinstrument `q : SubInstrument R R ℕ` to the register and continues with the
classical outcome. Outcomes are codes in `ℕ` so that `QProg R E O α : Type`; `QProg.op` applies a
subinstrument with outcomes in any countable type through its encoding. Unitary gates (one
outcome), measurements (the outcome is the result) and preparations are subinstruments, and so is
sampling: a sub-distribution is a diagonal subinstrument (`SubInstrument.ofSDistr` of
`CatCryptCore.Quantum.ClassicalLiftSys`), and a classical program is a quantum party through the
map of effect signatures `ProgE.mapOp`.

The quantum effect handler `QProg.handler` runs an operation in the monad `SubInstrument R R`; it
is lawful (`QProg.handler_lawful`). The denotation is a quantum reactive system
`ReactiveUC.QRSys` whose classical state is the residual program: an activation on the event `e`
is the generic activation `ProgE.act` at the quantum handler, the await phase `ProgE.awaitK`
followed by the emit phase `ProgE.emitK` (`QProg.act`). A finite program denotes
`QProg.toQRSys p`, an unbounded session the loop `QProg.loopQSys body s₀`.

## Qubit ports and linear ownership

The register of a quantum reactive system is shared with the environment and with the other
systems of a composition. A sub-register is owned by a program when the other programs act on it
by the identity, which is the case for the right factor `N` of `M × N` when they are framed
programs on `M` (`QProg.frameR`, by `SubInstrument.frame`, and `QProg.frameL`, by
`OpenSystem.frameLeft`); both are maps of effect signatures (`ProgE.mapOp`). A qubit port moves
the ownership of a factor across the boundary:

* `QProg.sendQ o k` on `M × N` emits `o` together with the factor `N` and continues as the
  program `k` on `M`, framed: the register of the sender shrinks to `M`, and no later operation of
  the sender acts on `N`;
* `QProg.recvQ p k` on `M × N` runs the program `p` on `M`, framed, then waits for the event that
  hands over `N` and continues on the whole register `M × N`.

Linearity is enforced by the register type: a program on `M` cannot name an operation on `N`,
and every operation is a completely positive map on the register, so no step copies the state of
a factor (no cloning). The framing of a program denotes the framing of its system
(`QProg.toQRSys_frameR`, `QProg.toQRSys_frameL`), so a sent factor is untouched by the sender.

## Main definitions

* `Party.QProg R E O α`: quantum party programs, the abbreviation of
  `ProgE (SubInstrument R R ℕ) E O α`.
* `Party.QProg.op`, `Party.QProg.opE`: the effect operation on a countable type of outcomes.
* `Party.QProg.handler`: the quantum effect handler.
* `Party.QProg.emitK`, `Party.QProg.awaitK`, `Party.QProg.act`: the phases of an activation.
* `Party.QProg.toQRSys`, `Party.QProg.loopQSys`: the denotations of a program and of a loop.
* `Party.QProg.frameR`, `Party.QProg.frameL`, `Party.QProg.sendQ`, `Party.QProg.recvQ`.
* `Party.QProg.qotpRealBody`: the real world of the reactive quantum one-time pad as a loop body.

## Main results

* `Party.QProg.handler_lawful`: the quantum handler is lawful.
* `Party.QProg.emitK_bind`, `Party.QProg.awaitK_bind`, `Party.QProg.emitK_op`.
* `Party.QProg.act_recv_send`: a receive followed by a send is one step.
* `Party.QProg.loopQSys_stepEq`: a loop of one-activation iterations is step-equivalent to the
  system with the iteration as its step.
* `Party.QProg.toQRSys_par`: the denotation of the parallel composition `ProgE.par p q` is
  step-equivalent to the parallel composition `QRSys.par` of the denotations, the tensor product
  of `QSysCat`.
* `Party.QProg.toQRSys_frameR`, `Party.QProg.toQRSys_frameL`: framing commutes with the
  denotation.
* `Party.QProg.qotpRealBody_stepEq`: the loop of `qotpRealBody` is step-equivalent to the real
  world `QOTPReactive.qotpReal`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party

open CatCrypt.Core _root_.Quantum CatCrypt.Quantum.ReactiveUC

/-- Quantum programs of a party on the register `R` with input events `E` and outputs `O`: the
party language at the quantum effect, whose operations are subinstruments on `R` with outcome
codes. -/
abbrev QProg (R : Type) [Fintype R] (E O : Type) : Type → Type := ProgE (SubInstrument R R ℕ) E O

namespace QProg

export ProgE (ret recv send opN fail bind bind_ret bind_assoc recvE sendE retOr Child child_wf
  par parAwL parEmL parAwR parEmR)

variable {R : Type} [Fintype R] {E O E' O' α β γ σ : Type}

/-- Apply the subinstrument `q` with outcomes in a countable type, through the codes of its
encoding, and continue with the outcome. A code outside the image of the encoding fails. -/
noncomputable def op [Countable β] (q : SubInstrument R R β) (k : β → QProg R E O α) :
    QProg R E O α :=
  letI := Encodable.ofCountable β
  .opN (q.map Encodable.encode) fun n =>
    match Encodable.decode n with
    | some b => k b
    | none => .fail

/-- Apply the subinstrument `q` and return the outcome. -/
noncomputable def opE [Countable β] (q : SubInstrument R R β) : QProg R E O β :=
  op q .ret

/-! ## The quantum effect handler and activations -/

/-- The quantum effect handler: an operation is run as a subinstrument on the register `R`. -/
noncomputable def handler : Handler (SubInstrument R R ℕ) (SubInstrument R R) where
  pure a := SubInstrument.pure a
  bind c f := SubInstrument.bind c f
  fail := SubInstrument.fail
  run q := q

/-- The quantum effect handler is lawful. -/
theorem handler_lawful : (handler : Handler (SubInstrument R R ℕ) (SubInstrument R R)).Lawful where
  pure_bind a f := SubInstrument.pure_bind a f
  bind_assoc c f g := SubInstrument.bind_assoc c f g
  fail_bind f := SubInstrument.fail_bind f

/-- The emit phase: perform the operations up to the next `send o` and continue with `s o` at
the rest; a return continues with `r`; a `recv` or a failure fails. -/
noncomputable def emitK (s : O → QProg R E O α → SubInstrument R R γ)
    (r : α → SubInstrument R R γ) : QProg R E O α → SubInstrument R R γ :=
  ProgE.emitK handler s r

/-- Unfolding lemma of `emitK` at a return. -/
@[simp] theorem emitK_ret (s : O → QProg R E O α → SubInstrument R R γ)
    (r : α → SubInstrument R R γ) (a : α) : emitK s r (.ret a) = r a := rfl

/-- Unfolding lemma of `emitK` at a receive. -/
@[simp] theorem emitK_recv (s : O → QProg R E O α → SubInstrument R R γ)
    (r : α → SubInstrument R R γ) (k : E → QProg R E O α) :
    emitK s r (.recv k) = SubInstrument.fail := rfl

/-- Unfolding lemma of `emitK` at a send. -/
@[simp] theorem emitK_send (s : O → QProg R E O α → SubInstrument R R γ)
    (r : α → SubInstrument R R γ) (o : O) (p : QProg R E O α) :
    emitK s r (.send o p) = s o p := rfl

/-- Unfolding lemma of `emitK` at an operation. -/
@[simp] theorem emitK_opN (s : O → QProg R E O α → SubInstrument R R γ)
    (r : α → SubInstrument R R γ) (q : SubInstrument R R ℕ) (k : ℕ → QProg R E O α) :
    emitK s r (.opN q k) = q.bind fun n => emitK s r (k n) := rfl

/-- Unfolding lemma of `emitK` at a failure. -/
@[simp] theorem emitK_fail (s : O → QProg R E O α → SubInstrument R R γ)
    (r : α → SubInstrument R R γ) : emitK s r .fail = SubInstrument.fail := rfl

/-- The await phase on the event `e`: perform the operations up to the next `recv`, feed it `e`
and continue in the emit phase with `s` and `rE`; a return continues with `rA`; a `send` or a
failure fails. -/
noncomputable def awaitK (e : E) (s : O → QProg R E O α → SubInstrument R R γ)
    (rA rE : α → SubInstrument R R γ) : QProg R E O α → SubInstrument R R γ :=
  ProgE.awaitK handler e s rA rE

/-- Unfolding lemma of `awaitK` at a return. -/
@[simp] theorem awaitK_ret (e : E) (s : O → QProg R E O α → SubInstrument R R γ)
    (rA rE : α → SubInstrument R R γ) (a : α) : awaitK e s rA rE (.ret a) = rA a := rfl

/-- Unfolding lemma of `awaitK` at a receive. -/
@[simp] theorem awaitK_recv (e : E) (s : O → QProg R E O α → SubInstrument R R γ)
    (rA rE : α → SubInstrument R R γ) (k : E → QProg R E O α) :
    awaitK e s rA rE (.recv k) = emitK s rE (k e) := rfl

/-- Unfolding lemma of `awaitK` at a send. -/
@[simp] theorem awaitK_send (e : E) (s : O → QProg R E O α → SubInstrument R R γ)
    (rA rE : α → SubInstrument R R γ) (o : O) (p : QProg R E O α) :
    awaitK e s rA rE (.send o p) = SubInstrument.fail := rfl

/-- Unfolding lemma of `awaitK` at an operation. -/
@[simp] theorem awaitK_opN (e : E) (s : O → QProg R E O α → SubInstrument R R γ)
    (rA rE : α → SubInstrument R R γ) (q : SubInstrument R R ℕ) (k : ℕ → QProg R E O α) :
    awaitK e s rA rE (.opN q k) = q.bind fun n => awaitK e s rA rE (k n) := rfl

/-- Unfolding lemma of `awaitK` at a failure. -/
@[simp] theorem awaitK_fail (e : E) (s : O → QProg R E O α → SubInstrument R R γ)
    (rA rE : α → SubInstrument R R γ) : awaitK e s rA rE .fail = SubInstrument.fail := rfl

/-- The emit phase commutes with `bind`: a return of `p` continues with the emit phase of
`f`. -/
theorem emitK_bind (s : O → QProg R E O β → SubInstrument R R γ) (r : β → SubInstrument R R γ)
    (p : QProg R E O α) (f : α → QProg R E O β) :
    emitK s r (ProgE.bind p f) =
      emitK (fun o q => s o (ProgE.bind q f)) (fun a => emitK s r (f a)) p :=
  ProgE.emitK_bind handler s r p f

/-- The await phase commutes with `bind`: a return of `p` in the await phase continues with the
await phase of `f`, and in the emit phase with the emit phase of `f`. -/
theorem awaitK_bind (e : E) (s : O → QProg R E O β → SubInstrument R R γ)
    (rA rE : β → SubInstrument R R γ) (p : QProg R E O α) (f : α → QProg R E O β) :
    awaitK e s rA rE (ProgE.bind p f) =
      awaitK e (fun o q => s o (ProgE.bind q f)) (fun a => awaitK e s rA rE (f a))
        (fun a => emitK s rE (f a)) p :=
  ProgE.awaitK_bind handler e s rA rE p f

/-- A quantum operation in the emit phase. -/
theorem emitK_op [Countable β] (s : O → QProg R E O α → SubInstrument R R γ)
    (r : α → SubInstrument R R γ) (q : SubInstrument R R β) (k : β → QProg R E O α) :
    emitK s r (op q k) = q.bind fun b => emitK s r (k b) := by
  simp [op, SubInstrument.map_eq_bind_pure, SubInstrument.bind_assoc, Encodable.encodek]

/-- A quantum operation in the await phase. -/
theorem awaitK_op [Countable β] (e : E) (s : O → QProg R E O α → SubInstrument R R γ)
    (rA rE : α → SubInstrument R R γ) (q : SubInstrument R R β) (k : β → QProg R E O α) :
    awaitK e s rA rE (op q k) = q.bind fun b => awaitK e s rA rE (k b) := by
  simp [op, SubInstrument.map_eq_bind_pure, SubInstrument.bind_assoc, Encodable.encodek]

/-- One activation of the program `p` on the event `e` that continues with `restart a e` when
`p` returns `a` in the await phase: the residual program after the activation's `send`, and the
output. -/
noncomputable def stepWith (restart : α → E → SubInstrument R R (QProg R E O α × O))
    (p : QProg R E O α) (e : E) : SubInstrument R R (QProg R E O α × O) :=
  ProgE.stepWith handler restart p e

/-- Unfolding lemma of `stepWith`. -/
theorem stepWith_def (restart : α → E → SubInstrument R R (QProg R E O α × O))
    (p : QProg R E O α) (e : E) :
    stepWith restart p e =
      awaitK e (fun o q => SubInstrument.pure (q, o)) (fun a => restart a e)
        (fun _ => SubInstrument.fail) p :=
  rfl

/-- One activation of a program that halts on return: an activation after the return fails. -/
noncomputable def act (p : QProg R E O α) (e : E) : SubInstrument R R (QProg R E O α × O) :=
  ProgE.act handler p e

/-- Unfolding lemma of `act`. -/
theorem act_def (p : QProg R E O α) (e : E) :
    act p e = stepWith (fun _ _ => SubInstrument.fail) p e :=
  rfl

/-- The denotation of a program: the classical state is the residual program, the step an
activation. -/
noncomputable def toQRSys (p : QProg R E O α) : QRSys R (QProg R E O α) E O where
  init := p
  step := act

/-- The denotation of the loop of `body` from `s₀`: the classical state is the residual program
of the current iteration, starting at the return of `s₀`; a return of `s` in the await phase
continues the activation with `body s`. -/
noncomputable def loopQSys (body : σ → QProg R E O σ) (s₀ : σ) : QRSys R (QProg R E O σ) E O where
  init := .ret s₀
  step := stepWith fun s e => act (body s) e

/-- Unfolding lemma of `act`: a receive followed by a send is one step. -/
theorem act_recv_send (g : E → O) (p : E → QProg R E O α) (e : E) :
    act (.recv fun e => .send (g e) (p e)) e = SubInstrument.pure (p e, g e) :=
  ProgE.act_recv_send handler g p e

/-- Unfolding lemma of `loopQSys`: the step at the return of `s` is the activation of
`body s`. -/
theorem loopQSys_step_ret (body : σ → QProg R E O σ) (s₀ s : σ) (e : E) :
    (loopQSys body s₀).step (.ret s) e = act (body s) e := rfl

/-- **Loops of one activation.** When the activation of `body s` on every event is the step
`step s e` followed by a return, the loop of `body` from `s₀` is step-equivalent to the system
with initial state `s₀` and step `step`. -/
theorem loopQSys_stepEq (body : σ → QProg R E O σ) (s₀ : σ)
    (step : σ → E → SubInstrument R R (σ × O))
    (h : ∀ s e, act (body s) e =
      (step s e).bind fun q => SubInstrument.pure (ProgE.ret q.1, q.2)) :
    QRSys.StepEq (⟨QProg R E O σ, loopQSys body s₀⟩ : QRSys.Obj R E O) ⟨σ, ⟨s₀, step⟩⟩ :=
  Relation.EqvGen.symm _ _ (QRSys.StepMap.stepEq (f := ProgE.ret)
    ⟨rfl, fun s e => by rw [loopQSys_step_ret, h]⟩)

/-! ## Framing and qubit ports -/

section Frame

variable {M N : Type} [Fintype M] [Fintype N]

/-- The program `p` on the left factor of the register `M × N`: every operation is framed by the
identity on `N`. -/
noncomputable def frameR (p : QProg M E O α) (N : Type) [Fintype N] : QProg (M × N) E O α :=
  ProgE.mapOp (fun q => q.frame N) p

/-- Unfolding lemma of `frameR` at a return. -/
@[simp] theorem frameR_ret (a : α) : frameR (.ret a : QProg M E O α) N = .ret a := rfl

/-- Unfolding lemma of `frameR` at a receive. -/
@[simp] theorem frameR_recv (k : E → QProg M E O α) :
    frameR (.recv k) N = .recv fun e => frameR (k e) N := rfl

/-- Unfolding lemma of `frameR` at a send. -/
@[simp] theorem frameR_send (o : O) (p : QProg M E O α) :
    frameR (.send o p) N = .send o (frameR p N) := rfl

/-- Unfolding lemma of `frameR` at an operation. -/
@[simp] theorem frameR_opN (q : SubInstrument M M ℕ) (k : ℕ → QProg M E O α) :
    frameR (.opN q k) N = .opN (q.frame N) fun n => frameR (k n) N := rfl

/-- Unfolding lemma of `frameR` at a failure. -/
@[simp] theorem frameR_fail : frameR (.fail : QProg M E O α) N = .fail := rfl

/-- The program `p` on the right factor of the register `M × N`: every operation is framed by
the identity on `M`. -/
noncomputable def frameL (p : QProg N E O α) (M : Type) [Fintype M] : QProg (M × N) E O α :=
  ProgE.mapOp (fun q => CatCrypt.Quantum.OpenSystem.frameLeft q M) p

/-- Unfolding lemma of `frameL` at a return. -/
@[simp] theorem frameL_ret (a : α) : frameL (.ret a : QProg N E O α) M = .ret a := rfl

/-- Unfolding lemma of `frameL` at a receive. -/
@[simp] theorem frameL_recv (k : E → QProg N E O α) :
    frameL (.recv k) M = .recv fun e => frameL (k e) M := rfl

/-- Unfolding lemma of `frameL` at a send. -/
@[simp] theorem frameL_send (o : O) (p : QProg N E O α) :
    frameL (.send o p) M = .send o (frameL p M) := rfl

/-- Unfolding lemma of `frameL` at an operation. -/
@[simp] theorem frameL_opN (q : SubInstrument N N ℕ) (k : ℕ → QProg N E O α) :
    frameL (.opN q k) M =
      .opN (CatCrypt.Quantum.OpenSystem.frameLeft q M) fun n => frameL (k n) M := rfl

/-- Unfolding lemma of `frameL` at a failure. -/
@[simp] theorem frameL_fail : frameL (.fail : QProg N E O α) M = .fail := rfl

/-- **Send a sub-register.** Emit `o` together with the factor `N` of the register `M × N` and
continue as `k` on `M`: no later operation acts on `N`. -/
noncomputable def sendQ (o : O) (k : QProg M E O α) : QProg (M × N) E O α :=
  .send o (k.frameR N)

/-- **Receive a sub-register.** Run `p` on the factor `M` of the register `M × N`, then wait for
the event that hands over the factor `N` and continue on `M × N`. -/
noncomputable def recvQ (p : QProg M E O β) (k : β → E → QProg (M × N) E O α) :
    QProg (M × N) E O α :=
  ProgE.bind (p.frameR N) fun b => .recv (k b)

/-- The emit phase of a framed program is the framed emit phase. -/
theorem emitK_frameR (p : QProg M E O α) :
    emitK (fun o q => SubInstrument.pure (q, o)) (fun _ => SubInstrument.fail) (p.frameR N) =
      ((emitK (fun o q => SubInstrument.pure (q, o)) (fun _ => SubInstrument.fail) p).frame
        N).bind fun x => SubInstrument.pure (x.1.frameR N, x.2) := by
  induction p with
  | opN q k ih =>
    simp only [frameR_opN, emitK_opN, ih, SubInstrument.frame_bind, SubInstrument.bind_assoc]
  | _ => simp

/-- An activation of a framed program is the framed activation. -/
theorem act_frameR (p : QProg M E O α) (e : E) :
    act (p.frameR N) e =
      ((act p e).frame N).bind fun x => SubInstrument.pure (x.1.frameR N, x.2) := by
  induction p with
  | recv k ih => simp only [frameR_recv, act_def, stepWith_def, awaitK_recv, emitK_frameR]
  | opN q k ih =>
    simp only [act_def, stepWith_def] at ih
    simp only [frameR_opN, act_def, stepWith_def, awaitK_opN, ih, SubInstrument.frame_bind,
      SubInstrument.bind_assoc]
  | _ => simp [act_def, stepWith_def]

/-- **Framing commutes with the denotation** on the left factor: the framing of a program is a
step map image of the framing of its system. -/
theorem toQRSys_frameR (p : QProg M E O α) :
    QRSys.StepMap ((toQRSys p).frameR N) (toQRSys (p.frameR N)) (frameR · N) :=
  ⟨rfl, fun t e => (act_frameR t e).symm⟩

/-- Framing on the right factor keeps failure. -/
theorem frameLeft_fail {β : Type} :
    CatCrypt.Quantum.OpenSystem.frameLeft (SubInstrument.fail : SubInstrument N N β) M =
      SubInstrument.fail :=
  DSubInstrument.ext <| funext fun _ => MatrixMap.amplifyLeft_zero

/-- The emit phase of a program framed on the right factor is the framed emit phase. -/
theorem emitK_frameL (p : QProg N E O α) :
    emitK (fun o q => SubInstrument.pure (q, o)) (fun _ => SubInstrument.fail) (p.frameL M) =
      (CatCrypt.Quantum.OpenSystem.frameLeft
        (emitK (fun o q => SubInstrument.pure (q, o)) (fun _ => SubInstrument.fail) p) M).bind
        fun x => SubInstrument.pure (x.1.frameL M, x.2) := by
  induction p with
  | opN q k ih =>
    simp only [frameL_opN, emitK_opN, ih, CatCrypt.Quantum.OpenSystem.frameLeft_bind,
      SubInstrument.bind_assoc]
  | send o p ih =>
    simp [CatCrypt.Quantum.OpenSystem.frameLeft_pure]
  | _ => simp [frameLeft_fail]

/-- An activation of a program framed on the right factor is the framed activation. -/
theorem act_frameL (p : QProg N E O α) (e : E) :
    act (p.frameL M) e =
      (CatCrypt.Quantum.OpenSystem.frameLeft (act p e) M).bind
        fun x => SubInstrument.pure (x.1.frameL M, x.2) := by
  induction p with
  | recv k ih => simp only [frameL_recv, act_def, stepWith_def, awaitK_recv, emitK_frameL]
  | opN q k ih =>
    simp only [act_def, stepWith_def] at ih
    simp only [frameL_opN, act_def, stepWith_def, awaitK_opN, ih,
      CatCrypt.Quantum.OpenSystem.frameLeft_bind, SubInstrument.bind_assoc]
  | _ => simp [act_def, stepWith_def, frameLeft_fail]

/-- **Framing commutes with the denotation** on the right factor. -/
theorem toQRSys_frameL (p : QProg N E O α) :
    QRSys.StepMap ((toQRSys p).frameL M) (toQRSys (p.frameL M)) (frameL · M) :=
  ⟨rfl, fun t e => (act_frameL t e).symm⟩

/-- Unfolding lemma of `sendQ` in the emit phase: the residual program is the continuation,
framed. -/
theorem emitK_sendQ (o : O) (k : QProg M E O α) :
    emitK (fun o q => SubInstrument.pure (q, o)) (fun _ => SubInstrument.fail)
        (sendQ (N := N) o k) =
      SubInstrument.pure (k.frameR N, o) := rfl

end Frame

/-! ## Parallel composition -/

/-- The emit phase of `parEmL p q` is the emit phase of `p`, its residual composed with `q` and
its output tagged `inl`. -/
theorem emitK_parEmL (q : QProg R E' O' β) (p : QProg R E O α) :
    emitK (fun o r => SubInstrument.pure (r, o)) (fun _ => SubInstrument.fail) (parEmL p q) =
      (emitK (fun o r => SubInstrument.pure (r, o)) (fun _ => SubInstrument.fail) p).bind
        fun x => SubInstrument.pure (par x.1 q, Sum.inl x.2) :=
  ProgE.emitK_parEmL handler handler_lawful q p

/-- The emit phase of `parEmR p q` is the emit phase of `q`, `p` composed with its residual and
its output tagged `inr`. -/
theorem emitK_parEmR (p : QProg R E O α) (q : QProg R E' O' β) :
    emitK (fun o r => SubInstrument.pure (r, o)) (fun _ => SubInstrument.fail) (parEmR p q) =
      (emitK (fun o r => SubInstrument.pure (r, o)) (fun _ => SubInstrument.fail) q).bind
        fun x => SubInstrument.pure (par p x.1, Sum.inr x.2) :=
  ProgE.emitK_parEmR handler handler_lawful p q

/-- The emit phase of `parAwL e p q` is the activation of `p` on `e`. -/
theorem emitK_parAwL (e : E) (q : QProg R E' O' β) (p : QProg R E O α) :
    emitK (fun o r => SubInstrument.pure (r, o)) (fun _ => SubInstrument.fail) (parAwL e p q) =
      (act p e).bind fun x => SubInstrument.pure (par x.1 q, Sum.inl x.2) :=
  ProgE.emitK_parAwL handler handler_lawful e q p

/-- The emit phase of `parAwR e p q` is the activation of `q` on `e`. -/
theorem emitK_parAwR (e : E') (p : QProg R E O α) (q : QProg R E' O' β) :
    emitK (fun o r => SubInstrument.pure (r, o)) (fun _ => SubInstrument.fail) (parAwR e p q) =
      (act q e).bind fun x => SubInstrument.pure (par p x.1, Sum.inr x.2) :=
  ProgE.emitK_parAwR handler handler_lawful e p q

/-- An activation of `par p q` on a left event is the activation of `p`. -/
theorem act_par_inl (p : QProg R E O α) (q : QProg R E' O' β) (e : E) :
    act (par p q) (.inl e) =
      (act p e).bind fun x => SubInstrument.pure (par x.1 q, Sum.inl x.2) :=
  ProgE.act_par_inl handler handler_lawful p q e

/-- An activation of `par p q` on a right event is the activation of `q`. -/
theorem act_par_inr (p : QProg R E O α) (q : QProg R E' O' β) (e : E') :
    act (par p q) (.inr e) =
      (act q e).bind fun x => SubInstrument.pure (par p x.1, Sum.inr x.2) :=
  ProgE.act_par_inr handler handler_lawful p q e

/-- **The denotation of the parallel composition** is step-equivalent to the parallel
composition of the denotations, the tensor product of `QSysCat R`. -/
theorem toQRSys_par (p : QProg R E O α) (q : QProg R E' O' β) :
    QRSys.StepEq (⟨_, toQRSys (par p q)⟩ : QRSys.Obj R (E ⊕ E') (O ⊕ O'))
      ⟨_, (toQRSys p).par (toQRSys q)⟩ := by
  refine Relation.EqvGen.symm _ _ (QRSys.StepMap.stepEq (f := fun s => par s.1 s.2)
    ⟨rfl, fun s e => ?_⟩)
  rcases e with e | e
  · simp only [QRSys.par_step_inl, toQRSys, act_par_inl, SubInstrument.bind_assoc,
      SubInstrument.pure_bind]
  · simp only [QRSys.par_step_inr, toQRSys, act_par_inr, SubInstrument.bind_assoc,
      SubInstrument.pure_bind]

end QProg

/-! ## Example: the real world of the reactive quantum one-time pad -/

namespace QProg

open CatCrypt.Quantum.QOTPReactive

variable {n : ℕ}

/-- The real world of the reactive quantum one-time pad (`QOTPReactive.realStep`: the key
functionality, Alice, the authenticated quantum channel and Bob) as a loop body over its
phase. -/
noncomputable def qotpRealBody (n : ℕ) :
    Phase n → QProg (Reg n × Reg n) Event Out (Phase n)
  | .idle => do
    match ← recvE with
    | .send =>
      opE (swapOp (Reg n))
      let k ← opE (keyOp n)
      opE (encOp k)
      sendE .sent
      pure (.sent k)
    | .deliver | .steal =>
      sendE .ignored
      pure .idle
  | .sent k => do
    match ← recvE with
    | .send =>
      sendE .ignored
      pure (.sent k)
    | .deliver =>
      opE (decOp k)
      opE (swapOp (Reg n))
      sendE .received
      pure .done
    | .steal =>
      opE (swapOp (Reg n))
      sendE .aborted
      pure .done
  | .done => do
    let _ ← recvE
    sendE .ignored
    pure .done

/-- **The real world as a program.** The loop of `qotpRealBody n` from `idle` is
step-equivalent to the hand-written real world `QOTPReactive.qotpReal n`. -/
theorem qotpRealBody_stepEq :
    QRSys.StepEq (⟨_, loopQSys (qotpRealBody n) .idle⟩ : QRSys.Obj (Reg n × Reg n) Event Out)
      ⟨_, (qotpReal n).toQRSys⟩ :=
  loopQSys_stepEq _ _ (realStep n) fun s e => by
    cases s <;> cases e <;>
      simp [qotpRealBody, realStep, act_def, stepWith_def, ProgE.recvE, ProgE.sendE, opE,
        ProgE.bind, emitK_bind, emitK_op, SubInstrument.bind_assoc]

end QProg

end CatCrypt.Crypto.Party
