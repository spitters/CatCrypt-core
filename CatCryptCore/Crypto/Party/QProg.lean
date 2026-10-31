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

A quantum party on the register `R` (a finite type of basis states) with input events `E` and
outputs `O` is a first-order program tree `Party.QProg R E O α`. Its classical ports are those of
`Party.Prog`: it returns, waits for the next activation (`recv`), emits the output of the current
activation (`send`) or fails. Its quantum operation `opN q k` applies the subinstrument
`q : SubInstrument R R ℕ` to the register and continues with the classical outcome. Outcomes are
codes in `ℕ` so that `QProg R E O α : Type`; `QProg.op` applies a subinstrument with outcomes in
any countable type through its encoding. Unitary gates (one outcome), measurements (the
outcome is the result) and preparations are subinstruments, and so is sampling: a
sub-distribution is the diagonal subinstrument `QProg.diagOp`, each outcome scaling the state by
its probability.

The denotation is a quantum reactive system `ReactiveUC.QRSys` whose classical state is the
residual program, defined as for `Party.Prog`: an activation on the event `e` performs the
quantum operations up to the next `recv`, feeds it `e`, performs the operations up to the next
`send o` and stops there with the output `o` (`QProg.act`). A finite program denotes
`QProg.toQRSys p`, an unbounded session the loop `QProg.loopQSys body s₀`.

## Qubit ports and linear ownership

The register of a quantum reactive system is shared with the environment and with the other
systems of a composition. A sub-register is owned by a program when the other programs act on it
by the identity, which is the case for the right factor `N` of `M × N` when they are framed
programs on `M` (`QProg.frameR`, by `SubInstrument.frame`, and `QProg.frameL`, by
`OpenSystem.frameLeft`). A qubit port moves the ownership of a factor across the boundary:

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

* `Party.QProg R E O α`: quantum party programs, with `Monad (QProg R E O)`.
* `Party.QProg.recvE`, `Party.QProg.sendE`, `Party.QProg.op`, `Party.QProg.opE`.
* `Party.QProg.emitK`, `Party.QProg.awaitK`, `Party.QProg.act`: the phases of an activation.
* `Party.QProg.toQRSys`, `Party.QProg.loopQSys`: the denotations of a program and of a loop.
* `Party.QProg.frameR`, `Party.QProg.frameL`, `Party.QProg.sendQ`, `Party.QProg.recvQ`.
* `Party.QProg.par`: the parallel composition of two programs.
* `Party.QProg.diagOp`, `Party.Prog.toQProg`: the diagonal subinstrument of a sub-distribution
  and the embedding of classical programs.
* `Party.QProg.qotpRealBody`: the real world of the reactive quantum one-time pad as a loop body.

## Main results

* `Party.QProg.emitK_bind`, `Party.QProg.awaitK_bind`, `Party.QProg.emitK_op`.
* `Party.QProg.act_recv_send`: a receive followed by a send is one step.
* `Party.QProg.loopQSys_stepEq`: a loop of one-activation iterations is step-equivalent to the
  system with the iteration as its step.
* `Party.QProg.toQRSys_par`: the denotation of `par p q` is step-equivalent to the parallel
  composition `QRSys.par` of the denotations, the tensor product of `QSysCat`.
* `Party.QProg.toQRSys_frameR`, `Party.QProg.toQRSys_frameL`: framing commutes with the
  denotation.
* `Party.Prog.toQProg_bind`: the embedding of classical programs is a monad morphism.
* `Party.QProg.qotpRealBody_stepEq`: the loop of `qotpRealBody` is step-equivalent to the real
  world `QOTPReactive.qotpReal`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party

open CatCrypt.Core _root_.Quantum CatCrypt.Quantum.ReactiveUC
open scoped ComplexOrder

/-- Quantum programs of a party on the register `R` with input events `E` and outputs `O`,
returning `α`. -/
inductive QProg (R : Type) [Fintype R] (E O : Type) (α : Type) : Type where
  /-- Return `a`. -/
  | ret (a : α)
  /-- Wait for the next activation and continue with its event. -/
  | recv (k : E → QProg R E O α)
  /-- Emit `o` as the output of the current activation and continue. -/
  | send (o : O) (k : QProg R E O α)
  /-- Apply the subinstrument `q` to the register and continue with the outcome code. -/
  | opN (q : SubInstrument R R ℕ) (k : ℕ → QProg R E O α)
  /-- Failure. -/
  | fail

namespace QProg

variable {R : Type} [Fintype R] {E O E' O' α β γ σ : Type}

/-- Sequential composition of programs. -/
def bind : QProg R E O α → (α → QProg R E O β) → QProg R E O β
  | .ret a, f => f a
  | .recv k, f => .recv fun e => (k e).bind f
  | .send o p, f => .send o (p.bind f)
  | .opN q k, f => .opN q fun n => (k n).bind f
  | .fail, _ => .fail

instance : Monad (QProg R E O) where
  pure := .ret
  bind := bind

/-- Unfolding lemma of the monad instance: `pure` is `QProg.ret`. -/
@[simp] theorem pure_eq (a : α) : (pure a : QProg R E O α) = .ret a := rfl

/-- Unfolding lemma of the monad instance: `>>=` is `QProg.bind`. -/
@[simp] theorem bind_eq (p : QProg R E O α) (f : α → QProg R E O β) : p >>= f = p.bind f := rfl

/-- Unfolding lemma of the monad instance: `<$>` is `QProg.bind` followed by a return. -/
@[simp] theorem map_eq (f : α → β) (p : QProg R E O α) :
    f <$> p = p.bind fun a => .ret (f a) := rfl

/-- `bind` returning its argument is the identity. -/
theorem bind_ret (p : QProg R E O α) : p.bind .ret = p := by
  induction p with
  | ret a => rfl
  | recv k ih => simp only [bind, ih]
  | send o p ih => simp only [bind, ih]
  | opN q k ih => simp only [bind, ih]
  | fail => rfl

/-- `bind` is associative. -/
theorem bind_assoc (p : QProg R E O α) (f : α → QProg R E O β) (g : β → QProg R E O γ) :
    (p.bind f).bind g = p.bind fun a => (f a).bind g := by
  induction p with
  | ret a => rfl
  | recv k ih => simp only [bind, ih]
  | send o p ih => simp only [bind, ih]
  | opN q k ih => simp only [bind, ih]
  | fail => rfl

instance : LawfulMonad (QProg R E O) := LawfulMonad.mk'
  (id_map := fun p => bind_ret p)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun p f g => bind_assoc p f g)

/-- Wait for the next activation and return its event. -/
def recvE : QProg R E O E := .recv .ret

/-- Emit `o` as the output of the current activation. -/
def sendE (o : O) : QProg R E O Unit := .send o (.ret ())

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

/-! ## Activations -/

/-- The emit phase: perform the operations up to the next `send o` and continue with `s o` at
the rest; a return continues with `r`; a `recv` or a failure fails. -/
noncomputable def emitK (s : O → QProg R E O α → SubInstrument R R γ)
    (r : α → SubInstrument R R γ) : QProg R E O α → SubInstrument R R γ
  | .ret a => r a
  | .recv _ => SubInstrument.fail
  | .send o p => s o p
  | .opN q k => q.bind fun n => emitK s r (k n)
  | .fail => SubInstrument.fail

/-- The await phase on the event `e`: perform the operations up to the next `recv`, feed it `e`
and continue in the emit phase with `s` and `rE`; a return continues with `rA`; a `send` or a
failure fails. -/
noncomputable def awaitK (e : E) (s : O → QProg R E O α → SubInstrument R R γ)
    (rA rE : α → SubInstrument R R γ) : QProg R E O α → SubInstrument R R γ
  | .ret a => rA a
  | .recv k => emitK s rE (k e)
  | .send _ _ => SubInstrument.fail
  | .opN q k => q.bind fun n => awaitK e s rA rE (k n)
  | .fail => SubInstrument.fail

/-- The emit phase commutes with `bind`: a return of `p` continues with the emit phase of
`f`. -/
theorem emitK_bind (s : O → QProg R E O β → SubInstrument R R γ) (r : β → SubInstrument R R γ)
    (p : QProg R E O α) (f : α → QProg R E O β) :
    emitK s r (p.bind f) = emitK (fun o q => s o (q.bind f)) (fun a => emitK s r (f a)) p := by
  induction p with
  | ret a => rfl
  | recv k ih => rfl
  | send o p ih => rfl
  | opN q k ih => simp only [bind, emitK, ih]
  | fail => rfl

/-- The await phase commutes with `bind`: a return of `p` in the await phase continues with the
await phase of `f`, and in the emit phase with the emit phase of `f`. -/
theorem awaitK_bind (e : E) (s : O → QProg R E O β → SubInstrument R R γ)
    (rA rE : β → SubInstrument R R γ) (p : QProg R E O α) (f : α → QProg R E O β) :
    awaitK e s rA rE (p.bind f) =
      awaitK e (fun o q => s o (q.bind f)) (fun a => awaitK e s rA rE (f a))
        (fun a => emitK s rE (f a)) p := by
  induction p with
  | ret a => rfl
  | recv k ih => simp only [bind, awaitK, emitK_bind]
  | send o p ih => rfl
  | opN q k ih => simp only [bind, awaitK, ih]
  | fail => rfl

/-- A quantum operation in the emit phase. -/
theorem emitK_op [Countable β] (s : O → QProg R E O α → SubInstrument R R γ)
    (r : α → SubInstrument R R γ) (q : SubInstrument R R β) (k : β → QProg R E O α) :
    emitK s r (op q k) = q.bind fun b => emitK s r (k b) := by
  simp [op, emitK, SubInstrument.map_eq_bind_pure, SubInstrument.bind_assoc, Encodable.encodek]

/-- A quantum operation in the await phase. -/
theorem awaitK_op [Countable β] (e : E) (s : O → QProg R E O α → SubInstrument R R γ)
    (rA rE : α → SubInstrument R R γ) (q : SubInstrument R R β) (k : β → QProg R E O α) :
    awaitK e s rA rE (op q k) = q.bind fun b => awaitK e s rA rE (k b) := by
  simp [op, awaitK, SubInstrument.map_eq_bind_pure, SubInstrument.bind_assoc, Encodable.encodek]

/-- One activation of the program `p` on the event `e` that continues with `restart a e` when
`p` returns `a` in the await phase: the residual program after the activation's `send`, and the
output. -/
noncomputable def stepWith (restart : α → E → SubInstrument R R (QProg R E O α × O))
    (p : QProg R E O α) (e : E) : SubInstrument R R (QProg R E O α × O) :=
  awaitK e (fun o q => SubInstrument.pure (q, o)) (fun a => restart a e)
    (fun _ => SubInstrument.fail) p

/-- One activation of a program that halts on return: an activation after the return fails. -/
noncomputable def act (p : QProg R E O α) (e : E) : SubInstrument R R (QProg R E O α × O) :=
  stepWith (fun _ _ => SubInstrument.fail) p e

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
    act (.recv fun e => .send (g e) (p e)) e = SubInstrument.pure (p e, g e) := rfl

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
      (step s e).bind fun q => SubInstrument.pure (QProg.ret q.1, q.2)) :
    QRSys.StepEq (⟨QProg R E O σ, loopQSys body s₀⟩ : QRSys.Obj R E O) ⟨σ, ⟨s₀, step⟩⟩ :=
  Relation.EqvGen.symm _ _ (QRSys.StepMap.stepEq (f := QProg.ret)
    ⟨rfl, fun s e => by rw [loopQSys_step_ret, h]⟩)

/-! ## Framing and qubit ports -/

section Frame

variable {M N : Type} [Fintype M] [Fintype N]

/-- The program `p` on the left factor of the register `M × N`: every operation is framed by the
identity on `N`. -/
noncomputable def frameR (p : QProg M E O α) (N : Type) [Fintype N] : QProg (M × N) E O α :=
  match p with
  | .ret a => .ret a
  | .recv k => .recv fun e => (k e).frameR N
  | .send o p => .send o (p.frameR N)
  | .opN q k => .opN (q.frame N) fun n => (k n).frameR N
  | .fail => .fail

/-- The program `p` on the right factor of the register `M × N`: every operation is framed by
the identity on `M`. -/
noncomputable def frameL (p : QProg N E O α) (M : Type) [Fintype M] : QProg (M × N) E O α :=
  match p with
  | .ret a => .ret a
  | .recv k => .recv fun e => (k e).frameL M
  | .send o p => .send o (p.frameL M)
  | .opN q k => .opN (CatCrypt.Quantum.OpenSystem.frameLeft q M) fun n => (k n).frameL M
  | .fail => .fail

/-- **Send a sub-register.** Emit `o` together with the factor `N` of the register `M × N` and
continue as `k` on `M`: no later operation acts on `N`. -/
noncomputable def sendQ (o : O) (k : QProg M E O α) : QProg (M × N) E O α :=
  .send o (k.frameR N)

/-- **Receive a sub-register.** Run `p` on the factor `M` of the register `M × N`, then wait for
the event that hands over the factor `N` and continue on `M × N`. -/
noncomputable def recvQ (p : QProg M E O β) (k : β → E → QProg (M × N) E O α) :
    QProg (M × N) E O α :=
  (p.frameR N).bind fun b => .recv (k b)

/-- The emit phase of a framed program is the framed emit phase. -/
theorem emitK_frameR (p : QProg M E O α) :
    emitK (fun o q => SubInstrument.pure (q, o)) (fun _ => SubInstrument.fail) (p.frameR N) =
      ((emitK (fun o q => SubInstrument.pure (q, o)) (fun _ => SubInstrument.fail) p).frame
        N).bind fun x => SubInstrument.pure (x.1.frameR N, x.2) := by
  induction p with
  | opN q k ih =>
    simp only [frameR, emitK, ih, SubInstrument.frame_bind, SubInstrument.bind_assoc]
  | _ => simp [frameR, emitK]

/-- An activation of a framed program is the framed activation. -/
theorem act_frameR (p : QProg M E O α) (e : E) :
    act (p.frameR N) e =
      ((act p e).frame N).bind fun x => SubInstrument.pure (x.1.frameR N, x.2) := by
  induction p with
  | recv k ih => simp only [frameR, act, stepWith, awaitK, emitK_frameR]
  | opN q k ih =>
    simp only [act, stepWith] at ih
    simp only [frameR, act, stepWith, awaitK, ih, SubInstrument.frame_bind,
      SubInstrument.bind_assoc]
  | _ => simp [frameR, act, stepWith, awaitK]

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
    simp only [frameL, emitK, ih, CatCrypt.Quantum.OpenSystem.frameLeft_bind,
      SubInstrument.bind_assoc]
  | send o p ih =>
    simp [frameL, emitK, CatCrypt.Quantum.OpenSystem.frameLeft_pure]
  | _ => simp [frameL, emitK, frameLeft_fail]

/-- An activation of a program framed on the right factor is the framed activation. -/
theorem act_frameL (p : QProg N E O α) (e : E) :
    act (p.frameL M) e =
      (CatCrypt.Quantum.OpenSystem.frameLeft (act p e) M).bind
        fun x => SubInstrument.pure (x.1.frameL M, x.2) := by
  induction p with
  | recv k ih => simp only [frameL, act, stepWith, awaitK, emitK_frameL]
  | opN q k ih =>
    simp only [act, stepWith] at ih
    simp only [frameL, act, stepWith, awaitK, ih, CatCrypt.Quantum.OpenSystem.frameLeft_bind,
      SubInstrument.bind_assoc]
  | _ => simp [frameL, act, stepWith, awaitK, frameLeft_fail]

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

/-! ## The immediate-subprogram relation and parallel composition -/

/-- `Child c p`: `c` is an immediate subprogram of `p`, a continuation after one operation. -/
inductive Child : QProg R E O α → QProg R E O α → Prop where
  /-- The continuation of a receive at an event. -/
  | recv (k : E → QProg R E O α) (e : E) : Child (k e) (.recv k)
  /-- The continuation of a send. -/
  | send (o : O) (p : QProg R E O α) : Child p (.send o p)
  /-- The continuation of an operation at an outcome code. -/
  | opN (q : SubInstrument R R ℕ) (k : ℕ → QProg R E O α) (n : ℕ) : Child (k n) (.opN q k)

/-- The immediate-subprogram relation is well founded. -/
theorem child_wf : WellFounded (@Child R _ E O α) := by
  refine ⟨fun p => ?_⟩
  induction p with
  | ret a => exact ⟨_, fun y h => nomatch h⟩
  | recv k ih => exact ⟨_, fun y h => by cases h; exact ih _⟩
  | send o p ih => exact ⟨_, fun y h => by cases h; exact ih⟩
  | opN q k ih => exact ⟨_, fun y h => by cases h; exact ih _⟩
  | fail => exact ⟨_, fun y h => nomatch h⟩

/-- Programs ordered by the immediate-subprogram relation. -/
instance instWellFoundedRelation : WellFoundedRelation (QProg R E O α) :=
  ⟨Child, child_wf⟩

mutual

/-- **Parallel composition.** Wait for an event and run one activation of the program on its
side; the program on the other side is unchanged. Both programs act on the shared register. -/
noncomputable def par (p : QProg R E O α) (q : QProg R E' O' β) :
    QProg R (E ⊕ E') (O ⊕ O') Empty :=
  .recv fun e => match e with
    | .inl e₁ => parAwL e₁ p q
    | .inr e₂ => parAwR e₂ p q
  termination_by (p, q, 2)
  decreasing_by
    all_goals exact Prod.Lex.right _ (Prod.Lex.right _ (by decide))

/-- The await phase of the left program on the event `e`. -/
noncomputable def parAwL (e : E) (p : QProg R E O α) (q : QProg R E' O' β) :
    QProg R (E ⊕ E') (O ⊕ O') Empty :=
  match p with
  | .recv k => parEmL (k e) q
  | .opN c k => .opN c fun n => parAwL e (k n) q
  | .ret _ => .fail
  | .send _ _ => .fail
  | .fail => .fail
  termination_by (p, q, 1)
  decreasing_by
    · exact Prod.Lex.left _ _ (Child.recv _ _)
    · exact Prod.Lex.left _ _ (Child.opN _ _ _)

/-- The emit phase of the left program. -/
noncomputable def parEmL (p : QProg R E O α) (q : QProg R E' O' β) :
    QProg R (E ⊕ E') (O ⊕ O') Empty :=
  match p with
  | .send o r => .send (.inl o) (par r q)
  | .opN c k => .opN c fun n => parEmL (k n) q
  | .ret _ => .fail
  | .recv _ => .fail
  | .fail => .fail
  termination_by (p, q, 0)
  decreasing_by
    · exact Prod.Lex.left _ _ (Child.send _ _)
    · exact Prod.Lex.left _ _ (Child.opN _ _ _)

/-- The await phase of the right program on the event `e`. -/
noncomputable def parAwR (e : E') (p : QProg R E O α) (q : QProg R E' O' β) :
    QProg R (E ⊕ E') (O ⊕ O') Empty :=
  match q with
  | .recv k => parEmR p (k e)
  | .opN c k => .opN c fun n => parAwR e p (k n)
  | .ret _ => .fail
  | .send _ _ => .fail
  | .fail => .fail
  termination_by (p, q, 1)
  decreasing_by
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (Child.recv _ _))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (Child.opN _ _ _))

/-- The emit phase of the right program. -/
noncomputable def parEmR (p : QProg R E O α) (q : QProg R E' O' β) :
    QProg R (E ⊕ E') (O ⊕ O') Empty :=
  match q with
  | .send o r => .send (.inr o) (par p r)
  | .opN c k => .opN c fun n => parEmR p (k n)
  | .ret _ => .fail
  | .recv _ => .fail
  | .fail => .fail
  termination_by (p, q, 0)
  decreasing_by
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (Child.send _ _))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (Child.opN _ _ _))

end

/-- The emit phase of `parEmL p q` is the emit phase of `p`, its residual composed with `q` and
its output tagged `inl`. -/
theorem emitK_parEmL (q : QProg R E' O' β) (p : QProg R E O α) :
    emitK (fun o r => SubInstrument.pure (r, o)) (fun _ => SubInstrument.fail) (parEmL p q) =
      (emitK (fun o r => SubInstrument.pure (r, o)) (fun _ => SubInstrument.fail) p).bind
        fun x => SubInstrument.pure (par x.1 q, Sum.inl x.2) := by
  induction p with
  | opN c k ih => simp only [parEmL, emitK, ih, SubInstrument.bind_assoc]
  | _ => simp [parEmL, emitK]

/-- The emit phase of `parEmR p q` is the emit phase of `q`, `p` composed with its residual and
its output tagged `inr`. -/
theorem emitK_parEmR (p : QProg R E O α) (q : QProg R E' O' β) :
    emitK (fun o r => SubInstrument.pure (r, o)) (fun _ => SubInstrument.fail) (parEmR p q) =
      (emitK (fun o r => SubInstrument.pure (r, o)) (fun _ => SubInstrument.fail) q).bind
        fun x => SubInstrument.pure (par p x.1, Sum.inr x.2) := by
  induction q with
  | opN c k ih => simp only [parEmR, emitK, ih, SubInstrument.bind_assoc]
  | _ => simp [parEmR, emitK]

/-- The emit phase of `parAwL e p q` is the activation of `p` on `e`. -/
theorem emitK_parAwL (e : E) (q : QProg R E' O' β) (p : QProg R E O α) :
    emitK (fun o r => SubInstrument.pure (r, o)) (fun _ => SubInstrument.fail) (parAwL e p q) =
      (act p e).bind fun x => SubInstrument.pure (par x.1 q, Sum.inl x.2) := by
  induction p with
  | recv k => simp only [parAwL, act, stepWith, awaitK, emitK_parEmL]
  | opN c k ih =>
    simp only [act, stepWith] at ih
    simp only [parAwL, emitK, act, stepWith, awaitK, ih, SubInstrument.bind_assoc]
  | _ => simp [parAwL, emitK, act, stepWith, awaitK]

/-- The emit phase of `parAwR e p q` is the activation of `q` on `e`. -/
theorem emitK_parAwR (e : E') (p : QProg R E O α) (q : QProg R E' O' β) :
    emitK (fun o r => SubInstrument.pure (r, o)) (fun _ => SubInstrument.fail) (parAwR e p q) =
      (act q e).bind fun x => SubInstrument.pure (par p x.1, Sum.inr x.2) := by
  induction q with
  | recv k => simp only [parAwR, act, stepWith, awaitK, emitK_parEmR]
  | opN c k ih =>
    simp only [act, stepWith] at ih
    simp only [parAwR, emitK, act, stepWith, awaitK, ih, SubInstrument.bind_assoc]
  | _ => simp [parAwR, emitK, act, stepWith, awaitK]

/-- An activation of `par p q` on a left event is the activation of `p`. -/
theorem act_par_inl (p : QProg R E O α) (q : QProg R E' O' β) (e : E) :
    act (par p q) (.inl e) =
      (act p e).bind fun x => SubInstrument.pure (par x.1 q, Sum.inl x.2) := by
  rw [par]
  exact emitK_parAwL e q p

/-- An activation of `par p q` on a right event is the activation of `q`. -/
theorem act_par_inr (p : QProg R E O α) (q : QProg R E' O' β) (e : E') :
    act (par p q) (.inr e) =
      (act q e).bind fun x => SubInstrument.pure (par p x.1, Sum.inr x.2) := by
  rw [par]
  exact emitK_parAwR e p q

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

/-! ## Classical sampling as a diagonal subinstrument -/

/-- The map `ρ ↦ (√c)ρ(√c)` is the scaling by `c ≥ 0`. -/
theorem conj_sqrt_smul_one_apply [DecidableEq R] (c : ℝ) (hc : 0 ≤ c) (ρ : Matrix R R ℂ) :
    MatrixMap.conj (((Real.sqrt c : ℝ) : ℂ) • (1 : Matrix R R ℂ)) ρ = (c : ℂ) • ρ := by
  have hs : ((Real.sqrt c : ℝ) : ℂ) * star ((Real.sqrt c : ℝ) : ℂ) = (c : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  rw [MatrixMap.conj_apply, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    hs]

/-- The probabilities of finitely many codes sum to at most `1`. -/
theorem sum_toReal_le_one (μ : CatCrypt.Prob.SDistr ℕ) (s : Finset ℕ) :
    ∑ n ∈ s, (μ (some n)).toReal ≤ 1 := by
  have h1 : ∑ n ∈ s, μ (some n) ≤ 1 :=
    calc ∑ n ∈ s, μ (some n) ≤ ∑' n, μ (some n) := ENNReal.sum_le_tsum s
      _ ≤ ∑' x, μ x := ENNReal.tsum_comp_le_tsum_of_injective (Option.some_injective _) _
      _ = 1 := μ.tsum_coe
  rw [← ENNReal.toReal_sum (fun n _ => PMF.apply_ne_top μ _)]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h1)

/-- The diagonal subinstrument of the sub-distribution `μ` on codes: the branch at `n` scales the
state by the probability of `n`. -/
noncomputable def diagOp [DecidableEq R] (μ : CatCrypt.Prob.SDistr ℕ) : SubInstrument R R ℕ where
  branch n := MatrixMap.conj (((Real.sqrt (μ (some n)).toReal : ℝ) : ℂ) • (1 : Matrix R R ℂ))
  isCP_branch _ := MatrixMap.isCP_conj _
  trace_le s ρ hρ := by
    simp only [conj_sqrt_smul_one_apply _ ENNReal.toReal_nonneg, Matrix.trace_smul, smul_eq_mul,
      Complex.re_ofReal_mul, ← Finset.sum_mul]
    exact mul_le_of_le_one_left (Complex.nonneg_iff.mp hρ.trace_nonneg).1
      (sum_toReal_le_one μ s)

/-- The branch of `diagOp μ` at `n` scales the state by the probability of `n`. -/
theorem diagOp_branch_apply [DecidableEq R] (μ : CatCrypt.Prob.SDistr ℕ) (n : ℕ)
    (ρ : Matrix R R ℂ) : (diagOp μ).branch n ρ = ((μ (some n)).toReal : ℂ) • ρ :=
  conj_sqrt_smul_one_apply _ ENNReal.toReal_nonneg ρ

/-- Sampling from `μ` at the heap `h` as a diagonal subinstrument: the code marginal of `μ h`.
The heap after the sample is discarded. -/
noncomputable def sampleAt [DecidableEq R] (h : Heap) (μ : SPComp ℕ) : SubInstrument R R ℕ :=
  diagOp ((μ h).map (Option.map Prod.fst))

end QProg

namespace Prog

variable {R : Type} [Fintype R] {E O α β : Type}

/-- **The classical embedding.** The classical program `p` as a quantum program on `R`, each
sample `μ` interpreted by the subinstrument `L μ` (for instance the diagonal subinstrument
`QProg.sampleAt h`). -/
noncomputable def toQProg (L : SPComp ℕ → SubInstrument R R ℕ) : Prog E O α → QProg R E O α
  | .ret a => .ret a
  | .recv k => .recv fun e => toQProg L (k e)
  | .send o p => .send o (toQProg L p)
  | .sampleN μ k => .opN (L μ) fun n => toQProg L (k n)
  | .fail => .fail

/-- The classical embedding is a monad morphism. -/
theorem toQProg_bind (L : SPComp ℕ → SubInstrument R R ℕ) (p : Prog E O α)
    (f : α → Prog E O β) : toQProg L (p.bind f) = (toQProg L p).bind fun a => toQProg L (f a) := by
  induction p with
  | ret a => rfl
  | recv k ih => simp only [Prog.bind, QProg.bind, toQProg, ih]
  | send o p ih => simp only [Prog.bind, QProg.bind, toQProg, ih]
  | sampleN μ k ih => simp only [Prog.bind, QProg.bind, toQProg, ih]
  | fail => rfl

end Prog

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
      simp [qotpRealBody, realStep, act, stepWith, awaitK, emitK, recvE, sendE, opE, bind,
        emitK_bind, emitK_op, SubInstrument.bind_assoc]

end QProg

end CatCrypt.Crypto.Party
