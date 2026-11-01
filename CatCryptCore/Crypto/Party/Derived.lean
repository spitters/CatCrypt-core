/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Call
public import CatCryptCore.Crypto.Party.Compose

/-!
# Structure derived from party programs: port typing, opacity, unwinding

The structural facts of a party of the party language are read off the syntax of its program
`Party.Prog E O α`, once for all programs, instead of being proved for each hand-written system.

Step unfolding. The activation `Prog.act` of a program, the step of its denotation
`Prog.toSys`, unfolds along `ret`, `recv`, `send`, a sample and `fail` (`Prog.act_ret`,
`Prog.act_recv`, `Prog.act_send`, `Prog.act_sampleN`, `Prog.act_fail`) and along `bind`
(`Prog.act_bind`).

Port typing. `ProgE.Ports Pe Po p` says that the program `p` emits only outputs satisfying `Po`,
accepts at each `recv` the events satisfying `Pe` and fails on the other events. The denotation
of such a program keeps the predicate on its states, emits only outputs satisfying `Po`, and has
no outcome on an event outside `Pe` (`Prog.toSys_ports`, `Prog.loopSys_ports`).

Opacity. Information flow is the relation `ProgE.ViewRel V RA p p'` on programs for a public
view `V` (`UCTransparent.PubView`): the two programs have the same shape, perform the same
samples, emit outputs related by `V.out`, and continue after a `recv` at events related by
`V.ev` with related programs. A program related to itself has `ViewRel V RA` as an unwinding
relation of its denotation in the sense of `Sys.Unwinding`, so the denotation is opaque for `V`
(`Prog.toSys_opaque`, and `Prog.loopSys_opaque` for loops).

Factoring through a projection. A program whose continuations after each `recv` depend on the
event `e` only through `f e` (`ProgE.ReadsVia f p`) has equal activations on events with equal
images (`Prog.ReadsVia.act_eq`), and, for a section `g` of `f`, its denotation is step-equivalent
to the denotation of the program on the projected events `ProgE.comapEv g p`, with ports
relabelled by `f` (`Prog.toSys_stepEq_of_readsVia`).

The worked example is the X3DH simulator written as a program (`X3DHProg.simBody`): its loop is
opaque from the view of `F_AKE` to the view of the real interface
(`X3DHProg.simLoopSys_opaque`), from the port typing of its sampling subprograms and the
relatedness of the answers of the simulator (`X3DHSquare.simOut_rel`).

Search words: party language, information flow, opacity, unwinding, port typing, step
unfolding.

## Main definitions

* `Party.ProgE.Ports`: port typing of programs.
* `Party.ProgE.ViewRel`: the information-flow relation of programs for a public view.
* `Party.ProgE.comapEv`, `Party.ProgE.ReadsVia`: programs on projected events, and programs that
  read events through a projection.
* `UCTransparent.PubView.callView`: the view of a system on the sum interface of a multi-call
  simulator.

## Main results

* `Party.Prog.act_bind` and the unfolding lemmas of `Party.Prog.act`.
* `Party.Prog.toSys_ports`, `Party.Prog.loopSys_ports`: port typing of the denotation.
* `Party.Prog.toSys_unwinding`, `Party.Prog.toSys_opaque`, `Party.Prog.loopSys_unwinding`,
  `Party.Prog.loopSys_opaque`: opacity from information flow.
* `Party.Prog.ReadsVia.act_eq`, `Party.Prog.toSys_stepEq_of_readsVia`: factoring through a
  projection of events.
* `Party.X3DHProg.simLoopSys_opaque`: opacity of the X3DH simulator program.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent.PubView

variable {E O EG OG : Type}

/-- The view of a system on the sum interface of a multi-call simulator with outer view `V` and
subroutine view `W`: outer events related by `V.ev` and subroutine answers by `W.out`; the
outputs are the decisions of the simulator, related by `PubView.StepRel V W`. -/
def callView (V : PubView E O) (W : PubView EG OG) : PubView (E ⊕ OG) (EG ⊕ O) where
  ev := Sum.LiftRel V.ev W.out
  out := StepRel V W

end CatCrypt.Crypto.UCTransparent.PubView

namespace CatCrypt.Crypto.Party

open CatCrypt.Core CatCrypt.Crypto.UCTransparent CatCrypt.Relational

namespace ProgE

variable {Op : Type} {E E' O α β : Type}

/-! ## Port typing -/

/-- **Port typing.** `Ports Pe Po p`: every output the program `p` emits satisfies `Po`; at each
`recv` the continuation at an event satisfying `Pe` is typed, and at any other event it is the
failure. -/
inductive Ports (Pe : E → Prop) (Po : O → Prop) : ProgE Op E O α → Prop where
  /-- A return is typed. -/
  | ret (a : α) : Ports Pe Po (.ret a)
  /-- A receive accepting the events of `Pe` and failing on the others. -/
  | recv (k : E → ProgE Op E O α) (hacc : ∀ e, Pe e → Ports Pe Po (k e))
      (hrej : ∀ e, ¬ Pe e → k e = .fail) : Ports Pe Po (.recv k)
  /-- A send of an output of `Po`. -/
  | send (o : O) (p : ProgE Op E O α) (ho : Po o) (hp : Ports Pe Po p) :
      Ports Pe Po (.send o p)
  /-- An effect operation with typed continuations. -/
  | opN (q : Op) (k : ℕ → ProgE Op E O α) (hk : ∀ n, Ports Pe Po (k n)) :
      Ports Pe Po (.opN q k)
  /-- Failure is typed. -/
  | fail : Ports Pe Po .fail

/-- Port typing is closed under `bind`. -/
theorem Ports.bind {Pe : E → Prop} {Po : O → Prop} {p : ProgE Op E O α}
    {f : α → ProgE Op E O β} (hp : Ports Pe Po p) (hf : ∀ a, Ports Pe Po (f a)) :
    Ports Pe Po (p.bind f) := by
  induction hp with
  | ret a => exact hf a
  | recv k _ hrej ih =>
    exact Ports.recv (fun e => (k e).bind f) ih fun e he => by simp only [hrej e he, ProgE.bind]
  | send o p ho _ ih => exact Ports.send o _ ho ih
  | opN q k _ ih => exact Ports.opN q _ ih
  | fail => exact Ports.fail

/-! ## Information flow -/

/-- **Information flow for a public view.** `ViewRel V RA p p'`: the programs `p` and `p'` have
the same shape, perform the same effect operations, emit outputs related by `V.out`, continue
after a `recv` at events related by `V.ev` with related programs, and return values related by
`RA`. A program related to itself reads of each event only what `V.ev` keeps, and shows of each
output only what `V.out` keeps. -/
inductive ViewRel (V : PubView E O) (RA : α → α → Prop) :
    ProgE Op E O α → ProgE Op E O α → Prop where
  /-- Related returns. -/
  | ret {a a' : α} (h : RA a a') : ViewRel V RA (.ret a) (.ret a')
  /-- Receives with related continuations at related events. -/
  | recv {k k' : E → ProgE Op E O α} (h : ∀ e e', V.ev e e' → ViewRel V RA (k e) (k' e')) :
      ViewRel V RA (.recv k) (.recv k')
  /-- Sends of related outputs with related continuations. -/
  | send {o o' : O} {p p' : ProgE Op E O α} (ho : V.out o o') (hp : ViewRel V RA p p') :
      ViewRel V RA (.send o p) (.send o' p')
  /-- The same effect operation with related continuations. -/
  | opN (q : Op) {k k' : ℕ → ProgE Op E O α} (h : ∀ n, ViewRel V RA (k n) (k' n)) :
      ViewRel V RA (.opN q k) (.opN q k')
  /-- Failures. -/
  | fail : ViewRel V RA .fail .fail

/-- Information flow is closed under `bind`. -/
theorem ViewRel.bind {V : PubView E O} {RA : α → α → Prop} {RB : β → β → Prop}
    {p p' : ProgE Op E O α} {f f' : α → ProgE Op E O β} (hp : ViewRel V RA p p')
    (hf : ∀ a a', RA a a' → ViewRel V RB (f a) (f' a')) :
    ViewRel V RB (p.bind f) (p'.bind f') := by
  induction hp with
  | ret h => exact hf _ _ h
  | recv _ ih => exact ViewRel.recv ih
  | send ho _ ih => exact ViewRel.send ho ih
  | opN q _ ih => exact ViewRel.opN q ih
  | fail => exact ViewRel.fail

/-- A program that neither receives nor sends is related to itself for every view. -/
theorem ViewRel.refl_of_ports {V : PubView E O} {RA : α → α → Prop} (hRA : ∀ a, RA a a)
    {p : ProgE Op E O α} (hp : Ports (fun _ => False) (fun _ => False) p) : ViewRel V RA p p := by
  induction hp with
  | ret a => exact ViewRel.ret (hRA a)
  | recv k _ hrej _ =>
    exact ViewRel.recv fun e e' _ => by
      rw [hrej e not_false, hrej e' not_false]
      exact ViewRel.fail
  | send o p ho _ _ => exact ho.elim
  | opN q k _ ih => exact ViewRel.opN q ih
  | fail => exact ViewRel.fail

/-! ## Programs on projected events -/

/-- The program `p` on the events `E`, reading the event `e` as `f e`. -/
def comapEv (f : E → E') : ProgE Op E' O α → ProgE Op E O α
  | .ret a => .ret a
  | .recv k => .recv fun e => comapEv f (k (f e))
  | .send o p => .send o (comapEv f p)
  | .opN q k => .opN q fun n => comapEv f (k n)
  | .fail => .fail

/-- `ReadsVia f p`: the continuation of each `recv` of `p` depends on the event `e` only through
`f e`. -/
inductive ReadsVia (f : E → E') : ProgE Op E O α → Prop where
  /-- A return. -/
  | ret (a : α) : ReadsVia f (.ret a)
  /-- A receive whose continuation factors through `f`. -/
  | recv {k : E → ProgE Op E O α} (hk : ∀ e e', f e = f e' → k e = k e')
      (h : ∀ e, ReadsVia f (k e)) : ReadsVia f (.recv k)
  /-- A send. -/
  | send (o : O) {p : ProgE Op E O α} (h : ReadsVia f p) : ReadsVia f (.send o p)
  /-- An effect operation. -/
  | opN (q : Op) {k : ℕ → ProgE Op E O α} (h : ∀ n, ReadsVia f (k n)) : ReadsVia f (.opN q k)
  /-- Failure. -/
  | fail : ReadsVia f .fail

/-- A program that reads events through `f` is the program on projected events of its
precomposition with a section `g` of `f`. -/
theorem ReadsVia.comapEv_comapEv {f : E → E'} {g : E' → E} (hfg : ∀ x, f (g x) = x)
    {p : ProgE Op E O α} (h : ReadsVia f p) : comapEv f (comapEv g p) = p := by
  induction h with
  | ret a => rfl
  | recv hk _ ih =>
    simp only [comapEv, ih]
    congr 1
    funext e
    exact hk _ _ (hfg (f e))
  | send o _ ih => simp only [comapEv, ih]
  | opN q _ ih => simp only [comapEv, ih]
  | fail => rfl

/-- A program that reads events through `f` is related to itself for the view of `f`. -/
theorem ReadsVia.viewRel {f : E → E'} {LO : Type} (po : O → LO) {p : ProgE Op E O α}
    (h : ReadsVia f p) : ViewRel (PubView.ofProj f po) Eq p p := by
  induction h with
  | ret a => exact ViewRel.ret rfl
  | recv hk _ ih =>
    refine ViewRel.recv fun e e' he => ?_
    rw [← hk e e' he]
    exact ih e
  | send o _ ih => exact ViewRel.send rfl ih
  | opN q _ ih => exact ViewRel.opN q ih
  | fail => exact ViewRel.fail

variable {M : Type → Type} {γ : Type}

/-- The emit phase of a program on projected events. -/
theorem emitK_comapEv (H : Handler Op M) (f : E → E') (s : O → ProgE Op E O α → M γ)
    (r : α → M γ) (p : ProgE Op E' O α) :
    emitK H s r (comapEv f p) = emitK H (fun o q => s o (comapEv f q)) r p := by
  induction p with
  | opN q k ih => simp only [comapEv, emitK, ih]
  | _ => rfl

/-- The await phase of a program on projected events reads the projected event. -/
theorem awaitK_comapEv (H : Handler Op M) (f : E → E') (e : E) (s : O → ProgE Op E O α → M γ)
    (rA rE : α → M γ) (p : ProgE Op E' O α) :
    awaitK H e s rA rE (comapEv f p) =
      awaitK H (f e) (fun o q => s o (comapEv f q)) rA rE p := by
  induction p with
  | recv k => exact emitK_comapEv H f s rE (k (f e))
  | opN q k ih => simp only [comapEv, awaitK, ih]
  | _ => rfl

end ProgE

namespace Prog

variable {E E' O α β σ : Type}

/-! ## Step unfolding -/

/-- Unfolding lemma of `toSys`: the step is the activation. -/
@[simp] theorem toSys_step (p : Prog E O α) : (toSys p).step = act := rfl

/-- Unfolding lemma of `act` at a return: an activation after the return fails. -/
@[simp] theorem act_ret (a : α) (e : E) : act (.ret a : Prog E O α) e = SPComp.fail := rfl

/-- Unfolding lemma of `act` at a receive: the emit phase of the continuation at the event. -/
@[simp] theorem act_recv (k : E → Prog E O α) (e : E) :
    act (.recv k) e = emitK (fun o q => SPComp.pure (q, o)) (fun _ => SPComp.fail) (k e) := rfl

/-- Unfolding lemma of `act` at a send: a send before the receive fails. -/
@[simp] theorem act_send (o : O) (p : Prog E O α) (e : E) :
    act (.send o p) e = SPComp.fail := rfl

/-- Unfolding lemma of `act` at a sample. -/
@[simp] theorem act_sampleN (μ : SPComp ℕ) (k : ℕ → Prog E O α) (e : E) :
    act (.opN μ k) e = SPComp.bind μ fun n => act (k n) e := rfl

/-- Unfolding lemma of `act` at a failure. -/
@[simp] theorem act_fail (e : E) : act (.fail : Prog E O α) e = SPComp.fail := rfl

/-- **The activation of a `bind`**: the await phase of `p`, its residual followed by `f`; a
return of `p` before the `recv` continues with the activation of `f`, after it with the emit
phase of `f`. -/
theorem act_bind (p : Prog E O α) (f : α → Prog E O β) (e : E) :
    act (ProgE.bind p f) e =
      awaitK e (fun o q => SPComp.pure (ProgE.bind q f, o)) (fun a => act (f a) e)
        (fun a => emitK (fun o q => SPComp.pure (q, o)) (fun _ => SPComp.fail) (f a)) p :=
  awaitK_bind e _ _ _ p f

/-! ## Port typing of the denotation -/

/-- A failure has no outcome. -/
theorem not_isOutcome_fail {γ : Type} (a : γ) : ¬ IsOutcome (SPComp.fail : SPComp γ) a := by
  rintro ⟨hp, hp', h⟩
  exact h (by simp [SPComp.fail])

/-- The outcomes of the emit phase of a typed program are typed residuals with outputs of
`Po`. -/
theorem Ports.emitK_outcome {Pe : E → Prop} {Po : O → Prop} {p : Prog E O α}
    (hp : ProgE.Ports Pe Po p) {q : Prog E O α × O}
    (h : IsOutcome (emitK (fun o r => SPComp.pure (r, o)) (fun _ => SPComp.fail) p) q) :
    Po q.2 ∧ ProgE.Ports Pe Po q.1 := by
  induction hp with
  | ret a => exact absurd h (not_isOutcome_fail _)
  | recv k _ _ _ => exact absurd h (not_isOutcome_fail _)
  | send o p ho hp _ =>
    obtain rfl := isOutcome_pure h
    exact ⟨ho, hp⟩
  | opN μ k _ ih =>
    rw [emitK_sampleN] at h
    obtain ⟨n, -, hn⟩ := isOutcome_bind h
    exact ih n hn
  | fail => exact absurd h (not_isOutcome_fail _)

/-- The outcomes of an activation of a typed program, which continues with `restart` on a
return, are typed residuals with outputs of `Po`, at events of `Pe`. -/
theorem Ports.stepWith_outcome {Pe : E → Prop} {Po : O → Prop}
    {restart : α → E → SPComp (Prog E O α × O)} {e : E}
    (hr : ∀ a q, IsOutcome (restart a e) q → Pe e ∧ Po q.2 ∧ ProgE.Ports Pe Po q.1)
    {p : Prog E O α} (hp : ProgE.Ports Pe Po p) {q : Prog E O α × O}
    (h : IsOutcome (stepWith restart p e) q) : Pe e ∧ Po q.2 ∧ ProgE.Ports Pe Po q.1 := by
  induction hp with
  | ret a => exact hr a q h
  | recv k hacc hrej _ =>
    by_cases he : Pe e
    · exact ⟨he, Ports.emitK_outcome (hacc e he) h⟩
    · rw [stepWith_def, awaitK_recv, hrej e he, emitK_fail] at h
      exact absurd h (not_isOutcome_fail _)
  | send o p _ _ _ => exact absurd h (not_isOutcome_fail _)
  | opN μ k _ ih =>
    rw [stepWith_def, awaitK_sampleN] at h
    obtain ⟨n, -, hn⟩ := isOutcome_bind h
    exact ih n hn
  | fail => exact absurd h (not_isOutcome_fail _)

/-- **Port typing of the denotation.** The states of the denotation of a typed program stay
typed, its outputs satisfy `Po`, and it has no outcome on an event outside `Pe`. -/
theorem toSys_ports {Pe : E → Prop} {Po : O → Prop} {p : Prog E O α}
    (hp : ProgE.Ports Pe Po p) :
    ProgE.Ports Pe Po (toSys p).init ∧
      ∀ t e, ProgE.Ports Pe Po t → ∀ q, IsOutcome ((toSys p).step t e) q →
        Pe e ∧ Po q.2 ∧ ProgE.Ports Pe Po q.1 :=
  ⟨hp, fun _ _ ht _ h =>
    Ports.stepWith_outcome (fun _ _ h => absurd h (not_isOutcome_fail _)) ht h⟩

/-- **Port typing of a loop.** When every iteration is typed, the states of the loop stay typed,
its outputs satisfy `Po`, and it has no outcome on an event outside `Pe`. -/
theorem loopSys_ports {Pe : E → Prop} {Po : O → Prop} (body : σ → Prog E O σ) (s₀ : σ)
    (hb : ∀ s, ProgE.Ports Pe Po (body s)) :
    ProgE.Ports Pe Po (loopSys body s₀).init ∧
      ∀ t e, ProgE.Ports Pe Po t → ∀ q, IsOutcome ((loopSys body s₀).step t e) q →
        Pe e ∧ Po q.2 ∧ ProgE.Ports Pe Po q.1 :=
  ⟨ProgE.Ports.ret s₀, fun _ _ ht _ h =>
    Ports.stepWith_outcome (fun s _ h => Ports.stepWith_outcome
      (fun _ _ h => absurd h (not_isOutcome_fail _)) (hb s) h) ht h⟩

/-! ## Opacity from information flow -/

/-- The emit phases of related programs are coupled at equal heaps into related residuals and
related outputs. -/
theorem ViewRel.emitK_rHoare {V : PubView E O} {RA : α → α → Prop} {p p' : Prog E O α}
    (h : ProgE.ViewRel V RA p p') :
    rHoare eqPre (emitK (fun o r => SPComp.pure (r, o)) (fun _ => SPComp.fail) p)
      (emitK (fun o r => SPComp.pure (r, o)) (fun _ => SPComp.fail) p')
      (fun r h r' h' => h = h' ∧ ProgE.ViewRel V RA r.1 r'.1 ∧ V.out r.2 r'.2) := by
  induction h with
  | ret _ => exact rHoare_fail
  | recv _ _ => exact rHoare_fail
  | send ho hp _ => exact rHoare_ret fun _ _ hh => ⟨hh, hp, ho⟩
  | opN μ _ ih =>
    rw [emitK_sampleN, emitK_sampleN]
    refine rHoare_bind (rHoare_refl μ) fun n n' h₁ h₂ hpre => ?_
    obtain ⟨rfl, rfl⟩ := hpre
    exact ih n h₁ h₁ rfl
  | fail => exact rHoare_fail

/-- **Activations of related programs** on related events are coupled at equal heaps into
related residuals and related outputs, when the restarts on related returns are. -/
theorem ViewRel.stepWith_rHoare {V : PubView E O} {RA : α → α → Prop}
    {restart restart' : α → E → SPComp (Prog E O α × O)} {e e' : E}
    (hr : ∀ a a', RA a a' → rHoare eqPre (restart a e) (restart' a' e')
      (fun r h r' h' => h = h' ∧ ProgE.ViewRel V RA r.1 r'.1 ∧ V.out r.2 r'.2))
    {p p' : Prog E O α} (h : ProgE.ViewRel V RA p p') (he : V.ev e e') :
    rHoare eqPre (stepWith restart p e) (stepWith restart' p' e')
      (fun r h r' h' => h = h' ∧ ProgE.ViewRel V RA r.1 r'.1 ∧ V.out r.2 r'.2) := by
  induction h with
  | ret ha => exact hr _ _ ha
  | recv hk _ => exact ViewRel.emitK_rHoare (hk e e' he)
  | send _ _ _ => exact rHoare_fail
  | opN μ _ ih =>
    rw [stepWith_def, stepWith_def, awaitK_sampleN, awaitK_sampleN]
    refine rHoare_bind (rHoare_refl μ) fun n n' h₁ h₂ hpre => ?_
    obtain ⟨rfl, rfl⟩ := hpre
    exact ih n h₁ h₁ rfl
  | fail => exact rHoare_fail

/-- **The unwinding condition of a program.** For a program related to itself for the view
`V`, information flow `ViewRel V RA` is an unwinding relation of its denotation. -/
theorem toSys_unwinding {V : PubView E O} {RA : α → α → Prop} {p : Prog E O α}
    (hp : ProgE.ViewRel V RA p p) : Sys.Unwinding (toSys p) V (ProgE.ViewRel V RA) :=
  ⟨hp, fun _ _ _ _ ht he => ViewRel.stepWith_rHoare (restart := fun _ _ => SPComp.fail)
    (restart' := fun _ _ => SPComp.fail) (fun _ _ _ => rHoare_fail) ht he⟩

/-- **Opacity of a program**: a program related to itself for the view `V` denotes a system
opaque for `V`. -/
theorem toSys_opaque {V : PubView E O} {RA : α → α → Prop} {p : Prog E O α}
    (hp : ProgE.ViewRel V RA p p) : (toSys p).Opaque V :=
  ⟨_, toSys_unwinding hp⟩

/-- **The unwinding condition of a loop.** When the initial state is related to itself by `RA`
and the iterations from `RA`-related states are related, information flow `ViewRel V RA` is an
unwinding relation of the loop. -/
theorem loopSys_unwinding {V : PubView E O} {RA : σ → σ → Prop} (body : σ → Prog E O σ)
    (s₀ : σ) (h₀ : RA s₀ s₀) (hb : ∀ s s', RA s s' → ProgE.ViewRel V RA (body s) (body s')) :
    Sys.Unwinding (loopSys body s₀) V (ProgE.ViewRel V RA) :=
  ⟨ProgE.ViewRel.ret h₀, fun _ _ _ _ ht he =>
    ViewRel.stepWith_rHoare (fun s s' hs => ViewRel.stepWith_rHoare
      (restart := fun _ _ => SPComp.fail) (restart' := fun _ _ => SPComp.fail)
      (fun _ _ _ => rHoare_fail) (hb s s' hs) he) ht he⟩

/-- **Opacity of a loop** whose iterations from related states are related. -/
theorem loopSys_opaque {V : PubView E O} {RA : σ → σ → Prop} (body : σ → Prog E O σ)
    (s₀ : σ) (h₀ : RA s₀ s₀) (hb : ∀ s s', RA s s' → ProgE.ViewRel V RA (body s) (body s')) :
    (loopSys body s₀).Opaque V :=
  ⟨_, loopSys_unwinding body s₀ h₀ hb⟩

/-! ## Factoring through a projection of events -/

/-- A program that reads events through `f` has equal activations on events with equal
images. -/
theorem ReadsVia.act_eq {f : E → E'} {p : Prog E O α} (h : ProgE.ReadsVia f p) {e e' : E}
    (he : f e = f e') : act p e = act p e' := by
  induction h with
  | recv hk _ _ => rw [act_recv, act_recv, hk e e' he]
  | opN μ _ ih => exact congrArg (SPComp.bind μ) (funext ih)
  | _ => rfl

/-- The activation of a program on projected events is the activation on the projected event,
its residual on projected events. -/
theorem act_comapEv (f : E → E') (q : Prog E' O α) (e : E) :
    act (ProgE.comapEv f q) e =
      SPComp.map (fun x => (ProgE.comapEv f x.1, x.2)) (act q (f e)) := by
  have h := ProgE.bind_awaitK handler handler_lawful (f e) (fun o r => SPComp.pure (r, o))
    (fun _ => SPComp.fail) (fun _ => SPComp.fail)
    (fun x : Prog E' O α × O => SPComp.pure (ProgE.comapEv f x.1, x.2)) q
  simp only [handler, SPComp.pure_bind, SPComp.fail_bind] at h
  simp only [act, ProgE.act, ProgE.stepWith, ProgE.awaitK_comapEv, SPComp.map]
  exact h.symm

/-- The denotation of a program with ports relabelled by `f` steps along `comapEv f` to the
denotation of the program on projected events. -/
theorem comapEv_stepMap (f : E → E') (q : Prog E' O α) :
    Sys.StepMapOn ((toSys q).mapPorts f id) (toSys (ProgE.comapEv f q)) (fun _ => True)
      (ProgE.comapEv f) :=
  Sys.StepMapOn.of_step _ rfl fun t e => by
    simp [Sys.mapPorts, Sys.relabel, toSys, act_comapEv, SPComp.map_comp, Function.comp_def]

/-- **Factoring through a projection.** The denotation of a program that reads events through
`f` is step-equivalent to the denotation of its precomposition with a section `g` of `f`, with
ports relabelled by `f`. -/
theorem toSys_stepEq_of_readsVia {f : E → E'} {g : E' → E} (hfg : ∀ x, f (g x) = x)
    {p : Prog E O α} (h : ProgE.ReadsVia f p) :
    Sys.StepEq ⟨_, (toSys (ProgE.comapEv g p)).mapPorts f id⟩ ⟨_, toSys p⟩ := by
  have hs := (comapEv_stepMap f (ProgE.comapEv g p)).stepEq
  rwa [h.comapEv_comapEv hfg] at hs

end Prog

/-! ## Example: opacity of the X3DH simulator program -/

namespace X3DHProg

open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract Prog

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- Programs that neither receive nor send. -/
abbrev NoIO {α : Type} (p : P S W K α) : Prop := ProgE.Ports (fun _ => False) (fun _ => False) p

omit [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- Sampling from a countable type keeps a program free of receives and sends. -/
theorem noIO_sample {α β : Type} [Countable β] {μ : SPComp β} {k : β → P S W K α}
    (hk : ∀ b, NoIO (k b)) : NoIO (Prog.sample μ k) := by
  unfold Prog.sample
  refine ProgE.Ports.opN _ _ fun n => ?_
  split
  · exact hk _
  · exact ProgE.Ports.fail

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- `ltP` neither receives nor sends. -/
theorem ltP_noIO (s : RSt S W K) (pid : PartyId) : NoIO (ltP s pid : P S W K _) := by
  unfold ltP
  split
  · exact ProgE.Ports.ret _
  · exact noIO_sample fun _ => ProgE.Ports.ret _

omit [Field S] [Fintype S] [DecidableEq W] [Inhabited K] in
/-- `roP` neither receives nor sends. -/
theorem roP_noIO {D : Type} [DecidableEq D] (tb : List (D × K)) (x : D) :
    NoIO (roP tb x : P S W K _) := by
  unfold roP
  split
  · exact ProgE.Ports.ret _
  · exact noIO_sample fun _ => ProgE.Ports.ret _

omit [Field S] [Fintype S] in
/-- `deliverP` neither receives nor sends. -/
theorem deliverP_noIO (rs : RSt S W K) (inp : Inst → Option (Inp W)) (x : Inst) (r : Rec K)
    (ip : Inp W) : NoIO (deliverP rs inp x r ip) := by
  unfold deliverP
  split
  · exact ProgE.Ports.bind (roP_noIO _ _) fun _ => ProgE.Ports.ret _
  · exact ProgE.Ports.ret _

/-- `simCompleteP` neither receives nor sends. -/
theorem simCompleteP_noIO (s : SimSt S W K) (x : Inst) : NoIO (simCompleteP G s x) := by
  unfold simCompleteP
  cases s.1.st.recs x with
  | none => exact ProgE.Ports.ret _
  | some r =>
    cases s.1.eph x with
    | none => exact ProgE.Ports.ret _
    | some ek =>
      dsimp only
      cases opkOf s.1 x.1 r.peer with
      | none => exact ProgE.Ports.ret _
      | some opk =>
        dsimp only
        split
        · exact ProgE.Ports.bind (ltP_noIO _ _) fun _ => ProgE.Ports.bind (ltP_noIO _ _)
            fun _ => deliverP_noIO _ _ _ _ _
        · exact ProgE.Ports.ret _

/-- `simSendP` neither receives nor sends. -/
theorem simSendP_noIO (s : SimSt S W K) (x : Inst) (e : W) : NoIO (simSendP G s x e) := by
  unfold simSendP
  cases s.1.st.recs x with
  | none => exact ProgE.Ports.ret _
  | some r =>
    cases s.1.eph x with
    | none => exact ProgE.Ports.ret _
    | some opk =>
      dsimp only
      split
      · exact ProgE.Ports.bind (ltP_noIO _ _) fun _ => ProgE.Ports.bind (ltP_noIO _ _)
          fun _ => deliverP_noIO _ _ _ _ _
      · exact ProgE.Ports.ret _

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- `simCorruptP` neither receives nor sends. -/
theorem simCorruptP_noIO (s : SimSt S W K) (pid : PartyId) : NoIO (simCorruptP s pid) := by
  unfold simCorruptP
  split
  · exact ProgE.Ports.ret _
  · exact ProgE.Ports.bind (ltP_noIO _ _) fun _ => ProgE.Ports.ret _

/-- `simStartP` neither receives nor sends. -/
theorem simStartP_noIO (s : SimSt S W K) (e : OEv W) : NoIO (simStartP G s e) := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ | pid |
    ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | x)
  · simp only [simStartP]
    split
    · exact noIO_sample fun _ => ProgE.Ports.ret _
    · exact ProgE.Ports.ret _
  · exact ProgE.Ports.ret _
  · exact ProgE.Ports.ret _
  · exact ProgE.Ports.ret _
  · exact ProgE.Ports.bind (ltP_noIO _ _) fun _ => ProgE.Ports.ret _
  · exact ProgE.Ports.ret _
  · exact simCorruptP_noIO _ _
  · exact simCompleteP_noIO G _ _
  · exact simSendP_noIO G _ _ _
  · exact ProgE.Ports.bind (roP_noIO _ _) fun _ => ProgE.Ports.ret _

omit [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The end of an activation is related to itself: the answers of `F_AKE` related by the view
of `F_AKE` give related outputs (`simOut_rel`). -/
theorem simDecide_viewRel (q : SimSt S W K × Dec S W K) :
    ProgE.ViewRel (PubView.callView outerView subView) Eq (simDecide q) (simDecide q) := by
  rcases q with ⟨s, f | o⟩
  · refine ProgE.ViewRel.send (stepRel_refl (.inl f : Dec S W K))
      (ProgE.ViewRel.recv fun x x' hx => ?_)
    cases hx with
    | inl _ => exact ProgE.ViewRel.fail
    | inr ha => exact ProgE.ViewRel.send (simOut_rel s.2.2 ha) (ProgE.ViewRel.ret rfl)
  · exact ProgE.ViewRel.send (stepRel_refl (.inr o)) (ProgE.ViewRel.ret rfl)

/-- The X3DH simulator program is related to itself for the view of its sum interface. -/
theorem simBody_viewRel (s : SimSt S W K) :
    ProgE.ViewRel (PubView.callView outerView subView) Eq (simBody G s) (simBody G s) := by
  unfold simBody
  refine ProgE.ViewRel.bind (RA := Eq) ?_ fun e e' he => ?_
  · refine ProgE.ViewRel.recv fun x x' hx => ?_
    cases hx with
    | @inl a b h =>
      have h' : a = b := by
        cases h with
        | inl h => exact congrArg Sum.inl h
        | inr h => exact congrArg Sum.inr h
      subst h'
      exact ProgE.ViewRel.ret rfl
    | inr _ => exact ProgE.ViewRel.fail
  · subst he
    refine ProgE.ViewRel.bind
      (ProgE.ViewRel.refl_of_ports (fun _ => rfl) (simStartP_noIO G s e)) fun q q' hq => ?_
    subst hq
    exact simDecide_viewRel q

/-- **Opacity of the X3DH simulator program.** The loop of `simBody` is opaque from the view of
`F_AKE` to the view of the real interface: its decisions, up to the honest values they carry,
depend only on the public parts of its events and of the answers of `F_AKE`. -/
theorem simLoopSys_opaque (s₀ : SimSt S W K) :
    (loopSys (simBody G) s₀).Opaque (PubView.callView outerView subView) :=
  loopSys_opaque _ s₀ rfl fun s _ hs => hs ▸ simBody_viewRel G s

end X3DHProg

end CatCrypt.Crypto.Party
