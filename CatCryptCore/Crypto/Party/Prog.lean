/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCLoopbackTrace
public import Mathlib.Logic.Encodable.Basic

/-!
# Party programs and their denotation as reactive systems

A party with input events `E` and outputs `O` is a first-order program tree `Party.Prog E O α`:
it returns, waits for the next activation (`recv`), emits the output of the current activation
(`send`), samples (`sampleN`, a sub-distribution on codes in `ℕ`; `Prog.sample` samples any
countable type through its encoding) or fails. Programs form a monad, so parties are written in
`do` notation.

The denotation is a reactive system `UCTransparent.Sys` whose state is the residual program.
An activation on the event `e` runs the residual program in two phases. In the await phase it
performs the samples up to the next `recv` and feeds it `e`; in the emit phase it performs the
samples up to the next `send o` and stops there with the output `o`. The residual program after
that `send` is the new state, so the samples a party performs after its output and before its
next `recv` are performed at the start of the next activation. A second `recv` before the
`send`, a `send` before the `recv`, or a return in the emit phase is a failure. The two phases
are the continuation-passing interpreters `Prog.emitK` and `Prog.awaitK`, which commute with
`bind` (`Prog.emitK_bind`, `Prog.awaitK_bind`).

A finite program `p` denotes `Prog.toSys p`: after `p` returns, every activation fails. An
unbounded session is `Prog.loopSys body s₀`: when the residual program returns a state `s` in
the await phase, the activation continues with `body s`. When every iteration of `body` is one
activation, `loopSys body s₀` is step-equivalent to the system with state `s₀` and the
iteration as its step (`Prog.loopSys_stepEq`).

## Main definitions

* `Party.Prog E O α`: party programs, with `Monad (Prog E O)`.
* `Party.Prog.recvE`, `Party.Prog.sendE`, `Party.Prog.sampleE`: the operations in `do` notation.
* `Party.Prog.emitK`, `Party.Prog.awaitK`: the two phases of an activation.
* `Party.Prog.act`: one activation of a program that halts on return.
* `Party.Prog.toSys`, `Party.Prog.loopSys`: the denotations of a program and of a loop.
* `Party.Prog.forward`: the stateless forwarding party.

## Main results

* `Party.Prog.emitK_bind`, `Party.Prog.awaitK_bind`: the phases respect `bind`.
* `Party.Prog.awaitK_sample`, `Party.Prog.emitK_sample`: sampling in the phases.
* `Party.Prog.act_recv_send`: a receive followed by a send is one step.
* `Party.Prog.loopSys_stepEq`: a loop of one-activation iterations is step-equivalent to the
  system with the iteration as its step.
* `Party.Prog.forward_stepEq`: the forwarding party denotes `Sys.ofFun`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party

open CatCrypt.Core CatCrypt.Crypto.UCTransparent

/-- Programs of a party with input events `E` and outputs `O`, returning `α`. -/
inductive Prog (E O : Type) (α : Type) : Type where
  /-- Return `a`. -/
  | ret (a : α)
  /-- Wait for the next activation and continue with its event. -/
  | recv (k : E → Prog E O α)
  /-- Emit `o` as the output of the current activation and continue. -/
  | send (o : O) (k : Prog E O α)
  /-- Sample a code from `μ` and continue with it. -/
  | sampleN (μ : SPComp ℕ) (k : ℕ → Prog E O α)
  /-- Failure. -/
  | fail

namespace Prog

variable {E O α β γ σ : Type}

/-- Sequential composition of programs. -/
def bind : Prog E O α → (α → Prog E O β) → Prog E O β
  | .ret a, f => f a
  | .recv k, f => .recv fun e => (k e).bind f
  | .send o p, f => .send o (p.bind f)
  | .sampleN μ k, f => .sampleN μ fun n => (k n).bind f
  | .fail, _ => .fail

instance : Monad (Prog E O) where
  pure := .ret
  bind := bind

/-- `bind` returning its argument is the identity. -/
theorem bind_ret (p : Prog E O α) : p.bind .ret = p := by
  induction p with
  | ret a => rfl
  | recv k ih => simp only [bind, ih]
  | send o p ih => simp only [bind, ih]
  | sampleN μ k ih => simp only [bind, ih]
  | fail => rfl

/-- `bind` is associative. -/
theorem bind_assoc (p : Prog E O α) (f : α → Prog E O β) (g : β → Prog E O γ) :
    (p.bind f).bind g = p.bind fun a => (f a).bind g := by
  induction p with
  | ret a => rfl
  | recv k ih => simp only [bind, ih]
  | send o p ih => simp only [bind, ih]
  | sampleN μ k ih => simp only [bind, ih]
  | fail => rfl

instance : LawfulMonad (Prog E O) := LawfulMonad.mk'
  (id_map := fun p => bind_ret p)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun p f g => bind_assoc p f g)

/-- Wait for the next activation and return its event. -/
def recvE : Prog E O E := .recv .ret

/-- Emit `o` as the output of the current activation. -/
def sendE (o : O) : Prog E O Unit := .send o (.ret ())

/-- Sample from `μ` on a countable type through the codes of its encoding, and continue with
the outcome. A code outside the image of the encoding fails. -/
noncomputable def sample {β : Type} [Countable β] (μ : SPComp β) (k : β → Prog E O α) :
    Prog E O α :=
  letI := Encodable.ofCountable β
  .sampleN (SPComp.map Encodable.encode μ) fun n =>
    match Encodable.decode n with
    | some b => k b
    | none => .fail

/-- Sample from `μ` on a countable type and return the outcome. -/
noncomputable def sampleE {β : Type} [Countable β] (μ : SPComp β) : Prog E O β :=
  sample μ .ret

/-! ## Activations -/

/-- The emit phase: perform the samples up to the next `send o` and continue with `s o` at the
rest; a return continues with `r`; a `recv` or a failure fails. -/
noncomputable def emitK (s : O → Prog E O α → SPComp γ) (r : α → SPComp γ) :
    Prog E O α → SPComp γ
  | .ret a => r a
  | .recv _ => SPComp.fail
  | .send o p => s o p
  | .sampleN μ k => SPComp.bind μ fun n => emitK s r (k n)
  | .fail => SPComp.fail

/-- The await phase on the event `e`: perform the samples up to the next `recv`, feed it `e` and
continue in the emit phase with `s` and `rE`; a return continues with `rA`; a `send` or a
failure fails. -/
noncomputable def awaitK (e : E) (s : O → Prog E O α → SPComp γ) (rA rE : α → SPComp γ) :
    Prog E O α → SPComp γ
  | .ret a => rA a
  | .recv k => emitK s rE (k e)
  | .send _ _ => SPComp.fail
  | .sampleN μ k => SPComp.bind μ fun n => awaitK e s rA rE (k n)
  | .fail => SPComp.fail

/-- The emit phase commutes with `bind`: a return of `p` continues with the emit phase of
`f`. -/
theorem emitK_bind (s : O → Prog E O β → SPComp γ) (r : β → SPComp γ) (p : Prog E O α)
    (f : α → Prog E O β) :
    emitK s r (p.bind f) = emitK (fun o q => s o (q.bind f)) (fun a => emitK s r (f a)) p := by
  induction p with
  | ret a => rfl
  | recv k ih => rfl
  | send o p ih => rfl
  | sampleN μ k ih => simp only [bind, emitK, ih]
  | fail => rfl

/-- The await phase commutes with `bind`: a return of `p` in the await phase continues with the
await phase of `f`, and in the emit phase with the emit phase of `f`. -/
theorem awaitK_bind (e : E) (s : O → Prog E O β → SPComp γ) (rA rE : β → SPComp γ)
    (p : Prog E O α) (f : α → Prog E O β) :
    awaitK e s rA rE (p.bind f) =
      awaitK e (fun o q => s o (q.bind f)) (fun a => awaitK e s rA rE (f a))
        (fun a => emitK s rE (f a)) p := by
  induction p with
  | ret a => rfl
  | recv k ih => simp only [bind, awaitK, emitK_bind]
  | send o p ih => rfl
  | sampleN μ k ih => simp only [bind, awaitK, ih]
  | fail => rfl

/-- Sampling in the emit phase. -/
theorem emitK_sample {β : Type} [Countable β] (s : O → Prog E O α → SPComp γ)
    (r : α → SPComp γ) (μ : SPComp β) (k : β → Prog E O α) :
    emitK s r (sample μ k) = SPComp.bind μ fun b => emitK s r (k b) := by
  simp [sample, emitK, SPComp.map, Encodable.encodek]

/-- Sampling in the await phase. -/
theorem awaitK_sample {β : Type} [Countable β] (e : E) (s : O → Prog E O α → SPComp γ)
    (rA rE : α → SPComp γ) (μ : SPComp β) (k : β → Prog E O α) :
    awaitK e s rA rE (sample μ k) = SPComp.bind μ fun b => awaitK e s rA rE (k b) := by
  simp [sample, awaitK, SPComp.map, Encodable.encodek]

/-- One activation of the program `p` on the event `e` that continues with `restart a e` when
`p` returns `a` in the await phase: the residual program after the activation's `send`, and the
output. -/
noncomputable def stepWith (restart : α → E → SPComp (Prog E O α × O)) (p : Prog E O α)
    (e : E) : SPComp (Prog E O α × O) :=
  awaitK e (fun o q => SPComp.pure (q, o)) (fun a => restart a e) (fun _ => SPComp.fail) p

/-- One activation of a program that halts on return: an activation after the return fails. -/
noncomputable def act (p : Prog E O α) (e : E) : SPComp (Prog E O α × O) :=
  stepWith (fun _ _ => SPComp.fail) p e

/-- The denotation of a program: the state is the residual program, the step an activation. -/
noncomputable def toSys (p : Prog E O α) : Sys (Prog E O α) E O where
  init := p
  step := act

/-- The denotation of the loop of `body` from `s₀`: the state is the residual program of the
current iteration, starting at the return of `s₀`; a return of `s` in the await phase continues
the activation with `body s`. -/
noncomputable def loopSys (body : σ → Prog E O σ) (s₀ : σ) : Sys (Prog E O σ) E O where
  init := .ret s₀
  step := stepWith fun s e => act (body s) e

/-- Unfolding lemma of `act`: a receive followed by a send is one step. -/
theorem act_recv_send (g : E → O) (p : E → Prog E O α) (e : E) :
    act (.recv fun e => .send (g e) (p e)) e = SPComp.pure (p e, g e) := rfl

/-- Unfolding lemma of `loopSys`: the step at the return of `s` is the activation of
`body s`. -/
theorem loopSys_step_ret (body : σ → Prog E O σ) (s₀ s : σ) (e : E) :
    (loopSys body s₀).step (.ret s) e = act (body s) e := rfl

/-- The returned state, or `d` at a program that is not a return. -/
def retOr (d : σ) : Prog E O σ → σ
  | .ret s => s
  | _ => d

/-- **Loops of one activation.** When the activation of `body s` on every event is the step
`step s e` followed by a return, the loop of `body` from `s₀` is step-equivalent to the system
with initial state `s₀` and step `step`. -/
theorem loopSys_stepEq (body : σ → Prog E O σ) (s₀ : σ) (step : σ → E → SPComp (σ × O))
    (h : ∀ s e, act (body s) e = SPComp.map (fun q => (Prog.ret q.1, q.2)) (step s e)) :
    Sys.StepEq ⟨Prog E O σ, loopSys body s₀⟩ ⟨σ, ⟨s₀, step⟩⟩ := by
  refine Sys.StepMapOn.stepEq (Inv := fun p => ∃ s, p = .ret s) (f := retOr s₀) ?_
  refine ⟨⟨s₀, rfl⟩, rfl, ?_, ?_⟩
  · rintro t e ⟨s, rfl⟩ q hq
    rw [loopSys_step_ret, h] at hq
    obtain ⟨a, -, rfl⟩ := exists_of_isOutcome_map hq
    exact ⟨a.1, rfl⟩
  · rintro t e ⟨s, rfl⟩
    rw [loopSys_step_ret, h, SPComp.map_comp]
    exact SPComp.map_id _

/-! ## Example: the forwarding party -/

/-- The forwarding party for `f`: receive an event `e` and emit `f e`. -/
def forward (f : E → O) : Prog E O Unit := do
  let e ← recvE
  sendE (f e)

/-- The loop of the forwarding party is step-equivalent to the stateless system `Sys.ofFun f`. -/
theorem forward_stepEq (f : E → O) :
    Sys.StepEq ⟨Prog E O Unit, loopSys (fun _ => forward f) ()⟩ ⟨Unit, Sys.ofFun f⟩ :=
  loopSys_stepEq _ _ _ fun _ e => by rw [SPComp.map_pure]; rfl

end Prog

end CatCrypt.Crypto.Party
