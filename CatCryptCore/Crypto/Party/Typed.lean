/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Derived

/-!
# Intrinsically typed party programs

A dependent interface `Party.Iface E O` is a protocol state of a party with input events `E` and
outputs `O`: at `recvAt accept K` the party waits for an event, accepts exactly the events of
`accept` and continues at `K e`; at `sendAt allow K` it emits an output of `allow` and continues
at `K o`; at `stop` the protocol is over. This is the interaction-tree form of a session type
(Hancock–Setzer), with the moves given as predicates on the event and output types of the party.

A program typed by the interface `I` is a term of the inductive family `Party.TProg Op α I`: a
receive takes only accepted events, a send carries the proof that its output is allowed. Its
erasure `Party.TProg.erase` is a program `ProgE Op E O α` of the party language that fails on
events outside the accepted set.

Port typing of erased programs is a theorem. The interface-indexed port typing
`Party.ProgE.PortsAt I p` says that `p` follows the protocol from the state `I`; every erased
program satisfies it (`Party.TProg.erase_portsAt`), and it implies the global port typing
`ProgE.Ports` at the events and outputs that occur in the interface (`Party.ProgE.PortsAt.ports`).
The denotation `Prog.toSys` keeps the interface-indexed typing along every activation: the
residual after an activation on `e` with output `o` follows the protocol from the state that `I`
reaches by the move `e`, `o` (`Party.Prog.toSys_portsAt`).

## Main definitions

* `Party.Iface E O`: dependent interfaces; `Party.Iface.Acc`, `Party.Iface.Allow`: the events
  and the outputs that occur in an interface; `Party.Iface.Step`: one activation of the protocol;
  `Party.Iface.dual`: the interface of the environment.
* `Party.ProgE.PortsAt`: interface-indexed port typing of programs.
* `Party.TProg Op α I`: programs typed by the interface `I`; `Party.TProg.erase`.

## Main results

* `Party.ProgE.Ports.mono`: port typing is monotone in the port predicates.
* `Party.ProgE.PortsAt.ports`: interface-indexed port typing implies port typing.
* `Party.TProg.erase_portsAt`, `Party.TProg.erase_ports`: port typing of erased programs.
* `Party.Prog.toSys_portsAt`, `Party.TProg.toSys_erase_ports`: the typing of the denotation.
* `Party.Iface.dual_dual`: duality is an involution.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party

open CatCrypt.Core CatCrypt.Crypto.UCTransparent

/-- A dependent interface of a party with input events `E` and outputs `O`: a protocol state that
fixes the events accepted and the outputs allowed at each point. -/
inductive Iface (E O : Type) : Type where
  /-- The protocol is over. -/
  | stop
  /-- Wait for an event of `accept` and continue at `K e`. -/
  | recvAt (accept : E → Prop) (K : E → Iface E O)
  /-- Emit an output of `allow` and continue at `K o`. -/
  | sendAt (allow : O → Prop) (K : O → Iface E O)

namespace Iface

variable {E O : Type}

/-- The events accepted somewhere in the interface, along accepted events and allowed
outputs. -/
def Acc : Iface E O → E → Prop
  | .stop, _ => False
  | .recvAt acc K, e => acc e ∨ ∃ e', acc e' ∧ (K e').Acc e
  | .sendAt allow K, e => ∃ o, allow o ∧ (K o).Acc e

/-- The outputs allowed somewhere in the interface, along accepted events and allowed
outputs. -/
def Allow : Iface E O → O → Prop
  | .stop, _ => False
  | .recvAt acc K, o => ∃ e, acc e ∧ (K e).Allow o
  | .sendAt allow K, o => allow o ∨ ∃ o', allow o' ∧ (K o').Allow o

/-- One activation of the protocol: from `I`, the event `e` is accepted, the output `o` is
allowed next, and the protocol continues at `J`. -/
inductive Step : Iface E O → E → O → Iface E O → Prop where
  /-- Receive an accepted event, then send an allowed output. -/
  | mk {acc : E → Prop} {K : E → Iface E O} {allow : O → Prop} {K' : O → Iface E O}
      (e : E) (o : O) (he : acc e) (hK : K e = .sendAt allow K') (ho : allow o) :
      Step (.recvAt acc K) e o (K' o)

/-- The interface of the environment: its outputs are the party's events and its events the
party's outputs. -/
def dual : Iface E O → Iface O E
  | .stop => .stop
  | .recvAt acc K => .sendAt acc fun e => (K e).dual
  | .sendAt allow K => .recvAt allow fun o => (K o).dual

/-- Duality is an involution. -/
theorem dual_dual (I : Iface E O) : I.dual.dual = I := by
  induction I with
  | stop => rfl
  | recvAt acc K ih => simp only [dual, ih]
  | sendAt allow K ih => simp only [dual, ih]

end Iface

namespace ProgE

variable {Op E O α : Type}

/-- Port typing is monotone in the port predicates. -/
theorem Ports.mono {Pe Pe' : E → Prop} {Po Po' : O → Prop} (he : ∀ e, Pe e → Pe' e)
    (ho : ∀ o, Po o → Po' o) {p : ProgE Op E O α} (hp : Ports Pe Po p) : Ports Pe' Po' p := by
  induction hp with
  | ret a => exact Ports.ret a
  | recv k _ hrej ih =>
    refine Ports.recv k (fun e _ => ?_) fun e he' => hrej e fun h => he' (he e h)
    by_cases h : Pe e
    · exact ih e h
    · rw [hrej e h]; exact Ports.fail
  | send o p ho' _ ih => exact Ports.send o p (ho o ho') ih
  | opN q k _ ih => exact Ports.opN q k ih
  | fail => exact Ports.fail

/-- **Interface-indexed port typing.** `PortsAt I p`: the program `p` follows the protocol from
the state `I`; a `recv` occurs at a `recvAt` state and fails on the events it does not accept,
a `send` occurs at a `sendAt` state with an allowed output. -/
inductive PortsAt : Iface E O → ProgE Op E O α → Prop where
  /-- A return, at any state. -/
  | ret {I : Iface E O} (a : α) : PortsAt I (.ret a)
  /-- A receive at a receiving state. -/
  | recv {acc : E → Prop} {K : E → Iface E O} (k : E → ProgE Op E O α)
      (hacc : ∀ e, acc e → PortsAt (K e) (k e)) (hrej : ∀ e, ¬ acc e → k e = .fail) :
      PortsAt (.recvAt acc K) (.recv k)
  /-- A send of an allowed output at a sending state. -/
  | send {allow : O → Prop} {K : O → Iface E O} (o : O) (p : ProgE Op E O α) (ho : allow o)
      (hp : PortsAt (K o) p) : PortsAt (.sendAt allow K) (.send o p)
  /-- An effect operation, at any state. -/
  | opN {I : Iface E O} (q : Op) (k : ℕ → ProgE Op E O α) (hk : ∀ n, PortsAt I (k n)) :
      PortsAt I (.opN q k)
  /-- Failure, at any state. -/
  | fail {I : Iface E O} : PortsAt I .fail

/-- Interface-indexed port typing implies port typing at the events and outputs of the
interface. -/
theorem PortsAt.ports {I : Iface E O} {p : ProgE Op E O α} (hp : PortsAt I p) :
    Ports I.Acc I.Allow p := by
  induction hp with
  | ret a => exact Ports.ret a
  | @recv acc K k _ hrej ih =>
    refine Ports.recv k (fun e _ => ?_) fun e he => hrej e fun h => he (Or.inl h)
    by_cases h : acc e
    · exact (ih e h).mono (fun x hx => Or.inr ⟨e, h, hx⟩) fun o ho => ⟨e, h, ho⟩
    · rw [hrej e h]; exact Ports.fail
  | send o p ho _ ih =>
    exact Ports.send o p (Or.inl ho) <| ih.mono (fun x hx => ⟨o, ho, hx⟩)
      fun o' ho' => Or.inr ⟨o, ho, ho'⟩
  | opN q k _ ih => exact Ports.opN q k ih
  | fail => exact Ports.fail

end ProgE

/-- Programs over the effect signature `Op` typed by the interface `I`, returning `α`: a receive
takes only accepted events, a send carries the proof that its output is allowed. -/
inductive TProg (Op : Type) {E O : Type} (α : Type) : Iface E O → Type where
  /-- Return `a`, at any state. -/
  | ret {I : Iface E O} (a : α) : TProg Op α I
  /-- Wait for an accepted event and continue with it. -/
  | recv {acc : E → Prop} {K : E → Iface E O} (k : ∀ e, acc e → TProg Op α (K e)) :
      TProg Op α (.recvAt acc K)
  /-- Emit the allowed output `o` and continue. -/
  | send {allow : O → Prop} {K : O → Iface E O} (o : O) (ho : allow o) (k : TProg Op α (K o)) :
      TProg Op α (.sendAt allow K)
  /-- Perform the effect operation `q` and continue with its outcome code. -/
  | opN {I : Iface E O} (q : Op) (k : ℕ → TProg Op α I) : TProg Op α I
  /-- Failure. -/
  | fail {I : Iface E O} : TProg Op α I

namespace TProg

variable {Op E O α : Type}

open Classical in
/-- The erasure of a typed program to a program of the party language: a receive fails on the
events its state does not accept. -/
noncomputable def erase : {I : Iface E O} → TProg Op α I → ProgE Op E O α
  | _, .ret a => .ret a
  | _, @recv _ _ _ _ acc _ k => .recv fun e => if h : acc e then erase (k e h) else .fail
  | _, .send o _ k => .send o (erase k)
  | _, .opN q k => .opN q fun n => erase (k n)
  | _, .fail => .fail

/-- **Port typing of erased programs**, indexed by the interface: an erased program follows the
protocol from its state. -/
theorem erase_portsAt {I : Iface E O} (t : TProg Op α I) : t.erase.PortsAt I := by
  induction t with
  | ret a => exact ProgE.PortsAt.ret a
  | @recv acc K k ih =>
    refine ProgE.PortsAt.recv _ (fun e he => ?_) fun e he => ?_
    · simp only [he, dite_true]
      exact ih e he
    · simp only [he, dite_false]
  | send o ho k ih => exact ProgE.PortsAt.send o _ ho ih
  | opN q k ih => exact ProgE.PortsAt.opN q _ ih
  | fail => exact ProgE.PortsAt.fail

/-- **Port typing of erased programs**: an erased program emits only outputs allowed in its
interface and fails at each `recv` on events its interface never accepts. -/
theorem erase_ports {I : Iface E O} (t : TProg Op α I) : t.erase.Ports I.Acc I.Allow :=
  t.erase_portsAt.ports

end TProg

namespace Prog

variable {E O α : Type}

/-- The outcomes of the emit phase of a program that follows the protocol from `J`: the state `J`
sends, the output is allowed, and the residual follows the protocol from the next state. -/
theorem PortsAt.emitK_outcome {J : Iface E O} {p : Prog E O α} (hp : ProgE.PortsAt J p)
    {q : Prog E O α × O}
    (h : IsOutcome (emitK (fun o r => SPComp.pure (r, o)) (fun _ => SPComp.fail) p) q) :
    ∃ allow K', J = .sendAt allow K' ∧ allow q.2 ∧ ProgE.PortsAt (K' q.2) q.1 := by
  induction hp with
  | ret a => exact absurd h (not_isOutcome_fail _)
  | recv k _ _ _ => exact absurd h (not_isOutcome_fail _)
  | @send allow K o p ho hp _ =>
    obtain rfl := isOutcome_pure h
    exact ⟨allow, K, rfl, ho, hp⟩
  | opN μ k _ ih =>
    rw [emitK_sampleN] at h
    obtain ⟨n, -, hn⟩ := isOutcome_bind h
    exact ih n hn
  | fail => exact absurd h (not_isOutcome_fail _)

/-- The outcomes of an activation of a program that follows the protocol from `I`: the protocol
makes the step of the event and the output, and the residual follows it from the next state. -/
theorem PortsAt.act_outcome {I : Iface E O} {p : Prog E O α} (hp : ProgE.PortsAt I p) {e : E}
    {q : Prog E O α × O} (h : IsOutcome (act p e) q) :
    ∃ J, I.Step e q.2 J ∧ ProgE.PortsAt J q.1 := by
  rw [act_def] at h
  induction hp with
  | ret a => exact absurd h (not_isOutcome_fail _)
  | @recv acc K k hacc hrej _ =>
    by_cases he : acc e
    · obtain ⟨allow, K', hK, ho, hq⟩ := PortsAt.emitK_outcome (hacc e he) h
      exact ⟨K' q.2, Iface.Step.mk e q.2 he hK ho, hq⟩
    · rw [stepWith_def, awaitK_recv, hrej e he, emitK_fail] at h
      exact absurd h (not_isOutcome_fail _)
  | send o p _ _ _ => exact absurd h (not_isOutcome_fail _)
  | opN μ k _ ih =>
    rw [stepWith_def, awaitK_sampleN] at h
    obtain ⟨n, -, hn⟩ := isOutcome_bind h
    exact ih n hn
  | fail => exact absurd h (not_isOutcome_fail _)

/-- **The denotation follows the protocol.** The initial state of the denotation of a program
that follows the protocol from `I` does so; from a state that follows it from `J`, each outcome
of an activation is a step of the protocol from `J`, and the residual follows the protocol from
the next state. -/
theorem toSys_portsAt {I : Iface E O} {p : Prog E O α} (hp : ProgE.PortsAt I p) :
    ProgE.PortsAt I (toSys p).init ∧
      ∀ J t e, ProgE.PortsAt J t → ∀ q, IsOutcome ((toSys p).step t e) q →
        ∃ J', J.Step e q.2 J' ∧ ProgE.PortsAt J' q.1 :=
  ⟨hp, fun _ _ _ ht _ h => PortsAt.act_outcome ht h⟩

end Prog

namespace TProg

variable {E O α : Type}

/-- **Port typing of the denotation of a typed program**: its states stay typed, its outputs
are allowed in the interface, and it has no outcome on an event the interface never accepts. -/
theorem toSys_erase_ports {I : Iface E O} (t : TProg (SPComp ℕ) α I) :
    ProgE.Ports I.Acc I.Allow (Prog.toSys t.erase).init ∧
      ∀ s e, ProgE.Ports I.Acc I.Allow s → ∀ q, IsOutcome ((Prog.toSys t.erase).step s e) q →
        I.Acc e ∧ I.Allow q.2 ∧ ProgE.Ports I.Acc I.Allow q.1 :=
  Prog.toSys_ports t.erase_ports

end TProg

end CatCrypt.Crypto.Party
