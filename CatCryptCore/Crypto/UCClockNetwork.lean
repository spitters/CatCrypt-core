/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCTransparentHybrid

@[expose] public section
set_option autoImplicit false

/-!
# Global clock and Δ-bounded network as transparent functionalities

Placeholder.
-/

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-! ## Deterministic transparent functionalities -/

/-- A deterministic reactive functionality: an initial state and a
    transition function from a state and an event to the next state and the
    output. Adversarial choices (delays, delivery order) enter as adversary
    events. -/
structure DetFunc (σ E O : Type) where
  /-- Initial state. -/
  init : σ
  /-- One activation: next state and output. -/
  step : σ → E → σ × O

namespace DetFunc

variable {σ E O : Type}

/-- The state reached from `s` after the events `es`. -/
def exec (D : DetFunc σ E O) (s : σ) (es : List E) : σ :=
  es.foldl (fun t e => (D.step t e).1) s

/-- The state at the end of the trace `tr`, or `s` on the empty trace. -/
def endState : σ → Trace σ E O → σ
  | s, [] => s
  | _, x :: tr => endState x.2.2 tr

/-- The trace `tr` is a run of `D` from `s`: every entry carries the state
    and output that `D.step` produces from the previous state on its event. -/
def legal [DecidableEq σ] [DecidableEq O] (D : DetFunc σ E O) : σ → Trace σ E O → Bool
  | _, [] => true
  | s, x :: tr => decide (D.step s x.1 = (x.2.2, x.2.1)) && D.legal x.2.2 tr

/-- The transparent functionality of `D`: its guard accepts exactly the
    traces that are runs of `D` from the initial state. -/
def toTFunc [DecidableEq σ] [DecidableEq O] (D : DetFunc σ E O) (exploded : O) : TFunc σ E O :=
  ⟨D.init, D.legal D.init, exploded⟩

/-- The reference implementation of `D` as a transition system. -/
noncomputable def proto (D : DetFunc σ E O) : Sys σ E O :=
  ⟨D.init, fun s e => SPComp.pure (D.step s e)⟩

@[simp] theorem exec_nil (D : DetFunc σ E O) (s : σ) : D.exec s [] = s := rfl

@[simp] theorem exec_cons (D : DetFunc σ E O) (s : σ) (e : E) (es : List E) :
    D.exec s (e :: es) = D.exec (D.step s e).1 es := rfl

theorem exec_append (D : DetFunc σ E O) (s : σ) (es es' : List E) :
    D.exec s (es ++ es') = D.exec (D.exec s es) es' := by
  simp [exec, List.foldl_append]

@[simp] theorem exec_concat (D : DetFunc σ E O) (s : σ) (es : List E) (e : E) :
    D.exec s (es ++ [e]) = (D.step (D.exec s es) e).1 := by
  simp [exec_append]

theorem endState_append (s : σ) (tr : Trace σ E O) (x : E × O × σ) :
    endState s (tr ++ [x]) = x.2.2 := by
  induction tr generalizing s with
  | nil => rfl
  | cons y tr ih => exact ih _

theorem legal_append [DecidableEq σ] [DecidableEq O] (D : DetFunc σ E O) (s : σ)
    (tr : Trace σ E O) (x : E × O × σ) :
    D.legal s (tr ++ [x]) =
      (D.legal s tr && decide (D.step (endState s tr) x.1 = (x.2.2, x.2.1))) := by
  induction tr generalizing s with
  | nil => simp [legal, endState]; congr
  | cons y tr ih => simp [legal, endState, ih, Bool.and_assoc]; congr

/-- The end state of a legal trace is the state reached on its events. -/
theorem endState_of_legal [DecidableEq σ] [DecidableEq O] (D : DetFunc σ E O) :
    ∀ (s : σ) (tr : Trace σ E O), D.legal s tr = true →
      endState s tr = D.exec s (tr.map Prod.fst) := by
  intro s tr
  induction tr generalizing s with
  | nil => intro _; rfl
  | cons x tr ih =>
    intro h
    simp only [legal, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [endState, List.map_cons, exec_cons, h.1]
    exact ih _ h.2

/-- Every prefix of a legal trace is legal. -/
theorem legal_of_legal_append [DecidableEq σ] [DecidableEq O] (D : DetFunc σ E O) (s : σ)
    (tr tr' : Trace σ E O) (h : D.legal s (tr ++ tr') = true) : D.legal s tr = true := by
  induction tr generalizing s with
  | nil => rfl
  | cons x tr ih =>
    simp only [List.cons_append, legal, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ih _ h.2⟩

/-- A state predicate preserved by every step holds on every state reached
    from a state satisfying it. -/
theorem exec_inv (D : DetFunc σ E O) (P : σ → Prop) (hP : ∀ s e, P s → P (D.step s e).1) :
    ∀ (es : List E) (s : σ), P s → P (D.exec s es) := by
  intro es
  induction es with
  | nil => intro s h; exact h
  | cons e es ih => intro s h; exact ih _ (hP _ _ h)

/-! ### The guard never fails on the reference implementation -/

/-- A system whose steps are deterministic and preserve an invariant on
    which `bad` is false never sets the bad flag: `prBad` is `0`. -/
theorem prBad_eq_zero_of_inv {τ ζ : Type} (S : Sys τ E O) (bad : τ → Bool)
    (f : τ → E → τ × O) (hf : ∀ t e, S.step t e = SPComp.pure (f t e))
    (Inv : τ → Prop) (hinit : Inv S.init) (hpres : ∀ t e, Inv t → Inv (f t e).1)
    (hbad : ∀ t, Inv t → bad t = false) (Z : Env (Strat ζ E O) ζ) :
    prBad S bad Z = 0 := by
  have key : ∀ n (z : ζ) (t : τ), Inv t →
      SPComp.bind (loop S bad Z.input n (z, t, false)) (fun c => SPComp.pure c.2.2) =
        SPComp.bind (loop S bad Z.input n (z, t, false)) (fun _ => SPComp.pure false) := by
    intro n
    induction n with
    | zero => intro z t _; simp [loop, SPComp.pure_bind]
    | succ n ih =>
      intro z t ht
      simp only [loop, SPComp.bind_assoc, hf, SPComp.pure_bind]
      congr 1; funext a; congr 1; funext z'
      rw [hbad _ (hpres t a.2 ht), Bool.false_or]
      exact ih _ _ (hpres t a.2 ht)
  unfold prBad run
  rw [hbad _ hinit, key _ _ _ hinit]
  refine le_antisymm ?_ bot_le
  calc _ ≤ prTrue (SPComp.bind (loop S bad Z.input Z.input.rounds (Z.input.init, S.init, false))
          (fun _ => (SPComp.fail : SPComp Bool))) Z.heap :=
        prTrue_bind_le_of_le _ _ _ _ fun _ h' => by simp [prTrue_pure]
    _ = 0 := by rw [bind_fail_right, prTrue_fail]

/-- The always-true guard never fails: `guardFail π (fun _ => true)` is `0`
    for every system `π` and environment. -/
theorem _root_.CatCrypt.Crypto.UCTransparent.guardFail_true {τ E' O' ζ : Type}
    (π : Sys τ E' O') (Z : Env (Strat ζ E' O') ζ) : guardFail π (fun _ => true) Z = 0 := by
  have key : ∀ (Mo : Sys (τ × Trace τ E' O' × Bool) E' O'),
      (∀ t e, Mo.step t e = SPComp.bind (π.step t.1 e) fun p =>
        SPComp.pure ((p.1, t.2.1 ++ [(e, p.2, p.1)], t.2.2 || !true), p.2)) →
      ∀ n (z : ζ) (t : τ × Trace τ E' O' × Bool), t.2.2 = false →
      SPComp.bind (loop Mo exploded Z.input n (z, t, false)) (fun c => SPComp.pure c.2.2) =
        SPComp.bind (loop Mo exploded Z.input n (z, t, false)) (fun _ => SPComp.pure false) := by
    intro Mo hstep n
    induction n with
    | zero => intro z t _; simp [loop, SPComp.pure_bind]
    | succ n ih =>
      intro z t ht
      simp only [loop, hstep, SPComp.bind_assoc, SPComp.pure_bind]
      congr 1; funext a; congr 1; funext p; congr 1; funext z'
      simp only [exploded, ht, Bool.not_true, Bool.or_false]
      exact ih _ _ rfl
  unfold guardFail prBad run
  rw [show exploded (monitor π fun _ => true).init = false from rfl,
    key _ (fun _ _ => rfl) _ _ _ rfl]
  refine le_antisymm ?_ bot_le
  calc _ ≤ prTrue (SPComp.bind (loop (monitor π fun _ => true) exploded Z.input Z.input.rounds
          (Z.input.init, (monitor π fun _ => true).init, false))
          (fun _ => (SPComp.fail : SPComp Bool))) Z.heap :=
        prTrue_bind_le_of_le _ _ _ _ fun _ h' => by simp [prTrue_pure]
    _ = 0 := by rw [bind_fail_right, prTrue_fail]

variable [DecidableEq σ] [DecidableEq O]

/-- On the reference implementation of a deterministic functionality the
    guard of `toTFunc` never fails: `guardFail` is `0` for every
    environment. -/
theorem guardFail_proto (D : DetFunc σ E O) (x : O) {ζ : Type} (Z : Env (Strat ζ E O) ζ) :
    guardFail D.proto (D.toTFunc x).guard Z = 0 := by
  unfold guardFail
  refine prBad_eq_zero_of_inv (monitor D.proto (D.toTFunc x).guard) exploded
    (fun t e => (((D.step t.1 e).1, t.2.1 ++ [(e, (D.step t.1 e).2, (D.step t.1 e).1)],
      t.2.2 || !D.legal D.init (t.2.1 ++ [(e, (D.step t.1 e).2, (D.step t.1 e).1)])),
      (D.step t.1 e).2))
    (fun t e => by simp [monitor, proto, toTFunc, SPComp.pure_bind])
    (fun t => t.2.2 = false ∧ D.legal D.init t.2.1 = true ∧ endState D.init t.2.1 = t.1)
    ⟨rfl, rfl, rfl⟩ ?_ (fun t h => h.1) Z
  rintro ⟨s, tr, b⟩ e ⟨hb, hl, he⟩
  simp only at hb hl he
  subst hb he
  have hl' : D.legal D.init (tr ++ [(e, (D.step (endState D.init tr) e).2,
      (D.step (endState D.init tr) e).1)]) = true := by
    simp [legal_append, hl]
  exact ⟨by simp [hl'], hl', endState_append _ _ _⟩

/-- **Transparency of a deterministic functionality.** The reference
    implementation of `D` realizes the ideal world of `toTFunc D x` with the
    copy simulator, with bound `0`. -/
theorem realizes_proto (D : DetFunc σ E O) (x : O) :
    Realizes D.proto (ideal (D.toTFunc x) D.proto) (fun _ _ => 0) := by
  intro ζ Z
  have h := transparent_realizes_copy D.proto (D.toTFunc x)
    (fun _ _ => SPComp.pure_noFail _) ζ Z
  beta_reduce at h
  rwa [guardFail_proto] at h

/-- **Hybrid composition with a deterministic functionality.** Let `π` be a
    hybrid protocol that calls `D`, and let `F` be a transparent
    functionality over the state space of the `D`-hybrid world
    `π.withSub (ideal (D.toTFunc x) D.proto)`, with a lossless simulator
    `S_F` that starts in the initial state of the hybrid world and agrees
    with it on every transition that keeps the guard of `F` true. Then `π`
    running with the reference implementation of `D` realizes
    `ideal F S_F`, with bound the probability that the guard of `F` fails on
    the run of the hybrid world. The contribution of `D` to the bound of
    `Hybrid.transparent_compose` is `0`. -/
theorem hybrid_compose {τ EH OH : Type} (D : DetFunc σ E O) (x : O) (π : Hybrid τ EH OH E O)
    (S_F : Sys (τ × σ × Trace σ E O × Bool) EH OH)
    (F : TFunc (τ × σ × Trace σ E O × Bool) EH OH)
    (hSF : ∀ s e, SPComp.NoFail (S_F.step s e))
    (hinitF : S_F.init = (π.withSub (ideal (D.toTFunc x) D.proto)).init)
    (hsimF : ∀ s (tr : Trace (τ × σ × Trace σ E O × Bool) EH OH) e,
      SPComp.bind ((π.withSub (ideal (D.toTFunc x) D.proto)).step s e)
        (fun p => if F.guard (tr ++ [(e, p.2, p.1)]) then SPComp.pure p else SPComp.fail) =
      SPComp.bind (S_F.step s e)
        (fun p => if F.guard (tr ++ [(e, p.2, p.1)]) then SPComp.pure p else SPComp.fail)) :
    Realizes (π.withSub D.proto) (ideal F S_F)
      (fun _ Z => guardFail (π.withSub (ideal (D.toTFunc x) D.proto)) F.guard Z) := by
  intro ζ Z
  have h := Hybrid.transparent_compose π D.proto D.proto (D.toTFunc x) S_F F
    (fun _ _ => SPComp.pure_noFail _) (fun _ _ => SPComp.pure_noFail _) hSF rfl hinitF
    (fun _ _ _ => rfl) hsimF ζ Z
  beta_reduce at h
  rwa [guardFail_proto, zero_add] at h

end DetFunc

/-! ## The global clock (Afgjort §2.1) -/

namespace ClockNet

variable {Pty M : Type}

/-- The state of the global clock: the current round and the set of parties
    that have signalled the end of the current round. -/
structure ClockSt (Pty : Type) where
  /-- Current round. -/
  round : ℕ
  /-- Parties that have signalled the end of the current round. -/
  signalled : Finset Pty
deriving DecidableEq

/-- Requests of a party to the clock. -/
inductive ClockReq where
  /-- Signal the end of the current round. -/
  | signal
  /-- Read the current round. -/
  | read
deriving DecidableEq

section Clock

variable [DecidableEq Pty]

/-- Clock events: a party request `(p, r)`, or an adversary read. -/
abbrev ClockEv (Pty : Type) := Event (Pty × ClockReq) Unit

/-- One activation of the clock with honest set `H`. A signal of `p` adds
    `p` to the signalled set; when the signalled set then contains `H`, the
    round advances by one and the signalled set is emptied. Every other event
    leaves the state unchanged. The output is the round after the step. -/
def clockStep (H : Finset Pty) (s : ClockSt Pty) : ClockEv Pty → ClockSt Pty × ℕ
  | .inl (p, .signal) =>
    if H ⊆ insert p s.signalled then (⟨s.round + 1, ∅⟩, s.round + 1)
    else (⟨s.round, insert p s.signalled⟩, s.round)
  | _ => (s, s.round)

/-- The global clock `G_CLOCK` with honest set `H`, from round `0`. -/
def clock (H : Finset Pty) : DetFunc (ClockSt Pty) (ClockEv Pty) ℕ :=
  ⟨⟨0, ∅⟩, clockStep H⟩

/-- The clock never goes back. -/
theorem clockStep_round_mono (H : Finset Pty) (s : ClockSt Pty) (e : ClockEv Pty) :
    s.round ≤ (clockStep H s e).1.round := by
  rcases e with ⟨p, _ | _⟩ | _ <;> simp only [clockStep] <;> (try split_ifs) <;> simp

/-- A step that changes the round is a signal of some party `p` after
    which all honest parties have signalled; it increments the round by one
    and empties the signalled set. -/
theorem clockStep_advance (H : Finset Pty) (s : ClockSt Pty) (e : ClockEv Pty)
    (h : (clockStep H s e).1.round ≠ s.round) :
    ∃ p, e = .inl (p, .signal) ∧ H ⊆ insert p s.signalled ∧
      (clockStep H s e).1 = ⟨s.round + 1, ∅⟩ := by
  rcases e with ⟨p, _ | _⟩ | _
  · simp only [clockStep] at h ⊢
    split_ifs at h ⊢ with hH
    · exact ⟨p, rfl, hH, rfl⟩
    · exact absurd rfl h
  · exact absurd rfl h
  · exact absurd rfl h

/-- Rounds increase monotonically along every run. -/
theorem clock_exec_round_mono (H : Finset Pty) (s : ClockSt Pty) (es : List (ClockEv Pty)) :
    s.round ≤ ((clock H).exec s es).round := by
  induction es generalizing s with
  | nil => exact le_rfl
  | cons e es ih => exact (clockStep_round_mono H s e).trans (ih _)

/-- Within a round, the signalled set holds only parties that signalled, and
    a change of round requires a signal of every honest party: for every run
    from `s` on the events `es`, if the round of the reached state differs
    from that of `s`, every honest party `q` was in the signalled set of `s`
    or issued a signal in `es`. -/
theorem clock_exec_signals (H : Finset Pty) (s : ClockSt Pty) (es : List (ClockEv Pty)) :
    (((clock H).exec s es).round = s.round →
        ∀ q ∈ ((clock H).exec s es).signalled, q ∈ s.signalled ∨ .inl (q, .signal) ∈ es) ∧
      (((clock H).exec s es).round ≠ s.round →
        ∀ q ∈ H, q ∈ s.signalled ∨ .inl (q, .signal) ∈ es) := by
  induction es using List.reverseRecOn with
  | nil => exact ⟨fun _ q hq => .inl hq, fun h => absurd rfl h⟩
  | append_singleton es e ih =>
    rw [DetFunc.exec_concat]
    set t := (clock H).exec s es with ht
    have hmono : s.round ≤ t.round := clock_exec_round_mono H s es
    have hsub : ∀ q, (q ∈ s.signalled ∨ .inl (q, .signal) ∈ es) →
        q ∈ s.signalled ∨ .inl (q, ClockReq.signal) ∈ es ++ [e] := by
      intro q hq; rcases hq with hq | hq
      · exact .inl hq
      · exact .inr (List.mem_append_left _ hq)
    by_cases hts : t.round = s.round
    · have ih1 := ih.1 hts
      rcases e with ⟨p, _ | _⟩ | _
      · simp only [clock, clockStep] at ih1 ⊢
        split_ifs with hH
        · refine ⟨fun h => absurd h (by simp only; omega), fun _ q hq => ?_⟩
          rcases Finset.mem_insert.mp (hH hq) with rfl | hq'
          · exact .inr (by simp)
          · exact hsub q (ih1 q hq')
        · refine ⟨fun _ q hq => ?_, fun h => absurd hts h⟩
          rcases Finset.mem_insert.mp hq with rfl | hq'
          · exact .inr (by simp)
          · exact hsub q (ih1 q hq')
      · exact ⟨fun _ q hq => hsub q (ih1 q hq), fun h => absurd hts h⟩
      · exact ⟨fun _ q hq => hsub q (ih1 q hq), fun h => absurd hts h⟩
    · have hlt : s.round < (clockStep H t e).1.round := lt_of_lt_of_le
        (lt_of_le_of_ne hmono (Ne.symm hts)) (clockStep_round_mono H t e)
      exact ⟨fun h => absurd h (by simp only [clock]; omega),
        fun _ q hq => hsub q (ih.2 hts q hq)⟩

/-- **Rounds advance only after all honest parties signal.** From a state at
    the start of a round (empty signalled set), if a run on the events `es`
    reaches a different round, then every honest party issued a signal in
    `es`. -/
theorem clock_advance_requires_signals (H : Finset Pty) (s : ClockSt Pty)
    (hs : s.signalled = ∅) (es : List (ClockEv Pty))
    (h : ((clock H).exec s es).round ≠ s.round) :
    ∀ q ∈ H, (.inl (q, .signal) : ClockEv Pty) ∈ es := by
  intro q hq
  rcases (clock_exec_signals H s es).2 h q hq with h' | h'
  · simp [hs] at h'
  · exact h'

end Clock

/-! ## The Δ-bounded network (Afgjort §4.2) -/

/-- A message in transit: sender, receiver, content and the round in which
    it was sent. -/
structure Msg (Pty M : Type) where
  /-- Sender. -/
  src : Pty
  /-- Receiver. -/
  dst : Pty
  /-- Content. -/
  body : M
  /-- Round in which the message was sent. -/
  sent : ℕ
deriving DecidableEq

/-- The state of the network: its view of the current round, the messages in
    transit (in sending order), and the delivered messages with their
    delivery round. -/
structure NetSt (Pty M : Type) where
  /-- Current round. -/
  round : ℕ
  /-- Messages in transit. -/
  pending : List (Msg Pty M)
  /-- Delivered messages with their delivery round. -/
  delivered : List (Msg Pty M × ℕ)
deriving DecidableEq

/-- The honest party `p` sends `m` to `q`: the message enters the pending
    list with the current round. Nothing is delivered. -/
def netSend (s : NetSt Pty M) (p q : Pty) (m : M) : NetSt Pty M × List (Msg Pty M) :=
  (⟨s.round, s.pending ++ [⟨p, q, m, s.round⟩], s.delivered⟩, [])

/-- The adversary delivers the `i`-th pending message now (no change if
    there is none). This is how the adversary chooses delays and order. -/
def netDeliver (s : NetSt Pty M) (i : ℕ) : NetSt Pty M × List (Msg Pty M) :=
  match s.pending[i]? with
  | some x => (⟨s.round, s.pending.eraseIdx i, s.delivered ++ [(x, s.round)]⟩, [x])
  | none => (s, [])

/-- The messages that must be delivered before round `s.round` ends:
    those sent at least `Δ` rounds ago. -/
def due (Δ : ℕ) (s : NetSt Pty M) : List (Msg Pty M) :=
  s.pending.filter fun x => decide (x.sent + Δ ≤ s.round)

/-- The end of a round: every due message is delivered in the current
    round, the others stay pending, and the round advances by one. -/
def netTick (Δ : ℕ) (s : NetSt Pty M) : NetSt Pty M × List (Msg Pty M) :=
  (⟨s.round + 1, s.pending.filter (fun x => !decide (x.sent + Δ ≤ s.round)),
    s.delivered ++ (due Δ s).map fun x => (x, s.round)⟩, due Δ s)

/-- Requests to the stand-alone network: an honest send, or the end of the
    round signalled by the clock. -/
inductive NetReq (Pty M : Type) where
  /-- The honest party `p` sends `m` to `q`. -/
  | send (p q : Pty) (m : M)
  /-- The clock has advanced. -/
  | tick
deriving DecidableEq

/-- Network events: requests, or the adversary delivering the `i`-th pending
    message. -/
abbrev NetEv (Pty M : Type) := Event (NetReq Pty M) ℕ

/-- One activation of the network with delay bound `Δ`. The output is the
    list of messages delivered in this activation. -/
def netStep (Δ : ℕ) (s : NetSt Pty M) : NetEv Pty M → NetSt Pty M × List (Msg Pty M)
  | .inl (.send p q m) => netSend s p q m
  | .inl .tick => netTick Δ s
  | .inr i => netDeliver s i

/-- The Δ-bounded network `F_NET` from round `0`. -/
def network (Δ : ℕ) : DetFunc (NetSt Pty M) (NetEv Pty M) (List (Msg Pty M)) :=
  ⟨⟨0, [], []⟩, netStep Δ⟩

/-- The network invariant: every pending message was sent in the current
    round or earlier and is not overdue (the current round is at most `Δ`
    after its sending round), and every delivered message was delivered no
    earlier than its sending round and at most `Δ` rounds after it. -/
def NetInv (Δ : ℕ) (s : NetSt Pty M) : Prop :=
  (∀ x ∈ s.pending, x.sent ≤ s.round ∧ s.round ≤ x.sent + Δ) ∧
    ∀ y ∈ s.delivered, y.1.sent ≤ y.2 ∧ y.2 ≤ y.1.sent + Δ

/-- The message `x` is still accounted for: pending or delivered. -/
def Tracked (x : Msg Pty M) (s : NetSt Pty M) : Prop :=
  x ∈ s.pending ∨ ∃ d, (x, d) ∈ s.delivered

/-- A step of the network state from `s` to `s'` that preserves the
    invariant and loses no message. -/
def NetStepOK (Δ : ℕ) (s s' : NetSt Pty M) : Prop :=
  (NetInv Δ s → NetInv Δ s') ∧ ∀ x, Tracked x s → Tracked x s'

theorem netStepOK_refl (Δ : ℕ) (s : NetSt Pty M) : NetStepOK Δ s s :=
  ⟨id, fun _ => id⟩

theorem netSend_ok (Δ : ℕ) (s : NetSt Pty M) (p q : Pty) (m : M) :
    NetStepOK Δ s (netSend s p q m).1 := by
  refine ⟨fun ⟨h1, h2⟩ => ⟨fun x hx => ?_, h2⟩, fun x hx => ?_⟩
  · simp only [netSend, List.mem_append, List.mem_singleton] at hx ⊢
    rcases hx with hx | rfl
    · exact h1 x hx
    · simp
  · rcases hx with hx | hx
    · exact .inl (by simp [netSend, hx])
    · exact .inr (by simpa [netSend] using hx)

theorem netDeliver_ok (Δ : ℕ) (s : NetSt Pty M) (i : ℕ) :
    NetStepOK Δ s (netDeliver s i).1 := by
  unfold netDeliver
  split
  · rename_i x hx
    have hxm : x ∈ s.pending := List.mem_of_getElem? hx
    refine ⟨fun ⟨h1, h2⟩ => ⟨fun y hy => h1 y (List.mem_of_mem_eraseIdx hy), fun y hy => ?_⟩,
      fun y hy => ?_⟩
    · simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact h2 y hy
      · exact h1 x hxm
    · rcases hy with hy | ⟨d, hd⟩
      · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hy
        by_cases hji : j = i
        · subst hji
          rw [hx] at hj
          cases hj
          exact .inr ⟨s.round, by simp⟩
        · exact .inl (List.mem_eraseIdx_iff_getElem?.mpr ⟨j, hji, hj⟩)
      · exact .inr ⟨d, by simp [hd]⟩
  · exact netStepOK_refl Δ s

theorem netTick_ok (Δ : ℕ) (s : NetSt Pty M) : NetStepOK Δ s (netTick Δ s).1 := by
  refine ⟨fun ⟨h1, h2⟩ => ⟨fun x hx => ?_, fun y hy => ?_⟩, fun x hx => ?_⟩
  · simp only [netTick, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not,
      not_le] at hx ⊢
    have := h1 x hx.1
    omega
  · simp only [netTick, due, List.mem_append, List.mem_map, List.mem_filter,
      decide_eq_true_eq] at hy
    rcases hy with hy | ⟨x, ⟨hx, -⟩, rfl⟩
    · exact h2 y hy
    · exact h1 x hx
  · rcases hx with hx | ⟨d, hd⟩
    · by_cases hdue : x.sent + Δ ≤ s.round
      · exact .inr ⟨s.round, by simp [netTick, due, hx, hdue]⟩
      · exact .inl (by simp [netTick, hx, hdue])
    · exact .inr ⟨d, by simp [netTick, hd]⟩

theorem netStep_ok (Δ : ℕ) (s : NetSt Pty M) (e : NetEv Pty M) :
    NetStepOK Δ s (netStep Δ s e).1 := by
  rcases e with (⟨p, q, m⟩ | _) | i
  · exact netSend_ok Δ s p q m
  · exact netTick_ok Δ s
  · exact netDeliver_ok Δ s i

/-- A tracked message whose deadline has passed is delivered, and its
    delivery round lies between its sending round and `Δ` rounds later. -/
theorem delivered_of_tracked (Δ : ℕ) (s : NetSt Pty M) (x : Msg Pty M)
    (hinv : NetInv Δ s) (hx : Tracked x s) (hlate : x.sent + Δ < s.round) :
    ∃ d, (x, d) ∈ s.delivered ∧ x.sent ≤ d ∧ d ≤ x.sent + Δ := by
  rcases hx with hx | ⟨d, hd⟩
  · have := (hinv.1 x hx).2
    omega
  · exact ⟨d, hd, hinv.2 _ hd⟩

/-- Every state reached by the network satisfies the invariant. -/
theorem network_inv (Δ : ℕ) (es : List (NetEv Pty M)) :
    NetInv Δ ((network (M := M) (Pty := Pty) Δ).exec (network Δ).init es) :=
  DetFunc.exec_inv _ (NetInv Δ) (fun s e h => (netStep_ok Δ s e).1 h) es _
    ⟨fun _ h => by simp [network] at h, fun _ h => by simp [network] at h⟩

/-- **Δ-bounded delivery for the stand-alone network.** Let `pre` be the
    events before the honest party `p` sends `m` to `q`, sent in round
    `r`, and `post` the events after it. If the round reached after `post`
    exceeds `r + Δ`, the message has been delivered in a round `d` with
    `r ≤ d ≤ r + Δ`. -/
theorem network_delivered_within (Δ : ℕ) (pre post : List (NetEv Pty M)) (p q : Pty) (m : M)
    (hlate : ((network Δ).exec (network Δ).init pre).round + Δ <
      ((network Δ).exec (network Δ).init (pre ++ .inl (.send p q m) :: post)).round) :
    ∃ d, (⟨p, q, m, ((network Δ).exec (network Δ).init pre).round⟩, d) ∈
        ((network Δ).exec (network Δ).init (pre ++ .inl (.send p q m) :: post)).delivered ∧
      ((network Δ).exec (network Δ).init pre).round ≤ d ∧
      d ≤ ((network Δ).exec (network Δ).init pre).round + Δ := by
  set s₀ := (network (M := M) (Pty := Pty) Δ).exec (network Δ).init pre
  set x : Msg Pty M := ⟨p, q, m, s₀.round⟩
  rw [DetFunc.exec_append, DetFunc.exec_cons] at hlate ⊢
  have h₁ : NetInv Δ ((network Δ).step s₀ (.inl (.send p q m))).1 ∧
      Tracked x ((network Δ).step s₀ (.inl (.send p q m))).1 :=
    ⟨(netSend_ok Δ s₀ p q m).1 (network_inv Δ pre), .inl (by simp [network, netStep, netSend, x])⟩
  have h₂ := DetFunc.exec_inv (network Δ) (fun s => NetInv Δ s ∧ Tracked x s)
    (fun s e h => ⟨(netStep_ok Δ s e).1 h.1, (netStep_ok Δ s e).2 x h.2⟩) post _ h₁
  exact delivered_of_tracked Δ _ x h₂.1 h₂.2 hlate

/-! ## Clock and network together -/

/-- Requests of a party to the clock-and-network functionality. -/
inductive CNReq (Pty M : Type) where
  /-- Signal the end of the current round. -/
  | signal
  /-- Read the current round. -/
  | read
  /-- Send `m` to `q`. -/
  | send (q : Pty) (m : M)
deriving DecidableEq

/-- Adversary requests to the clock-and-network functionality. -/
inductive CNAdv where
  /-- Read the current round. -/
  | read
  /-- Deliver the `i`-th pending message now. -/
  | deliver (i : ℕ)
deriving DecidableEq

/-- Events of the clock-and-network functionality: a request `(p, r)` of
    party `p`, or an adversary request. -/
abbrev CNEv (Pty M : Type) := Event (Pty × CNReq Pty M) CNAdv

/-- Outputs: the current round and the messages delivered in the
    activation. -/
abbrev CNOut (Pty M : Type) := ℕ × List (Msg Pty M)

/-- The state of the clock-and-network functionality. -/
abbrev CNSt (Pty M : Type) := ClockSt Pty × NetSt Pty M

/-- The clock event underlying a clock-and-network event: signals and reads
    of parties are passed on; sends and adversary requests are clock
    reads. -/
def toClockEv : CNEv Pty M → ClockEv Pty
  | .inl (p, .signal) => .inl (p, .signal)
  | .inl (p, _) => .inl (p, .read)
  | .inr _ => .inr ()

section CN

variable [DecidableEq Pty]

/-- One activation of the clock-and-network functionality with honest set
    `H` and delay bound `Δ`. Signals go to the clock; when the clock
    advances, the network ends its round (`netTick`) and delivers every due
    message. Sends of party `p` and adversary deliveries go to the network.
    The output is the current clock round and the delivered messages. -/
def cnStep (H : Finset Pty) (Δ : ℕ) (s : CNSt Pty M) : CNEv Pty M → CNSt Pty M × CNOut Pty M
  | .inl (p, .signal) =>
    if (clockStep H s.1 (.inl (p, .signal))).1.round = s.1.round then
      (((clockStep H s.1 (.inl (p, .signal))).1, s.2), (s.1.round, []))
    else
      (((clockStep H s.1 (.inl (p, .signal))).1, (netTick Δ s.2).1),
        ((clockStep H s.1 (.inl (p, .signal))).1.round, (netTick Δ s.2).2))
  | .inl (p, .send q m) => ((s.1, (netSend s.2 p q m).1), (s.1.round, (netSend s.2 p q m).2))
  | .inr (.deliver i) => ((s.1, (netDeliver s.2 i).1), (s.1.round, (netDeliver s.2 i).2))
  | _ => (s, (s.1.round, []))

/-- The clock-and-network functionality `G_CLOCK ∥ F_NET` with honest set
    `H` and delay bound `Δ`, from round `0`. -/
def clockNet (H : Finset Pty) (Δ : ℕ) : DetFunc (CNSt Pty M) (CNEv Pty M) (CNOut Pty M) :=
  ⟨(⟨0, ∅⟩, ⟨0, [], []⟩), cnStep H Δ⟩

/-- The clock component of a step is the clock step on the underlying clock
    event. -/
theorem cnStep_clock (H : Finset Pty) (Δ : ℕ) (s : CNSt Pty M) (e : CNEv Pty M) :
    (cnStep H Δ s e).1.1 = (clockStep H s.1 (toClockEv e)).1 := by
  rcases e with ⟨p, _ | _ | ⟨q, m⟩⟩ | (_ | i) <;> simp only [cnStep, toClockEv, clockStep]
  split_ifs <;> rfl

/-- The clock component of a run is the run of the clock on the underlying
    clock events. -/
theorem clockNet_exec_clock (H : Finset Pty) (Δ : ℕ) (s : CNSt Pty M) (es : List (CNEv Pty M)) :
    ((clockNet H Δ).exec s es).1 = (clock H).exec s.1 (es.map toClockEv) := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    simp only [DetFunc.exec_cons, List.map_cons, ih]
    congr 1
    exact cnStep_clock H Δ s e

/-- The clock-and-network invariant: the network round equals the clock
    round, and the network invariant holds. -/
def CNInv (Δ : ℕ) (s : CNSt Pty M) : Prop := s.2.round = s.1.round ∧ NetInv Δ s.2

/-- Every step preserves `CNInv` and loses no message. -/
theorem cnStep_ok (H : Finset Pty) (Δ : ℕ) (s : CNSt Pty M) (e : CNEv Pty M) :
    (CNInv Δ s → CNInv Δ (cnStep H Δ s e).1) ∧ NetStepOK Δ s.2 (cnStep H Δ s e).1.2 := by
  rcases e with ⟨p, _ | _ | ⟨q, m⟩⟩ | (_ | i)
  · simp only [cnStep]
    split_ifs with hr
    · exact ⟨fun h => ⟨h.1.trans hr.symm, h.2⟩, netStepOK_refl Δ s.2⟩
    · obtain ⟨_, -, -, hc⟩ := clockStep_advance H s.1 _ hr
      refine ⟨fun h => ⟨?_, (netTick_ok Δ s.2).1 h.2⟩, netTick_ok Δ s.2⟩
      rw [hc]; simp [netTick, h.1]
  · exact ⟨id, netStepOK_refl Δ s.2⟩
  · exact ⟨fun h => ⟨h.1, (netSend_ok Δ s.2 p q m).1 h.2⟩, netSend_ok Δ s.2 p q m⟩
  · exact ⟨id, netStepOK_refl Δ s.2⟩
  · refine ⟨fun h => ⟨?_, (netDeliver_ok Δ s.2 i).1 h.2⟩, netDeliver_ok Δ s.2 i⟩
    simp only [cnStep, netDeliver]
    split <;> exact h.1

/-- Every state reached by the clock-and-network functionality satisfies
    `CNInv`. -/
theorem clockNet_inv (H : Finset Pty) (Δ : ℕ) (es : List (CNEv Pty M)) :
    CNInv Δ ((clockNet H Δ).exec (clockNet H Δ).init es) :=
  DetFunc.exec_inv _ (CNInv Δ) (fun s e h => (cnStep_ok H Δ s e).1 h) es _
    ⟨rfl, fun _ h => by simp [clockNet] at h, fun _ h => by simp [clockNet] at h⟩

/-- **Rounds advance only after all honest parties signal.** For every run of
    the clock-and-network functionality from a state at the start of a round
    (empty signalled set), if the clock round changes then every honest party
    issued a signal in the run. -/
theorem clockNet_advance_requires_signals (H : Finset Pty) (Δ : ℕ) (s : CNSt Pty M)
    (hs : s.1.signalled = ∅) (es : List (CNEv Pty M))
    (h : ((clockNet H Δ).exec s es).1.round ≠ s.1.round) :
    ∀ q ∈ H, (.inl (q, .signal) : CNEv Pty M) ∈ es := by
  intro q hq
  rw [clockNet_exec_clock] at h
  have hmem := clock_advance_requires_signals H s.1 hs _ h q hq
  obtain ⟨e, he, hee⟩ := List.mem_map.mp hmem
  rcases e with ⟨p, _ | _ | _⟩ | _ <;> simp [toClockEv] at hee
  obtain ⟨rfl, -⟩ := hee
  exact he

/-- After a change of round the signalled set is empty: every round starts
    with no signals, so `clockNet_advance_requires_signals` applies between
    any two consecutive round changes. -/
theorem cnStep_advance_resets (H : Finset Pty) (Δ : ℕ) (s : CNSt Pty M) (e : CNEv Pty M)
    (h : (cnStep H Δ s e).1.1.round ≠ s.1.round) : (cnStep H Δ s e).1.1.signalled = ∅ := by
  rw [cnStep_clock] at h ⊢
  obtain ⟨_, -, -, hc⟩ := clockStep_advance H s.1 _ h
  rw [hc]

/-- **Δ-bounded delivery.** Let `pre` be the events of a run of the
    clock-and-network functionality before the honest party `p` sends `m` to
    `q` in clock round `r`, and `post` the events after it. If the clock
    round reached after `post` exceeds `r + Δ`, the message has been
    delivered in a round `d` with `r ≤ d ≤ r + Δ`. -/
theorem clockNet_delivered_within (H : Finset Pty) (Δ : ℕ) (pre post : List (CNEv Pty M))
    (p q : Pty) (m : M)
    (hlate : ((clockNet H Δ).exec (clockNet H Δ).init pre).1.round + Δ <
      ((clockNet H Δ).exec (clockNet H Δ).init (pre ++ .inl (p, .send q m) :: post)).1.round) :
    ∃ d, (⟨p, q, m, ((clockNet H Δ).exec (clockNet H Δ).init pre).1.round⟩, d) ∈
        ((clockNet H Δ).exec (clockNet H Δ).init (pre ++ .inl (p, .send q m) :: post)).2.delivered ∧
      ((clockNet H Δ).exec (clockNet H Δ).init pre).1.round ≤ d ∧
      d ≤ ((clockNet H Δ).exec (clockNet H Δ).init pre).1.round + Δ := by
  set s₀ := (clockNet (M := M) H Δ).exec (clockNet H Δ).init pre
  have hinv₀ : CNInv Δ s₀ := clockNet_inv H Δ pre
  set x : Msg Pty M := ⟨p, q, m, s₀.1.round⟩
  rw [DetFunc.exec_append, DetFunc.exec_cons] at hlate ⊢
  have h₁ : CNInv Δ ((clockNet H Δ).step s₀ (.inl (p, .send q m))).1 ∧
      Tracked x ((clockNet H Δ).step s₀ (.inl (p, .send q m))).1.2 :=
    ⟨(cnStep_ok H Δ s₀ _).1 hinv₀,
      .inl (by simp [clockNet, cnStep, netSend, x, hinv₀.1])⟩
  have h₂ := DetFunc.exec_inv (clockNet H Δ) (fun s => CNInv Δ s ∧ Tracked x s.2)
    (fun s e h => ⟨(cnStep_ok H Δ s e).1 h.1, (cnStep_ok H Δ s e).2.2 x h.2⟩) post _ h₁
  rw [← h₂.1.1] at hlate
  exact delivered_of_tracked Δ _ x h₂.1.2 h₂.2 hlate

end CN

/-! ## Transparency and trace properties -/

section Transparent

variable [DecidableEq Pty] [DecidableEq M]

/-- The global clock as a transparent functionality (exploded output `0`). -/
def clockF (H : Finset Pty) : TFunc (ClockSt Pty) (ClockEv Pty) ℕ := (clock H).toTFunc 0

/-- The Δ-bounded network as a transparent functionality (exploded output
    the empty delivery list). -/
def networkF (Δ : ℕ) : TFunc (NetSt Pty M) (NetEv Pty M) (List (Msg Pty M)) :=
  (network Δ).toTFunc []

/-- The clock-and-network functionality as a transparent functionality
    (exploded output `(0, [])`). -/
def clockNetF (H : Finset Pty) (Δ : ℕ) : TFunc (CNSt Pty M) (CNEv Pty M) (CNOut Pty M) :=
  (clockNet H Δ).toTFunc (0, [])

/-- **The clock is transparent.** Its reference implementation realizes the
    ideal world of `clockF H` with the copy simulator, with bound `0`. -/
theorem clock_realizes (H : Finset Pty) :
    Realizes (clock H).proto (ideal (clockF H) (clock H).proto) (fun _ _ => 0) :=
  DetFunc.realizes_proto _ _

/-- **The network is transparent.** Its reference implementation realizes
    the ideal world of `networkF Δ` with the copy simulator, with bound
    `0`. -/
theorem network_realizes (Δ : ℕ) :
    Realizes (network (Pty := Pty) (M := M) Δ).proto (ideal (networkF Δ) (network Δ).proto)
      (fun _ _ => 0) :=
  DetFunc.realizes_proto _ _

/-- **The clock-and-network functionality is transparent.** Its reference
    implementation realizes the ideal world of `clockNetF H Δ` with the copy
    simulator, with bound `0`. -/
theorem clockNet_realizes (H : Finset Pty) (Δ : ℕ) :
    Realizes (clockNet (M := M) H Δ).proto (ideal (clockNetF H Δ) (clockNet H Δ).proto)
      (fun _ _ => 0) :=
  DetFunc.realizes_proto _ _

/-- **Δ-bounded delivery on accepted traces.** Let `tr` be a trace accepted
    by the guard of `clockNetF H Δ` whose events are `pre`, a send of `m`
    from the honest party `p` to `q`, and `post`. Let `r` be the clock round
    after `pre`. If the clock round at the end of `tr` exceeds `r + Δ`, then
    the message is in the delivered list of the final state with a delivery
    round `d` such that `r ≤ d ≤ r + Δ`. -/
theorem clockNetF_delivered_within (H : Finset Pty) (Δ : ℕ)
    (tr : Trace (CNSt Pty M) (CNEv Pty M) (CNOut Pty M)) (hg : (clockNetF H Δ).guard tr = true)
    (pre post : List (CNEv Pty M)) (p q : Pty) (m : M)
    (hev : tr.map Prod.fst = pre ++ .inl (p, .send q m) :: post)
    (hlate : ((clockNet H Δ).exec (clockNet H Δ).init pre).1.round + Δ <
      (DetFunc.endState (clockNet H Δ).init tr).1.round) :
    ∃ d, (⟨p, q, m, ((clockNet H Δ).exec (clockNet H Δ).init pre).1.round⟩, d) ∈
        (DetFunc.endState (clockNet H Δ).init tr).2.delivered ∧
      ((clockNet H Δ).exec (clockNet H Δ).init pre).1.round ≤ d ∧
      d ≤ ((clockNet H Δ).exec (clockNet H Δ).init pre).1.round + Δ := by
  rw [DetFunc.endState_of_legal _ _ _ hg, hev] at hlate ⊢
  exact clockNet_delivered_within H Δ pre post p q m hlate

/-- **Round advance on accepted traces.** On every trace accepted by the
    guard of `clockNetF H Δ` whose final clock round is not `0`, every
    honest party has signalled in the trace. -/
theorem clockNetF_advance_requires_signals (H : Finset Pty) (Δ : ℕ)
    (tr : Trace (CNSt Pty M) (CNEv Pty M) (CNOut Pty M)) (hg : (clockNetF H Δ).guard tr = true)
    (h : (DetFunc.endState (clockNet H Δ).init tr).1.round ≠ 0) :
    ∀ q ∈ H, (.inl (q, .signal) : CNEv Pty M) ∈ tr.map Prod.fst := by
  rw [DetFunc.endState_of_legal _ _ _ hg] at h
  exact clockNet_advance_requires_signals H Δ _ rfl _ h

/-- **Composition in the clock-and-network hybrid model.** Let `π` be a
    hybrid protocol that calls the clock-and-network functionality, and let
    `F` be a transparent functionality over the state space of the hybrid
    world `π.withSub (ideal (clockNetF H Δ) (clockNet H Δ).proto)`, with a
    lossless simulator `S_F` that starts in the initial state of the hybrid
    world and agrees with it on every transition that keeps the guard of `F`
    true. Then `π` running with the reference implementation of the clock
    and the network realizes `ideal F S_F`, with bound the probability that
    the guard of `F` fails on the run of the hybrid world: the
    clock-and-network term of `Hybrid.transparent_compose` is `0`. -/
theorem clockNet_hybrid_compose {τ EH OH : Type} (H : Finset Pty) (Δ : ℕ)
    (π : Hybrid τ EH OH (CNEv Pty M) (CNOut Pty M))
    (S_F : Sys (τ × CNSt Pty M × Trace (CNSt Pty M) (CNEv Pty M) (CNOut Pty M) × Bool) EH OH)
    (F : TFunc (τ × CNSt Pty M × Trace (CNSt Pty M) (CNEv Pty M) (CNOut Pty M) × Bool) EH OH)
    (hSF : ∀ s e, SPComp.NoFail (S_F.step s e))
    (hinitF : S_F.init = (π.withSub (ideal (clockNetF H Δ) (clockNet H Δ).proto)).init)
    (hsimF : ∀ s (tr : Trace (τ × CNSt Pty M × Trace (CNSt Pty M) (CNEv Pty M) (CNOut Pty M) ×
        Bool) EH OH) e,
      SPComp.bind ((π.withSub (ideal (clockNetF H Δ) (clockNet H Δ).proto)).step s e)
        (fun p => if F.guard (tr ++ [(e, p.2, p.1)]) then SPComp.pure p else SPComp.fail) =
      SPComp.bind (S_F.step s e)
        (fun p => if F.guard (tr ++ [(e, p.2, p.1)]) then SPComp.pure p else SPComp.fail)) :
    Realizes (π.withSub (clockNet H Δ).proto) (ideal F S_F)
      (fun _ Z => guardFail (π.withSub (ideal (clockNetF H Δ) (clockNet H Δ).proto)) F.guard Z) :=
  DetFunc.hybrid_compose (clockNet H Δ) (0, []) π S_F F hSF hinitF hsimF

end Transparent

/-! ## Non-vacuity: two parties, Δ = 1 -/

namespace Example

/-- Both parties of `Fin 2` are honest. -/
def H₂ : Finset (Fin 2) := Finset.univ

/-- The clock-and-network functionality for two honest parties, `Δ = 1`,
    unit messages. -/
abbrev CN₂ : DetFunc (CNSt (Fin 2) Unit) (CNEv (Fin 2) Unit) (CNOut (Fin 2) Unit) :=
  clockNet H₂ 1

/-- After the send of party `0` to party `1` in round `0`: both parties
    signal twice, and the adversary never delivers. -/
def post₂ : List (CNEv (Fin 2) Unit) :=
  [.inl (0, .signal), .inl (1, .signal), .inl (0, .signal), .inl (1, .signal)]

/-- The full run: the send, then `post₂`. -/
def run₂ : List (CNEv (Fin 2) Unit) := [] ++ .inl (0, .send 1 ()) :: post₂

/-- The run reaches round `2`. -/
theorem run₂_round : (CN₂.exec CN₂.init run₂).1.round = 2 := by decide

/-- The message was delivered by the network in round `1` (forced at the
    end of round `1`, its deadline), and nothing is pending. -/
theorem run₂_net : (CN₂.exec CN₂.init run₂).2 = ⟨2, [], [(⟨0, 1, (), 0⟩, 1)]⟩ := by decide

/-- The hypothesis of `clockNet_delivered_within` holds on `run₂`
    (`0 + 1 < 2`), and its conclusion is witnessed by the delivery round
    `1`. -/
theorem run₂_delivered :
    (CN₂.exec CN₂.init []).1.round + 1 < (CN₂.exec CN₂.init run₂).1.round ∧
      ∃ d, ((⟨0, 1, (), (CN₂.exec CN₂.init []).1.round⟩ : Msg (Fin 2) Unit), d) ∈
          (CN₂.exec CN₂.init run₂).2.delivered ∧
        (CN₂.exec CN₂.init []).1.round ≤ d ∧ d ≤ (CN₂.exec CN₂.init []).1.round + 1 := by
  have h : (CN₂.exec CN₂.init []).1.round + 1 < (CN₂.exec CN₂.init run₂).1.round := by
    rw [run₂_round]; decide
  exact ⟨h, clockNet_delivered_within H₂ 1 [] post₂ 0 1 () h⟩

/-- The hypotheses of `clockNet_advance_requires_signals` hold on `run₂`
    (initial signalled set empty, round changed), and both parties signal. -/
theorem run₂_signals : ∀ q ∈ H₂, (.inl (q, .signal) : CNEv (Fin 2) Unit) ∈ run₂ :=
  clockNet_advance_requires_signals H₂ 1 CN₂.init rfl run₂ (by rw [run₂_round]; decide)

/-- With only one of the two parties signalling, the round does not
    change. -/
theorem one_signal_no_advance :
    (CN₂.exec CN₂.init [.inl (0, .signal), .inl (0, .signal)]).1.round = 0 := by decide

/-- The adversary may deliver early: delivering the pending message right
    after it is sent puts it in the delivered list in round `0`. -/
theorem early_delivery :
    (CN₂.exec CN₂.init [.inl (0, .send 1 ()), .inr (.deliver 0)]).2 =
      ⟨0, [], [(⟨0, 1, (), 0⟩, 0)]⟩ := by decide

/-- The pass-through hybrid protocol: every outer event is forwarded to the
    clock-and-network functionality and its answer is returned. -/
noncomputable def passthrough :
    Hybrid Unit (CNEv (Fin 2) Unit) (CNOut (Fin 2) Unit) (CNEv (Fin 2) Unit) (CNOut (Fin 2) Unit)
    where
  init := ()
  pre s e := SPComp.pure (s, e)
  post s o := SPComp.pure (s, o)
  pre_noFail _ _ := SPComp.pure_noFail _
  post_noFail _ _ := SPComp.pure_noFail _

/-- The hybrid world of `passthrough`. -/
noncomputable abbrev hybridWorld₂ :=
  passthrough.withSub (ideal (clockNetF H₂ 1) CN₂.proto)

/-- A transparent functionality over the hybrid world with the always-true
    guard. -/
noncomputable def trueF :
    TFunc (Unit × CNSt (Fin 2) Unit × Trace (CNSt (Fin 2) Unit) (CNEv (Fin 2) Unit)
      (CNOut (Fin 2) Unit) × Bool) (CNEv (Fin 2) Unit) (CNOut (Fin 2) Unit) :=
  ⟨hybridWorld₂.init, fun _ => true, (0, [])⟩

/-- **Non-vacuity of the composition theorem.** All hypotheses of
    `clockNet_hybrid_compose` hold for `passthrough` with the copy simulator,
    and the resulting bound is `0`: `passthrough` running with the reference
    clock and network realizes `ideal trueF hybridWorld₂` exactly. -/
theorem passthrough_realizes :
    Realizes (passthrough.withSub CN₂.proto) (ideal trueF hybridWorld₂) (fun _ _ => 0) := by
  intro ζ Z
  have h := clockNet_hybrid_compose H₂ 1 passthrough hybridWorld₂ trueF
    (Hybrid.withSub_noFail _ _ (Hybrid.ideal_noFail _ _ fun _ _ => SPComp.pure_noFail _))
    rfl (fun _ _ _ => rfl) ζ Z
  beta_reduce at h
  rwa [show trueF.guard = fun _ => true from rfl, guardFail_true] at h

end Example

end ClockNet

end CatCrypt.Crypto.UCTransparent
