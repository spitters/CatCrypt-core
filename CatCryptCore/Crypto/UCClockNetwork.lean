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

variable {Pty M : Type} [DecidableEq Pty] [DecidableEq M]

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

end ClockNet

end CatCrypt.Crypto.UCTransparent
