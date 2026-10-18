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
# Deterministic transparent functionalities

A deterministic functionality `D : DetFunc σ E O` is an initial state and a
transition function `σ → E → σ × O`. Adversarial choices enter as adversary
events. Its transparent functionality `D.toTFunc x` (in the sense of
`CatCryptCore.Crypto.UCTransparent`) has as guard the predicate `D.legal`:
the trace is a run of `D` from the initial state. Its reference
implementation `D.proto` is the system that applies `D.step`.

## Main results

* `DetFunc.endState_of_legal` — the end state of an accepted trace is the
  state reached on its events, so properties proved of `DetFunc.exec` hold
  on every accepted trace.
* `DetFunc.guardFail_proto` — the guard never fails on the run of the
  reference implementation: `guardFail D.proto (D.toTFunc x).guard Z = 0`
  for every environment `Z`.
* `DetFunc.realizesBound_proto` — the instance: `D.proto` realizes
  `ideal (D.toTFunc x) D.proto` with bound `0`.
* `DetFunc.hybrid_compose` — `Hybrid.transparent_compose` with `D` as the
  subroutine: the subroutine term of the bound vanishes.
* `guardFail_true` — the always-true guard never fails.

The global clock and the Δ-bounded network built on this are in
`CatCryptCore.Crypto.UCClockNetwork`.
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

/-- The reference implementation of a deterministic functionality is lossless. -/
instance lossless_proto (D : DetFunc σ E O) : Lossless D.proto :=
  ⟨fun _ _ => SPComp.pure_noFail _⟩

/-- **Transparency of a deterministic functionality.** The reference implementation of `D`
    realizes the ideal world of `toTFunc D x` with the copy simulator, with bound `0`. -/
instance realizesBound_proto (D : DetFunc σ E O) (x : O) :
    RealizesBound D.proto (ideal (D.toTFunc x) D.proto) (fun _ _ => 0) :=
  haveI : GuardFailBound D.proto (D.toTFunc x).guard (fun _ _ => 0) :=
    ⟨fun _ Z => (guardFail_proto D x Z).le⟩
  inferInstance

/-- **Hybrid composition with a deterministic functionality** (composition
    plumbing). Let `π` be a
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

end CatCrypt.Crypto.UCTransparent
