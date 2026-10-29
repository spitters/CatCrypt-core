/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCTransparent

/-!
# One-shot protocols as reactive systems

A one-shot protocol `π : hon → SPComp α` maps an input to a result. This file embeds a one-shot
protocol into the reactive systems of `UCTransparent` and transfers a concrete distance
(`UCConcrete.DistC`) between one-shot protocols into a `UCTransparent.Realizes` statement
between their embeddings.

The system `Sys.oneShot π` has state `Bool` (used or not). Its first activation with input `a`
runs `π a` and outputs `some r` for the result `r`; every later activation outputs `none`. An
interactive environment against it reduces to a one-shot environment: its first choice of
input, then its processing of the output and its remaining idle rounds (`Strat.toOneShot`). The
realization bound is the one-shot bound at these environments, taken over the outcomes and heaps
after the first choice.

## Main definitions

* `Sys.oneShot π` — the one-activation system of a one-shot protocol.
* `Strat.idle Z n z` — the environment `Z` run for `n` rounds against an exhausted one-shot
  system.
* `Strat.toOneShot Z D y h` — the one-shot environment of the strategy `Z` with distinguisher
  `D`, after its first choice `y` and heap `h`.
* `oneShotBound b` — the realization bound induced by a one-shot bound `b`.

## Main results

* `loop_oneShot_used` — after the first activation the run is the idle run.
* `view_oneShot_succ` — the view of `Sys.oneShot π` for a strategy with at least one round, in
  one-shot form.
* `realizes_oneShot_of_distC` — a concrete distance between one-shot protocols gives a
  realization between their one-shot systems.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

variable {hon α ζ : Type}

/-- The one-activation system of the one-shot protocol `π`: the first activation runs `π` on
its input and outputs `some` of the result; later activations output `none`. -/
noncomputable def Sys.oneShot (π : hon → SPComp α) : Sys Bool hon (Option α) where
  init := false
  step
    | false, a => SPComp.bind (π a) fun r => SPComp.pure (true, some r)
    | true, _ => SPComp.pure (true, none)

/-- The environment `Z` run for `n` rounds from state `z` against an exhausted one-shot system,
which answers every activation with `none`. -/
noncomputable def Strat.idle (Z : Strat ζ hon (Option α)) : ℕ → ζ → SPComp ζ
  | 0, z => SPComp.pure z
  | n + 1, z => SPComp.bind (Z.next z) fun p =>
      SPComp.bind (Z.obs p.1 none) fun z' => Strat.idle Z n z'

/-- The one-shot environment of the strategy `Z` with distinguisher `D`, after its first choice
`y` (environment state and input) and heap `h`: the input `y.2`, the heap `h`, and the
distinguisher that observes the output, runs the remaining idle rounds and applies `D`. -/
noncomputable def Strat.toOneShot (Z : Strat ζ hon (Option α)) (D : ζ → SPComp Bool)
    (y : ζ × hon) (h : Heap) : Env hon α :=
  ⟨y.2, h, fun r =>
    SPComp.bind (SPComp.bind (Z.obs y.1 (some r)) (Strat.idle Z (Z.rounds - 1))) D⟩

/-- The realization bound induced by the one-shot bound `b`: the supremum of `b` over the
one-shot environments of the strategy, over the outcomes and heaps after its first choice. -/
noncomputable def oneShotBound (b : Env hon α → ℝ≥0∞) (ζ : Type)
    (Z : Env (Strat ζ hon (Option α)) ζ) : ℝ≥0∞ :=
  ⨆ (y : ζ × hon) (h : Heap), b (Strat.toOneShot Z.input Z.dist y h)

/-- The first activation of `Sys.oneShot π` runs `π`. -/
@[simp] theorem oneShot_step_false (π : hon → SPComp α) (a : hon) :
    (Sys.oneShot π).step false a = SPComp.bind (π a) fun r => SPComp.pure (true, some r) :=
  rfl

/-- A later activation of `Sys.oneShot π` outputs `none`. -/
@[simp] theorem oneShot_step_true (π : hon → SPComp α) (a : hon) :
    (Sys.oneShot π).step true a = SPComp.pure (true, none) :=
  rfl

/-- `Sys.oneShot π` starts unused. -/
@[simp] theorem oneShot_init (π : hon → SPComp α) : (Sys.oneShot π).init = false :=
  rfl

/-- After the first activation, the run against `Sys.oneShot π` is the idle run. -/
theorem loop_oneShot_used (π : hon → SPComp α) (Z : Strat ζ hon (Option α)) (n : ℕ)
    (z : ζ) :
    loop (Sys.oneShot π) (fun _ => false) Z n (z, true, false) =
      SPComp.map (fun z' => (z', true, false)) (Strat.idle Z n z) := by
  induction n generalizing z with
  | zero => simp only [loop, Strat.idle, SPComp.map, SPComp.pure_bind]
  | succ n ih =>
    simp only [loop, Strat.idle, oneShot_step_true, SPComp.pure_bind, Bool.or_false, ih,
      SPComp.map, SPComp.bind_assoc]

/-- The view of `Sys.oneShot π` for a strategy with `n + 1` rounds: the first choice, one run
of `π`, the observation of its result, and `n` idle rounds. -/
theorem view_oneShot_succ (π : hon → SPComp α) (Z : Strat ζ hon (Option α)) (n : ℕ)
    (hn : Z.rounds = n + 1) :
    view (Sys.oneShot π) Z = SPComp.bind (Z.next Z.init) fun y =>
      SPComp.bind (π y.2) fun r => SPComp.bind (Z.obs y.1 (some r)) (Strat.idle Z n) := by
  simp only [view, run, hn, loop, oneShot_init, oneShot_step_false, SPComp.bind_assoc,
    SPComp.pure_bind, Bool.or_false, loop_oneShot_used, SPComp.map, SPComp.bind_pure]

/-- A concrete distance `b` between one-shot protocols gives a realization between their
one-shot systems, with bound `oneShotBound b`. -/
theorem realizes_oneShot_of_distC {π₁ π₂ : hon → SPComp α} {b : Env hon α → ℝ≥0∞}
    (h : DistC π₁ π₂ b) :
    Realizes (Sys.oneShot π₁) (Sys.oneShot π₂) (oneShotBound b) := by
  intro ζ Z
  obtain ⟨Zs, h₀, D⟩ := Z
  cases hr : Zs.rounds with
  | zero =>
    have hv : view (Sys.oneShot π₁) Zs = view (Sys.oneShot π₂) Zs := by
      simp only [view, run, hr, loop, oneShot_init]
    simp [Env.gap, hv]
  | succ n =>
    have hg : DistC
        (fun y : ζ × hon => SPComp.bind (π₁ y.2) fun r =>
          SPComp.bind (Zs.obs y.1 (some r)) (Strat.idle Zs n))
        (fun y : ζ × hon => SPComp.bind (π₂ y.2) fun r =>
          SPComp.bind (Zs.obs y.1 (some r)) (Strat.idle Zs n))
        (fun W => b (Strat.toOneShot Zs W.dist W.input W.heap)) := by
      intro W
      simpa only [Env.gap, Strat.toOneShot, SPComp.bind_assoc, hr, Nat.add_sub_cancel] using
        h (Strat.toOneShot Zs W.dist W.input W.heap)
    have hc := DistC.comp_left (fun _ : Unit => Zs.next Zs.init) hg ⟨(), h₀, D⟩
    simpa only [Env.gap, oneShotBound, view_oneShot_succ _ _ _ hr] using hc

end CatCrypt.Crypto.UCTransparent
