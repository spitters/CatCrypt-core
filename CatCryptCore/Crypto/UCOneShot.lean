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
* `simOf s` — the straight-line simulator map: the simulator runs `s` and hands the result to
  the adversary.
* `idealOf F s` — the ideal functionality `F` followed by `s` on the simulator interface.
* `Sys.lazyShot π` — the lazy one-shot system: idle on the input `none`, it runs `π` on its
  first input `some x`.
* `lazyShotBound b` — the realization bound of the lazy one-shot system induced by a
  one-shot bound `b`.

## Main results

* `loop_oneShot_used` — after the first activation the run is the idle run.
* `view_oneShot_succ` — the view of `Sys.oneShot π` for a strategy with at least one round, in
  one-shot form.
* `realizes_oneShot_of_distC` — a concrete distance between one-shot protocols gives a
  realization between their one-shot systems.
* `realizes_oneShot_of_ucEmulatesCSim` — a `UCEmulatesCSim` statement with simulator map
  `simOf s` gives `Realizes (Sys.oneShot π) (Sys.oneShot (idealOf F s))`, with the bound at the
  dummy adversary `SPComp.pure`.
* `realizes_oneShot_of_ucEmulatesCSim_id` — the same for the identity simulator map.
* `realizes_lazyShot_of_distC` — a concrete distance between one-shot protocols gives a
  realization between their lazy one-shot systems.
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

/-! ## Concrete UC statements of one-shot protocols -/

/-- The straight-line simulator map of `s`: the simulator runs `s` on the simulator interface
and hands the result to the adversary. -/
noncomputable def simOf {sim_if leak V : Type} (s : sim_if → SPComp leak) :
    (leak → SPComp V) → sim_if → SPComp V :=
  fun A x => SPComp.bind (s x) A

/-- At the dummy adversary `SPComp.pure`, the straight-line simulator is `s`. -/
@[simp] theorem simOf_pure {sim_if leak : Type} (s : sim_if → SPComp leak) :
    simOf s SPComp.pure = s :=
  funext fun x => SPComp.bind_pure (s x)

/-- The ideal functionality `F` followed by `s` on the simulator interface. -/
noncomputable def idealOf {out sim_if leak : Type} (F : hon → SPComp (out ⊕ sim_if))
    (s : sim_if → SPComp leak) : hon → SPComp (out ⊕ leak) :=
  fun a => SPComp.bind (F a) (mapSum SPComp.pure s)

/-- A concrete UC emulation of `F` by `π` whose simulator map is the straight-line `simOf s`
gives a realization of `Sys.oneShot (idealOf F s)` by `Sys.oneShot π`; the bound is the
one-shot bound of the UC statement at the dummy adversary `SPComp.pure`. -/
theorem realizes_oneShot_of_ucEmulatesCSim {out sim_if leak : Type}
    {π : hon → SPComp (out ⊕ leak)} {F : hon → SPComp (out ⊕ sim_if)}
    {s : sim_if → SPComp leak}
    {bound : (leak → SPComp leak) → Env hon (out ⊕ leak) → ℝ≥0∞}
    (h : UCEmulatesCSim ⟨hon, out, leak, sim_if, leak⟩ π F (simOf s) bound) :
    Realizes (Sys.oneShot π) (Sys.oneShot (idealOf F s))
      (oneShotBound (bound SPComp.pure)) := by
  have h₀ : DistC π (idealOf F s) (bound SPComp.pure) := fun Z => by
    simpa [Env.gap, idealOf] using h SPComp.pure Z
  exact realizes_oneShot_of_distC h₀

/-- A concrete UC emulation of `F` by `π` with the identity simulator map (`S = A`, the form
of `UCEmulatesCSim_of_DistC` and `UCFromGameC`) gives a realization of `Sys.oneShot F` by
`Sys.oneShot π`; the bound is the one-shot bound of the UC statement at the dummy adversary
`SPComp.pure`. -/
theorem realizes_oneShot_of_ucEmulatesCSim_id {out leak : Type}
    {π F : hon → SPComp (out ⊕ leak)}
    {bound : (leak → SPComp leak) → Env hon (out ⊕ leak) → ℝ≥0∞}
    (h : UCEmulatesCSim ⟨hon, out, leak, leak, leak⟩ π F id bound) :
    Realizes (Sys.oneShot π) (Sys.oneShot F) (oneShotBound (bound SPComp.pure)) :=
  realizes_oneShot_of_distC fun Z => by simpa [Env.gap] using h SPComp.pure Z

/-! ## Lazy one-shot systems -/

section Lazy

/-- The lazy one-shot system of `π`: the input `none` leaves it unchanged with output
`none`; the first input `some x` runs `π x` and outputs `some` of the result; later
activations output `none`. -/
noncomputable def Sys.lazyShot (π : hon → SPComp α) : Sys Bool (Option hon) (Option α) where
  init := false
  step
    | false, none => SPComp.pure (false, none)
    | false, some x => SPComp.bind (π x) fun r => SPComp.pure (true, some r)
    | true, _ => SPComp.pure (true, none)

/-- Unfolding lemma of `Sys.lazyShot`: it starts unused. -/
@[simp] theorem lazyShot_init (π : hon → SPComp α) : (Sys.lazyShot π).init = false := rfl

/-- Unfolding lemma of `Sys.lazyShot`: an unused system is idle on `none`. -/
@[simp] theorem lazyShot_step_false_none (π : hon → SPComp α) :
    (Sys.lazyShot π).step false none = SPComp.pure (false, none) := rfl

/-- Unfolding lemma of `Sys.lazyShot`: the first input `some x` runs `π x`. -/
@[simp] theorem lazyShot_step_false_some (π : hon → SPComp α) (x : hon) :
    (Sys.lazyShot π).step false (some x) =
      SPComp.bind (π x) fun r => SPComp.pure (true, some r) := rfl

/-- Unfolding lemma of `Sys.lazyShot`: a used system outputs `none`. -/
@[simp] theorem lazyShot_step_true (π : hon → SPComp α) (a : Option hon) :
    (Sys.lazyShot π).step true a = SPComp.pure (true, none) := rfl

/-- The run of `Z` against an unused lazy one-shot system for `n` rounds up to its first
input `some x`: the final environment state when no such input occurs (`inl`), or the
environment state, the input `x` and the number of rounds left (`inr`). -/
noncomputable def Strat.lazyPre (Z : Strat ζ (Option hon) (Option α)) :
    ℕ → ζ → SPComp (ζ ⊕ (ζ × hon × ℕ))
  | 0, z => SPComp.pure (Sum.inl z)
  | n + 1, z => SPComp.bind (Z.next z) fun y =>
      match y.2 with
      | none => SPComp.bind (Z.obs y.1 none) (Strat.lazyPre Z n)
      | some x => SPComp.pure (Sum.inr (y.1, x, n))

/-- The rest of the run after `Strat.lazyPre`: one run of `π` on the input, the
observation of its result and the remaining idle rounds. -/
noncomputable def Strat.lazyCont (Z : Strat ζ (Option hon) (Option α)) (π : hon → SPComp α) :
    ζ ⊕ (ζ × hon × ℕ) → SPComp ζ
  | .inl z => SPComp.pure z
  | .inr y => SPComp.bind (π y.2.1) fun r =>
      SPComp.bind (Z.obs y.1 (some r)) (Strat.idle Z y.2.2)

/-- After its first input `some x`, the run against `Sys.lazyShot π` is the idle run. -/
theorem loop_lazyShot_used (π : hon → SPComp α) (Z : Strat ζ (Option hon) (Option α)) (n : ℕ)
    (z : ζ) :
    loop (Sys.lazyShot π) (fun _ => false) Z n (z, true, false) =
      SPComp.map (fun z' => (z', true, false)) (Strat.idle Z n z) := by
  induction n generalizing z with
  | zero => simp only [loop, Strat.idle, SPComp.map, SPComp.pure_bind]
  | succ n ih =>
    simp only [loop, Strat.idle, lazyShot_step_true, SPComp.pure_bind, Bool.or_false, ih,
      SPComp.map, SPComp.bind_assoc]

/-- The view of `Z` from an unused lazy one-shot system is `Strat.lazyPre` followed by
`Strat.lazyCont`. -/
theorem map_fst_loop_lazyShot (π : hon → SPComp α) (Z : Strat ζ (Option hon) (Option α))
    (n : ℕ) (z : ζ) :
    SPComp.map Prod.fst (loop (Sys.lazyShot π) (fun _ => false) Z n (z, false, false)) =
      SPComp.bind (Strat.lazyPre Z n z) (Strat.lazyCont Z π) := by
  induction n generalizing z with
  | zero => simp only [loop, Strat.lazyPre, Strat.lazyCont, SPComp.map, SPComp.pure_bind]
  | succ n ih =>
    simp only [loop, Strat.lazyPre, SPComp.map, SPComp.bind_assoc] at ih ⊢
    congr 1; funext y
    rcases y with ⟨z₁, _ | x⟩
    · simp only [lazyShot_step_false_none, SPComp.pure_bind, Bool.or_false, SPComp.bind_assoc]
      congr 1; funext z₂
      exact ih z₂
    · simp only [lazyShot_step_false_some, SPComp.pure_bind, SPComp.bind_assoc, Bool.or_false,
        loop_lazyShot_used, Strat.lazyCont, SPComp.map, SPComp.bind_pure]

/-- The one-shot environment of the strategy `Z` with distinguisher `D` at the outcome
`y = (z, x, k)` of `Strat.lazyPre` and the heap `h`: the input `x`, the heap `h`, and the
distinguisher that observes the output from `z`, runs `k` idle rounds and applies `D`. -/
noncomputable def Strat.lazyOneShot (Z : Strat ζ (Option hon) (Option α)) (D : ζ → SPComp Bool)
    (y : ζ × hon × ℕ) (h : Heap) : Env hon α :=
  ⟨y.2.1, h, fun r => SPComp.bind (SPComp.bind (Z.obs y.1 (some r)) (Strat.idle Z y.2.2)) D⟩

/-- The realization bound of lazy one-shot systems induced by the one-shot bound `b`: the
supremum of `b` over the one-shot environments of the strategy, over the outcomes of
`Strat.lazyPre` and the heaps. -/
noncomputable def lazyShotBound (b : Env hon α → ℝ≥0∞) (ζ : Type)
    (Z : Env (Strat ζ (Option hon) (Option α)) ζ) : ℝ≥0∞ :=
  ⨆ (y : ζ × hon × ℕ) (h : Heap), b (Strat.lazyOneShot Z.input Z.dist y h)

/-- A concrete distance `b` between one-shot protocols gives a realization between their
lazy one-shot systems, with bound `lazyShotBound b`. -/
theorem realizes_lazyShot_of_distC {π₁ π₂ : hon → SPComp α} {b : Env hon α → ℝ≥0∞}
    (h : DistC π₁ π₂ b) :
    Realizes (Sys.lazyShot π₁) (Sys.lazyShot π₂) (lazyShotBound b) := by
  intro ζ Z
  obtain ⟨Zs, h₀, D⟩ := Z
  have hg : DistC (Strat.lazyCont Zs π₁) (Strat.lazyCont Zs π₂)
      (fun W => Sum.elim (fun _ => 0) (fun y => b (Strat.lazyOneShot Zs W.dist y W.heap))
        W.input) := by
    intro W
    obtain ⟨w, hw, Dw⟩ := W
    cases w with
    | inl z => simp [Env.gap, Strat.lazyCont]
    | inr y =>
      simpa only [Env.gap, Strat.lazyCont, Strat.lazyOneShot, SPComp.bind_assoc, Sum.elim_inr]
        using h (Strat.lazyOneShot Zs Dw y hw)
  have hc := DistC.comp_left (fun _ : Unit => Strat.lazyPre Zs Zs.rounds Zs.init) hg ⟨(), h₀, D⟩
  have hv : ∀ π : hon → SPComp α,
      view (Sys.lazyShot π) Zs = SPComp.bind (Strat.lazyPre Zs Zs.rounds Zs.init)
        (Strat.lazyCont Zs π) := fun π => by
    simp only [view, run, lazyShot_init]
    exact map_fst_loop_lazyShot π Zs Zs.rounds Zs.init
  simp only [Env.gap] at hc ⊢
  rw [hv, hv]
  refine le_trans hc (iSup₂_le fun w h' => ?_)
  cases w with
  | inl z => exact zero_le
  | inr y => exact le_iSup₂_of_le (f := fun y h => b (Strat.lazyOneShot Zs D y h)) y h' le_rfl

end Lazy

end CatCrypt.Crypto.UCTransparent
