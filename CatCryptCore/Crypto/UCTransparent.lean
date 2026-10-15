/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCConcrete
public import CatCryptCore.Crypto.NomPkgBridge

@[expose] public section
set_option autoImplicit false

/-!
# Transparent functionalities: realization up to a guard

A functionality is *transparent* (Afgjort, SCN 2020, §4.2; Enig, ePrint
2022/201, §3) when honest parties have no secret inputs and the adversary
drives every state change, subject to a guard on the trace: the functionality
accepts a proposed transition when the extended trace satisfies the guard
(common prefix, chain growth, chain quality, ...) and otherwise sets an
`Exploded` flag, after which every output is the designated exploded output.
The simulator runs the protocol on the real inputs and copies its state into
the functionality. This file proves once and generically that the simulation
is perfect up to the event that the guard fails on the real trace.

## Model

* `Sys τ E O` — a reactive transition system with state `τ`, input events
  `E` and outputs `O`: one probabilistic step `τ → E → SPComp (τ × O)` per
  activation. Protocols, simulators, and ideal worlds are all `Sys`.
* `Event P A = P ⊕ A` — inputs from honest parties (`P`) and from the
  adversary (`A`).
* `Strat ζ E O` — an interactive environment with internal state `ζ`: it
  chooses the next event, observes the output, and runs for `rounds`
  activations. Under the dummy-adversary convention the environment also
  drives the adversary's inputs. Its two transition functions are lossless
  (`next_noFail`, `obs_noFail`): environments always halt.
* `loop`, `run` — the joint run of an environment and a system, carrying a
  *bad flag* that is the disjunction of a state predicate `bad` over all
  visited states. The bad event is therefore part of the run itself.
* `view S Z` — the final environment state; `adv R I Z` is the advantage of
  the environment `Z` (input strategy, initial heap, distinguisher) between
  two systems.
* `Realizes R I bound` — for every environment state type `ζ` and every
  environment `Z`, `adv R I Z ≤ bound ζ Z`.
* `Trace`, `TFunc` — traces of `(event, output, state)` entries and
  transparent functionalities (initial state, trace guard, exploded output).
* `monitor π G` — the protocol `π` together with a passive monitor that
  records the trace and the guard failure flag; its view is that of `π`
  (`view_monitor`).
* `ideal F S` — the ideal world of `F` with simulator `S`: the simulator
  proposes `(output, state)`, the functionality appends it to its trace and
  accepts iff the guard holds; on a guard failure it explodes.
* `guardFail π G Z` — the probability that the guard `G` fails somewhere on
  the real trace of `π` under the environment `Z`.

## Main results

* `restrictGood_loop_eq` — two systems whose steps agree from every good
  state, after discarding transitions into bad states, have equal runs once
  runs that ever visit a bad state are discarded.
* `adv_le_prBad` — the up-to-bad lemma on the joint run: under that
  hypothesis and losslessness of both systems, the advantage of every
  environment is at most the probability of the bad flag in the first run.
* `transparent_realizes` — if the simulator agrees with the protocol on
  every transition that keeps the guard true, then `π` realizes `ideal F S`
  with bound `guardFail π F.guard`.
* `transparent_realizes_copy` — the copy simulator `S = π` satisfies the
  hypothesis by construction.
* `Realizes.toUCEmulatesCSim` — a realization gives `UCEmulatesCSim` for the
  spec whose honest input is the environment strategy.

The hybrid composition theorem is in
`CatCryptCore.Crypto.UCTransparentHybrid`, the non-vacuity instance in
`CatCryptCore.Crypto.UCTransparentExample`.

## On the up-to-bad formulation

`BadEvent.advantage_upto_bad` takes the bad event as a separate game `bad`
with the hypothesis `G₀ ≤ G₁ + bad` pointwise on `(result, final heap)`. Its
bad game is not tied to the runs of `G₀` and `G₁`, and the `UpToBadA` form
quantifies that hypothesis over all adversaries with one shared bad game,
which can force the two games to coincide. This file does not use it.
Instead the bad flag is computed inside each run (`loop`), and the
hypothesis (`hagree` of `adv_le_prBad`) compares single steps of the two
systems from a good state after filtering out the transitions into bad
states. The hypothesis does not force the systems to be equal: in the
instance of `UCTransparentExample` they differ on every exploded run and the
advantage equals the guard-failure probability.

## Relation to `UCConcrete`

Reused: `UCConcrete.Env` (input, initial heap, distinguisher) with the input
taken to be the interactive strategy, `Env.gap` as the advantage (`adv` is
`Env.gap` of the two view maps), `DistC` as the realization statement
(`Realizes` is `DistC` for every `ζ`), `DistC.triangle` for the hybrid step,
and `UCEmulatesCSim_of_DistC` with `DistC.comp_right` for the bridge
`Realizes.toUCEmulatesCSim`.

Not reused: `UCEmulatesCSim` itself as the definition. Its runs
`π : hon → SPComp (out ⊕ leak)` are one-shot: the protocol produces its whole
output and leakage, and the adversary post-processes the leakage once. A
transparent functionality is reactive: the environment chooses each input
after seeing earlier outputs, and the guard is a predicate on the whole
interleaved trace. The interactive execution (`loop`) is therefore defined
here, and its view map `view S : Strat ζ E O → SPComp ζ` is then an ordinary
Kleisli morphism to which `DistC` applies. The adversary is folded into the
environment (dummy adversary), so the bridge uses the empty leakage type and
the identity simulator map.
-/

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCDSL CatCrypt.Crypto.UCComposition
open scoped ENNReal

/-! ## Transition systems and environments -/

/-- Input events: inputs of honest parties (`P`) or of the adversary (`A`). -/
abbrev Event (P A : Type) := P ⊕ A

/-- A reactive probabilistic transition system with state `τ`, input events
    `E` and outputs `O`. -/
structure Sys (τ E O : Type) where
  /-- Initial state. -/
  init : τ
  /-- One activation: new state and output. -/
  step : τ → E → SPComp (τ × O)

/-- An interactive environment with internal state `ζ`. It runs for `rounds`
    activations; each activation chooses an event with `next` and processes
    the output with `obs`. Both are lossless. -/
structure Strat (ζ E O : Type) where
  /-- Number of activations. -/
  rounds : ℕ
  /-- Initial environment state. -/
  init : ζ
  /-- Choice of the next event. -/
  next : ζ → SPComp (ζ × E)
  /-- Observation of an output. -/
  obs : ζ → O → SPComp ζ
  /-- `next` never fails. -/
  next_noFail : ∀ z, SPComp.NoFail (next z)
  /-- `obs` never fails. -/
  obs_noFail : ∀ z o, SPComp.NoFail (obs z o)

variable {τ υ σ ζ E O : Type}

/-- The joint run of the environment `Z` and the system `S` for `n`
    activations, from configuration `(environment state, system state, flag)`.
    The flag is updated to `flag || bad t'` at every new system state `t'`. -/
noncomputable def loop (S : Sys τ E O) (bad : τ → Bool) (Z : Strat ζ E O) :
    ℕ → ζ × τ × Bool → SPComp (ζ × τ × Bool)
  | 0, c => SPComp.pure c
  | n + 1, c =>
    SPComp.bind (Z.next c.1) fun a =>
      SPComp.bind (S.step c.2.1 a.2) fun p =>
        SPComp.bind (Z.obs a.1 p.2) fun z =>
          loop S bad Z n (z, p.1, c.2.2 || bad p.1)

/-- The full run of `Z` against `S`, from the initial states. -/
noncomputable def run (S : Sys τ E O) (bad : τ → Bool) (Z : Strat ζ E O) :
    SPComp (ζ × τ × Bool) :=
  loop S bad Z Z.rounds (Z.init, S.init, bad S.init)

/-- The view of the environment: its final state, from a run without flag. -/
noncomputable def view (S : Sys τ E O) (Z : Strat ζ E O) : SPComp ζ :=
  SPComp.map Prod.fst (run S (fun _ => false) Z)

/-- The advantage of the environment `Z` (strategy, initial heap,
    distinguisher) between the systems `R` and `I`: `UCConcrete.Env.gap` of
    the two view maps. -/
noncomputable def adv (R : Sys τ E O) (I : Sys υ E O) (Z : Env (Strat ζ E O) ζ) : ℝ≥0∞ :=
  Env.gap (view R) (view I) Z

/-- Realization: for every environment state type `ζ` the view maps are at
    concrete distance `bound ζ` (`UCConcrete.DistC`). -/
def Realizes (R : Sys τ E O) (I : Sys υ E O)
    (bound : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞) : Prop :=
  ∀ ζ : Type, DistC (view R (ζ := ζ)) (view I) (bound ζ)

/-- The probability that the bad flag is set at the end of the run of `Z`
    against `S`, from the initial heap of `Z`. -/
noncomputable def prBad (S : Sys τ E O) (bad : τ → Bool) (Z : Env (Strat ζ E O) ζ) : ℝ≥0∞ :=
  prTrue (SPComp.bind (run S bad Z.input) fun c => SPComp.pure c.2.2) Z.heap

/-- `adv` unfolds to the absolute difference of acceptance probabilities. -/
theorem adv_eq (R : Sys τ E O) (I : Sys υ E O) (Z : Env (Strat ζ E O) ζ) :
    adv R I Z = absDiff (prTrue (SPComp.bind (view R Z.input) Z.dist) Z.heap)
      (prTrue (SPComp.bind (view I Z.input) Z.dist) Z.heap) := rfl

/-- On the empty initial heap, `adv` is CatCrypt's `AdvantageA` of the two
    view computations against the distinguisher. -/
theorem adv_eq_advantageA (R : Sys τ E O) (I : Sys υ E O) (Z : Env (Strat ζ E O) ζ)
    (hZ : Z.heap = Heap.empty) :
    adv R I Z = AdvantageA (view R Z.input) (view I Z.input) Z.dist := by
  rw [adv_eq, hZ]; rfl

/-! ## Auxiliary facts on `SPComp` -/

theorem bind_fail_right {α β : Type} (c : SPComp α) :
    SPComp.bind c (fun _ => (SPComp.fail : SPComp β)) = SPComp.fail := by
  funext h
  simp only [SPComp.bind_def, SPComp.fail]
  show SDistr.bind (c h) (fun _ => SDistr.fail) = SDistr.fail
  simp only [SDistr.bind, SDistr.fail]
  calc PMF.bind (c h) _ = PMF.bind (c h) (fun _ => PMF.pure (none : Option (β × Heap))) := by
        congr 1; funext oa; cases oa <;> rfl
    _ = PMF.pure none := PMF.bind_const _ _

/-- Splitting the acceptance probability of a bind along a predicate. -/
theorem prTrue_bind_split {α : Type} (X : SPComp α) (K : α → SPComp Bool) (q : α → Bool)
    (h₀ : Heap) :
    prTrue (SPComp.bind X K) h₀ =
      prTrue (SPComp.bind X fun a => if q a then SPComp.fail else K a) h₀ +
      prTrue (SPComp.bind X fun a => if q a then K a else SPComp.fail) h₀ := by
  rw [prTrue_bind_eq_weighted, prTrue_bind_eq_weighted, prTrue_bind_eq_weighted,
    ← ENNReal.tsum_add]
  congr 1; funext p
  rw [← mul_add]; congr 1
  rcases p with _ | ⟨a, h'⟩
  · simp
  · by_cases hq : q a
    · simp [hq, prTrue, SPComp.fail, SDistr.fail, PMF.pure_apply]
    · simp [hq, prTrue, SPComp.fail, SDistr.fail, PMF.pure_apply]

/-- Pointwise monotonicity of the acceptance probability of a bind. -/
theorem prTrue_bind_le_of_le {α : Type} (X : SPComp α) (K₁ K₂ : α → SPComp Bool) (h₀ : Heap)
    (hK : ∀ a h', prTrue (K₁ a) h' ≤ prTrue (K₂ a) h') :
    prTrue (SPComp.bind X K₁) h₀ ≤ prTrue (SPComp.bind X K₂) h₀ := by
  rw [prTrue_bind_eq_weighted, prTrue_bind_eq_weighted]
  refine ENNReal.tsum_le_tsum fun p => ?_
  rcases p with _ | ⟨a, h'⟩
  · simp
  · exact mul_le_mul_right (hK a h') _

theorem prTrue_pure (b : Bool) (h : Heap) :
    prTrue (SPComp.pure b) h = if b then 1 else 0 := by
  cases b <;> simp [prTrue, SPComp.pure, SDistr.pure, PMF.pure_apply]

theorem prTrue_fail (h : Heap) : prTrue (SPComp.fail : SPComp Bool) h = 0 := by
  simp [prTrue, SPComp.fail, SDistr.fail, PMF.pure_apply]

/-- A lossless computation followed by `pure true` accepts with probability 1. -/
theorem prTrue_bind_const_true {α : Type} (X : SPComp α) (hX : SPComp.NoFail X) (h₀ : Heap) :
    prTrue (SPComp.bind X fun _ => SPComp.pure true) h₀ = 1 := by
  rw [prTrue_bind_eq_weighted]
  have hsum := (X h₀).tsum_coe
  rw [SDistr.tsum_option_eq_add, hX h₀, zero_add] at hsum
  rw [SDistr.tsum_option_eq_add]
  simp only [mul_zero, zero_add, prTrue_pure, if_true, mul_one]
  exact hsum

/-- `absDiff (a + x) (a + y) ≤ max x y`. -/
theorem absDiff_add_left_le (a x y : ℝ≥0∞) : absDiff (a + x) (a + y) ≤ max x y := by
  unfold absDiff
  apply max_le
  · rw [tsub_le_iff_right]
    calc a + x ≤ max x y + a := by rw [add_comm]; gcongr; exact le_max_left _ _
      _ ≤ max x y + (a + y) := by gcongr; exact le_self_add
  · rw [tsub_le_iff_right]
    calc a + y ≤ max x y + a := by rw [add_comm]; gcongr; exact le_max_right _ _
      _ ≤ max x y + (a + x) := by gcongr; exact le_self_add

/-! ## The run: losslessness and views -/

/-- The run of a lossless system against an environment never fails. -/
theorem loop_noFail (S : Sys τ E O) (bad : τ → Bool) (Z : Strat ζ E O)
    (hS : ∀ t e, SPComp.NoFail (S.step t e)) :
    ∀ n c, SPComp.NoFail (loop S bad Z n c) := by
  intro n
  induction n with
  | zero => intro c; exact SPComp.pure_noFail c
  | succ n ih =>
    intro c
    exact Assumptions.SPComp.bind_noFail (Z.next_noFail _) fun a =>
      Assumptions.SPComp.bind_noFail (hS _ _) fun p =>
        Assumptions.SPComp.bind_noFail (Z.obs_noFail _ _) fun z => ih _

/-- A state map that commutes with single steps commutes with whole runs.
    The flag of the second run is computed with `bad' ∘ f`. -/
theorem loop_map (S : Sys τ E O) (S' : Sys υ E O) (f : τ → υ) (bad : τ → Bool)
    (bad' : υ → Bool) (Z : Strat ζ E O)
    (hstep : ∀ t e, SPComp.map (fun p => (f p.1, p.2)) (S.step t e) = S'.step (f t) e)
    (hbad : ∀ t, bad' (f t) = bad t) :
    ∀ n c, SPComp.map (fun c => (c.1, f c.2.1, c.2.2)) (loop S bad Z n c) =
      loop S' bad' Z n (c.1, f c.2.1, c.2.2) := by
  intro n
  induction n with
  | zero => intro c; simp [loop, SPComp.map]
  | succ n ih =>
    intro c
    simp only [loop, SPComp.map, SPComp.bind_assoc] at ih ⊢
    congr 1; funext a
    rw [← hstep]
    simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1; funext p; congr 1; funext z
    rw [ih, hbad]

/-- The view does not depend on the bad flag function. -/
theorem map_fst_loop_flag (S : Sys τ E O) (bad bad' : τ → Bool) (Z : Strat ζ E O) :
    ∀ n c b, SPComp.map Prod.fst (loop S bad Z n c) =
      SPComp.map Prod.fst (loop S bad' Z n (c.1, c.2.1, b)) := by
  intro n
  induction n with
  | zero => intro c b; simp [loop, SPComp.map]
  | succ n ih =>
    intro c b
    simp only [loop, SPComp.map, SPComp.bind_assoc] at ih ⊢
    congr 1; funext a; congr 1; funext p; congr 1; funext z
    exact ih _ _

/-- The view as the first projection of a flagged run. -/
theorem view_eq_map_run (S : Sys τ E O) (bad : τ → Bool) (Z : Strat ζ E O) :
    view S Z = SPComp.map Prod.fst (run S bad Z) := by
  unfold view run
  exact map_fst_loop_flag S _ _ Z _ _ _

/-! ## The up-to-bad lemma on the joint run -/

/-- Discard the transitions into bad states (they become failure). -/
noncomputable def goodK {α : Type} (bad : τ → Bool) (p : τ × α) : SPComp (τ × α) :=
  if bad p.1 then SPComp.fail else SPComp.pure p

/-- Discard the runs whose flag is set (they become failure). -/
noncomputable def restrictGood (X : SPComp (ζ × τ × Bool)) : SPComp (ζ × τ × Bool) :=
  SPComp.bind X fun c => if c.2.2 then SPComp.fail else SPComp.pure c

/-- Once the flag is set it stays set: the restricted run is failure. -/
theorem restrictGood_loop_of_flag (S : Sys τ E O) (bad : τ → Bool) (Z : Strat ζ E O) :
    ∀ n (c : ζ × τ × Bool), c.2.2 = true → restrictGood (loop S bad Z n c) = SPComp.fail := by
  intro n
  induction n with
  | zero => intro c hc; simp [restrictGood, loop, hc]
  | succ n ih =>
    intro c hc
    simp only [restrictGood, loop, SPComp.bind_assoc] at ih ⊢
    have : ∀ (z : ζ) (t : τ), SPComp.bind (loop S bad Z n (z, t, c.2.2 || bad t))
        (fun c => if c.2.2 then SPComp.fail else SPComp.pure c) = SPComp.fail := by
      intro z t; exact ih _ (by simp [hc])
    simp only [this, bind_fail_right]

/-- One step of a restricted run from a configuration with flag unset: the
    step is filtered by `goodK` before the continuation. -/
theorem restrictGood_loop_succ (S : Sys τ E O) (bad : τ → Bool) (Z : Strat ζ E O) (n : ℕ)
    (z : ζ) (t : τ) :
    restrictGood (loop S bad Z (n + 1) (z, t, false)) =
      SPComp.bind (Z.next z) fun a =>
        SPComp.bind (SPComp.bind (S.step t a.2) (goodK bad)) fun p =>
          SPComp.bind (Z.obs a.1 p.2) fun z' =>
            restrictGood (loop S bad Z n (z', p.1, false || bad p.1)) := by
  have hfl : ∀ (z' : ζ) (t' : τ), restrictGood (loop S bad Z n (z', t', true)) = SPComp.fail :=
    fun z' t' => restrictGood_loop_of_flag S bad Z n _ rfl
  unfold restrictGood at hfl ⊢
  simp only [loop, SPComp.bind_assoc]
  congr 1; funext a; congr 1; funext p
  unfold goodK
  by_cases hp : bad p.1
  · simp only [hp, if_true, SPComp.fail_bind, Bool.false_or, hfl, bind_fail_right]
  · simp [hp]

/-- Two systems whose steps from every good state agree after transitions
    into bad states are discarded have equal runs after runs that ever set
    the flag are discarded, from every configuration whose system state is
    good when its flag is unset. -/
theorem restrictGood_loop_eq (R I : Sys τ E O) (bad : τ → Bool) (Z : Strat ζ E O)
    (hagree : ∀ t e, bad t = false →
      SPComp.bind (R.step t e) (goodK bad) = SPComp.bind (I.step t e) (goodK bad)) :
    ∀ n (c : ζ × τ × Bool), (c.2.2 = false → bad c.2.1 = false) →
      restrictGood (loop R bad Z n c) = restrictGood (loop I bad Z n c) := by
  intro n
  induction n with
  | zero => intro c _; rfl
  | succ n ih =>
    rintro ⟨z, t, b⟩ hc
    cases b with
    | true =>
      rw [restrictGood_loop_of_flag R bad Z _ _ rfl, restrictGood_loop_of_flag I bad Z _ _ rfl]
    | false =>
      have ht : bad t = false := hc rfl
      rw [restrictGood_loop_succ, restrictGood_loop_succ]
      congr 1; funext a
      rw [hagree t a.2 ht]
      congr 1; funext p; congr 1; funext z'
      exact ih _ (by simp)

/-- **Up-to-bad on the joint run.** Let `R` and `I` be lossless systems on
    the same state space with the same initial state, and assume that from
    every good state their single steps agree once transitions into bad
    states are discarded. Then the advantage of every environment `Z` is at
    most the probability that the run of `Z` against `R` visits a bad
    state. -/
theorem adv_le_prBad (R I : Sys τ E O) (bad : τ → Bool)
    (hinit : R.init = I.init)
    (hR : ∀ t e, SPComp.NoFail (R.step t e)) (hI : ∀ t e, SPComp.NoFail (I.step t e))
    (hagree : ∀ t e, bad t = false →
      SPComp.bind (R.step t e) (goodK bad) = SPComp.bind (I.step t e) (goodK bad))
    (Z : Env (Strat ζ E O) ζ) :
    adv R I Z ≤ prBad R bad Z := by
  set X := run R bad Z.input with hX
  set Y := run I bad Z.input with hY
  have hgood : restrictGood X = restrictGood Y := by
    rw [hX, hY, run, run, hinit]
    exact restrictGood_loop_eq R I bad Z.input hagree _ _ (fun h => by simpa using h)
  have hXnf : SPComp.NoFail X := loop_noFail R bad Z.input hR _ _
  have hYnf : SPComp.NoFail Y := loop_noFail I bad Z.input hI _ _
  -- The good part of a bind is a bind of the restricted run.
  have hgoodpart : ∀ (W : SPComp (ζ × τ × Bool)) (K : ζ × τ × Bool → SPComp Bool),
      SPComp.bind W (fun c => if c.2.2 then SPComp.fail else K c) =
        SPComp.bind (restrictGood W) K := by
    intro W K
    unfold restrictGood
    rw [SPComp.bind_assoc]; congr 1; funext c
    by_cases hc : c.2.2 <;> simp [hc]
  -- Bad mass, written with a failing continuation.
  set bX := prTrue (SPComp.bind X fun c => if c.2.2 then SPComp.pure true else SPComp.fail)
    Z.heap
  set bY := prTrue (SPComp.bind Y fun c => if c.2.2 then SPComp.pure true else SPComp.fail)
    Z.heap
  set g := prTrue (SPComp.bind (restrictGood X) fun _ => SPComp.pure true) Z.heap
  have hmassX : g + bX = 1 := by
    have := prTrue_bind_split X (fun _ => SPComp.pure true) (fun c => c.2.2) Z.heap
    rw [prTrue_bind_const_true X hXnf, hgoodpart] at this
    exact this.symm
  have hmassY : g + bY = 1 := by
    have := prTrue_bind_split Y (fun _ => SPComp.pure true) (fun c => c.2.2) Z.heap
    rw [prTrue_bind_const_true Y hYnf, hgoodpart, ← hgood] at this
    exact this.symm
  have hg_ne_top : g ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hmassX ▸ le_self_add)
  have hbXY : bY = bX := by
    have h := hmassY.trans hmassX.symm
    exact (ENNReal.add_right_inj hg_ne_top).mp h
  have hbX_eq : bX = prBad R bad Z := by
    unfold prBad
    refine le_antisymm (prTrue_bind_le_of_le _ _ _ _ fun c h' => ?_)
      (prTrue_bind_le_of_le _ _ _ _ fun c h' => ?_)
    · by_cases hc : c.2.2 <;> simp [hc, prTrue_pure, prTrue_fail]
    · by_cases hc : c.2.2 <;> simp [hc, prTrue_pure, prTrue_fail]
  -- Split both acceptance probabilities.
  rw [adv_eq, view_eq_map_run R bad, view_eq_map_run I bad]
  simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  rw [← hX, ← hY]
  rw [prTrue_bind_split X _ (fun c => c.2.2), prTrue_bind_split Y _ (fun c => c.2.2),
    hgoodpart X, hgoodpart Y, ← hgood]
  refine le_trans (absDiff_add_left_le _ _ _) (max_le ?_ ?_)
  · rw [← hbX_eq]
    exact prTrue_bind_le_of_le _ _ _ _ fun c h' => by
      by_cases hc : c.2.2
      · simp [hc, prTrue_pure, prTrue_le_one]
      · simp [hc, prTrue_fail]
  · rw [← hbX_eq, ← hbXY]
    exact prTrue_bind_le_of_le _ _ _ _ fun c h' => by
      by_cases hc : c.2.2
      · simp [hc, prTrue_pure, prTrue_le_one]
      · simp [hc, prTrue_fail]

/-! ## Transparent functionalities -/

/-- A trace: the list of `(event, output, state)` entries of the run. -/
abbrev Trace (σ E O : Type) := List (E × O × σ)

/-- A transparent functionality: an initial state, a guard on traces, and the
    output given after explosion. Every state change is proposed through the
    adversary interface (by the simulator) and accepted iff the extended trace
    satisfies the guard. -/
structure TFunc (σ E O : Type) where
  /-- Initial state. -/
  init : σ
  /-- The guard: a decidable predicate on traces. -/
  guard : Trace σ E O → Bool
  /-- The output after the guard has failed. -/
  exploded : O

/-- The protocol `π` with a passive monitor that records the trace and sets
    the flag when the guard `G` fails on a prefix of the trace. -/
noncomputable def monitor (π : Sys σ E O) (G : Trace σ E O → Bool) :
    Sys (σ × Trace σ E O × Bool) E O where
  init := (π.init, [], false)
  step t e := SPComp.bind (π.step t.1 e) fun p =>
    SPComp.pure ((p.1, t.2.1 ++ [(e, p.2, p.1)], t.2.2 || !G (t.2.1 ++ [(e, p.2, p.1)])), p.2)

/-- The ideal world of the transparent functionality `F` with simulator `S`:
    the simulator proposes `(state, output)`; the functionality appends the
    entry to its trace, explodes if the guard fails, and outputs the proposed
    output unless exploded. -/
noncomputable def ideal (F : TFunc σ E O) (S : Sys σ E O) :
    Sys (σ × Trace σ E O × Bool) E O where
  init := (S.init, [], false)
  step t e := SPComp.bind (S.step t.1 e) fun p =>
    let tr := t.2.1 ++ [(e, p.2, p.1)]
    let x := t.2.2 || !F.guard tr
    SPComp.pure ((p.1, tr, x), if x then F.exploded else p.2)

/-- The flag of `monitor` and `ideal`. -/
def exploded (t : σ × Trace σ E O × Bool) : Bool := t.2.2

/-- The probability that the guard `G` fails on the real trace of `π`. -/
noncomputable def guardFail (π : Sys σ E O) (G : Trace σ E O → Bool)
    (Z : Env (Strat ζ E O) ζ) : ℝ≥0∞ :=
  prBad (monitor π G) exploded Z

/-- The monitor is passive: its view is that of the protocol. -/
theorem view_monitor (π : Sys σ E O) (G : Trace σ E O → Bool) (Z : Strat ζ E O) :
    view (monitor π G) Z = view π Z := by
  unfold view run
  have h := loop_map (monitor π G) π Prod.fst (fun _ => false) (fun _ => false) Z
    (fun t e => by simp [monitor, SPComp.map, SPComp.bind_assoc]) (fun _ => rfl)
    Z.rounds (Z.init, (monitor π G).init, false)
  have h2 : SPComp.map Prod.fst (loop (monitor π G) (fun _ => false) Z Z.rounds
      (Z.init, (monitor π G).init, false)) =
      SPComp.map Prod.fst (SPComp.map (fun c => (c.1, c.2.1.1, c.2.2))
        (loop (monitor π G) (fun _ => false) Z Z.rounds (Z.init, (monitor π G).init, false))) := by
    simp [SPComp.map, SPComp.bind_assoc]
  rw [h2, h]; rfl

/-- **Transparent realization.** Let `π` be a lossless protocol, `F` a
    transparent functionality and `S` a lossless simulator with the initial
    state of `π`, such that for every state `s`, trace `tr` and event `e`, the
    steps of `S` and of `π` from `s` agree on the transitions whose extended
    trace satisfies the guard. Then `π` realizes `ideal F S` with bound the
    probability that the guard fails on the real trace of `π`. -/
theorem transparent_realizes (π : Sys σ E O) (F : TFunc σ E O) (S : Sys σ E O)
    (hinit : S.init = π.init)
    (hπ : ∀ s e, SPComp.NoFail (π.step s e)) (hS : ∀ s e, SPComp.NoFail (S.step s e))
    (hsim : ∀ s (tr : Trace σ E O) e,
      SPComp.bind (π.step s e) (fun p => if F.guard (tr ++ [(e, p.2, p.1)])
        then SPComp.pure p else SPComp.fail) =
      SPComp.bind (S.step s e) (fun p => if F.guard (tr ++ [(e, p.2, p.1)])
        then SPComp.pure p else SPComp.fail)) :
    Realizes π (ideal F S) (fun _ Z => guardFail π F.guard Z) := by
  intro ζ Z
  have h := adv_le_prBad (ζ := ζ) (monitor π F.guard) (ideal F S) exploded
    (by simp [monitor, ideal, hinit])
    (fun t e => by
      simp only [monitor]
      exact Assumptions.SPComp.bind_noFail (hπ _ _) fun _ => SPComp.pure_noFail _)
    (fun t e => by
      simp only [ideal]
      exact Assumptions.SPComp.bind_noFail (hS _ _) fun _ => SPComp.pure_noFail _)
    ?_ Z
  · unfold adv at h
    rw [show (view (monitor π F.guard) : Strat ζ E O → SPComp ζ) = view π from
      funext (view_monitor π F.guard)] at h
    exact h
  · rintro ⟨s, tr, x⟩ e hx
    simp only [exploded] at hx
    subst hx
    -- Both filtered steps are the filtered protocol step followed by `pure`.
    have hfac : ∀ (T : Sys σ E O) (out : σ × O → O),
        (∀ p, F.guard (tr ++ [(e, p.2, p.1)]) = true → out p = p.2) →
        SPComp.bind (SPComp.bind (T.step s e) fun p =>
            SPComp.pure ((p.1, tr ++ [(e, p.2, p.1)], false || !F.guard (tr ++ [(e, p.2, p.1)])),
              out p)) (goodK exploded) =
          SPComp.bind (SPComp.bind (T.step s e) fun p => if F.guard (tr ++ [(e, p.2, p.1)])
            then SPComp.pure p else SPComp.fail) fun p =>
              SPComp.pure ((p.1, tr ++ [(e, p.2, p.1)], false), p.2) := by
      intro T out hout
      simp only [SPComp.bind_assoc, SPComp.pure_bind]
      congr 1; funext p
      by_cases hg : F.guard (tr ++ [(e, p.2, p.1)])
      · simp [goodK, exploded, hg, hout p hg]
      · simp [goodK, exploded, hg]
    have h1 := hfac π (fun p => p.2) (fun _ _ => rfl)
    have h2 := hfac S (fun p => if false || !F.guard (tr ++ [(e, p.2, p.1)])
        then F.exploded else p.2) (fun p hg => by simp [hg])
    simp only [monitor, ideal]
    rw [h1, h2, hsim s tr e]

/-- The copy simulator `S = π` realizes every transparent functionality with
    bound the guard-failure probability on the real trace. -/
theorem transparent_realizes_copy (π : Sys σ E O) (F : TFunc σ E O)
    (hπ : ∀ s e, SPComp.NoFail (π.step s e)) :
    Realizes π (ideal F π) (fun _ Z => guardFail π F.guard Z) :=
  transparent_realizes π F π rfl hπ hπ fun _ _ _ => rfl

/-! ## Bridge to `UCEmulatesCSim` -/

/-- A realization gives concrete UC emulation in the sense of
    `UCConcrete.UCEmulatesCSim`, for the spec whose honest input is the
    environment strategy, whose honest output is the environment's final
    state, with empty leakage (the adversary is part of the environment) and
    the identity simulator map. -/
theorem Realizes.toUCEmulatesCSim {R : Sys τ E O} {I : Sys υ E O}
    {bound : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : Realizes R I bound)
    (ζ V : Type) :
    UCEmulatesCSim ⟨Strat ζ E O, ζ, Empty, Empty, V⟩
      (fun s => SPComp.bind (view R s) fun z => SPComp.pure (Sum.inl z))
      (fun s => SPComp.bind (view I s) fun z => SPComp.pure (Sum.inl z)) id
      (fun A Z => bound ζ (Env.postcomp (fun z => SPComp.pure (Sum.inl z))
        (Env.postcomp (mapSum SPComp.pure A) Z))) :=
  UCEmulatesCSim_of_DistC ((h ζ).comp_right fun z => SPComp.pure (Sum.inl z))

end CatCrypt.Crypto.UCTransparent
