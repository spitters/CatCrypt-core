/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCTransparent

@[expose] public section
set_option autoImplicit false

/-!
# A transparent functionality with a two-state guard

A concrete instance showing that the hypotheses of
`UCTransparent.transparent_realizes` are satisfiable and that its bound is
attained.

* State space `Bool`: `false` is the safe state, `true` the broken state.
* Protocol `coinProto`: on every event it samples a uniform bit `c`, moves
  from `s` to `s || c`, and outputs `false`.
* Functionality `coinFunc`: the guard holds on a trace iff every entry is in
  the safe state; the exploded output is `true`.
* Environment `probeEnv`: one activation through the adversary interface; it
  outputs whether it has observed `true`.

## Main results

* `coin_realizes` — `coinProto` realizes `ideal coinFunc coinProto` with
  bound the guard-failure probability (copy simulator).
* `coin_guardFail` — the guard fails on the real trace with probability
  `1/2` under `probeEnv`.
* `coin_adv` — the advantage of `probeEnv` is `1/2`.
* `coin_adv_eq_guardFail` — the advantage equals the bound, so the bound of
  `transparent_realizes` is tight and the agreement hypothesis does not
  force the real and ideal systems to be indistinguishable.
-/

namespace CatCrypt.Crypto.UCTransparent.Example

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-- Events: one party input and one adversary input, both without content. -/
abbrev Ev := Event Unit Unit

/-- The protocol: sample a bit `c`, move to `s || c`, output `false`. -/
noncomputable def coinProto : Sys Bool Ev Bool where
  init := false
  step s _ := SPComp.bind (SPComp.sample Bool) fun c => SPComp.pure (s || c, false)

/-- The two-state guard: every entry of the trace is in the safe state. -/
def coinGuard (tr : Trace Bool Ev Bool) : Bool := tr.all fun x => !x.2.2

/-- The transparent functionality with the two-state guard; it outputs
    `true` once exploded. -/
def coinFunc : TFunc Bool Ev Bool := ⟨false, coinGuard, true⟩

/-- The protocol never fails. -/
theorem coinProto_noFail : ∀ s e, SPComp.NoFail (coinProto.step s e) := by
  intro s e
  simp only [coinProto]
  exact Assumptions.SPComp.bind_noFail Assumptions.SPComp.sample_noFail fun _ => SPComp.pure_noFail _

/-- The probing environment: one adversary activation; its state records
    whether it has observed the output `true`. -/
noncomputable def probe : Strat Bool Ev Bool where
  rounds := 1
  init := false
  next z := SPComp.pure (z, Sum.inr ())
  obs z o := SPComp.pure (z || o)
  next_noFail _ := SPComp.pure_noFail _
  obs_noFail _ _ := SPComp.pure_noFail _

/-- The probing environment with the empty heap and the identity
    distinguisher. -/
noncomputable def probeEnv : Env (Strat Bool Ev Bool) Bool :=
  ⟨probe, Heap.empty, SPComp.pure⟩

/-- A uniform bit is `true` with probability `1/2`. -/
theorem prTrue_sample_Bool : prTrue (SPComp.sample Bool) Heap.empty = 2⁻¹ := by
  have h := prTrue_bind_sample_Bool SPComp.pure Heap.empty
  rw [SPComp.bind_pure] at h
  simp [h, prTrue_pure]

/-- `coinProto` realizes the ideal world of `coinFunc` with the copy
    simulator, with bound the guard-failure probability (composition
    plumbing). -/
theorem coin_realizes :
    Realizes coinProto (ideal coinFunc coinProto) (fun _ Z => guardFail coinProto coinGuard Z) :=
  transparent_realizes_copy coinProto coinFunc coinProto_noFail

/-- Under `probeEnv` the guard fails on the real trace with probability `1/2`. -/
theorem coin_guardFail : guardFail coinProto coinGuard probeEnv = 2⁻¹ := by
  simp [guardFail, prBad, run, loop, probeEnv, probe, monitor, coinProto, coinGuard,
    exploded, SPComp.bind_assoc, prTrue_sample_Bool]

/-- The advantage of `probeEnv` between the real and the ideal world is `1/2`. -/
theorem coin_adv : adv coinProto (ideal coinFunc coinProto) probeEnv = 2⁻¹ := by
  simp [adv_eq, view, run, loop, probeEnv, probe, ideal, coinFunc, coinProto, coinGuard,
    SPComp.map, SPComp.bind_assoc, prTrue_sample_Bool, prTrue_bind_sample_Bool, prTrue_pure,
    absDiff]

/-- The advantage equals the guard-failure probability: the bound of
    `transparent_realizes` is attained. -/
theorem coin_adv_eq_guardFail :
    adv coinProto (ideal coinFunc coinProto) probeEnv = guardFail coinProto coinGuard probeEnv := by
  rw [coin_adv, coin_guardFail]

end CatCrypt.Crypto.UCTransparent.Example
