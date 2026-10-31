/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.RC

/-!
# Robust compilation from a value-and-constant-time gate conclusion

`GateConclusion` is the shape of a joint value and constant-time theorem of a compiler, over
abstract entry states `St`, values `V` and leakage traces `Tr`:

* **value**: every source run from an entry state satisfying `Pre` to a value `v` is matched by
  a target result `v` from the same entry state (a forward simulation);
* **constant time**: two terminating target runs from entry states that satisfy `Pre`, agree
  on the public data (`Pub`) and from each of which the source has a run, have equal leakage
  traces.

The domain `Dom Pre srcRun leakRun` is the set of entry states satisfying `Pre` from which the
source has a run and the target has a terminating run. On it, `resOf` is the result of the
target, `leakOf` its leakage trace and `srcOf` the value of the source run. The simulator
`simLeak` is an existential (choice) simulator: from a public projection `p` it returns the
trace of some entry state of the domain whose public projection is `p`.

The real observation `realObs` is the target result with the target trace; the ideal
observation `idealObs` is the source value with the simulated trace. Their equality
(`realObs_eq_idealObs`) carries value correctness and constant time together: the first
components agree by value correctness and determinism of the target result, the second by
constant time.

## Main results

* `GateConclusion` — value correctness and constant time of a target, relative to a source.
* `leakOf_eq_simLeak` — the target trace is the simulator applied to the public projection.
* `resOf_eq_srcOf` — the target result is the source value.
* `realObs_eq_idealObs` — the real and the ideal observations are equal.
* `rc_of_gate` — `RobustCompilation 0` between the real and the ideal observation.
* `rhp_of_gate` — a protocol built on the ideal observation and one built on the real
  observation satisfy the same `RHP` statements.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.RCGate

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

variable {St V Tr P : Type}

/-- **The gate conclusion** of a compilation, relative to a source relation `srcRun`
    (`srcRun s v`: the source reaches `v` from entry state `s`), a target result relation
    `tgtRes` (`tgtRes s v`: the target halts from `s` with result `v`) and a target leakage
    relation `leakRun` (`leakRun s t`: the target has a terminating run from `s` with leakage
    trace `t`). -/
structure GateConclusion (Pre : St → Prop) (Pub : St → St → Prop) (srcRun : St → V → Prop)
    (tgtRes : St → V → Prop) (leakRun : St → Tr → Prop) : Prop where
  /-- Every source run from an entry state satisfying `Pre` is matched by a target result. -/
  value : ∀ s v, Pre s → srcRun s v → tgtRes s v
  /-- Terminating target runs from entry states that satisfy `Pre`, agree on `Pub` and from
      each of which the source has a run, have equal leakage traces. -/
  ct : ∀ s₁ s₂ t₁ t₂,
    (Pub s₁ s₂ ∧ Pre s₁ ∧ Pre s₂ ∧ (∃ v, srcRun s₁ v) ∧ ∃ v, srcRun s₂ v) →
      leakRun s₁ t₁ → leakRun s₂ t₂ → t₁ = t₂

/-- The entry states satisfying `Pre` from which the source has a run and the target has a
    terminating run. -/
abbrev Dom (Pre : St → Prop) (srcRun : St → V → Prop) (leakRun : St → Tr → Prop) : Type :=
  {s : St // (Pre s ∧ ∃ v, srcRun s v) ∧ ∃ t, leakRun s t}

variable {Pre : St → Prop} {Pub : St → St → Prop} {srcRun : St → V → Prop}
  {tgtRes : St → V → Prop} {leakRun : St → Tr → Prop}

/-- The leakage trace of the target from an entry state of the domain. -/
noncomputable def leakOf (i : Dom Pre srcRun leakRun) : Tr :=
  Classical.choose i.2.2

/-- The value of a source run from an entry state of the domain. -/
noncomputable def srcOf (i : Dom Pre srcRun leakRun) : V :=
  Classical.choose i.2.1.2

/-- The target result from an entry state of the domain: a value `v` with `tgtRes i.1 v`
    when one exists (under `GateConclusion` it does, `tgtRes_resOf`). -/
noncomputable def resOf (tgtRes : St → V → Prop) (i : Dom Pre srcRun leakRun) : V :=
  @Classical.epsilon V ⟨srcOf i⟩ (tgtRes i.1)

/-- The leakage simulator, an existential (choice) simulator: from a public projection `p`,
    the trace of some entry state that satisfies `Pre`, from which the source has a run, and
    that has public projection `p`. -/
noncomputable def simLeak [Nonempty Tr] (Pre : St → Prop) (srcRun : St → V → Prop)
    (leakRun : St → Tr → Prop) (pub : St → P) (p : P) : Tr :=
  Classical.epsilon fun t => ∃ s, pub s = p ∧ (Pre s ∧ ∃ v, srcRun s v) ∧ leakRun s t

/-- **Constant time makes the leakage simulatable.** When equal public projections imply
    `Pub`, the target trace from an entry state of the domain is the simulator applied to its
    public projection. -/
theorem leakOf_eq_simLeak [Nonempty Tr] (g : GateConclusion Pre Pub srcRun tgtRes leakRun)
    (pub : St → P) (hpub : ∀ s₁ s₂, pub s₁ = pub s₂ → Pub s₁ s₂) (i : Dom Pre srcRun leakRun) :
    leakOf i = simLeak Pre srcRun leakRun pub (pub i.1) := by
  have hex : ∃ t, ∃ s, pub s = pub i.1 ∧ (Pre s ∧ ∃ v, srcRun s v) ∧ leakRun s t :=
    ⟨leakOf i, i.1, rfl, i.2.1, Classical.choose_spec i.2.2⟩
  obtain ⟨s, hs, ⟨hpre, hsrc⟩, hrun⟩ := Classical.epsilon_spec hex
  exact g.ct i.1 s _ _ ⟨hpub _ _ hs.symm, i.2.1.1, hpre, i.2.1.2, hsrc⟩
    (Classical.choose_spec i.2.2) hrun

/-- Under the gate conclusion, `resOf tgtRes i` is a target result from `i`. -/
theorem tgtRes_resOf (g : GateConclusion Pre Pub srcRun tgtRes leakRun)
    (i : Dom Pre srcRun leakRun) : tgtRes i.1 (resOf tgtRes i) :=
  @Classical.epsilon_spec V (tgtRes i.1)
    ⟨srcOf i, g.value _ _ i.2.1.1 (Classical.choose_spec i.2.1.2)⟩

/-- **Value correctness on the domain.** For a deterministic target, the target result from
    an entry state of the domain is the value of the source run. -/
theorem resOf_eq_srcOf (g : GateConclusion Pre Pub srcRun tgtRes leakRun)
    (htgt : ∀ s v w, Pre s → tgtRes s v → tgtRes s w → v = w) (i : Dom Pre srcRun leakRun) :
    resOf tgtRes i = srcOf i :=
  htgt _ _ _ i.2.1.1 (tgtRes_resOf g i)
    (g.value _ _ i.2.1.1 (Classical.choose_spec i.2.1.2))

/-- The real observation: the target result and the leakage trace of the target. -/
noncomputable def realObs (tgtRes : St → V → Prop) (i : Dom Pre srcRun leakRun) :
    SPComp (V × Tr) :=
  SPComp.pure (resOf tgtRes i, leakOf i)

/-- The ideal observation: the source value and the simulated leakage trace from the public
    projection. -/
noncomputable def idealObs [Nonempty Tr] (pub : St → P) (i : Dom Pre srcRun leakRun) :
    SPComp (V × Tr) :=
  SPComp.pure (srcOf i, simLeak Pre srcRun leakRun pub (pub i.1))

/-- **Value correctness and constant time together.** For a deterministic target, the real
    observation (target result, target trace) equals the ideal observation (source value,
    trace simulated from the public projection). -/
theorem realObs_eq_idealObs [Nonempty Tr] (g : GateConclusion Pre Pub srcRun tgtRes leakRun)
    (pub : St → P) (hpub : ∀ s₁ s₂, pub s₁ = pub s₂ → Pub s₁ s₂)
    (htgt : ∀ s v w, Pre s → tgtRes s v → tgtRes s w → v = w) :
    realObs (Pre := Pre) (srcRun := srcRun) (leakRun := leakRun) tgtRes = idealObs pub := by
  funext i
  simp only [realObs, idealObs, leakOf_eq_simLeak g pub hpub i, resOf_eq_srcOf g htgt i]

/-- **Robust compilation from the gate conclusion.** For a deterministic target, the real
    observation and the ideal observation are at distance `0` in every context and for every
    distinguisher; the conjunct carries value correctness and constant time together. -/
theorem rc_of_gate [Nonempty Tr] (g : GateConclusion Pre Pub srcRun tgtRes leakRun)
    (pub : St → P) (hpub : ∀ s₁ s₂, pub s₁ = pub s₂ → Pub s₁ s₂)
    (htgt : ∀ s v w, Pre s → tgtRes s v → tgtRes s w → v = w) :
    RobustCompilation 0 (realObs (Pre := Pre) (srcRun := srcRun) (leakRun := leakRun) tgtRes)
      (idealObs pub) :=
  RC_of_sdist (by rw [realObs_eq_idealObs g pub hpub htgt]; exact (sdist_self _).le)

/-- **RHP transfer from the gate conclusion.** For a deterministic target and a protocol `Q`
    run on the observation, the protocol on the real observation satisfies `RHP ε` against `F`
    exactly when the protocol on the ideal observation does. -/
theorem rhp_of_gate [Nonempty Tr] (g : GateConclusion Pre Pub srcRun tgtRes leakRun)
    (pub : St → P) (hpub : ∀ s₁ s₂, pub s₁ = pub s₂ → Pub s₁ s₂)
    (htgt : ∀ s v w, Pre s → tgtRes s v → tgtRes s w → v = w)
    {out leak sim_if view : Type} (Q : V × Tr → SPComp (out ⊕ leak))
    (F : Dom Pre srcRun leakRun → SPComp (out ⊕ sim_if)) (ε : ℝ≥0∞) :
    RHP ε (Dom Pre srcRun leakRun) out leak sim_if view
        (fun i => SPComp.bind (realObs tgtRes i) Q) F ↔
      RHP ε (Dom Pre srcRun leakRun) out leak sim_if view
        (fun i => SPComp.bind (idealObs pub i) Q) F := by
  rw [realObs_eq_idealObs g pub hpub htgt]

end CatCrypt.Crypto.RCGate
