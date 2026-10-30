/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCGlobalSquare
public import CatCryptCore.Crypto.UCCoupling
public import CatCryptCore.NonUniform.Sample

/-!
# Global setups as global functionalities

A global functionality over the interface `(EG, OG)` is a system `G : Sys τ EG OG`; a protocol
over it is a multi-call hybrid with subroutine interface `(EG, OG)`, and `gOpen` exposes the
port of `G` to the environment (`UCGlobalSquare`). The global setups below are such systems.

* A setup given by a query handler `query : Q → St → SPComp (A × St)` from an initial state is
  the system `Sys.ofQuery init query`.
* The log of a system (`Sys.logged`) records every answered event with its answer. Forgetting
  the log is a realization at distance `0` in both directions (`Sys.realizes_logged`,
  `Sys.logged_realizes`).
* An observable setup (`Sys.observable X obs`) has a second event, answered by the observation
  `obs` of the state, which leaves the state unchanged. The observable global random oracle of
  Canetti, Jain and Scafuro (CCS 2014) is the lazy random oracle with its log, observed through
  the log (`obsRO`).
* The lazy random oracle (`lazyRO`) has the partial table of answered points as state and
  answers a fresh point with a uniform value.
* The global common reference string (`crsSys`) samples a value of a distribution at its first
  activation and gives its public part on every activation.

A realization whose error per activation grows with a measure of the state, by at most one per
activation, has as bound the sum of the errors over the activations of the run
(`realizes_of_couplingGraded`): an observable random oracle charges a fresh query the
probability that its uniform answer hits one of the digests already answered, which grows with
the length of the log.

## Main definitions

* `Sys.ofQuery`, `Sys.logged`, `Sys.observable`: global functionalities from query handlers,
  logs and observations.
* `lazyROStep`, `lazyRO`, `obsRO`: the lazy and the observable global random oracle.
* `crsSample`, `crsSys`: the global common reference string.

## Main results

* `Sys.realizes_logged`, `Sys.logged_realizes`: the log is invisible at distance `0`.
* `Sys.observable_step_inr`: an observation leaves the state unchanged.
* `loop_rHoareApprox_graded`, `realizes_of_couplingGraded`: realization with an error per
  activation that grows with a measure of the state.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Relational CatCrypt.NonUniform CatCrypt.Crypto.UCCoupling
open scoped ENNReal

/-! ## Global functionalities from query handlers -/

namespace Sys

variable {τ St Q A L E O : Type}

/-- The global functionality of a setup with initial state `init` and query handler `query`:
an event `q` runs `query q` on the state and answers its result. -/
noncomputable def ofQuery (init : St) (query : Q → St → SPComp (A × St)) : Sys St Q A where
  init := init
  step t q := SPComp.map (fun p => (p.2, p.1)) (query q t)

/-- The system `X` with the log of its answered events: every step of `X` on `e` with answer
`o` appends `(e, o)` to the log. -/
noncomputable def logged (X : Sys τ E O) : Sys (τ × List (E × O)) E O where
  init := (X.init, [])
  step t e := SPComp.map (fun p => ((p.1, t.2 ++ [(e, p.2)]), p.2)) (X.step t.1 e)

/-- The system with its log realizes the system at distance `0`. -/
theorem realizes_logged (X : Sys τ E O) : Realizes X.logged X (fun _ _ => 0) :=
  realizes_zero_of_stepMap X.logged X Prod.fst rfl fun t e => by
    simp only [logged, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    exact SPComp.bind_pure _

/-- The system realizes the system with its log at distance `0`. -/
theorem logged_realizes (X : Sys τ E O) : Realizes X X.logged (fun _ _ => 0) :=
  UCCoupling.realizes_symm (realizes_logged X)

/-- The observable form of `X`: the event `inl e` is a step of `X` with answer `inl`, and the
event `inr ()` answers `inr (obs t)` for the state `t` and leaves the state unchanged. -/
noncomputable def observable (X : Sys τ E O) (obs : τ → L) : Sys τ (E ⊕ Unit) (O ⊕ L) where
  init := X.init
  step t := Sum.elim (fun e => SPComp.map (fun p => (p.1, .inl p.2)) (X.step t e))
    (fun _ => SPComp.pure (t, .inr (obs t)))

/-- An event of `X` in the observable form is a step of `X`. -/
@[simp] theorem observable_step_inl (X : Sys τ E O) (obs : τ → L) (t : τ) (e : E) :
    (X.observable obs).step t (.inl e) = SPComp.map (fun p => (p.1, .inl p.2)) (X.step t e) :=
  rfl

/-- An observation leaves the state unchanged and answers the observation of the state. -/
@[simp] theorem observable_step_inr (X : Sys τ E O) (obs : τ → L) (t : τ) (u : Unit) :
    (X.observable obs).step t (.inr u) = SPComp.pure (t, .inr (obs t)) :=
  rfl

end Sys

/-! ## The lazy and the observable global random oracle -/

section RandomOracle

variable (K C : Type) [DecidableEq K] [Fintype C] [Nonempty C]

variable {K C} in
/-- One query of the lazy random oracle with the answered points `m`: the recorded value, or
a uniform value recorded at `k`. -/
noncomputable def lazyROStep (m : K → Option C) (k : K) : PMF ((K → Option C) × C) :=
  match m k with
  | some e => PMF.pure (m, e)
  | none => (PMF.uniformFintype C).map fun e => (Function.update m k (some e), e)

/-- The lazy random oracle as a global functionality: its state is the partial function of
answered points. -/
noncomputable def lazyRO : Sys (K → Option C) K C where
  init := fun _ => none
  step m k := sampleFrom (ofPMF (lazyROStep m k))

/-- **The observable global random oracle**: the lazy random oracle with the log of its
queries, the event `inl k` a query at `k` and the event `inr ()` the observation of the log
of answered queries. -/
noncomputable def obsRO :
    Sys ((K → Option C) × List (K × C)) (K ⊕ Unit) (C ⊕ List (K × C)) :=
  (lazyRO K C).logged.observable Prod.snd

end RandomOracle

/-! ## The global common reference string -/

section CRS

variable {X C : Type}

/-- The reference string `x` when it is sampled, and a sample of `d` otherwise. -/
noncomputable def crsSample (d : PMF X) : Option X → PMF X
  | none => d
  | some x => PMF.pure x

/-- **The global common reference string**: it samples a value `x` of `d` at its first
activation, keeps it, and gives its public part `pub x` on every activation. -/
noncomputable def crsSys (d : PMF X) (pub : X → C) : Sys (Option X) Unit C where
  init := none
  step s _ := sampleFrom (ofPMF ((crsSample d s).map fun x => (some x, pub x)))

end CRS

/-! ## Graded couplings with an error that grows with the state -/

section Graded

variable {τ υ ζ E O : Type}

/-- **Graded runs with a growing error.** Let `μ` measure the states of `R`. If every activation
from related states `t`, `u` is an `rHoareApprox (ε (μ t))` judgment whose post relates the new
states with a measure at most `μ t + 1`, and `ε` is monotone, then `n` activations from related
states with `μ t ≤ m` are an `rHoareApprox` judgment with the sum of `ε (m + j)` for `j < n`. -/
theorem loop_rHoareApprox_graded (R : Sys τ E O) (I : Sys υ E O) (rel : τ → υ → Prop)
    (μ : τ → ℕ) (ε : ℕ → ℝ≥0∞) (hε : Monotone ε)
    (hstep : ∀ t u e, rel t u → rHoareApprox (ε (μ t)) eqPre (R.step t e) (I.step u e)
      (stepPost fun t' u' => rel t' u' ∧ μ t' ≤ μ t + 1))
    (bad : τ → Bool) (bad' : υ → Bool) (Z : Strat ζ E O) :
    ∀ (n : ℕ) z t u b b' m, rel t u → μ t ≤ m →
      rHoareApprox (∑ j ∈ Finset.range n, ε (m + j)) eqPre (loop R bad Z n (z, t, b))
        (loop I bad' Z n (z, u, b')) (loopPost rel) := by
  intro n
  induction n with
  | zero =>
    intro z t u b b' m hr _
    refine rHoareApprox_mono_eps (by simp) (rHoareApprox_of_rHoare ?_)
    exact rHoare_ret fun h h' heq => ⟨heq, rfl, hr⟩
  | succ n ih =>
    intro z t u b b' m hr hm
    simp only [loop]
    refine rHoareApprox_mono_eps ?_ (rHoareApprox_bind
      (ε₂ := ε m + (0 + ∑ j ∈ Finset.range n, ε (m + 1 + j)))
      (rHoareApprox_refl_of_pre (Z.next z) fun _ _ h => h) fun a a' => ?_)
    · rw [Finset.sum_range_succ', zero_add, zero_add, add_zero, add_comm]
      exact le_of_eq (congrArg₂ _ (Finset.sum_congr rfl fun j _ => by
        rw [add_assoc, add_comm 1 j]) rfl)
    refine rHoareApprox_of_pre_fact (fun _ _ hh => hh.1) fun ha => ?_
    subst ha
    refine rHoareApprox_bind (Ψ := stepPost fun t' u' => rel t' u' ∧ μ t' ≤ μ t + 1)
      (ε₂ := 0 + ∑ j ∈ Finset.range n, ε (m + 1 + j))
      (rHoareApprox_conseq (fun _ _ hh => hh.2) (fun _ _ _ _ => id) (hε hm)
        (hstep t u a.2 hr)) fun p q => ?_
    refine rHoareApprox_of_pre_fact (fun _ _ hh => hh.2) fun ⟨⟨hpq, hμ⟩, ho⟩ => ?_
    rw [← ho]
    refine rHoareApprox_bind (ε₂ := ∑ j ∈ Finset.range n, ε (m + 1 + j))
      (rHoareApprox_refl_of_pre (Z.obs a.1 p.2) fun _ _ hh => hh.1) fun z₁ z₂ => ?_
    refine rHoareApprox_of_pre_fact (fun _ _ hh => hh.1) fun hz => ?_
    subst hz
    exact rHoareApprox_conseq (fun _ _ hh => hh.2) (fun _ _ _ _ => id) le_rfl
      (ih _ _ _ _ _ _ hpq (by omega))

/-- **Realization with an error that grows with the state.** If the initial states are related,
`ε` is monotone, and every activation from related states `t`, `u` is an
`rHoareApprox (ε (μ t))` judgment whose post relates the new states with a measure at most
`μ t + 1`, then `R` realizes `I` with bound the sum of `ε (μ R.init + j)` over the activations
`j < Z.input.rounds` of the run. -/
theorem realizes_of_couplingGraded (R : Sys τ E O) (I : Sys υ E O) (rel : τ → υ → Prop)
    (μ : τ → ℕ) (ε : ℕ → ℝ≥0∞) (hε : Monotone ε) (hinit : rel R.init I.init)
    (hstep : ∀ t u e, rel t u → rHoareApprox (ε (μ t)) eqPre (R.step t e) (I.step u e)
      (stepPost fun t' u' => rel t' u' ∧ μ t' ≤ μ t + 1)) :
    Realizes R I (fun _ Z => ∑ j ∈ Finset.range Z.input.rounds, ε (μ R.init + j)) := by
  intro ζ Z
  have hv : rHoareApprox (∑ j ∈ Finset.range Z.input.rounds, ε (μ R.init + j)) eqPre
      (view R Z.input) (view I Z.input) eqPost := by
    unfold view run SPComp.map
    refine rHoareApprox_mono_eps (le_of_eq (add_zero _)) (rHoareApprox_bind
      (loop_rHoareApprox_graded R I rel μ ε hε hstep _ _ Z.input _ _ _ _ _ _ _ hinit le_rfl)
      fun c d => ?_)
    exact rHoareApprox_of_rHoare (rHoare_ret fun h h' hh => ⟨hh.2.1, hh.1⟩)
  exact rHoareApprox_absDiff_prTrue hv Z.dist Z.heap

end Graded

end CatCrypt.Crypto.UCTransparent
