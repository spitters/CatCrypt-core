/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Tactics.StdCosts
public import CatCryptCore.Crypto.UCTransparentMultiTimed
public import CatCryptCore.Crypto.UCRoundHybrid

/-!
# Tests of the derive tactics on hybrid machines and simulations over tables

* `derive_hybrid_time` on a hybrid machine `cntHyb` (steps `pre`, `post`) and a multi-call
  machine `cntMulti` (steps `start`, `resume`, `finish`): the time theorem of the costed machine
  from the time theorems of its steps;
* the session reduction `sessRed`, whose handler state is a table of session states: its costed
  handler passes the cost companion of the table (zero) to `sessImpl.timed` and returns lifted
  states, so `OracleAdv.Timed.timeBound_simulateHat` bounds its simulation by `T + q * (c + 8)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveGaps2Test

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Crypto.UCTransparent

/-- A forwarding hybrid machine that counts the outer events. -/
noncomputable def cntHyb (E O : Type) : Hybrid ℕ E O E O where
  init := 0
  pre s e := SPComp.pure (s + 1, e)
  post s o := SPComp.pure (s, o)
  pre_noFail _ _ := SPComp.pure_noFail _
  post_noFail _ _ := SPComp.pure_noFail _

/-- A forwarding multi-call machine that counts the outer events. -/
noncomputable def cntMulti (E O : Type) : MultiHybrid ℕ E O E O where
  init := 0
  fuel := 0
  start s e := SPComp.pure (s + 1, .inl e)
  resume s o := SPComp.pure (s, .inr o)
  finish s o := SPComp.pure (s, o)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

end CatCrypt.Tactics.DeriveGaps2Test

namespace CatCrypt.Tactics.DeriveGaps2Test

derive_reduction cntHyb
derive_time_bound cntHyb.pre.tree
derive_time_bound cntHyb.post.tree
derive_hybrid_time cntHyb

derive_reduction cntMulti
derive_time_bound cntMulti.start.tree
derive_time_bound cntMulti.resume.tree
derive_time_bound cntMulti.finish.tree
derive_hybrid_time cntMulti

/-- The costed hybrid machine `cntHyb.timed` has a time bound on each step. -/
example (E O : Type) : ∃ a b, (cntHyb.timed E O).TimeBound a b :=
  ⟨_, _, cntHyb.timeBound_timed E O⟩

/-- The costed multi-call machine `cntMulti.timed` has a time bound on each step. -/
example (E O : Type) : ∃ a b c, (cntMulti.timed E O).TimeBound a b c :=
  ⟨_, _, _, cntMulti.timeBound_timed E O⟩

end CatCrypt.Tactics.DeriveGaps2Test

namespace CatCrypt.Crypto.UCTransparent.KeyedGame

derive_reduction sessRed

end CatCrypt.Crypto.UCTransparent.KeyedGame

namespace CatCrypt.Tactics.DeriveGaps2Test

open CatCrypt.Crypto CatCrypt.Crypto.UCTransparent OracleAdv.Timed

/-- The costed session reduction runs an adversary of time `T` with at most `q` queries in time
`T + q * (c + 8)` when the session oracles cost at most `c`. -/
example {Q A S : Type} (orc : ℕ → S → Q → PMF (A × S)) (orcCost : ℕ → S → Q → ℕ) {c : ℕ}
    (hc : ∀ j s q, orcCost j s q ≤ c) (i : ℕ) (s₀ : S) (B : OracleAdv.Timed (ℕ × Q) A Bool)
    {T q : ℕ} (hB : B.TimeBound T) (hq : B.erase.IsQueryBound q) :
    StepTimeBound (KeyedGame.sessRed.timed orc orcCost i s₀ B) (T + q * (c + 8)) := by
  have h := timeBound_simulateHat (t := c + 8) (fun y : (ℕ → S) × (ℕ → ℕ) => y.1)
    (fun y => (fun x => y x, fun _ => 0))
    (fun m d => delay 1 (KeyedGame.sessImpl.timed orc orcCost i m.1 m.2 d))
    (fun s d => by time_bound) (fun s d => by allret_bound) hB hq (fun _ => s₀)
  beta_reduce at h
  unfold KeyedGame.sessRed.timed
  refine (stepTimeBound_delay (timeBound_bind (n := 0) h.2 fun _ => ?_)).mono ?_
  exacts [⟨le_rfl, trivial⟩, by have := h.1; omega]

end CatCrypt.Tactics.DeriveGaps2Test
