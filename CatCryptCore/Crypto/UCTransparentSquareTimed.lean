/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCTransparentSquare
public import CatCryptCore.Crypto.UCSimulatorTimed
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.DeriveSimulator
import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.DeriveTimeBound.Basic

/-!
# Running time of the simulator of the adversary port

`derive_reduction` builds the costed form of the multi-call simulator `transSim S sp hS o₀` of
`UCTransparentSquare.lean`, whose steps run the step of the transparent simulator `S`, a costed
binder. Its costed state stores the completion of a forwarded honest input with a cost
companion, which the `resume` step reads; `derive_time_bound` bounds its steps, and the time on
the states of the invariant `TransInv` (each stored companion bounded by the bound on the cost of
`sp.rest`, plus one) is `transSim.timeBoundInv_timed`. `derive_simulator` builds the costed form
of the bundled simulator `transSimulator` from it.

No module imports this file.

## Main results

* `transSim.timed`, `transSim.erase_timed`, `transSim.timeBoundInv_timed`: the costed
  multi-call simulator, its erasure and its time on the states of `TransInv`.
* `transSimulator.timed`, `transSimulator.erase_timed`, `transSimulator.timeBound_timed`: the
  costed bundled simulator, its erasure and its time.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core

derive_reduction transSim
derive_time_bound transSim.start.treeHat
derive_time_bound transSim.resume.treeHat
derive_time_bound transSim.finish.treeHat

section Inv

variable {σ E O P : Type}

/-- The costed state of `transSim.timed`: the state of the transparent simulator and the costed
phase, whose `sub` and `peek` phases carry the completion with its cost companion. -/
abbrev TStHat (σ E P : Type) :=
  σ × (Unit ⊕ (P → E) × (P → ℕ) ⊕ (P → E) × (P → ℕ) ⊕ Unit ⊕ Unit)

/-- The invariant of the costed states of `transSim`: the cost companion stored in a `sub` or
`peek` phase is at most `c` at every honest input. -/
def TransInv (c : ℕ) (t : TStHat σ E P) : Prop :=
  match t.2 with
  | .inr (.inl r) => ∀ p, r.2 p ≤ c
  | .inr (.inr (.inl r)) => ∀ p, r.2 p ≤ c
  | _ => True

set_option linter.auxLemma false in
/-- **Running time of the costed simulator of the adversary port on the states of its
invariant**: from a state of `TransInv (1 + t_restCost)`, `start` costs at most
`t_honCost + t_stepCost + T_step + 4`, `resume` at most `t_stepCost + T_step + t_restCost + 5`,
`finish` at most `2`, and every step returns states of the invariant. -/
theorem transSim.timeBoundInv_timed (S : Sys σ E O) (sp : EvSplit E P)
    (hS : ∀ s e, SPComp.NoFail (S.step s e)) (o₀ : O) (hon : E → Option P) (honCost : E → ℕ)
    (rest : E → P → E) (restCost : E → P → ℕ) (step : σ → E → SPTree.Timed (σ × O))
    (stepCost : σ → E → ℕ) {t_honCost t_restCost T_step t_stepCost : ℕ}
    (hh : ∀ a, honCost a ≤ t_honCost) (hr : ∀ a b, restCost a b ≤ t_restCost)
    (hT : ∀ a b, (step a b).time ≤ T_step) (hc : ∀ a b, stepCost a b ≤ t_stepCost) :
    (transSim.timed S sp hS o₀ hon honCost rest restCost step stepCost).TimeBoundInv
      (TransInv (1 + t_restCost)) (t_honCost + (t_stepCost + T_step + 1) + 3)
      (t_stepCost + T_step + t_restCost + 5) 2 := by
  refine ⟨trivial, fun t e ht => ⟨?_, ?_⟩, fun t o ht => ⟨?_, ?_⟩, fun t o _ => ⟨?_, ?_⟩⟩
  · have := transSim.start.treeHat.timeBound_timed S sp hS o₀ hon honCost rest restCost step
      stepCost t e hh hr hT hc
    exact le_trans this (by simp only [Nat.zero_max]; omega)
  · simp only [transSim.timed, transSim.start.treeHat.timed, transSim.start.tree.match_1.timed,
      SPTree.Timed.delay]
    split
    · simp [SPTree.Timed.AllRet, TransInv, hr]
    · simp only [SPTree.Timed.allRet_bind, SPTree.Timed.AllRet, TransInv]
      exact SPTree.Timed.allRet_of_forall (fun _ => trivial) _
  · have := transSim.resume.treeHat.timeBound_timed S sp hS o₀ hon honCost rest restCost step
      stepCost t o hh hr hT hc
    refine this.trans ?_
    obtain ⟨s, _ | r | r | _ | _⟩ := t <;> simp only [TransInv] at ht <;> split <;> grind
  · obtain ⟨s, _ | r | r | _ | _⟩ := t <;>
      simp only [transSim.timed, transSim.resume.treeHat.timed,
        transSim.resume.tree.match_1.timed, SPTree.Timed.delay] <;> split <;>
      simp only [SPTree.Timed.allRet_bind, SPTree.Timed.AllRet, TransInv, Sum.elim_inr,
        Sum.elim_inl] <;>
      first
      | exact ht
      | exact SPTree.Timed.allRet_of_forall (fun _ => trivial) _
      | trivial
  · exact transSim.finish.treeHat.timeBound_timed S sp hS o₀ hon honCost rest restCost step
      stepCost t o hh hr hT hc
  · simp only [transSim.timed, transSim.finish.treeHat.timed,
      transSim.finish.tree.match_1.timed, SPTree.Timed.delay]
    split <;> simp [SPTree.Timed.AllRet, TransInv]

end Inv

derive_simulator transSimulator

end CatCrypt.Crypto.UCTransparent
