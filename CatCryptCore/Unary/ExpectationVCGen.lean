/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Unary.ExpectationVCGenCore
public import CatCryptCore.Unary.ExpectedCost
public import CatCryptCore.Examples.DetCPA
public import Std.Tactic.Do

@[expose] public section
set_option autoImplicit false

/-!
# Examples of `vcgen` on `SPComp` at the expectation carrier

Two quantitative statements proved by `vcgen` with the `WPMonad` instances of
`CatCryptCore.Unary.ExpectationVCGenCore`, which this module re-exports.

## Main statements

* `same_msg_prTrue_vcgen`, `prEventComp_bind_step_le_vcgen`: two quantitative
  statements of `CatCryptCore.Examples.DetCPA` and `CatCrypt.Unary.QueryBound` proved
  by `vcgen` and arithmetic.
-/

namespace CatCrypt.Unary

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal
open Std.WP

set_option mvcgen.warning false in
open CatCryptCore.Examples.DetCPA in
/-- `CatCryptCore.Examples.DetCPA.same_msg_prTrue` by `vcgen`: the equality adversary
returns `true` with probability `1` on two encryptions of one message. -/
theorem same_msg_prTrue_vcgen (m : Bool) :
    CatCrypt.Crypto.prTrue ((det_enc_pair xorDet m m).bind eq_adversary) Heap.empty = 1 := by
  refine le_antisymm (CatCrypt.Crypto.prTrue_le_one _ _) ?_
  rw [← wpE_indicator_eq_prTrue]
  have ht : Triple ((det_enc_pair xorDet m m).bind eq_adversary)
      (fun _ => (1 : ℝ≥0∞)) (fun (b : Bool) (_ : Heap) => if b then (1 : ℝ≥0∞) else 0)
      Lean.Order.bot := by
    unfold det_enc_pair eq_adversary xorDet
    vcgen
    all_goals simp only [leanOrder_rel_iff_le, tsum_bool, wp_eq_wpEF, wpEF_pure,
      Fintype.card_bool, beq_self_eq_true]
    all_goals simp only [ite_true, ← two_mul, Nat.cast_ofNat, mul_one]
    all_goals simp only [binderNameHint, wpEF_pure, beq_self_eq_true, ite_true, ← two_mul, mul_one]
    all_goals rw [ENNReal.inv_mul_cancel] <;> simp
  simp_all [triple_iff_le_wpE]

set_option mvcgen.warning false in
/-- `CatCrypt.Unary.prEventComp_bind_step_le` by `vcgen` on `SPCompU`: if from every
non-bad heap one step reaches a bad heap with probability at most `ε`, then appending
the step to `m` adds at most `ε` to the probability of a bad final heap. -/
theorem prEventComp_bind_step_le_vcgen
    (m : SPComp Unit) (step : SPComp Unit) (h₀ : Heap) (bad : Heap → Prop)
    (ε : ℝ≥0∞)
    (h_fresh : ∀ h₁ : Heap, ¬ bad h₁ →
      prEvent (step h₁) (fun _ h' => bad h') ≤ ε) :
    prEventComp (m.bind (fun _ => step)) h₀ (fun _ h' => bad h') ≤
      prEventComp m h₀ (fun _ h' => bad h') + ε := by
  classical
  rw [← wpE_indicator_eq_prEventComp, ← wpE_indicator_eq_prEventComp]
  have hstep : Triple (SPCompU.lift step)
      (fun h => OrderDual.toDual (if bad h then 1 else ε))
      (fun _ h => OrderDual.toDual (if bad h then (1 : ℝ≥0∞) else 0))
      (OrderDual.toDual 0) := by
    refine (SPCompU.triple_iff_wpE_le _ _ _).2 fun h => ?_
    rw [wpE_indicator_eq_prEventComp]
    by_cases hb : bad h
    · simpa [hb, prEventComp] using (prEvent_le_mass _ _).trans (sdistr_mass_le_one _)
    · simpa [hb, prEventComp] using h_fresh h hb
  have hm : ∀ post : Unit → Heap → ℝ≥0∞ᵒᵈ, Triple (SPCompU.lift m)
      (fun h => OrderDual.toDual (wpE m (fun a h' => OrderDual.ofDual (post a h')) h))
      post (OrderDual.toDual 0) := fun _ => SPCompU.spec_wpE m
  have ht : Triple
      (SPCompU.lift (α := PUnit) (SPComp.bind (α := PUnit) (β := PUnit) m fun _ => step))
      (fun h => OrderDual.toDual
        (wpE (α := PUnit) m (fun _ h' => if bad h' then (1 : ℝ≥0∞) else 0) h + ε))
      (fun (_ : PUnit) h => OrderDual.toDual (if bad h then (1 : ℝ≥0∞) else 0))
      (OrderDual.toDual 0) := by
    vcgen [hstep, hm]
    rename_i h
    simp only [leanOrder_rel_dual_iff, OrderDual.ofDual_toDual]
    calc wpE m (fun _ h' => OrderDual.ofDual (wp (SPCompU.lift step)
            (fun _ h => OrderDual.toDual (if bad h then (1 : ℝ≥0∞) else 0))
            (OrderDual.toDual 0) h')) h
        ≤ wpE m (fun _ h' => (if bad h' then (1 : ℝ≥0∞) else 0) + ε) h := by
          refine wpE_mono m (fun _ h' => ?_) h
          have hle := hstep.le_wp h'
          simp only [leanOrder_rel_dual_iff, OrderDual.ofDual_toDual] at hle
          refine le_trans hle ?_
          split_ifs <;> simp
      _ ≤ wpE m (fun _ h' => if bad h' then (1 : ℝ≥0∞) else 0) h + ε := by
          rw [wpE_add]
          exact add_le_add le_rfl (wpE_const_le m ε h)
  exact (SPCompU.triple_iff_wpE_le _ _ _).1 ht h₀

end CatCrypt.Unary
