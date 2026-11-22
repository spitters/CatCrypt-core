/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Refinement.RRelWRPProb

/-!
# Tests of refinement up to an error: the biased coin

A coin that is `true` with probability `3/4` is coupled with the constant `true` at grade `1/4`.
The coupling gives `RefinesUpTo` at the error `1/4`, at the error `1/4 + 1/4` along `bind`, and at
`1/4 + 1/4` by vertical composition of two refinements with nonzero error.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Refinement.WRP

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Unary RefinementWP
open scoped ENNReal

/-- A coin that is `true` with probability `3/4`. -/
noncomputable def biasedCoin : SPComp Bool :=
  (SPComp.sample (Fin 4)).bind fun x => SPComp.pure (decide (x ≠ 0))

/-- The biased coin and the constant `true` are coupled at grade `1/4`. -/
theorem rHoareApprox_biasedCoin :
    rHoareApprox 4⁻¹ eqPre biasedCoin (SPComp.pure true) (couplingPost eqPre Eq) := by
  classical
  refine rHoareApprox_pure_right_of_mass fun s => ?_
  have hmass : (∑' p : Bool × Heap,
      if couplingPost eqPre Eq p.1 p.2 true s then biasedCoin s (some p) else 0) =
      wpE biasedCoin (fun x h => if x = true ∧ h = s then 1 else 0) s := by
    rw [wpE_eq_tsum]
    exact tsum_congr fun p => by grind [couplingPost, eqPre]
  have hval : wpE biasedCoin (fun x h => if x = true ∧ h = s then 1 else 0) s = 4⁻¹ * 3 := by
    simp [biasedCoin, wpE_bind, wpE_sample, Fin.sum_univ_four]
    norm_num
  rw [hmass, hval, tsub_le_iff_right]
  calc (1 : ℝ≥0∞) = 4⁻¹ * 4 := (ENNReal.inv_mul_cancel (by simp) (by simp)).symm
    _ ≤ 4⁻¹ + 4⁻¹ * 3 := le_of_eq (by ring)

/-- The biased coin refines the constant `true` up to `1/4`. -/
theorem refinesUpTo_biasedCoin :
    RefinesUpTo 4⁻¹ Lean.Order.top (heapConc eqPre) (fun e => e)
      biasedCoin (SPComp.pure true) (indRel Eq) :=
  refinesUpTo_of_rHoareApprox rHoareApprox_biasedCoin _

/-- Two biased coins in sequence refine two constants `true` up to `1/4 + 1/4`. -/
theorem refinesUpTo_biasedCoin_bind :
    RefinesUpTo (4⁻¹ + 4⁻¹) Lean.Order.top (heapConc eqPre) (fun e => e)
      (biasedCoin.bind fun _ => biasedCoin)
      ((SPComp.pure true).bind fun _ => SPComp.pure true) (indRel Eq) :=
  refinesUpTo_biasedCoin.bind fun _ _ =>
    refinesUpTo_indRel_of_rHoareApprox fun _ => rHoareApprox_biasedCoin

/-- The constant `true` is refined by the biased coin up to `1/4` through the swapped coupling,
    and the biased coin by the constant `true` up to `1/4`. Vertical composition gives the
    refinement of the biased coin by itself at the composite concretization up to `1/4 + 1/4`. -/
theorem refinesUpTo_biasedCoin_vcomp :
    RefinesUpTo (4⁻¹ + 4⁻¹) Lean.Order.top ((heapConc eqPre).comp (heapConc eqPre)) (fun e => e)
      biasedCoin biasedCoin ((heapConc eqPre).relComp (indRel Eq) (indRel Eq)) := by
  have hswap : rHoareApprox 4⁻¹ eqPre (SPComp.pure true) biasedCoin (couplingPost eqPre Eq) :=
    fun s s' hs => liftRApprox_mono_rel (fun _ _ hr => ⟨hr.1.symm, hr.2.symm⟩)
      (liftRApprox_symm (rHoareApprox_biasedCoin s' s hs.symm))
  exact RefinesUpTo.vcomp_heapConc (refinesUpTo_of_rHoareApprox hswap _) refinesUpTo_biasedCoin

/-- The error `1/4 + 1/4` is below `1`. -/
theorem biasedCoin_error_lt_one : (4⁻¹ + 4⁻¹ : ℝ≥0∞) < 1 := by
  rw [← ENNReal.toReal_lt_toReal (by simp) (by simp), ENNReal.toReal_add (by simp) (by simp)]
  norm_num

end CatCrypt.Refinement.WRP
