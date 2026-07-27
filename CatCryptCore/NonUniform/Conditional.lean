/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.NonUniform.Sample

/-!
# Restricting, rescaling and conditioning a sub-distribution

`SDistr α` is a probability mass function on `Option α`, so the mass a
restriction removes has a place to go: `none`, the failure outcome. `restrict d P`
sends the mass outside `P` there, `scale d` divides the surviving mass by the
total mass, and `condition d P` is their composite — the distribution of a sample
from `d` given that the sample satisfies `P`.

## Main definitions

* `restrict d P` — `d` with the mass outside `P` sent to failure
* `scale d` — `d` rescaled to mass one, and `SDistr.fail` when `d` has mass zero
* `condition d P` — `scale (restrict d P)`
* `excepted d X` — `condition d (fun a => !X a)`

## Main results

* `restrict_apply_some`, `mass_restrict` — the weight of the restriction
* `scale_apply_some`, `mass_scale` — the weight of the rescaling
* `condition_apply_some` — the pointwise weight of the conditional distribution
* `mem_support_condition_iff` — the support of the conditional distribution
* `condition_eq_pure` — conditioning on a predicate met by a single point of
  positive weight is a point mass at that point

## Correspondence with EasyCrypt

The four definitions are the images of `drestrict`, `dscale`, `dcond` and `(\)`
of EasyCrypt's `Distr` and `Dexcepted` theories, whose definitions are
`dcond d p = dscale (drestrict d p)` and `d \ X = dscale (drestrict d (predC X))`.
`condition_apply_some` is the image of `dexcepted1E`, `mem_support_condition_iff`
of `supp_dexcepted`, and `mass_condition_of_ne_zero` of `dexcepted_ll`.
-/

set_option autoImplicit false

namespace CatCrypt.NonUniform

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

variable {α : Type*}

/-! ## The mass of a sub-distribution as a sum -/

/-- The mass of a sub-distribution is the total weight it puts on `some`. -/
theorem mass_eq_tsum (d : SDistr α) : SDistr.mass d = ∑' a, d (some a) := by
  have h : d none + ∑' a, d (some a) = 1 := by
    rw [← SDistr.tsum_option_eq_add]; exact d.tsum_coe
  exact ENNReal.sub_eq_of_eq_add (PMF.apply_ne_top d none) (by rw [← h]; ring)

/-- The mass of a sub-distribution is at most one. -/
theorem mass_le_one (d : SDistr α) : SDistr.mass d ≤ 1 := tsub_le_self

theorem mass_ne_top (d : SDistr α) : SDistr.mass d ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (mass_le_one d)

/-- A sub-distribution of mass zero puts no weight on any value. -/
theorem apply_some_eq_zero_of_mass_eq_zero {d : SDistr α} (h : SDistr.mass d = 0) (a : α) :
    d (some a) = 0 :=
  ENNReal.tsum_eq_zero.mp ((mass_eq_tsum d).symm.trans h) a

/-! ## Restriction -/

/-- The sub-distribution `d` with the weight outside the predicate `P` sent to
failure. -/
noncomputable def restrict (d : SDistr α) (P : α → Bool) : SDistr α :=
  d.bind fun a => if P a then SDistr.pure a else SDistr.fail

/-- A restriction keeps the weight of the values satisfying the predicate and
drops the rest. -/
theorem restrict_apply_some (d : SDistr α) (P : α → Bool) (b : α) :
    restrict d P (some b) = if P b then d (some b) else 0 := by
  classical
  rw [restrict, SDistr.bind, PMF.bind_apply, SDistr.tsum_option_eq_add]
  simp only [SDistr.fail_apply_some, mul_zero, zero_add]
  rw [tsum_eq_single b]
  · by_cases h : P b = true <;> simp [h, SDistr.pure_apply_some]
  · intro a ha
    by_cases h : P a = true <;> simp [h, SDistr.pure_apply_some, ha]

/-- The mass surviving a restriction is the weight of the values satisfying the
predicate. -/
theorem mass_restrict (d : SDistr α) (P : α → Bool) :
    SDistr.mass (restrict d P) = ∑' a, if P a then d (some a) else 0 := by
  rw [mass_eq_tsum]
  exact tsum_congr fun a => restrict_apply_some d P a

/-! ## Rescaling -/

/-- `d` rescaled to mass one. A sub-distribution of mass zero rescales to
`SDistr.fail`, which is what EasyCrypt's `dscale` returns for the null
distribution. -/
noncomputable def scale (d : SDistr α) : SDistr α :=
  ⟨fun oa =>
      match oa with
      | none => if SDistr.mass d = 0 then 1 else 0
      | some a => d (some a) / SDistr.mass d,
   ENNReal.summable.hasSum_iff.mpr (by
     rw [SDistr.tsum_option_eq_add]
     by_cases h : SDistr.mass d = 0
     · simp [h, apply_some_eq_zero_of_mass_eq_zero h]
     · simp only [if_neg h, zero_add, div_eq_mul_inv, ENNReal.tsum_mul_right,
         ← mass_eq_tsum d]
       exact ENNReal.mul_inv_cancel h (mass_ne_top d))⟩

/-- Rescaling divides every weight by the mass. -/
theorem scale_apply_some (d : SDistr α) (a : α) :
    scale d (some a) = d (some a) / SDistr.mass d := rfl

/-- A rescaled sub-distribution of nonzero mass never fails. -/
theorem scale_apply_none {d : SDistr α} (h : SDistr.mass d ≠ 0) : scale d none = 0 :=
  if_neg h

/-- Rescaling a sub-distribution of nonzero mass gives mass one. -/
theorem mass_scale {d : SDistr α} (h : SDistr.mass d ≠ 0) : SDistr.mass (scale d) = 1 := by
  rw [SDistr.mass, scale_apply_none h, tsub_zero]

/-! ## Conditioning -/

/-- The distribution of a sample from `d` given that it satisfies `P`. -/
noncomputable def condition (d : SDistr α) (P : α → Bool) : SDistr α :=
  scale (restrict d P)

/-- The distribution of a sample from `d` given that it avoids `X`. -/
noncomputable def excepted (d : SDistr α) (X : α → Bool) : SDistr α :=
  condition d (fun a => !X a)

/-- Conditioning on the complement of `X` is avoiding `X`. -/
theorem condition_not_eq_excepted (d : SDistr α) (X : α → Bool) :
    condition d (fun a => !X a) = excepted d X := rfl

/-- The weight the conditional distribution puts on a value: its weight under
`d` when it satisfies the predicate, divided by the total weight of the values
that do. -/
theorem condition_apply_some (d : SDistr α) (P : α → Bool) (a : α) :
    condition d P (some a)
      = (if P a then d (some a) else 0) / ∑' b, if P b then d (some b) else 0 := by
  rw [condition, scale_apply_some, restrict_apply_some, mass_restrict]

/-- The weight the excepted distribution puts on a value. -/
theorem excepted_apply_some (d : SDistr α) (X : α → Bool) (a : α) :
    excepted d X (some a)
      = (if X a then 0 else d (some a)) / ∑' b, if X b then 0 else d (some b) := by
  rw [excepted, condition_apply_some]
  simp only [Bool.not_eq_true']
  congr 1
  · cases hx : X a <;> simp
  · exact tsum_congr fun b => by cases hx : X b <;> simp

/-- The support of the conditional distribution is the part of `d`'s support the
predicate admits. -/
theorem mem_support_condition_iff (d : SDistr α) (P : α → Bool) (a : α) :
    a ∈ (condition d P).support ↔ a ∈ d.support ∧ P a := by
  have hden : (∑' b, if P b then d (some b) else 0) ≠ ⊤ :=
    ne_top_of_le_ne_top (mass_ne_top (restrict d P)) (le_of_eq (mass_restrict d P).symm)
  rw [SDistr.mem_support_iff, SDistr.mem_support_iff, condition_apply_some,
    Ne, ENNReal.div_eq_zero_iff]
  cases P a
  · simp
  · simp [hden]

/-- The mass of a conditional distribution is one when the predicate has
positive weight. -/
theorem mass_condition_of_ne_zero {d : SDistr α} {P : α → Bool}
    (h : (∑' b, if P b then d (some b) else 0) ≠ 0) :
    SDistr.mass (condition d P) = 1 :=
  mass_scale (by rwa [mass_restrict])

/-- Conditioning on a predicate that only one value of positive weight satisfies
is a point mass at that value. -/
theorem condition_eq_pure (d : SDistr α) (P : α → Bool) (a : α)
    (hunique : ∀ b, P b = true → b = a) (ha : P a = true) (hd : d (some a) ≠ 0) :
    condition d P = SDistr.pure a := by
  classical
  have hfalse : ∀ b : α, b ≠ a → P b = false := fun b hb => by
    cases hPb : P b
    · rfl
    · exact absurd (hunique b hPb) hb
  have hden : (∑' b, if P b then d (some b) else 0) = d (some a) := by
    refine (tsum_eq_single a fun b hb => by simp [hfalse b hb]).trans ?_
    rw [if_pos ha]
  refine SDistr.eq_of_some_eq fun b => ?_
  rw [condition_apply_some, hden, SDistr.pure_apply_some]
  by_cases hb : b = a
  · subst hb
    rw [if_pos ha, if_pos rfl, ENNReal.div_self hd (PMF.apply_ne_top d _)]
  · rw [if_neg (by simp [hfalse b hb]), if_neg (Ne.symm hb), ENNReal.zero_div]

/-! ## Sampling from a conditional distribution -/

/-- Sampling from a conditional distribution whose predicate admits a single
value of positive weight returns that value. -/
theorem sampleFrom_condition_eq_pure (d : SDistr α) (P : α → Bool) (a : α)
    (hunique : ∀ b, P b = true → b = a) (ha : P a = true) (hd : d (some a) ≠ 0) :
    sampleFrom (condition d P) = SPComp.pure a := by
  rw [condition_eq_pure d P a hunique ha hd, sampleFrom_pure]

end CatCrypt.NonUniform
