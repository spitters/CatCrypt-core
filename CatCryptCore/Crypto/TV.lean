/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Advantage
public import CatCryptCore.Crypto.SDist

/-!
# Total Variation Distance and Post-Processing Lemma

This file defines total variation distance for sub-distributions and proves
the post-processing lemma (PPL): post-processing cannot increase the
total variation distance.

## Main definitions

* `tvDist` — total variation distance between sub-distributions

## Main results

* `prTrue_bind_as_weighted_sum` — decompose `prTrue(c.bind D)` as weighted sum
* `absDiff_prTrue_bind_le_tvDist` — PPL for stateful channels
* `tvDist_self`, `tvDist_sym` — basic properties

## Application

The PPL shows that for any `c₁, c₂ : SPComp Bool` and post-processor `D`:
```
|prTrue(c₁.bind D)(h₀) - prTrue(c₂.bind D)(h₀)| ≤ tvDist(c₁(h₀), c₂(h₀))
```
This is the mathematical foundation for the NomPkg absorption lemma.
-/

@[expose] public section

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob

open scoped ENNReal

/-! ## Total Variation Distance -/

/-- Total variation distance for sub-distributions, defined as the supremum
    of `absDiff` over bounded test functions.

    `tvDist P Q = sup_{f : Option α → [0,1]} |E_P[f] - E_Q[f]|`

    This definition uses the variational characterization of TV distance,
    which makes the PPL immediate. -/
noncomputable def tvDist {α : Type*} (P Q : SDistr α) : ℝ≥0∞ :=
  ⨆ (f : Option α → ℝ≥0∞) (_ : ∀ x, f x ≤ 1),
    absDiff (∑' x, P x * f x) (∑' x, Q x * f x)

/-! ## Basic Properties -/

theorem tvDist_self {α : Type*} (P : SDistr α) : tvDist P P = 0 := by
  apply le_antisymm
  · apply iSup_le; intro f; apply iSup_le; intro _
    exact le_of_eq (absDiff_self _)
  · exact zero_le

theorem tvDist_sym {α : Type*} (P Q : SDistr α) : tvDist P Q = tvDist Q P := by
  simp only [tvDist]
  congr 1; funext f; congr 1; funext _
  exact absDiff_comm _ _

/-! ## Weighted Sum Decomposition -/

/-- `prTrue(c.bind D) h₀` decomposes as a weighted sum over the intermediate
    distribution `c h₀`. The weight at `x : Option (Bool × Heap)` is `(c h₀)(x)`,
    and the test function maps `some (b, h')` to `prTrue (D b) h'`. -/
theorem prTrue_bind_as_weighted_sum (c : SPComp Bool) (D : Bool → SPComp Bool) (h₀ : Heap) :
    prTrue (SPComp.bind c D) h₀ =
    ∑' (x : Option (Bool × Heap)), (c h₀) x *
      (match x with | none => 0 | some (b, h') => prTrue (D b) h') := by
  unfold prTrue
  -- Expand SPComp.bind
  simp only [SPComp.bind]
  -- Now: ∑' h, ((c h₀).bind (fun p => D p.1 p.2))(some(true, h))
  -- Expand SDistr.bind via PMF.bind_apply
  simp only [SDistr.bind, PMF.bind_apply]
  -- Now: ∑' h, ∑' x, (c h₀)(x) * (match x with
  --   | some p => D p.1 p.2 | none => SDistr.fail)(some(true, h))
  -- Swap the tsum order (Fubini for ENNReal)
  rw [ENNReal.tsum_comm]
  -- Factor out (c h₀)(x) from inner tsum
  congr 1; funext x
  rw [ENNReal.tsum_mul_left]
  congr 1
  -- Show: ∑' h, (match x ...)(some(true, h)) = match x ...
  cases x with
  | none =>
    -- ∑' h, fail(some(true, h)) = 0
    exact ENNReal.tsum_eq_zero.mpr (fun h => SDistr.fail_apply_some _)
  | some p =>
    -- ∑' h, (D p.1 p.2)(some(true, h)) = prTrue (D p.1) p.2
    rfl

/-! ## Post-Processing Lemma -/

/-- Post-Processing Lemma for stateful channels.

    Post-processing cannot increase the total variation distance.
    For any `c₁, c₂ : SPComp Bool`, post-processor `D`, and initial heap `h₀`:

    `|prTrue(c₁.bind D)(h₀) - prTrue(c₂.bind D)(h₀)| ≤ tvDist(c₁(h₀), c₂(h₀))`

    Proof: Express both sides as weighted sums, observe the test function
    `g(x) = match x with | none => 0 | some (b,h') => prTrue(D b) h'` is
    bounded by 1, and apply the tvDist definition. -/
theorem absDiff_prTrue_bind_le_tvDist (c₁ c₂ : SPComp Bool)
    (D : Bool → SPComp Bool) (h₀ : Heap) :
    absDiff (prTrue (SPComp.bind c₁ D) h₀) (prTrue (SPComp.bind c₂ D) h₀) ≤
    tvDist (c₁ h₀) (c₂ h₀) := by
  -- Step 1: Decompose both prTrue as weighted sums
  rw [prTrue_bind_as_weighted_sum c₁ D h₀, prTrue_bind_as_weighted_sum c₂ D h₀]
  -- Step 2: Define the test function
  let g : Option (Bool × Heap) → ℝ≥0∞ :=
    fun x => match x with | none => 0 | some (b, h') => prTrue (D b) h'
  -- Step 3: Show g is bounded by 1
  have hg : ∀ x, g x ≤ 1 := by
    intro x; cases x with
    | none => exact zero_le
    | some p => exact prTrue_le_one (D p.1) p.2
  -- Step 4: Apply tvDist definition (g is a valid test function)
  exact le_iSup₂_of_le g hg le_rfl

end CatCrypt.Crypto
