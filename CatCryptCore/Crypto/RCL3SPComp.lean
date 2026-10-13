/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.RCL3
public import CatCryptCore.Crypto.UCAdmClass.SPCompInstance

/-!
# Level 3 Parallel Composition for SPComp

This file provides the SPComp-specific parallel composition theorem for
`ucCdist` and `RobustCompilationL3`, which cannot be proven at the
abstract `UCMonadCompDist` level.

## Why SPComp-specific?

The abstract `ucCdist_mapSum_le` would require a new axiom
`ucDistComp_mapSum` on `UCMonadCompDist`, because the existing axioms
(PPL, triangle inequality) cannot decompose `ucSdist` over sum inputs.

For SPComp specifically, `ucCdist = ucSdist = sdist` (trivial admissibility),
so we bridge through the concrete `sdist_mapSum_le` from `RC.lean`.

## Main results

* `ucCdist_mapSum_le_SPComp` — `ucCdist (mapSum π₁ π₂) ≤ max(ucCdist π₁, ucCdist π₂)`
* `RobustCompilationL3_mapSum_SPComp` — parallel composition of RC_L3 for SPComp
-/

@[expose] public section

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob UCMonad

open scoped ENNReal

/-- For SPComp, `ucSdist f g = sdist f g` by the instance definition. -/
theorem ucSdist_eq_sdist {α β : Type}
    (f g : α → SPComp β) :
    UCMonadMetric.ucSdist (T := SPComp) f g = sdist f g := by
  show sdist f g = sdist f g; rfl

/-- Parallel composition bound for `ucCdist` on SPComp.

    Uses `ucCdist = ucSdist = sdist` (trivial admissibility) to bridge
    through the concrete `sdist_mapSum_le`. -/
theorem ucCdist_mapSum_le_SPComp {α₁ β₁ α₂ β₂ : Type}
    (f₁ f₂ : α₁ → SPComp β₁) (g₁ g₂ : α₂ → SPComp β₂)
    {ε₁ ε₂ : ℝ≥0∞}
    (hf : ucCdist (T := SPComp) f₁ f₂ ≤ ε₁)
    (hg : ucCdist (T := SPComp) g₁ g₂ ≤ ε₂) :
    ucCdist (T := SPComp) (mapSum f₁ g₁) (mapSum f₂ g₂) ≤ ε₁ ⊔ ε₂ := by
  -- ucCdist = ucSdist = sdist for SPComp (trivial admissibility)
  rw [ucCdist_eq_ucSdist_trivial] at hf hg ⊢
  rw [ucSdist_eq_sdist] at hf hg ⊢
  exact sdist_mapSum_le f₁ f₂ g₁ g₂ hf hg

/-- Parallel composition of `RobustCompilationL3` for SPComp. -/
theorem RobustCompilationL3_mapSum_SPComp {α₁ β₁ α₂ β₂ : Type}
    {ε₁ ε₂ : ℝ≥0∞}
    {π₁ F₁ : α₁ → SPComp β₁} {π₂ F₂ : α₂ → SPComp β₂}
    (h₁ : RobustCompilationL3 (T := SPComp) ε₁ π₁ F₁)
    (h₂ : RobustCompilationL3 (T := SPComp) ε₂ π₂ F₂) :
    RobustCompilationL3 (T := SPComp) (ε₁ ⊔ ε₂) (mapSum π₁ π₂) (mapSum F₁ F₂) :=
  RC_L3_of_ucCdist (ucCdist_mapSum_le_SPComp π₁ F₁ π₂ F₂
    (ucCdist_of_RC_L3 h₁) (ucCdist_of_RC_L3 h₂))

end CatCrypt.Crypto
