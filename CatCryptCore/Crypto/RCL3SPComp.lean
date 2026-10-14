/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.RCL3
public import CatCryptCore.Crypto.UCAdmClass.SPCompInstance

/-!
# Parallel composition at level 3 for `SPComp`

This file proves parallel composition of `ucCdist` bounds and of `RobustCompilationL3` for
the trivial `UCMonadCompDist SPComp` instance. There `ucCdist = ucSdist = sdist`
(`ucCdist_eq_ucSdist_trivial`, `ucSdist_eq_sdist`), and the bound follows from
`sdist_mapSum_le` of `RC.lean`. The generic statements are `UCMonad.ucCdist_mapSum_le` and
`RobustCompilationL3_mapSum`.

## Main results

* `ucSdist_eq_sdist` — `ucSdist = sdist` on `SPComp`
* `ucCdist_mapSum_le_SPComp` — `ucCdist (mapSum f₁ g₁) (mapSum f₂ g₂) ≤ ε₁ ⊔ ε₂`
* `RobustCompilationL3_mapSum_SPComp` — parallel composition of `RobustCompilationL3`

Relation to the literature: `CatCryptCore/Crypto/Complexity.md`.
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
