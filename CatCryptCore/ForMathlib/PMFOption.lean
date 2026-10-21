/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Distributions read through `Option.some`

## Main results

* `PMF.map_some_apply_some` — the image of `p` under `some` has weight `p a` at `some a`
-/

@[expose] public section

set_option autoImplicit false

namespace PMF

/-- The image of `p` under `some` has weight `p a` at `some a`. -/
theorem map_some_apply_some {α : Type*} (p : PMF α) (a : α) : (p.map some) (some a) = p a := by
  rw [PMF.map_apply, tsum_eq_single a fun b hb => by simp [Ne.symm hb]]
  simp

end PMF
