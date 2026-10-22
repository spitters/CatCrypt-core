/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Assumptions.OWF
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Time of the PRG distinguisher built from a one-way-function inverter

The computation tree and costed form of `prg_distinguisher_of_owf_inverter` of
`CatCryptCore.Crypto.Assumptions.OWF`, derived by `derive_reduction`, and its time bound.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per bookkeeping step and per equality
test; the stretch function is a primitive with cost companion `stretchCost`; the inverter call
costs its cost companion.

## Main results

* `prg_distinguisher_of_owf_inverter.tree.timeBound_timed` — an inverter of time `T` and call
  cost `a`, with a stretch of cost at most `ts`, gives a distinguisher of time at most
  `T + a + ts + 3`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core

derive_reduction prg_distinguisher_of_owf_inverter

/-- **Time of the PRG distinguisher.** An inverter `A` of time at most `T` and call cost at most
`a`, with a stretch of cost at most `ts`, gives a distinguisher of time at most
`T + a + ts + 3`. -/
theorem prg_distinguisher_of_owf_inverter.tree.timeBound_timed {W : Type} [DecidableEq W]
    (G : PRGDef W W) (A : W → SPTree.Timed W) (ACost : W → ℕ) (y : W) (stretch : W → W)
    (stretchCost : W → ℕ) {T a ts : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a)
    (hs : ∀ x, stretchCost x ≤ ts) :
    SPTree.Timed.stepTime
        (prg_distinguisher_of_owf_inverter.tree.timed G A ACost y stretch stretchCost) ≤
      T + a + ts + 3 := by
  time_bound

end CatCrypt.Crypto.Assumptions
