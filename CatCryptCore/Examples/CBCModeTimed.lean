/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.CBCMode
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Time of the CBC block-cipher reduction

The computation tree and costed form of `CBCBlockCipher.cbcRed` of
`CatCryptCore.Examples.CBCMode`, derived by `derive_reduction`, and its time bound.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per bookkeeping step; the adversary
call costs its cost companion.

## Main results

* `CBCBlockCipher.cbcRed.tree.timeBound_timed` — an adversary of time `T` and call cost `a`
  gives a distinguisher of time at most `T + a + 1`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.CBCMode

open CatCrypt.Core

derive_reduction CBCBlockCipher.cbcRed

/-- **Time of the CBC reduction.** An adversary `A` of time at most `T` and call cost at most
`a` gives a distinguisher of time at most `T + a + 1`. -/
theorem CBCBlockCipher.cbcRed.tree.timeBound_timed (C : CBCBlockCipher) (iv : C.Block)
    (A : C.Block × C.Block → SPTree.Timed Bool) (ACost : C.Block × C.Block → ℕ) {T a : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) (y : C.Block) :
    SPTree.Timed.stepTime (CBCBlockCipher.cbcRed.tree.timed C iv A ACost y) ≤ T + a + 1 := by
  time_bound

end CatCrypt.Examples.CBCMode
