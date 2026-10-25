/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCTransparentMulti
public import CatCryptCore.Tactics.DeriveTimedStructure
public import CatCryptCore.Tactics.DeriveReduction

/-!
# The costed mirrors of the hybrid machines

`Hybrid.Timed` and `MultiHybrid.Timed`, the costed mirrors of the hybrid machines of
UCTransparent by `derive_timed_structure`: each step field becomes a costed computation with its
cost companion and the no-failure fields are dropped. They are the result types of the costed
forms of simulators that return a hybrid machine, and are generated here once for every
companion that certifies such a simulator. `MultiHybrid.Timed.ErasesHat`, by
`derive_erases_hat`, is the erasure relation of a costed machine whose state holds functions:
each field erases to the plain field through the erasure of the costed state.

## Main definitions

* `Hybrid.Timed`, `Hybrid.Timed.Erases`, `Hybrid.Timed.TimeBound`
* `MultiHybrid.Timed`, `MultiHybrid.Timed.Erases`, `MultiHybrid.Timed.TimeBound`
* `MultiHybrid.Timed.ErasesHat`
-/

@[expose] public section

set_option autoImplicit false

derive_timed_structure CatCrypt.Crypto.UCTransparent.Hybrid

derive_timed_structure CatCrypt.Crypto.UCTransparent.MultiHybrid

derive_erases_hat CatCrypt.Crypto.UCTransparent.MultiHybrid
