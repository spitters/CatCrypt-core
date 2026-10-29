/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCFuelPad
public import CatCryptCore.Crypto.UCTransparentMultiTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.StdCosts

/-!
# Running time of the counted form of a multi-call hybrid

The costed form of the counted form `MultiHybrid.counted` of `UCFuelPad.lean`, derived by
`derive_reduction`, and the time theorems of its three steps, derived by `derive_time_bound`.
The steps of the underlying multi-call hybrid are primitives of the derivation, taken as costed
arguments. No module imports this file.

## Main results

* `MultiHybrid.counted.timed`, `MultiHybrid.counted.erase_timed`: the costed form and its
  erasure.
* `MultiHybrid.counted.start.tree.timeBound_timed`, `.resume.tree.timeBound_timed`,
  `.finish.tree.timeBound_timed`: the time bounds of the three costed steps.
-/

@[expose] public section

set_option autoImplicit false

derive_reduction CatCrypt.Crypto.UCTransparent.MultiHybrid.counted
derive_time_bound CatCrypt.Crypto.UCTransparent.MultiHybrid.counted.start.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.MultiHybrid.counted.resume.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.MultiHybrid.counted.finish.tree
