/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCGlobalSquare
public import CatCryptCore.Crypto.UCTransparentMultiTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.StdCosts

/-!
# Running time of the router over a global functionality

The costed form of the router `gRouter` of `UCGlobalSquare.lean`, derived by
`derive_reduction`, and the time theorems of its three steps, derived by `derive_time_bound`.
No module imports this file.

## Main results

* `gRouter.timed`, `gRouter.erase_timed`: the costed router and its erasure.
* `gRouter.start.tree.timeBound_timed`, `gRouter.resume.tree.timeBound_timed`,
  `gRouter.finish.tree.timeBound_timed`: the time bounds of the three costed steps.
-/

@[expose] public section

set_option autoImplicit false

derive_reduction CatCrypt.Crypto.UCTransparent.gRouter
derive_time_bound CatCrypt.Crypto.UCTransparent.gRouter.start.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.gRouter.resume.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.gRouter.finish.tree
