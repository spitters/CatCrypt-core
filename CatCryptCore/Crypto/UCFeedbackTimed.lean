/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCFeedback
public import CatCryptCore.Crypto.UCTransparentMultiTimed
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.DeriveTimeBound.Basic
public import CatCryptCore.Tactics.StdCosts
public import CatCryptCore.Crypto.OracleAdversaryFree
public import CatCryptCore.Core.SPTreeTimedFree
public import CatCryptCore.Tactics.AutoTime.Basic
public import CatCryptCore.Crypto.OracleAdversaryPotential
public import CatCryptCore.ForMathlib.ListLength

/-!
# Running time of the feedback hybrid

The costed form of the feedback hybrid `MultiHybrid.fbHybrid` of `UCFeedback.lean`, derived by
`derive_reduction`, and the time theorems of its three steps, derived by `derive_time_bound`.
No library module imports this file; the companion `UCWakeTimed` does.

## Main results

* `MultiHybrid.fbHybrid.timed`, `MultiHybrid.fbHybrid.erase_timed`: the costed form and its
  erasure.
* `MultiHybrid.fbHybrid.start.tree.timeBound_timed`, `.resume.tree.timeBound_timed`,
  `.finish.tree.timeBound_timed`: the time bounds of the three costed steps.
-/

@[expose] public section

set_option autoImplicit false

derive_reduction CatCrypt.Crypto.UCTransparent.MultiHybrid.fbHybrid
derive_time_bound CatCrypt.Crypto.UCTransparent.MultiHybrid.fbHybrid.start.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.MultiHybrid.fbHybrid.resume.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.MultiHybrid.fbHybrid.finish.tree
