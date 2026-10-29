/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Category.ProtBicatReactive
public import CatCryptCore.Crypto.UCTransparentMultiTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.StdCosts

/-!
# Running time of the one-call leak simulator

The costed form of the one-call simulator `simWrap` of `ProtBicatReactive.lean`, derived by
`derive_reduction`, and the time theorem of its `start` step, derived by `derive_time_bound`.
No module imports this file.
-/

@[expose] public section

set_option autoImplicit false

derive_reduction CatCrypt.Crypto.UCTransparent.simWrap
derive_time_bound CatCrypt.Crypto.UCTransparent.simWrap.start.tree
