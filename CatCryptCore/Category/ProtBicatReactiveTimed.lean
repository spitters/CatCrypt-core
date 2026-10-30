/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Category.ProtBicatReactive
public import CatCryptCore.Crypto.UCTransparentMultiTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Crypto.UCSimulatorTimed
public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.StdCosts

/-!
# Running time of the one-call leak simulator

The costed form of the one-call simulator `simWrap` of `ProtBicatReactive.lean`, derived by
`derive_reduction`, the time theorems of its three steps, derived by `derive_time_bound`, and
the costed form, erasure theorem and time theorem of the bundled simulator `simWrapSim`,
derived by `derive_simulator`. No module imports this file.
-/

@[expose] public section

set_option autoImplicit false

derive_reduction CatCrypt.Crypto.UCTransparent.simWrap
derive_time_bound CatCrypt.Crypto.UCTransparent.simWrap.start.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.simWrap.resume.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.simWrap.finish.tree
derive_simulator CatCrypt.Crypto.UCTransparent.simWrapSim
