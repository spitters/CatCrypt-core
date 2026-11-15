/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.UC.ChainEnv
public import CatCryptCore.Tactics.TimeCertTry
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.DeriveSimulator

/-!
# Time certificate of the chain simulator with the environment

The costed form of `chainSimE` of `ChainEnv.lean`, the chain world driven by the
environment with the ideal clock and network substituted.
Each derivation is wrapped in `time_cert_try`, so that a derivation the existing tactic does
not complete is recorded as a time-certificate exception and adds no declaration. No module
imports this one.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCryptCore.Consensus.UC.ChainEnv

time_cert_try derive_reduction chainSimE

end CatCryptCore.Consensus.UC.ChainEnv
