/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.UC.Finality
public import CatCryptCore.Tactics.TimeCertTry
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.DeriveSimulator

/-!
# Time certificate of the finality gadget simulator

The costed form of the finality gadget simulator `ffgSim` of `Finality.lean`.
Each derivation is wrapped in `time_cert_try`, so that a derivation the existing tactic does
not complete is recorded as a time-certificate exception and adds no declaration. No module
imports this one.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCryptCore.Consensus.UC.FFGGadget

time_cert_try derive_reduction ffgSim

end CatCryptCore.Consensus.UC.FFGGadget
