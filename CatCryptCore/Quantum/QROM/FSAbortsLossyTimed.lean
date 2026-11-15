/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.FSAbortsLossy
public import CatCryptCore.Tactics.TimeCertTry
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.DeriveSimulator

/-!
# Time certificate of `B_lossyQ`

The costed form of `B_lossyQ` of `FSAbortsLossy.lean`.
The derivation is wrapped in `time_cert_try`, so that a derivation the existing tactic does
not complete is recorded as a time-certificate exception and adds no declaration. No module
imports this one.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.QROM

time_cert_try derive_reduction B_lossyQ

end CatCrypt.Quantum.QROM
