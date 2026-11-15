/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.TripleRatchetDeployed
public import CatCryptCore.Tactics.TimeCertTry
import CatCryptCore.Tactics.DeriveReduction

/-!
# Time certificates of the reductions of `CatCryptCore.Crypto.Messaging.TripleRatchetDeployed`

The costed form of `tripleRatchetDeployedRed`. Each derivation is wrapped in `time_cert_try`, so that a derivation the existing tactic does
not complete is recorded as a time-certificate exception and adds no declaration. No module
imports this one.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging

time_cert_try derive_timed_structure CatCrypt.Crypto.Messaging.SMSchemeAdv

time_cert_try derive_reduction tripleRatchetDeployedRed

end CatCrypt.Crypto.Messaging
