/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMIDAuthFS
public import CatCryptCore.Tactics.TimeCertTry
import CatCryptCore.Tactics.DeriveReduction

/-!
# Time certificate of the forward-secure AEAD integrity reduction with headers

The costed form of `acdIDFSRed`, the integrity adversary against the forward-secure AEAD that
simulates the hop game of the immediate-decryption scheme with headers at a uniform root output.
The derivation is wrapped in `time_cert_try`, so that a derivation the existing tactic does not
complete is recorded as a time-certificate exception and adds no declaration. No module imports
this one.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging

time_cert_try derive_reduction acdIDFSRed

end CatCrypt.Crypto.Messaging
