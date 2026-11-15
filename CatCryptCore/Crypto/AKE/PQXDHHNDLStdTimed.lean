/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDHHNDLStd
public import CatCryptCore.Crypto.AKE.PQXDHPassiveHopsTimed
public import CatCryptCore.Tactics.TimeCertTry
import CatCryptCore.Tactics.DeriveReduction

/-!
# Time certificates of the single-session harvest-now-decrypt-later reductions of PQXDH

The costed forms of the two reductions of `CatCryptCore.Crypto.AKE.PQXDHHNDLStd`, derived by the
existing tactics: `hndlKemRed`, the KEM adversary that draws the five Diffie-Hellman key pairs and
runs the adversary on their secrets, and `hndlPrfRed`, the one-query PRF adversary against the
key-derivation function keyed in its KEM input. Each derivation is wrapped in `time_cert_try`, so
that a derivation the tactic does not complete is recorded as a time-certificate exception and
adds no declaration. No module imports this one.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.PQXDHPassive

time_cert_try derive_reduction hndlKemRed

time_cert_try derive_reduction hndlPrfRed

end CatCrypt.Crypto.Signal.PQXDHPassive
