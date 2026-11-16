/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.TLSSquareGDH
public import CatCryptCore.Crypto.AKE.X3DHSquareGDHTimed
public import CatCryptCore.Tactics.TimeCertTry
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.DeriveTimeBound.Basic

/-!
# Time certificate of the gap Diffie–Hellman reduction of the TLS square

The costed form of the reduction `tlsGdhRed` of `TLSSquareGDH.lean`. The derivation is wrapped in
`time_cert_try`, so that a derivation the existing tactic does not complete is recorded as a
time-certificate exception and adds no declaration. No module imports this one.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.TLSSquareGDH

time_cert_try derive_reduction tlsGdhRed

end CatCrypt.Crypto.AKE.TLSSquareGDH
