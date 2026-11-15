/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.TLSSquareSigned
public import CatCryptCore.Crypto.AKE.X3DHSquareSignedTimed
public import CatCryptCore.Crypto.UCOracleGameTimed
public import CatCryptCore.Tactics.TimeCertTry
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.DeriveTimeBound.Basic

/-!
# Time certificates of the forger of the signed TLS square

The costed forms of the step `forgeStep` and of the forger `tlsForgeRed` of
`TLSSquareSigned.lean`. Each derivation is wrapped in `time_cert_try`, so that a derivation the
existing tactic does not complete is recorded as a time-certificate exception and adds no
declaration. No module imports this one.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.TLSSquareSigned

time_cert_try derive_timed forgeStep

time_cert_try derive_reduction tlsForgeRed

end CatCrypt.Crypto.AKE.TLSSquareSigned
