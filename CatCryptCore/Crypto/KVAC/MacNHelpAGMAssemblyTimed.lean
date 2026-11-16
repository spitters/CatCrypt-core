/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KVAC.MacNHelpAGMAssembly
public import CatCryptCore.Tactics.TimeCertTry
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.DeriveSimulator

/-!
# Time certificate of the formal-polynomial simulator of the algebraic MAC

The costed form of `simF` of `MacNHelpAGMAssembly.lean`, the oracle
simulator that answers the queries from formal polynomials.
Each derivation is wrapped in `time_cert_try`, so that a derivation the existing tactic does
not complete is recorded as a time-certificate exception and adds no declaration. No module
imports this one.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.KVAC.MacNHelpAGM

time_cert_try derive_reduction simF

end CatCrypt.Crypto.KVAC.MacNHelpAGM
