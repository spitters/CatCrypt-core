/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KVAC.MacNHelpAGM
public import CatCryptCore.Tactics.TimeCertTry
import CatCryptCore.Tactics.DeriveReduction

/-!
# Time certificates of the reductions of the algebraic MAC in the algebraic group model

The costed forms of `reductionZ`, the discrete-logarithm adversary that runs the algebraic
adversary and reads the logarithm from the forged tag, and `reductionAlg`, the
`(q_m + 2)`-discrete-logarithm adversary that finds the secret exponent among the roots of the
forgery polynomial, and of `simO`, the oracle simulator that answers the queries from the
polynomials of the queries so far.
Each derivation is wrapped in `time_cert_try`, so that a derivation the
existing tactic does not complete is recorded as a time-certificate exception and adds no
declaration. No module imports this one.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.KVAC.MacNHelpAGM

time_cert_try derive_reduction reductionZ

time_cert_try derive_reduction reductionAlg

time_cert_try derive_reduction simO

end CatCrypt.Crypto.KVAC.MacNHelpAGM
