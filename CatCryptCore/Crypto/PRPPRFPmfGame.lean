/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PRPPRFSwitching
public import CatCryptCore.Crypto.NomPkgBridge

/-!
# Games given by a distribution on `Bool`

The game `liftPMF p` returns a sample of `p : PMF Bool` and leaves the heap unchanged.

## Main results

* `PRPPRF.advantageA_liftPMF_le` — a distinguisher run on the output bit of two such
  games has advantage at most the advantage of the games
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PRPPRF

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto

/-- A distinguisher run on the output bit of two games given by distributions on `Bool` has
advantage at most the advantage of the games. -/
theorem advantageA_liftPMF_le (p q : PMF Bool) (Z : Bool → SPComp Bool) :
    AdvantageA (liftPMF p) (liftPMF q) Z ≤ Advantage (liftPMF p) (liftPMF q) :=
  absDiff_bind_le_advantage (liftPMF_isPure p) (liftPMF_isPure q) (liftPMF_noFail p)
    (liftPMF_noFail q) Z Heap.empty

end CatCrypt.Crypto.PRPPRF
