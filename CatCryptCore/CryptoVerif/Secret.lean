/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.CryptoVerif.Event

/-!
# Bit secrecy of CryptoVerif games

CryptoVerif's `query secret b [cv_bit]` on a game that branches on the bit `b` shows that the
game with `b` false is indistinguishable from the game with `b` true. A proof of it is a
sequence of games from one to the other, whose bound is the sum of the step bounds.

## Main results

* `CvSecretBit` — `query secret b [cv_bit]` at a bound: `G false ≈_ε G true`.
* `CvSecretBit.of_chain` — two realization steps through an intermediate game give bit secrecy
  at the sum of the bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.CryptoVerifLogic

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent
open scoped ENNReal

variable {I : CvIface}

/-- CryptoVerif's `query secret b [cv_bit]` at the bound `ε`: the system of the game with the
bit false realizes the system of the game with the bit true. -/
def CvSecretBit (G : Bool → CvGame I) (ε : CvBound I) : Prop :=
  Realizes (G false).sys (G true).sys ε

/-- A sequence of two steps from the game with the bit false, through `H`, to the game with
the bit true proves bit secrecy at the sum of the step bounds. -/
theorem CvSecretBit.of_chain {G : Bool → CvGame I} {H : CvGame I} {ε₁ ε₂ : CvBound I}
    (h₁ : Realizes (G false).sys H.sys ε₁) (h₂ : Realizes H.sys (G true).sys ε₂) :
    CvSecretBit G fun ζ Z => ε₁ ζ Z + ε₂ ζ Z :=
  Realizes.trans h₁ h₂

end CatCrypt.Crypto.CryptoVerifLogic
