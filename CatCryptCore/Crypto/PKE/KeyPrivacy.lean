/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PKE.Games

/-!
# Key privacy of public-key encryption

The key-privacy game IK-CPA of Bellare, Boldyreva, Desai and Pointcheval (ASIACRYPT 2001,
Def. 1) for a public-key scheme `PKE.Games.Scheme`: two key pairs are generated, the adversary
receives both public keys and chooses a message, and guesses which of the two keys encrypts it
in the challenge.

## Main definitions

* `KeyPrivAdversary` — the two-stage adversary.
* `keyPrivGame` — the experiment with challenge bit `b`.
* `keyPrivAdvantage` — the distance between the two challenge bits.
-/

@[expose] public section

namespace CatCrypt.Crypto.PKE.Games

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open scoped ENNReal

variable {PK SK M C R : Type} [Fintype R] [Nonempty R]

variable (PK M C) in
/-- A two-stage IK-CPA adversary: `choose` receives the two public keys and returns a message
and a state; `guess` receives the state and the challenge ciphertext. -/
structure KeyPrivAdversary : Type 1 where
  /-- The state passed from the first to the second stage. -/
  St : Type
  /-- The first stage. -/
  choose : PK → PK → PMF (M × St)
  /-- The second stage. -/
  guess : St → C → PMF Bool

/-- **The IK-CPA experiment** with challenge bit `b`: two key pairs, and the challenge encrypts
the chosen message under the first public key when `b = true` and under the second when
`b = false`. -/
noncomputable def keyPrivGame (P : Scheme PK SK M C R) (A : KeyPrivAdversary PK M C) (b : Bool) :
    PMF Bool :=
  P.keygen.bind fun ks₀ => P.keygen.bind fun ks₁ => (A.choose ks₀.1 ks₁.1).bind fun x =>
    (P.encDist (if b then ks₀.1 else ks₁.1) x.1).bind fun c => A.guess x.2 c

/-- The IK-CPA advantage: the distance between the two challenge bits. -/
noncomputable def keyPrivAdvantage (P : Scheme PK SK M C R) (A : KeyPrivAdversary PK M C) :
    ℝ≥0∞ :=
  Advantage (liftPMF (keyPrivGame P A true)) (liftPMF (keyPrivGame P A false))

end CatCrypt.Crypto.PKE.Games
