/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Libcrux.Bridge_X25519Group
public import CatCryptCore.Crypto.SampledGameTimed

/-!
# Time of the reduction from X25519 DDH to DDH in the prime-order subgroup

The reduction of `DDH_AdvantageK_X25519_le` is `encodedRed encU3 A`: it encodes the three group
elements of a DDH triple of `G25519 B` by `encU` and runs `A` on the bytes. Its costed form is
the costed form `encodedRed.tree.timed` derived by `derive_reduction` in `SampledGameTimed`, with
the encoding `encU3` as its primitive; `encodedRed.tree.erase_timed` erases it to the reduction.

## Main results

* `encodedRed_encU3_timeBound` — with the adversary's `run` of time at most `T` and call cost
  at most `a`, and the encoding of the triple of cost at most `c`, time at most `T + a + c + 2`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Libcrux.Bridge_X25519Group

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Crypto.ECC
open CatCryptCore.Examples.CyclicGroupDDH

/-- **Time of the X25519 DDH reduction**: three encodings of total cost at most `c` and one call
of the adversary of time at most `T` and call cost at most `a`. -/
theorem encodedRed_encU3_timeBound {B : Curve25519Point} (encCost : DDHTriple (G25519 B) → ℕ)
    (run : Vector UInt8 32 × Vector UInt8 32 × Vector UInt8 32 → SPTree.Timed Bool)
    (runCost : Vector UInt8 32 × Vector UInt8 32 × Vector UInt8 32 → ℕ)
    (t : DDHTriple (G25519 B)) {T a c : ℕ} (hA : ∀ w, (run w).time ≤ T)
    (hAc : ∀ w, runCost w ≤ a) (hc : ∀ t, encCost t ≤ c) :
    SPTree.Timed.stepTime (encodedRed.tree.timed encU3 encCost run runCost t) ≤ T + a + c + 2 :=
  encodedRed.tree.timeBound_timed encU3 encCost run runCost t hA hAc hc

end CatCrypt.Crypto.Libcrux.Bridge_X25519Group
