/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.LinkTimed
public import CatCryptCore.Crypto.CryptoWord

/-!
# Tests of `link_timed` on a reduction over a `CryptoWord` parameter

`otpRed` samples a key over the word type `W`, masks the message by the method
`CryptoWord.wxor` of the local instance and calls the adversary. `reflect_d` represents `wxor` as
a D function value of the context; `link_timed` prices it at the unit step of its application
(the hypothesis `∀ v, wxorDCost v ≤ 0`), as `derive_timed` charges a `CryptoWord` method one
step.

## Main definitions

* `otpRed`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.LinkTimedClassTest

open CatCrypt.Core CatCrypt.Complexity.D CatCrypt.Complexity.D.Reflect CatCrypt.Crypto

/-- Sample a key, mask the message by `wxor` and call the adversary. -/
noncomputable def otpRed {W : Type} [CryptoWord W] (A : W → SPComp Bool) (m : W) :
    SPComp Bool := do
  let k ← SPComp.sample W
  A (CryptoWord.wxor k m)

derive_reduction otpRed (adv := A)

reflect_d otpRed.tree

link_timed otpRed

example := @otpRed.tree.d_timedSim

example := @otpRed.tree.d_cost_le

end CatCrypt.Tactics.LinkTimedClassTest
