/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Reflect
public import CatCryptCore.Crypto.CryptoWord
public import CatCryptCore.Examples.CyclicGroupDDH

/-!
# Tests for `reflect_d` on type parameters with class instances

Definitions over a type parameter `W` with an instance `CryptoWord W` and over `G` with an
instance `CyclicGroup G`, reflected by `reflect_d`. The instance is a binder of the theorems
and the class methods applied in the body are D values of the context:

* `wordMask`: the method `CryptoWord.wxor` twice, a D function with its hypothesis;
* `wordEq`: an equality and a disequality at `W`, decided by the equality method of the
  instance `DecidableEq W` that `CryptoWord W` provides;
* `wordOtp`: a sample over `W`, the method `wxor` and an adversary call;
* `groupBlind`: the group multiplication `*` (through a helper definition, unfolded) and the
  generator `CyclicGroup.gen`, a datum of the context.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D.ReflectClassTest

open CatCrypt.Core CatCrypt.Complexity.D CatCrypt.Crypto CatCryptCore.Examples.CyclicGroupDDH

/-- A key masked twice by `wxor`. -/
def wordMask {W : Type} [CryptoWord W] (k m : W) : W :=
  CryptoWord.wxor k (CryptoWord.wxor m k)

reflect_d wordMask

example := @wordMask.d_den

example := @wordMask.d_cost

/-- An equality and a disequality at the word type. -/
def wordEq {W : Type} [CryptoWord W] (a b : W) : Bool :=
  if a = b then true else decide (a ≠ b)

reflect_d wordEq

example := @wordEq.d_den

/-- A one-time pad: a sampled key `wxor` the message, given to the adversary. -/
noncomputable def wordOtp {W : Type} [CryptoWord W] (A : W → SPComp Bool) (m : W) :
    SPComp Bool := do
  let k ← SPComp.sample W
  A (CryptoWord.wxor k m)

reflect_d wordOtp

example := @wordOtp.d_den

example := @wordOtp.d_cost

/-- The square of a group element. -/
def groupSq {G : Type} [CyclicGroup G] (x : G) : G := x * x

/-- A blinding `x² · (y · g)` by the generator `g`. -/
def groupBlind {G : Type} [CyclicGroup G] (x y : G) : G :=
  groupSq x * (y * CyclicGroup.gen)

reflect_d groupBlind

example := @groupBlind.d_den

example := @groupBlind.d_cost

end CatCrypt.Complexity.D.ReflectClassTest
