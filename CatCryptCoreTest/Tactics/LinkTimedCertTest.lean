/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.LinkTimed

/-!
# Tests of `link_timed` through certified callees

Fresh definitions, none taken from a protocol. A callee with a certificate (`coin` and `coin2`,
linked by `link_timed`) is reflected at a call as the closure of its own D-term renamed into the
caller's context (`Ren.liftN`), the arguments before the last bound by `let`, and `link_timed`
applies its certificate `c.d_timedSim` at the call (`TSim.certCall`) instead of walking its body
again:

* `oneCoin` (a call on a computed argument at the root): allowance `1`, that of `coin`;
* `coinAfter` (a sample, then a call): allowance `2`;
* `twoCoins` (a call bound, then a call on the negated result): allowance `3`;
* `useCoin2` (a callee with two parameters, the first bound by `let`): allowance `2`;
* `plainCoin`, the body of `coin` written without the call, is reflected as before.

## Main definitions

* `coin`, `oneCoin`, `coinAfter`, `twoCoins`, `coin2`, `useCoin2`, `plainCoin`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.LinkTimedCertTest

open CatCrypt.Core CatCrypt.Complexity.D

/-- A coin flipped and combined with `b`. -/
noncomputable def coin (b : Bool) : SPTree Bool :=
  SPTree.sample Bool inferInstance inferInstance fun x => SPTree.ret (x && b)

derive_timed coin

reflect_d coin

link_timed coin

/-- One coin on the negation of `b`. -/
noncomputable def oneCoin (b : Bool) : SPTree Bool := coin (!b)

derive_timed oneCoin

reflect_d oneCoin

/-- The call is the closure of the D-term of `coin` on the negation: the body of `coin` is not
reflected again. -/
example : oneCoin.d =
    .app (.lam (coin.d.rename (Ren.liftN _))) (.prim .bnot (.var .here)) := rfl

link_timed oneCoin

example (b : Bool) :
    TimedSim (fun a w => a = w) 1 1 (oneCoin.timed b) (oneCoin.d.eval (Env.nil.cons b)) :=
  oneCoin.d_timedSim b

/-- A coin after a sample. -/
noncomputable def coinAfter (b : Bool) : SPTree Bool :=
  SPTree.sample Bool inferInstance inferInstance fun x => coin (x && b)

derive_timed coinAfter

reflect_d coinAfter

link_timed coinAfter

example (b : Bool) :
    TimedSim (fun a w => a = w) 1 2 (coinAfter.timed b) (coinAfter.d.eval (Env.nil.cons b)) :=
  coinAfter.d_timedSim b

/-- Two coins, the second on the negated result of the first. -/
noncomputable def twoCoins (b : Bool) : SPTree Bool :=
  SPTree.bind (coin b) fun x => coin (!x)

derive_timed twoCoins

reflect_d twoCoins

link_timed twoCoins

example (b : Bool) :
    TimedSim (fun a w => a = w) 1 3 (twoCoins.timed b) (twoCoins.d.eval (Env.nil.cons b)) :=
  twoCoins.d_timedSim b

/-- A coin combined with two bits. -/
noncomputable def coin2 (a b : Bool) : SPTree Bool :=
  SPTree.sample Bool inferInstance inferInstance fun x => SPTree.ret ((x && a) || b)

derive_timed coin2

reflect_d coin2

link_timed coin2

/-- A call of `coin2`: its first argument bound by `let`, its last the argument of the
closure. -/
noncomputable def useCoin2 (b : Bool) : SPTree Bool := coin2 b (!b)

derive_timed useCoin2

reflect_d useCoin2

example : useCoin2.d =
    .letE (.var .here) (.app (.lam (coin2.d.rename (Ren.liftN _)))
      (.prim .bnot (.var (.there .here)))) := rfl

link_timed useCoin2

example (b : Bool) :
    TimedSim (fun a w => a = w) 1 2 (useCoin2.timed b) (useCoin2.d.eval (Env.nil.cons b)) :=
  useCoin2.d_timedSim b

/-- The body of `coin` at the negation of `b`, without a call. -/
noncomputable def plainCoin (b : Bool) : SPTree Bool :=
  SPTree.sample Bool inferInstance inferInstance fun x => SPTree.ret (x && !b)

derive_timed plainCoin

reflect_d plainCoin

link_timed plainCoin

end CatCrypt.Tactics.LinkTimedCertTest
