/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.LinkTimed

/-!
# Tests of `link_timed` through a table write

A fresh definition, not taken from a protocol. A table `Tab := Fin 4 → BitVec 8` under a name
that does not unfold at reducible transparency is table data for `derive_timed`: the write
`Function.update t i v` costs one unit plus `Function.update.timedCost` and the costs of its
arguments. `reflect_d` reflects it as the primitive operation `Prim.tset` of one step, and
`link_timed` links it by `DSim.prim` with no deficit beyond the sample.

* `countCoin`: a sampled byte written into the table at an index: allowance `1`.

## Main definitions

* `Tab`, `countCoin`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.LinkTimedStoreTest

open CatCrypt.Core CatCrypt.Complexity.D

/-- A table of four bytes, under a name that does not unfold at reducible transparency. -/
def Tab : Type := Fin 4 → BitVec 8

/-- A sampled byte written into the table at `i`. -/
noncomputable def countCoin (s : Tab × Bool) (i : Fin 4) : SPTree (Tab × Bool) :=
  SPTree.sample (BitVec 8) inferInstance inferInstance fun x =>
    SPTree.ret (Function.update (β := fun _ => BitVec 8) s.1 i x, s.2)

derive_timed countCoin

reflect_d countCoin

link_timed countCoin

example (s : Tab × Bool) (i : Fin 4) :
    TimedSim (fun a w => a = w) 1 1 (countCoin.timed s i)
      (countCoin.d.eval (Env.cons i (Env.cons s Env.nil))) :=
  countCoin.d_timedSim s i

end CatCrypt.Tactics.LinkTimedStoreTest
