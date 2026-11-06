/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.LinkTimed

/-!
# Tests of `link_timed` through the soundness theorem at calls of parametric type and calls of
free function values

Fresh definitions of the two classes on which the comparison with `t.dt η` alone does not apply,
each linked through `Tm.timedSim_of_costLeA`; the theorem `T.d_run`, which `link_timed` proves
only on that route, is checked for each.

Calls at an argument of a type parameter, `base MF` in D, where `callCost (base MF)` is
undecided (the comparison runs at the charge `1` of every call, `Tm.dtC`):

* `tpCall`: a sample over a type parameter, a call on the sample and a Boolean operation;
* `tpData`: a call on the value of a data function between type parameters;
* `tpTwo`: a call at a type parameter, then a call at `Bool` on its result;
* `tpUnit`: a tree without arguments (a call on `unit`, a deficit of one at the charge `1`) and a
  call at a type parameter on its result.

Calls of projection and re-pairing values of a matched pair, which `derive_timed` charges
nothing for (the deficit paid by the allowance):

* `frSwap`: a match on a pair argument and a call on the swapped pair;
* `frSample`: a match on a pair argument, a sample and a call on an operation of a component and
  the sample;
* `frParam`: a match on a pair of a type parameter and a call on the swapped pair (both classes).

## Main definitions

* `tpCall`, `tpData`, `tpTwo`, `tpUnit`, `frSwap`, `frSample`, `frParam`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.LinkTimedDtParamTest

open CatCrypt.Core CatCrypt.Complexity.D CatCrypt.Complexity.D.Reflect

/-- Sample `x` of a type parameter, call the adversary on it and negate its answer. -/
noncomputable def tpCall {X : Type} [Fintype X] [Nonempty X] (A : X → SPComp Bool) :
    SPComp Bool := do
  let x ← SPComp.sample X
  let b ← A x
  return !b

derive_reduction tpCall (adv := A)

reflect_d tpCall.tree

link_timed tpCall

example := @tpCall.tree.d_run

/-- Call the adversary on the value of a data function `f` between type parameters. -/
noncomputable def tpData {X Y : Type} (f : X → Y) (A : Y → SPComp Bool) (x : X) : SPComp Bool :=
  A (f x)

derive_reduction tpData (adv := A)

reflect_d tpData.tree

link_timed tpData

example := @tpData.tree.d_run

/-- Call the adversary `A` at a type parameter, then `B` on its answer. -/
noncomputable def tpTwo {X : Type} (A : X → SPComp Bool) (B : Bool → SPComp Bool) (x : X) :
    SPComp Bool := do
  let b ← A x
  B b

derive_reduction tpTwo (adv := A)

reflect_d tpTwo.tree

link_timed tpTwo

example := @tpTwo.tree.d_run

/-- Run the public computation `p` and call the adversary on its result. -/
noncomputable def tpUnit {X : Type} (p : SPComp X) (A : X → SPComp Bool) : SPComp Bool := do
  let x ← p
  A x

derive_reduction tpUnit (adv := A)

reflect_d tpUnit.tree

link_timed tpUnit

example := @tpUnit.tree.d_run

/-- Match a pair argument and call the adversary on the swapped pair. -/
noncomputable def frSwap (A : Bool × Bool → SPComp Bool) : Bool × Bool → SPComp Bool :=
  fun (a, b) => A (b, a)

derive_reduction frSwap (adv := A)

reflect_d frSwap.tree

link_timed frSwap

example := @frSwap.tree.d_run

/-- Match a pair argument, sample a bit and call the adversary on the conjunction of the second
component and the bit. -/
noncomputable def frSample (A : Bool → SPComp Bool) : Bool × Bool → SPComp Bool :=
  fun (_, b) => do
    let c ← SPComp.sample Bool
    A (b && c)

derive_reduction frSample (adv := A)

reflect_d frSample.tree

link_timed frSample

example := @frSample.tree.d_run

/-- Match a pair of a type parameter and call the adversary on the swapped pair. -/
noncomputable def frParam {X : Type} (A : X × X → SPComp Bool) : X × X → SPComp Bool :=
  fun (x, y) => A (y, x)

derive_reduction frParam (adv := A)

reflect_d frParam.tree

link_timed frParam

example := @frParam.tree.d_run

end CatCrypt.Tactics.LinkTimedDtParamTest
