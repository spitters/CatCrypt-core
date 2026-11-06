/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.LinkTimed

/-!
# Tests of `link_timed` through the soundness theorem `Tm.dt_timedSim`

Fresh definitions in the fragment of `Tm.dt_timedSim`, each linked by comparing its costed form
with `t.dt η`; the theorem `T.d_run`, which `link_timed` proves only on that route, is checked
for each:

* `dtCond`: a sample, then a conditional on the sampled bit between a call and a leaf (a case
  split on a variable inside a sample node);
* `dtOps`: data `let`s of Boolean operations before a call;
* `dtFn`: a call on the value of a data function parameter with its cost companion;
* `dtSeq`: two bound calls and a Boolean operation on their results (binds stuck at a call);
* `dtPair`: a sample and a call on a pair;
* `dtBranch`: a conditional on a parameter whose branches bind a call and sample;
* `dtInj`: a call, a sample and a leaf that is a conditional between injections into a sum (the
  walk refuses a conditional at a leaf);
* `dtProj`: a `let` of a pair and a call on its projection;
* `dtNest`: a call, a sample, and a conditional between a call and a leaf on values of a data
  function parameter;
* `dtLeafPair`: a call and a pair leaf;
* `dtFold`: a call on a left fold, priced by the registered cost of `List.foldl`, compared
  through its monotonicity in the step cost (the walk refuses `foldl`).

## Main definitions

* `dtCond`, `dtOps`, `dtFn`, `dtSeq`, `dtPair`, `dtBranch`, `dtInj`, `dtProj`, `dtNest`,
  `dtLeafPair`, `dtFold`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.LinkTimedDtTest

open CatCrypt.Core

/-- Sample a bit; call the adversary on it when it is set, return its negation otherwise. -/
noncomputable def dtCond (A : Bool → SPComp Bool) : SPComp Bool := do
  let x ← SPComp.sample Bool
  if x = true then A x else return !x

derive_reduction dtCond (adv := A)

reflect_d dtCond.tree

link_timed dtCond

example := @dtCond.tree.d_run

/-- Two data `let`s of Boolean operations, then a call. -/
noncomputable def dtOps (A : Bool → SPComp Bool) (b c : Bool) : SPComp Bool := do
  let d := b && c
  let e := !d && b
  A (d && !e)

derive_reduction dtOps (adv := A)

reflect_d dtOps.tree

link_timed dtOps

example := @dtOps.tree.d_run

/-- A call on the value of a data function parameter. -/
noncomputable def dtFn (f : Bool → Bool) (A : Bool → SPComp Bool) (b : Bool) : SPComp Bool :=
  A (f b)

derive_reduction dtFn (adv := A)

reflect_d dtFn.tree

link_timed dtFn

example := @dtFn.tree.d_run

/-- Two bound calls and the conjunction of their results. -/
noncomputable def dtSeq (A : Bool → SPComp Bool) (b : Bool) : SPComp Bool := do
  let x ← A b
  let y ← A (!x)
  return x && y

derive_reduction dtSeq (adv := A)

reflect_d dtSeq.tree

link_timed dtSeq

example := @dtSeq.tree.d_run

/-- A sample and a call on a pair. -/
noncomputable def dtPair (A : Bool × Bool → SPComp Bool) (b : Bool) : SPComp Bool := do
  let x ← SPComp.sample Bool
  A (b, x)

derive_reduction dtPair (adv := A)

reflect_d dtPair.tree

link_timed dtPair

example := @dtPair.tree.d_run

/-- A conditional on a parameter whose branches bind a call or sample. -/
noncomputable def dtBranch (A : Bool → SPComp Bool) (b : Bool) : SPComp Bool :=
  if b = true then do
    let x ← A b
    return !x
  else do
    let y ← SPComp.sample Bool
    A y

derive_reduction dtBranch (adv := A)

reflect_d dtBranch.tree

link_timed dtBranch

example := @dtBranch.tree.d_run

/-- A call, a sample, and a leaf that is a conditional between injections into a sum. -/
noncomputable def dtInj (A : Bool → SPComp Bool) (b : Bool) : SPComp (Bool ⊕ Bool) := do
  let x ← A b
  let y ← SPComp.sample Bool
  return if x = true then .inl y else .inr (!y)

derive_reduction dtInj (adv := A)

reflect_d dtInj.tree

link_timed dtInj

example := @dtInj.tree.d_run

/-- A `let` of a pair and a call on its second projection. -/
noncomputable def dtProj (A : Bool → SPComp Bool) (b : Bool) : SPComp Bool :=
  let p := (b, !b)
  A p.2

derive_reduction dtProj (adv := A)

reflect_d dtProj.tree

link_timed dtProj

example := @dtProj.tree.d_run

/-- A call, a sample, and a conditional between a call and a leaf on values of a data function
parameter. -/
noncomputable def dtNest (f : Bool → Bool) (A : Bool → SPComp Bool) (b : Bool) :
    SPComp Bool := do
  let x ← A b
  let y ← SPComp.sample Bool
  if y = true then A (f x) else return f y

derive_reduction dtNest (adv := A)

reflect_d dtNest.tree

link_timed dtNest

example := @dtNest.tree.d_run

/-- A call and a pair leaf. -/
noncomputable def dtLeafPair (A : Bool → SPComp Bool) (b : Bool) : SPComp (Bool × Bool) := do
  let x ← A b
  return (x, !x)

derive_reduction dtLeafPair (adv := A)

reflect_d dtLeafPair.tree

link_timed dtLeafPair

example := @dtLeafPair.tree.d_run

/-- A call on the conjunction of a list by a left fold. -/
noncomputable def dtFold (A : Bool → SPComp Bool) (l : List Bool) : SPComp Bool :=
  A (l.foldl (fun acc x => acc && x) true)

derive_reduction dtFold (adv := A)

reflect_d dtFold.tree

link_timed dtFold

example := @dtFold.tree.d_run

end CatCrypt.Tactics.LinkTimedDtTest
