/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.LinkTimed

/-!
# `link_timed` at the eliminator of a structural recursion

`reflect_d` reflects a structural recursion over a Lean inductive type as the eliminator `fold`;
`derive_timed` charges its call by the cost companion `f.timedCost`, defined by the same
recursion. `link_timed` links the two at the fold (`TimedLink.DSim.foldEnc`): the induction over
the type takes at each constructor the walk of its step, whose recursive calls are the induction
hypotheses at the children (`DSim.appRec`), and closes the node condition by the equation of the
companion at the constructor (`DSim.node`). Fresh definitions:

* `Duo` (two children): `Duo.weight` under the tree `weighOf`;
* `Pick` (a function `Bool → Pick` of children, a fixed argument): `Pick.follow` under `followOf`;
* `Trio` (three children, a conditional at the leaves): `Trio.total` under the reduction
  `totalRed` with a sample and an adversary call.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D.LinkTimedFoldTest

open CatCrypt.Core

/-! ## Two children -/

/-- Binary trees of bytes. -/
inductive Duo where
  | tip
  | fork (l : Duo) (x : BitVec 8) (r : Duo)

/-- The sum of the bytes of a tree. -/
def Duo.weight : Duo → BitVec 8
  | .tip => 0
  | .fork l x r => x + (l.weight + r.weight)

/-- The weight as a tree. -/
def weighOf (t : Duo) : SPTree (BitVec 8) := .ret t.weight

derive_timed weighOf

reflect_d weighOf

link_timed weighOf

/-- The costed form charges the call by the companion of the recursion. -/
example (t : Duo) : weighOf.timed t = (1 + Duo.weight.timedCost t, .ret t.weight) := rfl

example (t : Duo) :
    TimedSim (fun a w => a = w) 1 0 (weighOf.timed t) (weighOf.d.eval (Env.nil.cons t.dEnc)) :=
  weighOf.d_timedSim t

/-- The D cost of the reflected recursion is the time of the costed form. -/
example (t : Duo) :
    weighOf.d.cost (Env.nil.cons t.dEnc) ≤ 0 + 1 * SPTree.Timed.stepTime (weighOf.timed t) :=
  weighOf.d_cost_le t

/-! ## A function of children -/

/-- Trees whose node holds a byte and a continuation on a Boolean. -/
inductive Pick where
  | stop (o : BitVec 8)
  | step (q : BitVec 8) (k : Bool → Pick)

/-- The XOR of the bytes along the path of the answers `b`. -/
def Pick.follow (b : Bool) : Pick → BitVec 8
  | .stop o => o
  | .step q k => q ^^^ (k b).follow b

/-- The path value as a tree. -/
def followOf (b : Bool) (t : Pick) : SPTree (BitVec 8) := .ret (t.follow b)

derive_timed followOf

reflect_d followOf

link_timed followOf

example (b : Bool) (t : Pick) :
    TimedSim (fun a w => a = w) 1 0 (followOf.timed b t)
      (followOf.d.eval ((Env.nil.cons (τ := .bool) b).cons t.dEnc)) :=
  followOf.d_timedSim b t

/-! ## Three children, in a reduction -/

/-- Ternary trees with a Boolean at the leaves. -/
inductive Trio where
  | leaf (b : Bool)
  | node (a : Trio) (x : BitVec 4) (b : Trio) (c : Trio)

/-- The sum of the words and of the true leaves. -/
def Trio.total : Trio → BitVec 4
  | .leaf b => if b then 1 else 0
  | .node a x b c => x + a.total + b.total + c.total

/-- A reduction: sample a word and call the adversary on its sum with the total of `t`. -/
noncomputable def totalRed (A : BitVec 4 → SPComp Bool) (t : Trio) : SPComp Bool := do
  let y ← SPComp.sample (BitVec 4)
  A (y + t.total)

derive_reduction totalRed (adv := A)

reflect_d totalRed.tree

link_timed totalRed

example := @totalRed.tree.d_timedSim

example := @totalRed.tree.d_cost_le

end CatCrypt.Complexity.D.LinkTimedFoldTest
