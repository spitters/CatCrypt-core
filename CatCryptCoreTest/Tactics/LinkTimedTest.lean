/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.LinkTimed
public import CatCryptCoreTest.Complexity.D.ReflectCertTest
public import CatCryptCoreTest.Tactics.DeriveReductionTest

/-!
# Tests of `link_timed`

`link_timed` on the reflected trees of `derive_reduction`, with the allowances it computes:

* `smSampleRedOf` (a sample, the view and the adversary call): allowance `1`, the allowance of
  the hand derivation in `CatCryptCore.Complexity.D.TimedLinkTest`;
* `ckaPubRedOf` (the public tree without arguments bound, the view and the adversary call):
  allowance `2`;
* `smPubRedOf` (a sample, then as `ckaPubRedOf`): allowance `3`;
* `twoCall` (two bound adversary calls, a Boolean operation, a literal of `ℕ`): allowance `2`;
* `iteRed` (a conditional, a call and a leaf): allowance `0`;
* `letRed` (a data `let` of a Boolean operation, a sample, a call): allowance `2`.

The corollary `smSampleRedOf.tree.d_cost_le_costTree` discharges the adversary hypothesis by
`CTree.timedSim_costTree` and bounds the D cost through the time theorem of `derive_reduction`.

## Main definitions

* `iteRed`, `letRed`

## Main results

* `smSampleRedOf.tree.d_cost_le_costTree`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.LinkTimedTest

open CatCrypt.Core CatCrypt.Complexity.D CatCrypt.Complexity.D.Reflect CatCrypt.Crypto.Messaging
  CatCrypt.Tactics.DeriveReductionTest

link_timed smSampleRedOf

example := @smSampleRedOf.tree.d_timedSim

link_timed ckaPubRedOf

example := @ckaPubRedOf.tree.d_cost_le

reflect_d smPubRedOf.tree

link_timed smPubRedOf

example := @smPubRedOf.tree.d_timedSim

reflect_d twoCall.tree

link_timed twoCall

example := @twoCall.tree.d_timedSim

/-- Call the adversary on `b` when `b` holds, return `false` otherwise. -/
noncomputable def iteRed (A : Bool → SPComp Bool) (b : Bool) : SPComp Bool :=
  if b = true then A b else return false

derive_reduction iteRed (adv := A)

reflect_d iteRed.tree

link_timed iteRed

example := @iteRed.tree.d_timedSim

/-- Negate `b`, sample a bit and call the adversary on their conjunction. -/
noncomputable def letRed (A : Bool → SPComp Bool) (b : Bool) : SPComp Bool := do
  let c := !b
  let x ← SPComp.sample Bool
  A (c && x)

derive_reduction letRed (adv := A)

reflect_d letRed.tree

link_timed letRed

example := @letRed.tree.d_timedSim

/-- The D cost of the reflected sampling distinguisher with a D adversary `gA` of cost at most
`a`: the generated simulation at the costed tree of `gA` (`CTree.timedSim_costTree`) and the
time theorem of `derive_reduction`. -/
theorem smSampleRedOf.tree.d_cost_le_costTree (XF YF VF : FTy)
    (view : XF.den → YF.den → VF.den) (viewCost : XF.den → YF.den → ℕ)
    (gview : Val (.arr (.prod (.base XF) (.base YF)) (.base VF)))
    (FC : Val (.prod (.base XF) (.base YF)) → ℕ)
    (hg : ∀ v, gview v = stepN CTree.tick (FC v) (.ret (view v.1 v.2)))
    (hFC : ∀ v, FC v ≤ viewCost v.1 v.2) (gA : Val (.arr (.base VF) .bool)) {a tv : ℕ}
    (hA : ∀ v, (gA v).cost ≤ a) (hv : ∀ x y, viewCost x y ≤ tv) (y : YF.den) :
    (smSampleRedOf.tree.d XF YF VF).cost
        ((Env.nil.cons gview).cons gA |>.cons (τ := .base YF) y) ≤ 1 + (a + a + tv + 3) := by
  have hs := smSampleRedOf.tree.d_cost_le XF YF VF view viewCost gview FC hg hFC
    (fun v => (gA v).costTree.2) (fun v => (gA v).costTree.1) gA
    (fun v => CTree.timedSim_costTree (gA v)) y
  have ht := smSampleRedOf.tree.timeBound_timed view viewCost (fun v => (gA v).costTree.2)
    (fun v => (gA v).costTree.1) (T := a) (a := a) (tv := tv)
    (fun x => le_trans (Nat.le_add_left _ _) ((CTree.stepTime_costTree_le (gA x)).trans (hA x)))
    (fun x => le_trans (Nat.le_add_right _ _) ((CTree.stepTime_costTree_le (gA x)).trans (hA x)))
    hv y
  omega

end CatCrypt.Tactics.LinkTimedTest

end
