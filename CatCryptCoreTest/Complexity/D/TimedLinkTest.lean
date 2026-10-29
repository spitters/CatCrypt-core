/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.TimedLink
public import CatCryptCoreTest.Complexity.D.ReflectCertTest

/-!
# The per-construct rules on a reflected reduction tree

The rules of `CatCryptCore.Complexity.D.TimedLink`, composed by hand for the sampling
distinguisher `smSampleRedOf`: its costed tree of `derive_reduction` simulates the evaluation of
its reflected tree `smSampleRedOf.tree.d` at factor `1` and allowance `1`, with the view a D
function value of cost function `FC` bounded by the companion `viewCost`, and the adversary a D
function value simulated by the costed adversary at factor `1` without allowance. The derivation
is `TSim.sample` over `TSim.call` (the adversary), whose argument is `DSim.app` (the view) of
`DSim.pair` of two variables.

## Main results

* `smSampleRedOf.tree.d_timedSim`, `smSampleRedOf.tree.d_cost_le`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D.TimedLinkTest

open CatCrypt.Core CatCrypt.Complexity.D CatCrypt.Complexity.D.Reflect
  CatCrypt.Complexity.D.TimedLink CatCrypt.Crypto.Messaging

/-- The costed sampling distinguisher simulates the evaluation of its reflected tree at factor
`1` and allowance `1`. -/
theorem smSampleRedOf.tree.d_timedSim (XF YF VF : FTy)
    (view : XF.den → YF.den → VF.den) (viewCost : XF.den → YF.den → ℕ)
    (g : Val (.arr (.prod (.base XF) (.base YF)) (.base VF)))
    (FC : Val (.prod (.base XF) (.base YF)) → ℕ)
    (hg : ∀ v, g v = stepN CTree.tick (FC v) (.ret (view v.1 v.2)))
    (hFC : ∀ v, FC v ≤ viewCost v.1 v.2)
    (A : VF.den → SPTree.Timed Bool) (ACost : VF.den → ℕ) (gA : Val (.arr (.base VF) .bool))
    (hA : ∀ v, TimedSim (fun b w => w = b) 1 0 (ACost v, A v) (gA v)) (y : YF.den) :
    TimedSim (fun b w => w = b) 1 1
      (smSampleRedOf.tree.timed (X := XF.den) (Y := YF.den) (V := VF.den) view viewCost A
        ACost y)
      ((smSampleRedOf.tree.d XF YF VF).eval
        ((Env.nil.cons g).cons gA |>.cons (τ := .base YF) y)) := by
  unfold smSampleRedOf.tree.timed smSampleRedOf.tree.d
  change TSim (fun (b : Bool) (w : Val Ty.bool) => w = b) 1 1 _ _
    ((Env.nil.cons g).cons gA |>.cons (τ := .base YF) y)
  refine TSim.sample le_rfl XF (Equiv.refl _) fun b => ?_
  exact TSim.call (n₁ := 0) (n₂ := 0) (y := (ACost (view b y), A (view b y))) le_rfl
    (CEq.var _ _)
    (DSim.app (d := viewCost b y) le_rfl (CEq.var _ _) (DSim.pair (DSim.var _) (DSim.var _))
      (hg (b, y)) (hFC (b, y))) (hA (view b y))
    (show 1 + (1 + viewCost b y + (0 + 0)) + ACost (view b y) ≤
      1 + (ACost (view b y) + (1 + viewCost b y)) by omega)

/-- The D cost of the reflected sampling distinguisher, from the time theorem of its costed
tree: the allowance `1` plus `T + a + tv + 3`. -/
theorem smSampleRedOf.tree.d_cost_le (XF YF VF : FTy)
    (view : XF.den → YF.den → VF.den) (viewCost : XF.den → YF.den → ℕ)
    (g : Val (.arr (.prod (.base XF) (.base YF)) (.base VF)))
    (FC : Val (.prod (.base XF) (.base YF)) → ℕ)
    (hg : ∀ v, g v = stepN CTree.tick (FC v) (.ret (view v.1 v.2)))
    (hFC : ∀ v, FC v ≤ viewCost v.1 v.2)
    (A : VF.den → SPTree.Timed Bool) (ACost : VF.den → ℕ) (gA : Val (.arr (.base VF) .bool))
    (hA : ∀ v, TimedSim (fun b w => w = b) 1 0 (ACost v, A v) (gA v)) {T a tv : ℕ}
    (hAT : ∀ v, (A v).time ≤ T) (hAc : ∀ v, ACost v ≤ a) (hv : ∀ x y, viewCost x y ≤ tv)
    (y : YF.den) :
    (smSampleRedOf.tree.d XF YF VF).cost
        ((Env.nil.cons g).cons gA |>.cons (τ := .base YF) y) ≤ 1 + (T + a + tv + 3) := by
  have hs := TimedSim.cost_le
    (smSampleRedOf.tree.d_timedSim XF YF VF view viewCost g FC hg hFC A ACost gA hA y)
  have ht := smSampleRedOf.tree.timeBound_timed view viewCost A ACost hAT hAc hv y
  rw [Nat.one_mul] at hs
  exact hs.trans (Nat.add_le_add_left ht 1)

end CatCrypt.Complexity.D.TimedLinkTest
