/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Reflect
public import CatCryptCore.Crypto.Messaging.DoubleRatchet
public import CatCryptCore.Crypto.Messaging.KEMCKA

/-!
# `reflect_d` on the trees of `derive_reduction`

The computation trees that `derive_reduction` builds for two messaging reductions, reflected into
D with their denotation and cost theorems:

* `smSampleRedOf.tree`: a sample over a type parameter, the curried view primitive
  `view : X → Y → V` (a D function on pairs) and the adversary;
* `ckaPubRedOf.tree`: an unused `SPComp` binder (a binder of the theorems only), the public
  tree primitive `pubT : SPTree P` without arguments (a D function on `unit`), the curried view
  and the adversary.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D.ReflectCertTest

open CatCrypt.Core CatCrypt.Complexity.D CatCrypt.Crypto.Messaging

reflect_d smSampleRedOf.tree

example := @smSampleRedOf.tree.d_den

example := @smSampleRedOf.tree.d_cost

reflect_d ckaPubRedOf.tree

example := @ckaPubRedOf.tree.d_den

example := @ckaPubRedOf.tree.d_cost

/-- The cost of the reflected sampling distinguisher: the sample, the view of cost at most `tv`,
the adversary call of cost at most `a` and four steps. -/
example (XF YF VF : FTy) (viewCost : Val (.prod (.base XF) (.base YF)) → ℕ) (a tv : ℕ)
    (htv : ∀ v, viewCost v ≤ tv) (view : XF.den → YF.den → VF.den)
    (g : Val (.arr (.prod (.base XF) (.base YF)) (.base VF)))
    (hg : ∀ v, g v = stepN CTree.tick (viewCost v) (.ret (view v.1 v.2)))
    (A : VF.den → SPTree Bool) (gA : Val (.arr (.base VF) .bool)) (hA : ∀ v, (gA v).cost ≤ a)
    (y : YF.den) :
    (smSampleRedOf.tree.d XF YF VF).cost ((Env.nil.cons g).cons gA |>.cons (τ := .base YF) y) ≤
      tv + a + 4 := by
  refine (smSampleRedOf.tree.d_cost XF YF VF viewCost a view g hg A gA hA y).trans (le_trans
    (Nat.add_le_add_left (Nat.add_le_add_left
      (Finset.sup_le (a := tv + a + 2) fun v _ => ?_) 1) 1) (by omega))
  exact le_trans (Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_left
    (Nat.add_le_add_right (htv _) 1) _) _) _) (by omega)

end CatCrypt.Complexity.D.ReflectCertTest
