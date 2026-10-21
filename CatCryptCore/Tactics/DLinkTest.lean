/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DLink
public import CatCryptCore.Crypto.Messaging.DoubleRatchet
public import CatCryptCore.Crypto.Messaging.KEMCKA

/-!
# Tests of the link between certificates and D

Derivations of `TimedSim` between the costed trees of `derive_reduction` and the evaluation of
the D-terms that `reflect_d` gives for the same reductions, assembled from the comparison lemmas
of `CatCryptCore.Tactics.DLink`:

* `smSampleRedOf.tree.d_sim`: a `letE` over a sample, a β-step, the application of the view
  primitive (an exact cost derivation) and the adversary call;
* `ckaPubRedOf.tree.d_sim`: a `letE` over the call of a computation primitive against a costed
  bind, then the same steps;
* `smSampleRedOf.timeReduction`: the sampling distinguisher as a `TimeReduction` through
  `TimeReduction.ofOpen`, the view closed by a realizing term (`Tm.closeOuter`), the time from
  `smSampleRedOf.tree.timeBound_timed` through `smSampleRedOf.tree.d_sim`, the meaning from
  `smSampleRedOf.d_den` through `Tm.run_eval_eraseArr`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D.DLinkTest

open CatCrypt.Core CatCrypt.Complexity.D CatCrypt.Complexity.D.Reflect CatCrypt.Crypto.Messaging

reflect_d smSampleRedOf

/-- The costed sampling distinguisher, with the adversary the costed tree of a D function value
`gA` and the view priced by the cost function `vc` of a D function value, simulates the
evaluation of the reflected distinguisher at factor `1` and allowance `1`. -/
theorem smSampleRedOf.tree.d_sim (XF YF VF : FTy)
    (vc : Val (.prod (.base XF) (.base YF)) → ℕ) (view : XF.den → YF.den → VF.den)
    (g : Val (.arr (.prod (.base XF) (.base YF)) (.base VF)))
    (hg : ∀ v, g v = stepN CTree.tick (vc v) (.ret (view v.1 v.2)))
    (gA : Val (.arr (.base VF) .bool)) (y : YF.den) :
    TimedSim (· = ·) 1 1
      (smSampleRedOf.tree.timed view (fun x y => vc (x, y)) (fun w => (gA w).costTree.2)
        (fun w => (gA w).costTree.1) y)
      ((smSampleRedOf.d XF YF VF).eval (((Env.nil.cons g).cons gA).cons y)) := by
  unfold smSampleRedOf.tree.timed smSampleRedOf.d
  refine TimedSim.eval_letE_sample (R := fun (a : Bool) (v : Val Ty.bool) => a = v) (f := XF)
    le_rfl (Equiv.refl XF.den) fun b => ?_
  refine TimedSim.tick (m := 1 + 1 * (1 + ((gA (view b y)).costTree.1 + (1 + vc (b, y)))) - 1)
    (c' := 0) (TimedSim.eval_app_ceq (n := _) (CEq.var _ _)
    (CEq.app (CEq.var _ _) (CEq.pair (CEq.var _ _) (CEq.var _ _)) (hg (b, y)))
    (TimedSim.costTree le_rfl (gA (view b y))) ?_) ?_
  · omega
  · beta_reduce
    omega

/-- The sampling distinguisher as a time reduction, at a view realized by the closed term `pv`
whose closure costs `vc v ≤ tv` per call: the time is the evaluation of `pv`, its β-step, and
the D cost bound obtained from the certificate's time theorem through `d_sim`. -/
noncomputable def smSampleRedOf.timeReduction (O : CTree.Oracle) (XF YF VF : FTy)
    (view : XF.den → YF.den → VF.den) (pv : Tm [] (.arr (.prod (.base XF) (.base YF)) (.base VF)))
    {ev : ℕ} {gv : Val (.arr (.prod (.base XF) (.base YF)) (.base VF))} (hpv : pv.EvalsTo ev gv)
    (vc : Val (.prod (.base XF) (.base YF)) → ℕ)
    (hg : ∀ v, gv v = stepN CTree.tick (vc v) (.ret (view v.1 v.2))) (tv : ℕ)
    (htv : ∀ v, vc v ≤ tv) : TimeReduction O (.base VF) .bool (.base YF) .bool :=
  TimeReduction.ofOpen O trivial trivial
    (Tm.closeOuter (Γ := [.base YF, .arr (.base VF) .bool]) pv (smSampleRedOf.d XF YF VF))
    (fun A u => smSampleRedOf view A u) (fun k => ev + 1 + (1 + 1 * (k + k + tv + 3)))
    (fun _ _ h => by simp only; omega)
    (fun g k hk u => by
      rw [Tm.cost_closeOuter _ _ _ hpv, Env.comp_rot_cons, Env.comp_rot_cons, Env.comp_rot_nil]
      have hs := (smSampleRedOf.tree.d_sim XF YF VF vc view gv hg g u).cost_le
      have ht := smSampleRedOf.tree.timeBound_timed view (fun x y => vc (x, y))
        (fun w => (g w).costTree.2) (fun w => (g w).costTree.1) (T := k) (a := k) (tv := tv)
        (fun x => le_trans (Nat.le_add_left _ _) ((CTree.stepTime_costTree_le (g x)).trans (hk x)))
        (fun x => le_trans (Nat.le_add_right _ _)
          ((CTree.stepTime_costTree_le (g x)).trans (hk x)))
        (fun x y => htv (x, y)) u
      exact Nat.add_le_add_left (hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 1 ht) 1)) _)
    (fun A g hA u => by
      rw [Tm.run_eval_closeOuter _ _ _ _ hpv, Env.comp_rot_cons, Env.comp_rot_cons,
        Env.comp_rot_nil, Tm.run_eval_eraseArr O (smSampleRedOf.d XF YF VF) trivial (by simp [Ty.FOArr, Ty.FO]),
        Env.eraseArr_cons, Env.eraseArr_cons, Env.eraseArr_cons, Env.eraseArr_nil]
      refine smSampleRedOf.d_den XF YF VF O view _ (fun v => ?_) A _ (fun v => ?_) u
      · rw [Val.eraseArr_arr]
        exact (congrArg CTree.erase (hg v)).trans (CTree.erase_stepN_tick _ _)
      · rw [Val.eraseArr_arr]
        show CTree.run O (g v).erase = _
        rw [CTree.run_erase, hA])

reflect_d ckaPubRedOf

/-- The costed distinguisher with a public computation, with the public computation and the
adversary the costed trees of D function values `gp` and `gA`, simulates the evaluation of the
reflected distinguisher at factor `1`; the allowance holds the step cost in front of the costed
tree of `gp`. -/
theorem ckaPubRedOf.tree.d_sim (YF PF VF : FTy) (gp : Val (.arr (.base .unit) (.base PF)))
    (vc : Val (.prod (.base PF) (.base YF)) → ℕ) (view : PF.den → YF.den → VF.den)
    (g : Val (.arr (.prod (.base PF) (.base YF)) (.base VF)))
    (hg : ∀ v, g v = stepN CTree.tick (vc v) (.ret (view v.1 v.2)))
    (gA : Val (.arr (.base VF) .bool)) (y : YF.den) :
    TimedSim (· = ·) 1 (1 + 1 + 1 * (gp ()).costTree.1)
      (ckaPubRedOf.tree.timed ((gp ()).run CTree.Oracle.zero) view (fun x y => vc (x, y))
        (fun w => (gA w).costTree.2) (fun w => (gA w).costTree.1) y (gp ()).costTree.2)
      ((ckaPubRedOf.d YF PF VF).eval ((((Env.nil.cons gp).cons g).cons gA).cons y)) := by
  unfold ckaPubRedOf.tree.timed ckaPubRedOf.d
  refine TimedSim.eval_letE_bind (S := fun (a : Bool) (v : Val Ty.bool) => a = v)
    (R := fun (a : PF.den) (v : Val (.base PF)) => a = v) (m := 1)
    (TimedSim.eval_app_ceq (m := 0) (CEq.var _ _) (CEq.lit _ _ _)
      (TimedSim.costTree le_rfl (gp ())) (by omega)) fun x v hxv => ?_
  subst hxv
  refine TimedSim.tick (m := 1 + 1 * (1 + ((gA (view x y)).costTree.1 + (1 + vc (x, y)))) - 1)
    (c' := 0) (TimedSim.eval_app_ceq (n := _) (CEq.var _ _)
    (CEq.app (CEq.var _ _) (CEq.pair (CEq.var _ _) (CEq.var _ _)) (hg (x, y)))
    (TimedSim.costTree le_rfl (gA (view x y))) ?_) ?_
  · omega
  · beta_reduce
    omega

end CatCrypt.Complexity.D.DLinkTest
