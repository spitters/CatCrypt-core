/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Refinement.WRPConvAttr
public import CatCryptCore.Refinement.RRelWRP
public import RefinementWP.Step

/-!
# Registered refinements as goals of `wrp_leaf`

A registered refinement `RefinesCall c a γ eps pre R` is the refinement
`Refines ⊤ γ eps c a R` under the hypothesis `pre`. When `pre` is a judgement `J` with a proved
conversion `J ↔ Refines ⊤ γ eps c a R`, the refinement follows from `pre` along the conversion.
This module adds the arm of `wrp_leaf` that reduces a goal `RefinesCall c a γ eps pre R` to the
refinement under `pre` and closes it by `pre`, directly or after the conversions of the simp set
`wrp_conv` have rewritten the refinement into a judgement. Hypotheses of a conversion are
discharged by assumption.

The conversions of the `RRelPT` forms of `CatCryptCore.Refinement.RRelWRP` are tagged here; a
module that proves a conversion tags it `@[wrp_conv ←]`.

## Main results

* The `wrp_leaf` arm at a goal `RefinesCall c a γ eps pre R`.

The example proves a registered refinement of a guarded update by the arm from the forward
simulation of a step relation, along `corresRel_iff_refines` with its hypothesis discharged by
assumption.
-/

@[expose] public section

set_option autoImplicit false

attribute [wrp_conv ←] CatCrypt.Refinement.WRP.rrelPT_optProg_iff_refines
  CatCrypt.Refinement.WRP.guardedRRelPT_iff_refines CatCrypt.Refinement.WRP.corresRel_iff_refines

/-- The arm of `wrp_leaf` at a registered refinement `RefinesCall c a γ eps pre R`: the goal is
the refinement under the hypothesis `pre`, which closes it, directly or after the conversions of
`wrp_conv` have rewritten the refinement into the judgement `pre`. -/
macro_rules
  | `(tactic| wrp_leaf) =>
    `(tactic| (refine RefinementWP.RefinesCall.mk fun hpre => ?_
               first
                 | exact hpre
                 | (simp (disch := assumption) only [wrp_conv]; exact hpre)))

namespace CatCrypt.Refinement.WRPCallGoal.Example

open RefinementWP Lean.Order Std.WP

open Classical in
/-- The forward simulation of a step relation `T` registers a refinement of the guarded update,
for a concrete program `c` whose transformer at `⊥` is the angelic transformer of `T`. -/
example {σ A CE : Type} [Assertion CE] {SR : σ → A → Prop}
    {P : A → Prop} {fa : A → A} {T : σ → σ → Prop} {CProg : Type}
    [WP CProg Unit (σ → Prop) CE] (c : CProg)
    (hc : ∀ (Q : Unit → σ → Prop) (s : σ), wp c Q bot s ↔ ∃ s', T s s' ∧ Q () s') :
    RefinesCall c (optD fun a => if P a then some ((), fa a) else none)
      (Concretization.ofStateRel SR) (fun _ : Unit => (bot : CE))
      (∀ s a, SR s a → P a → ∃ s', T s s' ∧ SR s' (fa a)) (fun _ _ _ => True) := by
  wrp_leaf

end CatCrypt.Refinement.WRPCallGoal.Example

end
