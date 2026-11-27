/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

/-!
# The simp set `wrp_conv` of conversions into refinements

A conversion is a theorem `J ↔ Refines P γ eps c a R` that states a judgement `J` as a refinement.
It is tagged `@[wrp_conv ←]`, so that the simp set rewrites a refinement into the judgement it
converts. The arm of `wrp_leaf` in `CatCryptCore.Refinement.WRPCallGoal` uses the set at a goal
`RefinesCall c a γ eps pre R` whose condition `pre` is the judgement. The attribute is declared in
this module and used in the modules that import it.

## Main definitions

* `wrp_conv`: the simp set of conversions into refinements, tagged in reverse.
-/

public section

/-- Conversions `J ↔ Refines P γ eps c a R` of a judgement into a refinement, tagged in reverse
(`@[wrp_conv ←]`) so that the set rewrites the refinement into the judgement. -/
register_simp_attr wrp_conv
