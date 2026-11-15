/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

/-!
# The simp sets `trace_nf` and `inner_nf`

The simp sets of the `trace_nf` tactic (`CatCryptCore.ForMathlib.Tactic.TraceNf`): `trace_nf`
distributes `Matrix.trace` over sums, differences, negations, scalar multiples and finite sums of
matrices and products over sums; `inner_nf` rewrites the vector forms `star x ⬝ᵥ (M *ᵥ y)` and
`‖WithLp.toLp 2 v‖ ^ 2` to `star x ⬝ᵥ (W *ᵥ y)` with `W` a right-associated product. The
lemmas are tagged in `CatCryptCore.ForMathlib.Tactic.TraceNf`.
-/

public section

/-- Linearity of `Matrix.trace` and distributivity of matrix products, for `trace_nf`. -/
register_simp_attr trace_nf

/-- Normalisation of sesquilinear vector forms `star x ⬝ᵥ (M *ᵥ y)` and squared Euclidean norms
`‖WithLp.toLp 2 v‖ ^ 2` to `star x ⬝ᵥ (W *ᵥ y)` with `W` right-associated, for `inner_nf`. -/
register_simp_attr inner_nf
