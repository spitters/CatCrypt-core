/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveCost
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Registered costs of polynomial operations

The costs of the Mathlib polynomial operations that reductions and simulators call, so that
`derive_timed` and `derive_reduction` price them, in the word model of the coefficient ring
(one unit per ring operation). A Mathlib polynomial is a finitely supported function with no
program, so its costs are registered by `timed_cost`, not derived:

* `Polynomial.eval x P` — Horner's rule, two operations per coefficient,
  `2 * (P.natDegree + 1)`;
* `Polynomial.coeff P` — the coefficient function `ℕ →₀ R` of `P`, which is the
  representation of `P`, `0`;
* `Finsupp.toFun f a` — one read of a finitely supported function at a point, `1`.

A coefficient read `P.coeff i` is the coercion `DFunLike.coe (Polynomial.coeff P) i`, which
unfolds to `Finsupp.toFun (Polynomial.coeff P) i` and so costs one read.

## Main results

* `Polynomial.eval.timedCost`, `Polynomial.coeff.timedCost`, `Finsupp.toFun.timedCost` —
  the registered costs
-/

@[expose] public section

set_option autoImplicit false

timed_cost Polynomial.eval := fun (R : Type _) [Semiring R] (_ : R) (P : Polynomial R) =>
  2 * (P.natDegree + 1)

timed_cost Polynomial.coeff := fun (R : Type _) [Semiring R] (_ : Polynomial R) => 0

timed_cost Finsupp.toFun := fun (α : Type _) (M : Type _) [Zero M] (_ : α →₀ M) (_ : α) => 1
