/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveCost
import Mathlib.Tactic.TypeStar

/-!
# Registered costs of polynomial operations

The costs of the Mathlib polynomial operations that reductions and simulators call, so that
`derive_timed` and `derive_reduction` price them, in the word model of the coefficient ring
(one unit per ring operation). A Mathlib polynomial is a finitely supported function with no
program, so its costs are registered by `timed_cost`, not derived:

* `Polynomial.eval x P` — Horner's rule, two operations per coefficient,
  `2 * (P.natDegree + 1)`;
* `AddMonoidAlgebra.coeff P` — the coefficient function `ℕ →₀ R` of a polynomial `P`
  (`Polynomial R` is `AddMonoidAlgebra R ℕ`), which is the representation of `P`, `0`;
* `Finsupp.toFun f a` — one read of a finitely supported function at a point, `1`;
* `Finsupp.single a b` — the finitely supported function with the one value `b` at `a`, the
  representation of a polynomial term (`Polynomial.C b`, `Polynomial.monomial n b`,
  `Polynomial.X` unfold to it): one coefficient written, `1`. Its Mathlib definition computes
  its support by deciding `b = 0` with `Classical.decEq`, a decision that `derive_timed` refuses
  (rule (n) of `CatCryptCore.Tactics.DeriveTimed`); on a coefficient array the term is one
  write, which decides nothing;
* `AddMonoidAlgebra.mul' x y` — the product of polynomials, which has no exposed body: the
  schoolbook product, one multiplication and one addition of coefficients for each pair of
  terms, `2 * (|x| * |y|)` for the numbers of terms `|x|`, `|y|` (the cardinalities of the
  supports);
* `Finsupp.zipWith f _ g₁ g₂` — the pointwise combination by `f`, to which a sum of polynomials
  unfolds (with `f` the addition of coefficients): one merge of the two supports, which at each
  term costs one unit and `fCost`, the cost companion of `f`, at the two values there. The sum
  over each support is charged, so a common term is charged twice and the cost is linear in
  `|g₁| + |g₂|`. Its Mathlib definition forms the union of the supports with `Classical.decEq`
  on the keys, which rule (n) refuses; the merge of two coefficient arrays does not. A classical
  decision inside `f` is still refused, as `fCost` is derived from `f`.

The addition instance of `AddMonoidAlgebra R M` has no constant of its own for the sum (it is
`Finsupp.zipWith` transported along `AddMonoidAlgebra.coeffEquiv`), so the cost of the sum is
registered at `Finsupp.zipWith`.

A coefficient read `P.coeff i` is the coercion `DFunLike.coe (AddMonoidAlgebra.coeff P) i`, which
unfolds to `Finsupp.toFun (AddMonoidAlgebra.coeff P) i` and so costs one read.

## Main results

* `Polynomial.eval.timedCost`, `AddMonoidAlgebra.coeff.timedCost`, `Finsupp.toFun.timedCost`,
  `Finsupp.single.timedCost`, `AddMonoidAlgebra.mul'.timedCost`, `Finsupp.zipWith.timedCost` —
  the registered costs
* `Finsupp.single.timedCost_eq` — a polynomial term costs one unit
-/

@[expose] public section

set_option autoImplicit false

timed_cost Polynomial.eval := fun (R : Type _) [Semiring R] (_ : R) (P : Polynomial R) =>
  2 * (P.natDegree + 1)

timed_cost AddMonoidAlgebra.coeff :=
  fun (R : Type _) (M : Type _) [Semiring R] (_ : AddMonoidAlgebra R M) => 0

timed_cost Finsupp.toFun := fun (α : Type _) (M : Type _) [Zero M] (_ : α →₀ M) (_ : α) => 1

timed_cost Finsupp.single := fun (α : Type _) (M : Type _) [Zero M] (_ : α) (_ : M) => 1

timed_cost AddMonoidAlgebra.mul' := fun (R : Type _) (M : Type _) [Semiring R] [Add M]
  (x y : AddMonoidAlgebra R M) => 2 * (x.coeff.support.card * y.coeff.support.card)

timed_cost Finsupp.zipWith := fun (α M N O : Type _) [Zero M] [Zero N] [Zero O]
  (f : M → N → O) (fCost : M → N → ℕ) (_ : f 0 0 = 0) (g₁ : α →₀ M) (g₂ : α →₀ N) =>
  ∑ i ∈ g₁.support, (1 + fCost (g₁ i) (g₂ i)) + ∑ i ∈ g₂.support, (1 + fCost (g₁ i) (g₂ i))

/-- A polynomial term costs the write of one coefficient. -/
theorem Finsupp.single.timedCost_eq (α M : Type*) [Zero M] (a : α) (b : M) :
    Finsupp.single.timedCost α M a b = 1 := by
  simp [Finsupp.single.timedCost]
