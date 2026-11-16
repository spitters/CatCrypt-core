/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import CatCryptCore.ForMathlib.Tactic.PositivityStar

/-!
# Tests for the `positivity` extensions of star-ordered rings and the CFC

One goal per clause of the grammar of the positive cone: star squares, congruences, squares and
even powers of self-adjoint elements, star projections and their complements, sums, scalars and
the functions of the continuous functional calculus.
-/

set_option autoImplicit false

section StarOrderedRing

variable {R : Type*} [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

example (c : R) : 0 ≤ star c * c := by positivity
example (c : R) : 0 ≤ c * star c := by positivity
example (a c : R) (ha : 0 ≤ a) : 0 ≤ star c * a * c := by positivity
example (a c : R) (ha : 0 ≤ a) : 0 ≤ c * a * star c := by positivity
example (a b c : R) (ha : 0 ≤ a) : 0 ≤ star c * (star b * a * b) * c + star b * b := by
  positivity
example (p : R) (hp : IsStarProjection p) : 0 ≤ p := by positivity
example (p : R) (hp : IsStarProjection p) : 0 ≤ 1 - p := by positivity
example (p : R) (hp : IsStarProjection p) : 0 ≤ 1 - (1 - p) := by positivity
example (p c : R) (hp : IsStarProjection p) : 0 ≤ star c * (1 - p) * c := by positivity
example (p q : R) (hp : IsStarProjection p) (hq : IsStarProjection q) : 0 ≤ p * q * p := by
  positivity
example (a b : R) (h : a ≤ b) : 0 ≤ b - a := by positivity
example (a : R) (ha : IsSelfAdjoint a) : 0 ≤ a * a := by positivity
example (a c : R) (ha : 0 ≤ a) (hc : IsSelfAdjoint c) : 0 ≤ c * a * c := by positivity
example (a : R) (ha : IsSelfAdjoint a) : 0 ≤ a ^ 4 := by positivity

/-- The congruence `(1 - F)ᴴ M (1 - F)` of `Quantum/PowersStormer.lean`. -/
example (F M : R) (hM : 0 ≤ M) : 0 ≤ star (1 - F) * M * (1 - F) := by positivity

example (a c : R) (ha : 0 ≤ a) : 0 ≤ (2 : ℕ) • (star c * a * c) := by positivity
example {ι : Type*} (s : Finset ι) (c : ι → R) : 0 ≤ ∑ i ∈ s, star (c i) * c i := by
  positivity

end StarOrderedRing

section Commutative

example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x ^ 3 + x * x := by positivity

open scoped ComplexOrder in
example (z : ℂ) : 0 ≤ star z * z := by positivity

end Commutative

section CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

example (a : A) : 0 ≤ CFC.sqrt a := by positivity
example (a : A) : 0 ≤ CFC.abs a := by positivity
example (a : A) : 0 ≤ a⁺ := by positivity
example (a : A) : 0 ≤ a⁻ := by positivity
example (a : A) (y : ℝ) : 0 ≤ a ^ y := by positivity
example (a : A) (y : NNReal) : 0 ≤ a ^ y := by positivity
example (a : A) (ha : 0 ≤ a) : 0 ≤ a ^ 3 := by positivity
example (a : A) : 0 ≤ cfc (fun x : ℝ => x ^ 2) a := by positivity
example (a : A) : 0 ≤ cfc Real.sqrt a := by positivity
example (a : A) : 0 ≤ cfc (fun x : ℝ => |x| + 1) a := by positivity
example (a c : A) : 0 ≤ star c * CFC.sqrt a * c := by positivity
example (a : A) (r : ℝ) (hr : 0 ≤ r) : 0 ≤ r • CFC.sqrt a := by positivity

end CStarAlgebra
