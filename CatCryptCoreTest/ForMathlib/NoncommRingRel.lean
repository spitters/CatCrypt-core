/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import CatCryptCore.ForMathlib.Tactic.NoncommRingRel
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Basic.Complex.Basic

/-!
# Tests for the `noncomm_ring_rel` tactic

Ring identities modulo word relations, restated over an abstract `Ring R`, `StarRing R` or a
square complex matrix ring from the quantum code in which they are proved by `rw [h]` followed
by `noncomm_ring`, or by hand chains of `mul_assoc`, `← mul_assoc` and the relation. The
partial-isometry and orthogonal-projection goals are not closed by `noncomm_ring [h]`.
-/

set_option autoImplicit false

section Ring

variable {R : Type*} [Ring R]

/-- An idempotent inside a longer product (needs the right-associated form of `P * P = P`). -/
example (P X Y : R) (hP : P * P = P) : X * P * P * Y = X * P * Y := by
  noncomm_ring_rel [hP]

/-- `(1 - F)² = 2 (1 - F)` for an involution (`PowersStormer.lean`). -/
example (F : R) (hF : F * F = 1) : (1 - F) ^ 2 = 2 * (1 - F) := by
  noncomm_ring_rel [hF]

/-- A relation given with its larger side on the right is reoriented. -/
example (P A : R) (hP : P = P * P) : A * P * P * P = A * P := by
  noncomm_ring_rel [hP]

/-- Quantified relations: families of involutions commuting with each other. -/
example (X Y : Fin 2 → R) (hX : ∀ x, X x * X x = 1) (hXY : ∀ x y, Y y * X x = X x * Y y) :
    Y 0 * X 1 * Y 1 * X 1 = Y 0 * Y 1 := by
  noncomm_ring_rel [hX, hXY]

/-- The critical-pair report on a confluent system. -/
example (P A : R) (hP : P * P = P) : A * P * P = A * P := by
  noncomm_ring_rel? [hP]

/-- The critical-pair report on a one-sided inverse. -/
example (X Y : R) (hXY : X * Y = 1) : Y * X * Y * X = Y * X := by
  noncomm_ring_rel? [hXY]

/-- The critical-pair report on a system that is not confluent: the overlap `X Y X` has the
reducts `Y X` and `X X`. -/
example (X Y : R) (h1 : X * Y = Y) (h2 : Y * X = X) : X * Y * X = X := by
  noncomm_ring_rel? [h1, h2]

end Ring

section StarRing

/-- The complement of a partial-isometry projection, `(1 - W* W)* (1 - W* W) = 1 - W* W`
(`PolarDecomposition.lean`); the relation `W* W W* = W*` comes from the star closure. -/
example {S : Type*} [Ring S] [StarRing S] (W : S) (h : W * star W * W = W) :
    star (1 - star W * W) * (1 - star W * W) = 1 - star W * W := by
  noncomm_ring_rel [h]

/-- Orthogonal self-adjoint projections: `Q P = 0` comes from `P Q = 0` by the star closure
(`Uncomputation.lean`). -/
example {S : Type*} [Ring S] [StarRing S] (P Q : S) (hPs : star P = P) (hQs : star Q = Q)
    (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : P * Q = 0) :
    (P + Q) * (P + Q) = P + Q := by
  noncomm_ring_rel [hPs, hQs, hP, hQ, hPQ]

end StarRing

section TiltedCHSH

/-- Bamps–Pironio sum of squares for the tilted CHSH operator (`TiltedCHSH.lean`): involutions,
commutation and symbolic scalars, with the scalar relation `β² = 8 + 2α²`. -/
example {K S : Type*} [Field K] [CharZero K] [Ring S] [Algebra K S] (X Y : Fin 2 → S)
    (α β : K) (hβ : β * β = 8 + 2 * α ^ 2) (hX : ∀ x, X x * X x = 1) (hY : ∀ y, Y y * Y y = 1)
    (hXY : ∀ x y, Y y * X x = X x * Y y) :
    (2 * β) • (β • (1 : S) - (α • X 0 +
        (X 0 * Y 0 + X 0 * Y 1 + X 1 * Y 0 - X 1 * Y 1))) =
      (2 • X 0 - (β / 2) • (Y 0 + Y 1) +
          (α / 2) • (X 0 * (Y 0 + Y 1) - X 1 * (Y 0 - Y 1))) ^ 2 +
        (2 • X 1 - (β / 2) • (Y 0 - Y 1) +
          (α / 2) • (X 0 * (Y 0 - Y 1) - X 1 * (Y 0 + Y 1))) ^ 2 := by
  noncomm_ring_rel [hX, hY, hXY, hβ]

end TiltedCHSH

section Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Conjugation by an isometry matrix is multiplicative. -/
example (U A B : Matrix n n ℂ) (hU : U.conjTranspose * U = 1) :
    (U * A * U.conjTranspose) * (U * B * U.conjTranspose) = U * (A * B) * U.conjTranspose := by
  noncomm_ring_rel [hU]

/-- A partial isometry `W Wᴴ W = W` gives the idempotent `Wᴴ W` (`PolarDecomposition.lean`). -/
example (W : Matrix n n ℂ) (h : W * W.conjTranspose * W = W) :
    (W.conjTranspose * W) * (W.conjTranspose * W) = W.conjTranspose * W := by
  noncomm_ring_rel [h]

/-- The complement of `Wᴴ W` for a partial isometry, with `ᴴ` pushed through the difference. -/
example (W : Matrix n n ℂ) (h : W * W.conjTranspose * W = W) :
    (1 - W.conjTranspose * W).conjTranspose * (1 - W.conjTranspose * W) =
      1 - W.conjTranspose * W := by
  noncomm_ring_rel [h]

/-- An involution with a complex scalar. -/
example (X : Matrix n n ℂ) (c : ℂ) (hX : X * X = 1) :
    (c • X) * (c • X) = (c * c) • (1 : Matrix n n ℂ) := by
  noncomm_ring_rel [hX]

end Matrix
