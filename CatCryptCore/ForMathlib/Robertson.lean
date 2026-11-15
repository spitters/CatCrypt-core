/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric

@[expose] public section

set_option autoImplicit false

/-!
# The Robertson uncertainty relation

For symmetric (Hermitian) operators `A`, `B` on a complex inner product space and a
vector `ψ`, the variances `Var_ψ(A) = ‖(A - ⟨A⟩_ψ) ψ‖²` satisfy
`Var_ψ(A) · Var_ψ(B) ≥ 1/4 |⟨ψ, [A, B] ψ⟩|²`, where `⟨A⟩_ψ = Re ⟨ψ, A ψ⟩`. For a unit
vector `ψ` this is the Robertson uncertainty relation; the inequality holds for every
vector and, more generally, for deviations from arbitrary real reference values.

## Main definitions

* `LinearMap.expectation A ψ` — `Re ⟨ψ, A ψ⟩`.
* `LinearMap.variance A ψ` — `‖A ψ - ⟨A⟩_ψ ψ‖²`.

## Main results

* `LinearMap.IsSymmetric.inner_commutator_eq` — `⟨ψ, [A, B] ψ⟩ = ⟨a, b⟩ - ⟨b, a⟩` for the
  deviations `a = A ψ - α ψ`, `b = B ψ - β ψ` and real `α`, `β`.
* `LinearMap.IsSymmetric.norm_inner_commutator_le` — `|⟨ψ, [A, B] ψ⟩| ≤ 2 ‖a‖ ‖b‖`.
* `LinearMap.IsSymmetric.robertson` — `1/4 |⟨ψ, [A, B] ψ⟩|² ≤ Var_ψ(A) · Var_ψ(B)`.

## References

* Robertson, *The uncertainty principle*, Phys. Rev. 34 (1929)
-/

open scoped InnerProductSpace

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The expectation value `Re ⟨ψ, A ψ⟩` of an operator in a vector. -/
noncomputable def expectation (A : E →ₗ[ℂ] E) (ψ : E) : ℝ :=
  (⟪ψ, A ψ⟫_ℂ).re

/-- The variance `‖A ψ - ⟨A⟩_ψ ψ‖²` of an operator in a vector. -/
noncomputable def variance (A : E →ₗ[ℂ] E) (ψ : E) : ℝ :=
  ‖A ψ - (expectation A ψ : ℂ) • ψ‖ ^ 2

namespace IsSymmetric

variable {A B : E →ₗ[ℂ] E}

/-- The commutator expectation in terms of the deviations from real reference values:
`⟨ψ, (A B - B A) ψ⟩ = ⟨a, b⟩ - ⟨b, a⟩` with `a = A ψ - α ψ` and `b = B ψ - β ψ`. -/
theorem inner_commutator_eq (hA : A.IsSymmetric) (hB : B.IsSymmetric) (ψ : E) (α β : ℝ) :
    ⟪ψ, A (B ψ)⟫_ℂ - ⟪ψ, B (A ψ)⟫_ℂ =
      ⟪A ψ - (α : ℂ) • ψ, B ψ - (β : ℂ) • ψ⟫_ℂ -
        ⟪B ψ - (β : ℂ) • ψ, A ψ - (α : ℂ) • ψ⟫_ℂ := by
  have h1 : ⟪ψ, A (B ψ)⟫_ℂ = ⟪A ψ, B ψ⟫_ℂ := (hA ψ (B ψ)).symm
  have h2 : ⟪ψ, B (A ψ)⟫_ℂ = ⟪B ψ, A ψ⟫_ℂ := (hB ψ (A ψ)).symm
  have hAψ : ⟪A ψ, ψ⟫_ℂ = ⟪ψ, A ψ⟫_ℂ := hA ψ ψ
  have hBψ : ⟪B ψ, ψ⟫_ℂ = ⟪ψ, B ψ⟫_ℂ := hB ψ ψ
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, h1, h2, hAψ, hBψ]
  ring

/-- `|⟨ψ, [A, B] ψ⟩| ≤ 2 ‖A ψ - α ψ‖ ‖B ψ - β ψ‖` for real `α`, `β`. -/
theorem norm_inner_commutator_le (hA : A.IsSymmetric) (hB : B.IsSymmetric) (ψ : E)
    (α β : ℝ) :
    ‖⟪ψ, A (B ψ)⟫_ℂ - ⟪ψ, B (A ψ)⟫_ℂ‖ ≤
      2 * (‖A ψ - (α : ℂ) • ψ‖ * ‖B ψ - (β : ℂ) • ψ‖) := by
  rw [inner_commutator_eq hA hB ψ α β]
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (A ψ - (α : ℂ) • ψ) (B ψ - (β : ℂ) • ψ)
  have h2 := norm_inner_le_norm (𝕜 := ℂ) (B ψ - (β : ℂ) • ψ) (A ψ - (α : ℂ) • ψ)
  linarith

/-- **Robertson uncertainty relation.** For symmetric operators `A`, `B` and every vector
`ψ` (a state when `‖ψ‖ = 1`), `1/4 |⟨ψ, [A, B] ψ⟩|² ≤ Var_ψ(A) · Var_ψ(B)`. -/
theorem robertson (hA : A.IsSymmetric) (hB : B.IsSymmetric) (ψ : E) :
    1 / 4 * ‖⟪ψ, A (B ψ)⟫_ℂ - ⟪ψ, B (A ψ)⟫_ℂ‖ ^ 2 ≤ variance A ψ * variance B ψ := by
  have h := norm_inner_commutator_le hA hB ψ (expectation A ψ) (expectation B ψ)
  have h0 : 0 ≤ ‖⟪ψ, A (B ψ)⟫_ℂ - ⟪ψ, B (A ψ)⟫_ℂ‖ := norm_nonneg _
  have hsq := pow_le_pow_left₀ h0 h 2
  simp only [variance]
  nlinarith [hsq]

/-- **Robertson uncertainty relation, commutator form**: with `[A, B] = A B - B A`,
`1/4 |⟨ψ, [A, B] ψ⟩|² ≤ Var_ψ(A) · Var_ψ(B)`. -/
theorem robertson_commutator (hA : A.IsSymmetric) (hB : B.IsSymmetric) (ψ : E) :
    1 / 4 * ‖⟪ψ, (A * B - B * A) ψ⟫_ℂ‖ ^ 2 ≤ variance A ψ * variance B ψ := by
  simpa [inner_sub_right] using robertson hA hB ψ

end IsSymmetric

end LinearMap
