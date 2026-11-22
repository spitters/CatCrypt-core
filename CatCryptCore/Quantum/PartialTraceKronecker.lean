/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.PartialTrace
public import CatCryptCore.Quantum.ChoiKraus

/-!
# Partial trace of a state against an effect on the traced register

For a positive semidefinite `M` on the second register of a bipartite system and a positive
semidefinite `ρ`, the partial trace `tr₂((1 ⊗ M) ρ)` is positive semidefinite. For all `M` and
`ρ` it has trace `tr((1 ⊗ M) ρ)`, and a complete family `∑ Mᵢ = 1` sums to `tr₂ ρ`.

## Main results

* `partialTrace₂_one_kronecker_mul_posSemidef` — `tr₂((1 ⊗ M) ρ) ≥ 0`.
* `trace_partialTrace₂_one_kronecker_mul` — `tr(tr₂((1 ⊗ M) ρ)) = tr((1 ⊗ M) ρ)`.
* `sum_partialTrace₂_one_kronecker_mul` — `∑ᵢ tr₂((1 ⊗ Mᵢ) ρ) = tr₂ ρ` for `∑ Mᵢ = 1`.

Search words: partial trace, conditional state, measurement on a subsystem, POVM, Born
probability, ensemble decomposition.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder
open Matrix CatCrypt.Quantum.TensorProduct CatCrypt.Quantum.PartialTrace

namespace CatCrypt.Quantum.PartialTrace

variable {d₁ d₂ : ℕ}

/-- `tr₂((1 ⊗ M) ρ)` is positive semidefinite for `M ≥ 0` and `ρ ≥ 0`. -/
theorem partialTrace₂_one_kronecker_mul_posSemidef {M : Matrix (Fin d₂) (Fin d₂) ℂ}
    (hM : M.PosSemidef) {ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ} (hρ : ρ.PosSemidef) :
    (partialTrace₂ (((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ M) * ρ)).PosSemidef := by
  obtain ⟨B, rfl⟩ := CatCrypt.Quantum.exists_eq_conjTranspose_mul_self_of_posSemidef hM
  have h1 : ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ (Bᴴ * B)) * ρ =
      ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ Bᴴ) *
        (((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ B) * ρ) := by
    rw [← Matrix.mul_assoc, kronecker_mul_kronecker, Matrix.one_mul]
  have h2 : (((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ B) * ρ) *
      ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ Bᴴ) =
      (((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ B) * ρ) *
        ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ B)ᴴ := by
    rw [conjTranspose_kronecker, conjTranspose_one]
  rw [h1, partialTrace₂_one_kronecker_mul_comm, h2]
  exact partialTrace₂_psd _ (hρ.mul_mul_conjTranspose_same _)

/-- `tr(tr₂((1 ⊗ M) ρ)) = tr((1 ⊗ M) ρ)` for all `M` and `ρ`; for an effect `M` and a state `ρ`
this is the Born probability of `M` on the second register. -/
theorem trace_partialTrace₂_one_kronecker_mul (M : Matrix (Fin d₂) (Fin d₂) ℂ)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    (partialTrace₂ (((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ M) * ρ)).trace =
      (((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ M) * ρ).trace :=
  trace_partialTrace₂ _

/-- A complete family `∑ Mᵢ = 1` on the second register sums to the partial trace:
`∑ᵢ tr₂((1 ⊗ Mᵢ) ρ) = tr₂ ρ`. -/
theorem sum_partialTrace₂_one_kronecker_mul {ι : Type} [Fintype ι]
    (M : ι → Matrix (Fin d₂) (Fin d₂) ℂ) (hM : ∑ i, M i = 1)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    ∑ i, partialTrace₂ (((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ M i) * ρ) = partialTrace₂ ρ := by
  rw [← map_sum, ← Finset.sum_mul, kronecker_finset_sum_right, hM, kronecker_one_one,
    Matrix.one_mul]

end CatCrypt.Quantum.PartialTrace
