/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.TraceNorm

/-!
# The trace norm through the characteristic polynomial

The trace norm `traceNormH A` of a Hermitian matrix is the sum of the absolute values of the real
parts of the roots of its characteristic polynomial. Hence it scales by `|c|` under a real
scalar `c`, since the characteristic polynomial of `c • A` has the roots `c λᵢ`.

## Main results

* `traceNormH_eq_sum_roots`: the trace norm is the sum of `|Re r|` over the roots `r`.
* `charpoly_ofReal_smul`: the characteristic polynomial of `c • A`.
* `traceNormH_ofReal_smul`: `‖c • A‖₁ = |c| ‖A‖₁`.
* `traceNormH_of_eq`: the trace norm does not depend on the Hermiticity proof.

## Search words

trace norm, characteristic polynomial roots, real scalar multiple, Hermitian eigenvalues
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum

open scoped Matrix ComplexOrder

open Matrix Polynomial Unitary

/-- The trace norm is the sum of the absolute values of the roots of the characteristic
polynomial. -/
theorem traceNormH_eq_sum_roots {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : A.IsHermitian) :
    traceNormH A hA = (A.charpoly.roots.map fun r => |r.re|).sum := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map, traceNormH, ← Finset.sum_map_val]
  congr 1

/-- The characteristic polynomial of `c • A` for a real `c` and a Hermitian `A`:
`∏ᵢ (X - c λᵢ)`. -/
theorem charpoly_ofReal_smul {n : Type} [Fintype n] [DecidableEq n] (c : ℝ) (A : Matrix n n ℂ)
    (hA : A.IsHermitian) :
    ((c : ℂ) • A).charpoly = ∏ i, (X - C ((c * hA.eigenvalues i : ℝ) : ℂ)) := by
  have h : (c : ℂ) • A = (conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary)
      (diagonal (RCLike.ofReal ∘ (c • hA.eigenvalues))) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [← map_smul]
    congr 1
    ext i j
    simp [diagonal_apply]
  rw [h, conjStarAlgAut_apply, charpoly_mul_comm, ← mul_assoc]
  simp [charpoly_diagonal]

/-- A real multiple of a Hermitian matrix is Hermitian. -/
theorem isHermitian_ofReal_smul {n : Type} (c : ℝ) {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ((c : ℂ) • A).IsHermitian := by
  rw [IsHermitian, conjTranspose_smul, hA.eq, Complex.star_def, Complex.conj_ofReal]

/-- The trace norm under a real scalar: `‖c • A‖₁ = |c| ‖A‖₁`. -/
theorem traceNormH_ofReal_smul {n : Type} [Fintype n] [DecidableEq n] (c : ℝ)
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (hcA : ((c : ℂ) • A).IsHermitian) :
    traceNormH ((c : ℂ) • A) hcA = |c| * traceNormH A hA := by
  rw [traceNormH_eq_sum_roots, charpoly_ofReal_smul c A hA,
    roots_prod _ _ (Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero _)]
  simp only [roots_X_sub_C]
  simp [traceNormH, Finset.mul_sum, abs_mul]

/-- The trace norm depends on the matrix only, not on the proof that it is Hermitian. -/
theorem traceNormH_of_eq {n : Type} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    traceNormH A hA = traceNormH B hB := by
  subst h
  rfl

end CatCrypt.Quantum
