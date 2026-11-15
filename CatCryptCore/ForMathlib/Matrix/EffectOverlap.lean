/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.Matrix.ProjectorRewinding

/-!
# Acceptance probability of an effect from the overlap with an accepted vector

If an effect `0 ≤ E ≤ 1` accepts the unit vector `ψ` with certainty, then `(1 - E) ψ = 0`,
so `E ψ = ψ`, and Cauchy–Schwarz for the positive semidefinite form `E` gives
`|⟨ψ, φ⟩|² = |⟨ψ, E φ⟩|² ≤ ⟨ψ, E ψ⟩ ⟨φ, E φ⟩ = ⟨φ, E φ⟩`.

## Main results

* `Matrix.normSq_star_dotProduct_le_re_star_dotProduct_mulVec` — an effect that accepts the
  unit vector `ψ` with certainty accepts `φ` with probability at least `|⟨ψ, φ⟩|²`.

## References

* A. Chailloux, I. Kerenidis, "Optimal bounds for quantum bit commitment", FOCS 2011, §3.1.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An effect that accepts the unit vector `ψ` with certainty accepts `φ` with probability
at least `|⟨ψ, φ⟩|²`. -/
theorem normSq_star_dotProduct_le_re_star_dotProduct_mulVec
    {E : Matrix n n ℂ} (hE : E.PosSemidef) (hE1 : (1 - E).PosSemidef) {ψ φ : n → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hacc : (star ψ ⬝ᵥ (E *ᵥ ψ)).re = 1) :
    Complex.normSq (star ψ ⬝ᵥ φ) ≤ (star φ ⬝ᵥ (E *ᵥ φ)).re := by
  have hq : (star ψ ⬝ᵥ ((1 - E) *ᵥ ψ)) = 0 := by
    have h0 : 0 ≤ star ψ ⬝ᵥ ((1 - E) *ᵥ ψ) := hE1.dotProduct_mulVec_nonneg ψ
    have h1 : star ψ ⬝ᵥ ((1 - E) *ᵥ ψ) = star ψ ⬝ᵥ ψ - star ψ ⬝ᵥ (E *ᵥ ψ) := by
      rw [sub_mulVec, one_mulVec, dotProduct_sub]
    have him : (star ψ ⬝ᵥ (E *ᵥ ψ)).im = 0 := by
      have := hE.dotProduct_mulVec_nonneg ψ
      exact (Complex.nonneg_iff.mp this).2.symm
    apply Complex.ext
    · rw [h1, hψ]; simp [hacc]
    · rw [h1, hψ]; simp [him]
  have hEψ : E *ᵥ ψ = ψ := by
    have := hE1.dotProduct_mulVec_zero_iff.mp hq
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at this
    exact this.symm
  set t : ℂ := star ψ ⬝ᵥ φ with ht
  have hpos := hE.dotProduct_mulVec_nonneg (φ - t • ψ)
  have hEherm : E.IsHermitian := hE.isHermitian
  have hψE : star ψ ⬝ᵥ (E *ᵥ φ) = t := by
    have h := Matrix.star_mulVec E ψ
    rw [hEψ, hEherm.eq] at h
    rw [dotProduct_mulVec, ← h]
  have hφψ : star φ ⬝ᵥ ψ = star t := by
    rw [ht, star_dotProduct]
  rw [mulVec_sub, mulVec_smul, hEψ, star_sub, star_smul, sub_dotProduct, dotProduct_sub,
    dotProduct_sub, smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul,
    hψE, hψ, hφψ] at hpos
  have hre := (Complex.nonneg_iff.mp hpos).1
  simp only [smul_eq_mul, mul_one, Complex.sub_re, Complex.star_def, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, sub_self, Complex.zero_re] at hre
  rw [Complex.normSq_apply]
  linarith [hre]

end Matrix
