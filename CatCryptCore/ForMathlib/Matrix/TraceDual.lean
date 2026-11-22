/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.Matrix.Schmidt

/-!
# The trace against contractions is maximised by a unitary

For a square complex matrix `M` with Schmidt (singular value) decomposition
`M = ∑ₖ sₖ aₖ bₖᵀ`, a unitary `U` with `U aₖ = conj bₖ` gives `tr(U M) = ∑ₖ sₖ`, the trace
norm of `M`. For every contraction `K`, `|tr(K M)| ≤ ∑ₖ sₖ |bₖᵀ K aₖ| ≤ ∑ₖ sₖ`, so the value
`tr(U M)` is real, nonnegative and maximal among the traces `|tr(K M)|`.

## Main results

* `Matrix.exists_unitary_forall_norm_trace_mul_le` — some unitary `U` makes `tr(U M)` real
  and at least `|tr(K M)|` for every contraction `K`.

## References

* J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018, §1.1.3
  (the trace norm and its variational characterisation).
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A square matrix has a unitary `U` with `tr(U M)` real, nonnegative and maximal: it
dominates `|tr(K M)|` for every contraction `K`. (`tr(U M)` is the trace norm of `M`.) -/
theorem exists_unitary_forall_norm_trace_mul_le (M : Matrix n n ℂ) :
    ∃ U ∈ unitaryGroup n ℂ, (U * M).trace.im = 0 ∧
      ∀ K : Matrix n n ℂ, (∀ x, ‖WithLp.toLp 2 (K *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖) →
        ‖(K * M).trace‖ ≤ (U * M).trace.re := by
  obtain ⟨r, s, a, b, hs, ha, hb, hM⟩ := exists_schmidt M
  have htr : ∀ K : Matrix n n ℂ,
      (K * M).trace = ∑ k, (s k : ℂ) * (b k ⬝ᵥ (K *ᵥ a k)) := by
    intro K
    simp only [trace, diag_apply, Matrix.mul_apply, hM, mulVec, dotProduct,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_lhs => enter [2, x]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hb' : ∀ k l, star (star (b k)) ⬝ᵥ star (b l) = if k = l then 1 else 0 := by
    intro k l
    have h := congrArg star (hb k l)
    simp only [star_dotProduct, dotProduct_comm] at h ⊢
    simpa [apply_ite] using h
  obtain ⟨U, hU, hUa⟩ := exists_unitary_mulVec_eq a (fun k => star (b k)) ha hb'
  have hbb : ∀ k, b k ⬝ᵥ star (b k) = 1 := fun k => by
    rw [dotProduct_comm]; simpa using hb k k
  have hUM : (U * M).trace = ((∑ k, s k : ℝ) : ℂ) := by
    rw [htr]
    simp [hUa, hbb]
  have hcs : ∀ (K : Matrix n n ℂ), (∀ x, ‖WithLp.toLp 2 (K *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖) →
      ∀ k, ‖b k ⬝ᵥ (K *ᵥ a k)‖ ≤ 1 := by
    intro K hK k
    have hn : ∀ v : n → ℂ, star v ⬝ᵥ v = 1 → ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ = 1 := by
      intro v hv
      have : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 = 1 := by
        rw [EuclideanSpace.norm_sq_eq]
        have h2 := congrArg Complex.re hv
        simp only [Complex.sq_norm, Complex.normSq_apply]
        simpa [dotProduct, Complex.mul_re, Complex.conj_re] using h2
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
    have hb1 : star (star (b k)) ⬝ᵥ star (b k) = 1 := by simpa using hb' k k
    have ha1 : star (a k) ⬝ᵥ a k = 1 := by simpa using ha k k
    have hinner : b k ⬝ᵥ (K *ᵥ a k) =
        inner ℂ (WithLp.toLp 2 (star (b k)) : EuclideanSpace ℂ n) (WithLp.toLp 2 (K *ᵥ a k)) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      simp
    rw [hinner]
    calc _ ≤ ‖(WithLp.toLp 2 (star (b k)) : EuclideanSpace ℂ n)‖ *
          ‖(WithLp.toLp 2 (K *ᵥ a k) : EuclideanSpace ℂ n)‖ := norm_inner_le_norm _ _
      _ ≤ 1 * 1 := by
          gcongr
          · exact (hn _ hb1).le
          · exact (hK _).trans (hn _ ha1).le
      _ = 1 := one_mul 1
  refine ⟨U, hU, ?_, ?_⟩
  · rw [hUM]; exact Complex.ofReal_im _
  · intro K hK
    rw [hUM, Complex.ofReal_re, htr K]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul]
    have h1 := hcs K hK k
    rw [Complex.norm_real, Real.norm_of_nonneg (hs k).le]
    nlinarith [hs k]

end Matrix
