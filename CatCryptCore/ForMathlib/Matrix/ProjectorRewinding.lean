/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The rewinding inequality for a family of orthogonal projectors

Let `P : Fin n → Matrix (Fin d) (Fin d) ℂ` be a family of orthogonal projectors
(`IsStarProjection`) and `A = n⁻¹ • ∑ θ, P θ` their average. For a vector `Φ`, the
average success probability of a single measurement is
`V Φ = n⁻¹ ∑ θ ‖P θ Φ‖²`, and the average success probability of two consecutive
measurements is `F Φ = n⁻² ∑ θ₁ ∑ θ₂ ‖P θ₂ P θ₁ Φ‖²`. The rewinding inequality of
Unruh states `V ^ 3 ≤ F` for unit vectors and for density matrices of trace at most one.

Mathlib candidates. The Cauchy–Schwarz inequality
`Matrix.PosSemidef.norm_star_dotProduct_mulVec_sq_le` belongs in
`Mathlib/Analysis/Matrix/PosDef.lean`; Mathlib has it only implicitly, as
`inner_mul_inner_self_le` for the instance `Matrix.toInnerProductSpace`, from which it is
derived here. The projector lemmas belong in `Mathlib/Analysis/Matrix/PosDef.lean`; the
rewinding inequality in a new file `Mathlib/Analysis/Matrix/ProjectorRewinding.lean`.

The vector form is proved from the Cauchy–Schwarz inequality for the positive
semidefinite form `x, y ↦ xᴴ A y`, without the spectral theorem. The density form uses
the decomposition of a positive semidefinite matrix as a sum of rank-one matrices
`∑ i, u i (u i)ᴴ` (`Matrix.posSemidef_iff_eq_sum_vecMulVec`), the vector form for each
`u i`, and Hölder's inequality `(∑ aᵢ)³ ≤ (∑ fᵢ) (∑ tᵢ)²` for `aᵢ³ ≤ fᵢ tᵢ²`.

Norms are Euclidean norms `‖WithLp.toLp 2 v‖`; the bridge to the dot product is
`Matrix.norm_toLp_sq_eq_re_star_dotProduct`.

## Main results

* `Matrix.PosSemidef.norm_star_dotProduct_mulVec_sq_le` — Cauchy–Schwarz for a positive
  semidefinite matrix: `‖xᴴ A y‖² ≤ re (xᴴ A x) * re (yᴴ A y)`.
* `Matrix.norm_toLp_sq_eq_re_star_dotProduct` — `‖v‖² = re (vᴴ v)`.
* `Matrix.rewinding_V_eq` and `Matrix.rewinding_F_eq` — `V Φ = re (Φᴴ A Φ)` and
  `F Φ = n⁻¹ ∑ θ re ((P θ Φ)ᴴ A (P θ Φ))`.
* `Matrix.rewinding_vector` — `V Φ ^ 3 ≤ F Φ * ‖Φ‖ ^ 4` for every vector `Φ`.
* `Matrix.rewinding_vector_of_norm_eq_one` — `V Φ ^ 3 ≤ F Φ` for a unit vector `Φ`.
* `Real.pow_three_sum_le_sum_mul_sq_sum` — `(∑ aᵢ)³ ≤ (∑ fᵢ) (∑ tᵢ)²` whenever
  `0 ≤ aᵢ, tᵢ, fᵢ` and `aᵢ³ ≤ fᵢ tᵢ²`.
* `Matrix.rewinding_density_trace` — `V ρ ^ 3 ≤ F ρ * (re (trace ρ)) ^ 2` for every
  positive semidefinite `ρ`, with `V ρ = n⁻¹ ∑ θ re (trace (P θ ρ))` and
  `F ρ = n⁻² ∑ θ₁ ∑ θ₂ re (trace (P θ₂ P θ₁ ρ P θ₁ P θ₂))`.
* `Matrix.rewinding_density` — `V ρ ^ 3 ≤ F ρ` for positive semidefinite `ρ` with
  `re (trace ρ) ≤ 1`.

## References

* D. Unruh, *Quantum Proofs of Knowledge*, EUROCRYPT 2012, Lemma 7.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder

namespace Matrix

section CauchySchwarz

variable {𝕜 : Type*} [RCLike 𝕜] {m : Type*} [Fintype m]

/-- The Cauchy–Schwarz inequality for the sesquilinear form of a positive semidefinite
matrix: `‖xᴴ A y‖² ≤ re (xᴴ A x) * re (yᴴ A y)`. -/
theorem PosSemidef.norm_star_dotProduct_mulVec_sq_le {A : Matrix m m 𝕜} (hA : A.PosSemidef)
    (x y : m → 𝕜) :
    ‖star x ⬝ᵥ (A *ᵥ y)‖ ^ 2 ≤
      RCLike.re (star x ⬝ᵥ (A *ᵥ x)) * RCLike.re (star y ⬝ᵥ (A *ᵥ y)) := by
  let := A.toSeminormedAddCommGroup hA
  let := A.toInnerProductSpace hA
  have h := inner_mul_inner_self_le (𝕜 := 𝕜) x y
  rw [norm_inner_symm y x, ← sq] at h
  have e : ∀ u v : m → 𝕜, (inner 𝕜 u v : 𝕜) = star u ⬝ᵥ (A *ᵥ v) := fun u v =>
    dotProduct_comm _ _
  simpa only [e] using h

end CauchySchwarz

variable {d : Type*} [Fintype d]

/-- The squared Euclidean norm is the real part of `vᴴ v`. -/
theorem norm_toLp_sq_eq_re_star_dotProduct (v : d → ℂ) :
    ‖WithLp.toLp 2 v‖ ^ 2 = (star v ⬝ᵥ v).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rfl

/-- For an orthogonal projector `P`, `(P x)ᴴ (P y) = xᴴ (P y)`. -/
theorem _root_.IsStarProjection.star_mulVec_dotProduct_mulVec {P : Matrix d d ℂ}
    (hP : IsStarProjection P) (x y : d → ℂ) :
    star (P *ᵥ x) ⬝ᵥ (P *ᵥ y) = star x ⬝ᵥ (P *ᵥ y) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
  have hs : Pᴴ = P := hP.isSelfAdjoint
  rw [hs, hP.isIdempotentElem.eq]

/-- An orthogonal projector is positive semidefinite. -/
theorem _root_.IsStarProjection.posSemidef {P : Matrix d d ℂ} (hP : IsStarProjection P) :
    P.PosSemidef := by
  have hs : Pᴴ = P := hP.isSelfAdjoint
  have : Pᴴ * P = P := by rw [hs, hP.isIdempotentElem.eq]
  exact this ▸ posSemidef_conjTranspose_mul_self P

/-- For a Hermitian matrix `A`, `xᴴ (A y) = (A x)ᴴ y`. -/
theorem IsHermitian.star_dotProduct_mulVec_comm {A : Matrix d d ℂ} (hA : A.IsHermitian)
    (x y : d → ℂ) : star x ⬝ᵥ (A *ᵥ y) = star (A *ᵥ x) ⬝ᵥ y := by
  rw [star_mulVec, hA.eq, dotProduct_mulVec]

variable {n : ℕ}

/-- The average of a family of orthogonal projectors is positive semidefinite. -/
theorem posSemidef_inv_natCast_smul_sum {P : Fin n → Matrix d d ℂ}
    (hP : ∀ θ, IsStarProjection (P θ)) : ((n : ℂ)⁻¹ • ∑ θ, P θ).PosSemidef :=
  (posSemidef_sum _ fun θ _ => (hP θ).posSemidef).smul (by positivity)

/-- The quadratic form of the average `A = n⁻¹ • ∑ θ, P θ` is the average of the
quadratic forms. -/
theorem re_star_dotProduct_inv_natCast_smul_sum_mulVec (P : Fin n → Matrix d d ℂ)
    (x y : d → ℂ) :
    (star x ⬝ᵥ (((n : ℂ)⁻¹ • ∑ θ, P θ) *ᵥ y)).re =
      (n : ℝ)⁻¹ * ∑ θ, (star x ⬝ᵥ (P θ *ᵥ y)).re := by
  rw [smul_mulVec, sum_mulVec, dotProduct_smul, dotProduct_sum, smul_eq_mul,
    show ((n : ℂ)⁻¹) = (((n : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
    Complex.re_sum]

/-- `V Φ = re (Φᴴ A Φ)`. -/
theorem rewinding_V_eq {P : Fin n → Matrix d d ℂ} (hP : ∀ θ, IsStarProjection (P θ))
    (Φ : d → ℂ) :
    (n : ℝ)⁻¹ * ∑ θ, ‖WithLp.toLp 2 (P θ *ᵥ Φ)‖ ^ 2 =
      (star Φ ⬝ᵥ (((n : ℂ)⁻¹ • ∑ θ, P θ) *ᵥ Φ)).re := by
  simp only [re_star_dotProduct_inv_natCast_smul_sum_mulVec, norm_toLp_sq_eq_re_star_dotProduct,
    (hP _).star_mulVec_dotProduct_mulVec]

/-- `F Φ = n⁻¹ ∑ θ re ((P θ Φ)ᴴ A (P θ Φ))`. -/
theorem rewinding_F_eq {P : Fin n → Matrix d d ℂ} (hP : ∀ θ, IsStarProjection (P θ))
    (Φ : d → ℂ) :
    ((n : ℝ) ^ 2)⁻¹ * ∑ θ₁, ∑ θ₂, ‖WithLp.toLp 2 (P θ₂ *ᵥ (P θ₁ *ᵥ Φ))‖ ^ 2 =
      (n : ℝ)⁻¹ * ∑ θ, (star (P θ *ᵥ Φ) ⬝ᵥ (((n : ℂ)⁻¹ • ∑ θ, P θ) *ᵥ (P θ *ᵥ Φ))).re := by
  simp only [re_star_dotProduct_inv_natCast_smul_sum_mulVec, norm_toLp_sq_eq_re_star_dotProduct,
    (hP _).star_mulVec_dotProduct_mulVec, Finset.mul_sum]
  simp only [sq, mul_inv, mul_assoc]

/-- `‖A Φ‖² = n⁻¹ ∑ θ re ((P θ Φ)ᴴ (A Φ))` for the average `A` of orthogonal projectors. -/
theorem re_star_mulVec_dotProduct_mulVec_avg {P : Fin n → Matrix d d ℂ}
    (hP : ∀ θ, IsStarProjection (P θ)) (Φ : d → ℂ) :
    (star (((n : ℂ)⁻¹ • ∑ θ, P θ) *ᵥ Φ) ⬝ᵥ (((n : ℂ)⁻¹ • ∑ θ, P θ) *ᵥ Φ)).re =
      (n : ℝ)⁻¹ * ∑ θ, (star (P θ *ᵥ Φ) ⬝ᵥ (((n : ℂ)⁻¹ • ∑ θ, P θ) *ᵥ Φ)).re := by
  rw [← (posSemidef_inv_natCast_smul_sum hP).isHermitian.star_dotProduct_mulVec_comm,
    re_star_dotProduct_inv_natCast_smul_sum_mulVec]
  simp only [((hP _).posSemidef.isHermitian.star_dotProduct_mulVec_comm Φ)]

end Matrix

namespace Real

/-- The averaging step of the rewinding inequality: if `z θ ^ 2 ≤ b θ * a` for every `θ`, then
`(n⁻¹ ∑ θ z θ) ^ 2 ≤ (n⁻¹ ∑ θ b θ) * a`. -/
theorem sq_inv_natCast_mul_sum_le {n : ℕ} (z b : Fin n → ℝ) (a : ℝ)
    (h : ∀ θ, z θ ^ 2 ≤ b θ * a) :
    ((n : ℝ)⁻¹ * ∑ θ, z θ) ^ 2 ≤ ((n : ℝ)⁻¹ * ∑ θ, b θ) * a := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := z)
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  have hsum : ∑ θ, z θ ^ 2 ≤ (∑ θ, b θ) * a := by
    rw [Finset.sum_mul]; exact Finset.sum_le_sum fun θ _ => h θ
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc ((n : ℝ)⁻¹ * ∑ θ, z θ) ^ 2 = ((n : ℝ) ^ 2)⁻¹ * (∑ θ, z θ) ^ 2 := by ring
    _ ≤ ((n : ℝ) ^ 2)⁻¹ * (n * ((∑ θ, b θ) * a)) := by
        gcongr; exact hcs.trans (by gcongr)
    _ = ((n : ℝ)⁻¹ * ∑ θ, b θ) * a := by field_simp

/-- The final step of the rewinding inequality: from `a ^ 2 ≤ s * w` and `w ^ 2 ≤ f * a`
with `a, f ≥ 0`, `a ^ 3 ≤ f * s ^ 2`. -/
theorem pow_three_le_of_sq_le_mul {a f s w : ℝ} (ha : 0 ≤ a) (hf : 0 ≤ f)
    (has : a ^ 2 ≤ s * w) (hwf : w ^ 2 ≤ f * a) : a ^ 3 ≤ f * s ^ 2 := by
  have h2 : (a ^ 2) ^ 2 ≤ (s * w) ^ 2 := pow_le_pow_left₀ (by positivity) has 2
  have h4 : a ^ 4 ≤ s ^ 2 * (f * a) := by
    nlinarith [mul_le_mul_of_nonneg_left hwf (sq_nonneg s)]
  rcases ha.eq_or_lt with h0 | hpos
  · rw [← h0, zero_pow three_ne_zero]; positivity
  · nlinarith [h4, hpos]

end Real

namespace Matrix

variable {d : Type*} [Fintype d] {n : ℕ}

/-- The squared real part of `xᴴ (A y)` is bounded by the Cauchy–Schwarz bound. -/
theorem PosSemidef.re_star_dotProduct_mulVec_sq_le {A : Matrix d d ℂ} (hA : A.PosSemidef)
    (x y : d → ℂ) :
    (star x ⬝ᵥ (A *ᵥ y)).re ^ 2 ≤ (star x ⬝ᵥ (A *ᵥ x)).re * (star y ⬝ᵥ (A *ᵥ y)).re := by
  have h1 := Complex.re_sq_le_normSq (star x ⬝ᵥ (A *ᵥ y))
  have h2 := hA.norm_star_dotProduct_mulVec_sq_le x y
  rw [Complex.sq_norm] at h2
  simp only [RCLike.re_to_complex] at h2
  nlinarith [h1, h2]

/-- The rewinding inequality in terms of the average `A`, with `a = re (Φᴴ A Φ)` and
`f = n⁻¹ ∑ θ re ((P θ Φ)ᴴ A (P θ Φ))`: `a ^ 3 ≤ f * (re (Φᴴ Φ)) ^ 2`. -/
theorem rewinding_vector_dotProduct {P : Fin n → Matrix d d ℂ}
    (hP : ∀ θ, IsStarProjection (P θ)) (Φ : d → ℂ) :
    (star Φ ⬝ᵥ (((n : ℂ)⁻¹ • ∑ θ, P θ) *ᵥ Φ)).re ^ 3 ≤
      ((n : ℝ)⁻¹ * ∑ θ, (star (P θ *ᵥ Φ) ⬝ᵥ (((n : ℂ)⁻¹ • ∑ θ, P θ) *ᵥ (P θ *ᵥ Φ))).re) *
        (star Φ ⬝ᵥ Φ).re ^ 2 := by
  classical
  have hA := posSemidef_inv_natCast_smul_sum hP
  refine Real.pow_three_le_of_sq_le_mul (hA.re_dotProduct_nonneg Φ)
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun θ _ => hA.re_dotProduct_nonneg _))
    (w := (star (((n : ℂ)⁻¹ • ∑ θ, P θ) *ᵥ Φ) ⬝ᵥ (((n : ℂ)⁻¹ • ∑ θ, P θ) *ᵥ Φ)).re) ?_ ?_
  · simpa using PosSemidef.one.re_star_dotProduct_mulVec_sq_le Φ (((n : ℂ)⁻¹ • ∑ θ, P θ) *ᵥ Φ)
  · rw [re_star_mulVec_dotProduct_mulVec_avg hP]
    exact Real.sq_inv_natCast_mul_sum_le _ _ _ fun θ =>
      hA.re_star_dotProduct_mulVec_sq_le (P θ *ᵥ Φ) Φ

/-- **Rewinding inequality**, vector form (Unruh 2012, Lemma 7):
`V Φ ^ 3 ≤ F Φ * ‖Φ‖ ^ 4`, with `V Φ = n⁻¹ ∑ θ ‖P θ Φ‖²` and
`F Φ = n⁻² ∑ θ₁ ∑ θ₂ ‖P θ₂ P θ₁ Φ‖²`. -/
theorem rewinding_vector {P : Fin n → Matrix d d ℂ} (hP : ∀ θ, IsStarProjection (P θ))
    (Φ : d → ℂ) :
    ((n : ℝ)⁻¹ * ∑ θ, ‖WithLp.toLp 2 (P θ *ᵥ Φ)‖ ^ 2) ^ 3 ≤
      (((n : ℝ) ^ 2)⁻¹ * ∑ θ₁, ∑ θ₂, ‖WithLp.toLp 2 (P θ₂ *ᵥ (P θ₁ *ᵥ Φ))‖ ^ 2) *
        ‖WithLp.toLp 2 Φ‖ ^ 4 := by
  rw [rewinding_V_eq hP, rewinding_F_eq hP, show ‖WithLp.toLp 2 Φ‖ ^ 4 =
    (‖WithLp.toLp 2 Φ‖ ^ 2) ^ 2 by ring, norm_toLp_sq_eq_re_star_dotProduct]
  exact rewinding_vector_dotProduct hP Φ

/-- **Rewinding inequality** for a unit vector: `V Φ ^ 3 ≤ F Φ`. -/
theorem rewinding_vector_of_norm_eq_one {P : Fin n → Matrix d d ℂ}
    (hP : ∀ θ, IsStarProjection (P θ)) {Φ : d → ℂ} (hΦ : ‖WithLp.toLp 2 Φ‖ = 1) :
    ((n : ℝ)⁻¹ * ∑ θ, ‖WithLp.toLp 2 (P θ *ᵥ Φ)‖ ^ 2) ^ 3 ≤
      ((n : ℝ) ^ 2)⁻¹ * ∑ θ₁, ∑ θ₂, ‖WithLp.toLp 2 (P θ₂ *ᵥ (P θ₁ *ᵥ Φ))‖ ^ 2 := by
  simpa [hΦ] using rewinding_vector hP Φ

end Matrix

namespace Real

/-- Hölder's inequality with exponents `3/2` and `3`, in the form used for the density version
of the rewinding inequality: if `0 ≤ a i, t i, f i` and `a i ^ 3 ≤ f i * t i ^ 2`, then
`(∑ a i) ^ 3 ≤ (∑ f i) * (∑ t i) ^ 2`. -/
theorem pow_three_sum_le_sum_mul_sq_sum {ι : Type*} (s : Finset ι) (a t f : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (ht : ∀ i ∈ s, 0 ≤ t i) (hf : ∀ i ∈ s, 0 ≤ f i)
    (h : ∀ i ∈ s, a i ^ 3 ≤ f i * t i ^ 2) :
    (∑ i ∈ s, a i) ^ 3 ≤ (∑ i ∈ s, f i) * (∑ i ∈ s, t i) ^ 2 := by
  -- `t i = 0` forces `a i = 0`
  have hat : ∀ i ∈ s, t i = 0 → a i = 0 := fun i hi h0 => by
    have := h i hi
    rw [h0] at this
    exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp
      (le_antisymm (by simpa using this) (pow_nonneg (ha i hi) 3))
  set T := ∑ i ∈ s, t i with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg ht
  rcases hT0.eq_or_lt with hT0 | hTpos
  · have hti : ∀ i ∈ s, t i = 0 := (Finset.sum_eq_zero_iff_of_nonneg ht).mp hT0.symm
    rw [Finset.sum_eq_zero fun i hi => hat i hi (hti i hi), ← hT0]
    simp
  have hw : ∀ i ∈ s, 0 ≤ t i / T := fun i hi => div_nonneg (ht i hi) hTpos.le
  have hw' : ∑ i ∈ s, t i / T = 1 := by rw [← Finset.sum_div, div_self hTpos.ne']
  have hz : ∀ i ∈ s, 0 ≤ a i / t i := fun i hi => div_nonneg (ha i hi) (ht i hi)
  have hj := Real.pow_arith_mean_le_arith_mean_pow s _ _ hw hw' hz 3
  have hl : ∀ i ∈ s, t i / T * (a i / t i) = a i / T := fun i hi => by
    rcases (ht i hi).eq_or_lt with h0 | hpos
    · rw [← h0, hat i hi h0.symm]; simp
    · field_simp
  have hr : ∀ i ∈ s, t i / T * (a i / t i) ^ 3 ≤ f i / T := fun i hi => by
    rcases (ht i hi).eq_or_lt with h0 | hpos
    · rw [← h0]; simpa using div_nonneg (hf i hi) hTpos.le
    · rw [div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) hTpos]
      have := h i hi
      calc t i * a i ^ 3 * T ≤ t i * (f i * t i ^ 2) * T := by gcongr
        _ = f i * (T * t i ^ 3) := by ring
  rw [Finset.sum_congr rfl hl, ← Finset.sum_div, div_pow] at hj
  have hj' := hj.trans (Finset.sum_le_sum hr)
  rw [← Finset.sum_div, div_le_div_iff₀ (by positivity) hTpos] at hj'
  nlinarith [hj', hTpos]

end Real

namespace Matrix

variable {d : Type*} [Fintype d] {n : ℕ}

/-- `trace (M * ∑ i, u i (u i)ᴴ) = ∑ i, (u i)ᴴ (M (u i))`. -/
theorem trace_mul_sum_vecMulVec_star {m : ℕ} (M : Matrix d d ℂ) (u : Fin m → d → ℂ) :
    (M * ∑ i, vecMulVec (u i) (star (u i))).trace = ∑ i, star (u i) ⬝ᵥ (M *ᵥ u i) := by
  rw [Finset.mul_sum, trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

/-- `trace (X * (∑ i, u i (u i)ᴴ) * Xᴴ) = ∑ i, (X (u i))ᴴ (X (u i))`. -/
theorem trace_mul_sum_vecMulVec_star_mul_conjTranspose {m : ℕ} (X : Matrix d d ℂ)
    (u : Fin m → d → ℂ) :
    (X * (∑ i, vecMulVec (u i) (star (u i))) * Xᴴ).trace =
      ∑ i, star (X *ᵥ u i) ⬝ᵥ (X *ᵥ u i) := by
  rw [Finset.mul_sum, Finset.sum_mul, trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_vecMulVec, vecMulVec_mul, trace_vecMulVec, star_mulVec, dotProduct_comm]

/-- **Rewinding inequality**, density form with the trace (Unruh 2012, Lemma 7): for a positive
semidefinite `ρ`, `V ρ ^ 3 ≤ F ρ * (re (trace ρ)) ^ 2`, with
`V ρ = n⁻¹ ∑ θ re (trace (P θ ρ))` and `F ρ = n⁻² ∑ θ₁ ∑ θ₂ re (trace (P θ₂ P θ₁ ρ P θ₁ P θ₂))`. -/
theorem rewinding_density_trace {P : Fin n → Matrix d d ℂ} (hP : ∀ θ, IsStarProjection (P θ))
    {ρ : Matrix d d ℂ} (hρ : ρ.PosSemidef) :
    ((n : ℝ)⁻¹ * ∑ θ, (P θ * ρ).trace.re) ^ 3 ≤
      (((n : ℝ) ^ 2)⁻¹ * ∑ θ₁, ∑ θ₂, (P θ₂ * P θ₁ * ρ * P θ₁ * P θ₂).trace.re) *
        ρ.trace.re ^ 2 := by
  classical
  obtain ⟨m, u, rfl⟩ := posSemidef_iff_eq_sum_vecMulVec.mp hρ
  have hV : (n : ℝ)⁻¹ * ∑ θ, (P θ * ∑ i, vecMulVec (u i) (star (u i))).trace.re =
      ∑ i, (n : ℝ)⁻¹ * ∑ θ, ‖WithLp.toLp 2 (P θ *ᵥ u i)‖ ^ 2 := by
    simp only [trace_mul_sum_vecMulVec_star, Complex.re_sum, norm_toLp_sq_eq_re_star_dotProduct,
      (hP _).star_mulVec_dotProduct_mulVec, ← Finset.mul_sum]
    rw [Finset.sum_comm]
  have hF : ((n : ℝ) ^ 2)⁻¹ * ∑ θ₁, ∑ θ₂,
        (P θ₂ * P θ₁ * (∑ i, vecMulVec (u i) (star (u i))) * P θ₁ * P θ₂).trace.re =
      ∑ i, ((n : ℝ) ^ 2)⁻¹ * ∑ θ₁, ∑ θ₂, ‖WithLp.toLp 2 (P θ₂ *ᵥ (P θ₁ *ᵥ u i))‖ ^ 2 := by
    have e : ∀ θ₁ θ₂, P θ₂ * P θ₁ * (∑ i, vecMulVec (u i) (star (u i))) * P θ₁ * P θ₂ =
        (P θ₂ * P θ₁) * (∑ i, vecMulVec (u i) (star (u i))) * (P θ₂ * P θ₁)ᴴ := fun θ₁ θ₂ => by
      have h1 : (P θ₁)ᴴ = P θ₁ := (hP θ₁).isSelfAdjoint
      have h2 : (P θ₂)ᴴ = P θ₂ := (hP θ₂).isSelfAdjoint
      rw [conjTranspose_mul, h1, h2, Matrix.mul_assoc _ (P θ₁) (P θ₂)]
    simp only [e, trace_mul_sum_vecMulVec_star_mul_conjTranspose, Complex.re_sum,
      norm_toLp_sq_eq_re_star_dotProduct, mulVec_mulVec, ← Finset.mul_sum]
    rw [Finset.sum_comm (γ := Fin m)]
    congr 1
    refine Finset.sum_congr rfl fun θ₁ _ => ?_
    rw [Finset.sum_comm]
  have ht : (∑ i, vecMulVec (u i) (star (u i))).trace.re = ∑ i, ‖WithLp.toLp 2 (u i)‖ ^ 2 := by
    rw [← Matrix.one_mul (∑ i, vecMulVec (u i) (star (u i))), trace_mul_sum_vecMulVec_star,
      Complex.re_sum]
    simp only [one_mulVec, norm_toLp_sq_eq_re_star_dotProduct]
  rw [hV, hF, ht]
  refine Real.pow_three_sum_le_sum_mul_sq_sum _ _ _ _ (fun i _ => by positivity)
    (fun i _ => by positivity) (fun i _ => by positivity) fun i _ => ?_
  have := rewinding_vector hP (u i)
  rwa [show ‖WithLp.toLp 2 (u i)‖ ^ 4 = (‖WithLp.toLp 2 (u i)‖ ^ 2) ^ 2 by ring] at this

/-- **Rewinding inequality**, density form (Unruh 2012, Lemma 7): for a positive semidefinite
`ρ` with `re (trace ρ) ≤ 1`, `V ρ ^ 3 ≤ F ρ`. -/
theorem rewinding_density {P : Fin n → Matrix d d ℂ} (hP : ∀ θ, IsStarProjection (P θ))
    {ρ : Matrix d d ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1) :
    ((n : ℝ)⁻¹ * ∑ θ, (P θ * ρ).trace.re) ^ 3 ≤
      ((n : ℝ) ^ 2)⁻¹ * ∑ θ₁, ∑ θ₂, (P θ₂ * P θ₁ * ρ * P θ₁ * P θ₂).trace.re := by
  have h := rewinding_density_trace hP hρ
  have ht0 : 0 ≤ ρ.trace.re := by
    simpa using Complex.nonneg_iff.mp hρ.trace_nonneg |>.1
  have hF : 0 ≤ ((n : ℝ) ^ 2)⁻¹ * ∑ θ₁, ∑ θ₂, (P θ₂ * P θ₁ * ρ * P θ₁ * P θ₂).trace.re := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun θ₁ _ => Finset.sum_nonneg
      fun θ₂ _ => ?_)
    have : (P θ₂ * P θ₁ * ρ * P θ₁ * P θ₂).PosSemidef := by
      have h1 : (P θ₁)ᴴ = P θ₁ := (hP θ₁).isSelfAdjoint
      have h2 : (P θ₂)ᴴ = P θ₂ := (hP θ₂).isSelfAdjoint
      have := hρ.mul_mul_conjTranspose_same (P θ₂ * P θ₁)
      rwa [conjTranspose_mul, h1, h2, ← Matrix.mul_assoc] at this
    simpa using Complex.nonneg_iff.mp this.trace_nonneg |>.1
  calc _ ≤ _ := h
    _ ≤ _ := mul_le_of_le_one_right hF (pow_le_one₀ ht0 htr)

end Matrix
