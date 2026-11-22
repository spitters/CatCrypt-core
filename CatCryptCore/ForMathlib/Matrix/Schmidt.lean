/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

set_option autoImplicit false

/-!
# The Schmidt decomposition and the unitary freedom of factorisations

A vector of `ℂ^m ⊗ ℂ^n` is a coefficient matrix `M : Matrix m n ℂ`. Diagonalising
`M Mᴴ = U D Uᴴ` gives `M = U R` with `R = Uᴴ M`, whose rows are orthogonal with squared
norms the eigenvalues `D`. Normalising the nonzero rows yields the Schmidt decomposition
`M = ∑ₖ sₖ aₖ bₖᵀ` with `sₖ > 0` and orthonormal families `(aₖ)`, `(bₖ)`.

If also `N Nᴴ = M Mᴴ`, the normalised rows of `Uᴴ M` and `Uᴴ N` are two orthonormal
families with the same index set; a unitary carrying one to the other, built from two
orthonormal bases extending them, gives `N = M V` for a unitary `V`. This is the
unitary freedom in the purification of a mixed state (Schrödinger, Hughston–Jozsa–Wootters).

## Main results

* `Matrix.exists_unitary_mulVec_eq` — two orthonormal families of `ℂⁿ` with the same index
  set are related by a unitary matrix.
* `Matrix.exists_schmidt` — the Schmidt decomposition of a coefficient matrix.
* `Matrix.exists_unitary_eq_mul_of_mul_conjTranspose_eq` — `N Nᴴ = M Mᴴ` implies `N = M V`
  for a unitary `V`.

## References

* Schmidt, *Zur Theorie der linearen und nichtlinearen Integralgleichungen*, Math. Ann. 63
  (1907)
* Hughston, Jozsa, Wootters, *A complete classification of quantum ensembles having a given
  density matrix*, Phys. Lett. A 183 (1993)
* Nielsen, Chuang, *Quantum Computation and Quantum Information*, Theorem 2.7 and §2.5
-/

open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Two orthonormal families of `ℂⁿ` indexed by the same finite type are related by a
unitary matrix. -/
theorem exists_unitary_mulVec_eq {K : Type*} [Fintype K] [DecidableEq K] (b b' : K → n → ℂ)
    (hb : ∀ k l, star (b k) ⬝ᵥ b l = if k = l then 1 else 0)
    (hb' : ∀ k l, star (b' k) ⬝ᵥ b' l = if k = l then 1 else 0) :
    ∃ W ∈ unitaryGroup n ℂ, ∀ k, W *ᵥ b k = b' k := by
  have hinner : ∀ x y : n → ℂ,
      ⟪(WithLp.toLp 2 x : EuclideanSpace ℂ n), WithLp.toLp 2 y⟫_ℂ = star x ⬝ᵥ y := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have hon : ∀ c : K → n → ℂ, (∀ k l, star (c k) ⬝ᵥ c l = if k = l then 1 else 0) →
      Orthonormal ℂ (fun k => (WithLp.toLp 2 (c k) : EuclideanSpace ℂ n)) := by
    intro c hc
    exact orthonormal_iff_ite.mpr fun k l => by rw [hinner, hc]
  have hcard : Fintype.card K ≤ Fintype.card n := by
    have := (hon b hb).linearIndependent.fintype_card_le_finrank
    simpa [finrank_euclideanSpace] using this
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
  have hext : ∀ w : K → EuclideanSpace ℂ n, Orthonormal ℂ w →
      ∃ β : OrthonormalBasis n ℂ (EuclideanSpace ℂ n), ∀ k, β (emb k) = w k := by
    intro w hw
    let u : n → EuclideanSpace ℂ n := Function.extend emb w 0
    have hu : ∀ k, u (emb k) = w k := fun k => emb.injective.extend_apply w 0 k
    have hor : Orthonormal ℂ ((Set.range emb).domRestrict u) := by
      have heq : (Set.range emb).domRestrict u =
          w ∘ (Equiv.ofInjective emb emb.injective).symm := by
        funext x
        obtain ⟨_, k, rfl⟩ := x
        have : (Equiv.ofInjective emb emb.injective).symm ⟨emb k, ⟨k, rfl⟩⟩ = k :=
          Equiv.ofInjective_symm_apply emb.injective k
        simp only [Set.domRestrict_apply, Function.comp_apply, this, hu]
      rw [heq]
      exact hw.comp _ (Equiv.injective _)
    obtain ⟨β, hβ⟩ := hor.exists_orthonormalBasis_extension_of_card_eq
      (by simp [finrank_euclideanSpace])
    exact ⟨β, fun k => by rw [hβ (emb k) ⟨k, rfl⟩, hu]⟩
  obtain ⟨β, hβ⟩ := hext _ (hon b hb)
  obtain ⟨β', hβ'⟩ := hext _ (hon b' hb')
  let B : Matrix n n ℂ := Matrix.of fun i l => WithLp.ofLp (β l) i
  let B' : Matrix n n ℂ := Matrix.of fun i l => WithLp.ofLp (β' l) i
  have hstarB : ∀ (γ : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (x : n → ℂ) (l : n),
      (star (Matrix.of fun i l => WithLp.ofLp (γ l) i) *ᵥ x) l =
        ⟪γ l, (WithLp.toLp 2 x : EuclideanSpace ℂ n)⟫_ℂ := by
    intro γ x l
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [mulVec, dotProduct, star_apply, mul_comm]
  have hunit : ∀ γ : OrthonormalBasis n ℂ (EuclideanSpace ℂ n),
      star (Matrix.of fun i l => WithLp.ofLp (γ l) i) *
        (Matrix.of fun i l => WithLp.ofLp (γ l) i) = 1 := by
    intro γ
    ext l l'
    have := orthonormal_iff_ite.mp γ.orthonormal l l'
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    rw [Matrix.one_apply, ← this]
    simp [Matrix.mul_apply, star_apply, dotProduct, mul_comm]
  have hB : B ∈ unitaryGroup n ℂ := mem_unitaryGroup_iff'.mpr (hunit β)
  have hB' : B' ∈ unitaryGroup n ℂ := mem_unitaryGroup_iff'.mpr (hunit β')
  refine ⟨B' * star B, Submonoid.mul_mem _ hB' (Unitary.star_mem hB), fun k => ?_⟩
  rw [← mulVec_mulVec]
  have hsingle : star B *ᵥ b k = Pi.single (emb k) 1 := by
    funext l
    rw [hstarB β (b k) l, ← hβ k, orthonormal_iff_ite.mp β.orthonormal l (emb k)]
    simp [Pi.single_apply]
  rw [hsingle, mulVec_single_one]
  funext i
  simp [B', hβ' k]

omit [DecidableEq n] in
/-- The rows of `Uᴴ M`, for `U` diagonalising `M Mᴴ`, are orthogonal with squared norms the
eigenvalues. -/
theorem eigenvectorUnitary_star_mul_conj (M : Matrix m n ℂ) :
    (star ((isHermitian_mul_conjTranspose_self M).eigenvectorUnitary : Matrix m m ℂ) * M) *
      (star ((isHermitian_mul_conjTranspose_self M).eigenvectorUnitary : Matrix m m ℂ) * M)ᴴ =
      diagonal (RCLike.ofReal ∘ (isHermitian_mul_conjTranspose_self M).eigenvalues) := by
  set hH := isHermitian_mul_conjTranspose_self M
  set U : Matrix m m ℂ := (hH.eigenvectorUnitary : Matrix m m ℂ)
  set D := diagonal (RCLike.ofReal ∘ hH.eigenvalues : m → ℂ)
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hspec : M * Mᴴ = U * D * star U := by
    have h := hH.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at h
  rw [conjTranspose_mul, ← star_eq_conjTranspose (star U), star_star]
  calc star U * M * (Mᴴ * U) = star U * (M * Mᴴ) * U := by simp only [Matrix.mul_assoc]
    _ = (star U * U) * D * (star U * U) := by
        rw [hspec]; simp only [Matrix.mul_assoc]
    _ = D := by rw [hUU, Matrix.one_mul, Matrix.mul_one]

omit [DecidableEq n] in
/-- `M = U (Uᴴ M)` for the unitary `U` diagonalising `M Mᴴ`. -/
theorem eq_eigenvectorUnitary_mul (M : Matrix m n ℂ) :
    M = ((isHermitian_mul_conjTranspose_self M).eigenvectorUnitary : Matrix m m ℂ) *
      (star ((isHermitian_mul_conjTranspose_self M).eigenvectorUnitary : Matrix m m ℂ) * M) := by
  rw [← Matrix.mul_assoc, Unitary.mul_star_self_of_mem (Subtype.prop _), Matrix.one_mul]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- A row of `R` with `(R Rᴴ) k k = 0` vanishes. -/
theorem row_eq_zero_of_mul_conjTranspose_diag_eq_zero {R : Matrix m n ℂ} {k : m}
    (h : (R * Rᴴ) k k = 0) : R k = 0 := by
  rw [Matrix.mul_apply] at h
  have : R k ⬝ᵥ star (R k) = 0 := by
    rw [← h]; simp [dotProduct, conjTranspose_apply]
  exact dotProduct_self_star_eq_zero.mp this

omit [DecidableEq n] in
/-- **Schmidt decomposition.** Every `M : Matrix m n ℂ` (a vector of `ℂ^m ⊗ ℂ^n`) is
`∑ₖ sₖ aₖ bₖᵀ` with `sₖ > 0` and orthonormal families `(aₖ)` of `ℂ^m` and `(bₖ)` of
`ℂ^n`. -/
theorem exists_schmidt (M : Matrix m n ℂ) :
    ∃ (r : ℕ) (s : Fin r → ℝ) (a : Fin r → m → ℂ) (b : Fin r → n → ℂ),
      (∀ k, 0 < s k) ∧
      (∀ k l, star (a k) ⬝ᵥ a l = if k = l then 1 else 0) ∧
      (∀ k l, star (b k) ⬝ᵥ b l = if k = l then 1 else 0) ∧
      ∀ i j, M i j = ∑ k, (s k : ℂ) * a k i * b k j := by
  set hH := isHermitian_mul_conjTranspose_self M
  set U : Matrix m m ℂ := (hH.eigenvectorUnitary : Matrix m m ℂ) with hUdef
  set R := star U * M with hR
  have hRR : R * Rᴴ = diagonal (RCLike.ofReal ∘ hH.eigenvalues : m → ℂ) :=
    eigenvectorUnitary_star_mul_conj M
  have hlam : ∀ k, 0 ≤ hH.eigenvalues k := fun k =>
    (posSemidef_self_mul_conjTranspose M).eigenvalues_nonneg k
  have hRRe : ∀ k l, ∑ j, R k j * star (R l j) =
      if k = l then (hH.eigenvalues k : ℂ) else 0 := by
    intro k l
    have := congrFun (congrFun hRR k) l
    simpa [Matrix.mul_apply, conjTranspose_apply, diagonal_apply] using this
  have hzero : ∀ k, hH.eigenvalues k = 0 → R k = 0 := by
    intro k hk
    apply row_eq_zero_of_mul_conjTranspose_diag_eq_zero
    rw [hRR]; simp [hk]
  let K := {k : m // hH.eigenvalues k ≠ 0}
  let e := Fintype.equivFin K
  have hs : ∀ k : K, (0 : ℝ) < Real.sqrt (hH.eigenvalues k) := fun k =>
    Real.sqrt_pos.mpr (lt_of_le_of_ne (hlam _) (Ne.symm k.2))
  have hsq : ∀ k : K, (Real.sqrt (hH.eigenvalues k) : ℂ) * (Real.sqrt (hH.eigenvalues k) : ℂ) =
      (hH.eigenvalues k : ℂ) := fun k => by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hlam _)]
  refine ⟨Fintype.card K, fun k => Real.sqrt (hH.eigenvalues (e.symm k)),
    fun k i => U i (e.symm k),
    fun k j => R (e.symm k) j / (Real.sqrt (hH.eigenvalues (e.symm k)) : ℂ),
    fun k => hs _, ?_, ?_, ?_⟩
  · intro k l
    have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
    have := congrFun (congrFun hUU (e.symm k : m)) (e.symm l : m)
    simp only [Matrix.mul_apply, star_apply, Matrix.one_apply] at this
    simp only [dotProduct, Pi.star_apply, this, Subtype.coe_inj, e.symm.injective.eq_iff]
  · intro k l
    simp only [dotProduct, Pi.star_apply, star_div₀, Complex.star_def, Complex.conj_ofReal]
    have h1 : ∀ j, (starRingEnd ℂ) (R (e.symm k) j) / (Real.sqrt (hH.eigenvalues (e.symm k)) : ℂ) *
        (R (e.symm l) j / (Real.sqrt (hH.eigenvalues (e.symm l)) : ℂ)) =
        R (e.symm l) j * star (R (e.symm k) j) /
          ((Real.sqrt (hH.eigenvalues (e.symm k)) : ℂ) *
            (Real.sqrt (hH.eigenvalues (e.symm l)) : ℂ)) := fun j => by
      rw [Complex.star_def]; ring
    simp only [h1, ← Finset.sum_div, hRRe]
    by_cases hkl : k = l
    · subst hkl
      have hne : (hH.eigenvalues (e.symm k) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (e.symm k).2
      simp [hsq, hne]
    · have : (e.symm l : m) ≠ e.symm k := fun h => hkl (e.symm.injective (Subtype.ext h)).symm
      simp [this, hkl]
  · intro i j
    have hM : M i j = ∑ κ, U i κ * R κ j := by
      conv_lhs => rw [eq_eigenvectorUnitary_mul M]
      rfl
    rw [hM, ← Fintype.sum_subtype_add_sum_subtype (fun κ => hH.eigenvalues κ ≠ 0)]
    have h0 : ∑ κ : {κ // ¬ hH.eigenvalues κ ≠ 0}, U i κ * R κ j = 0 :=
      Finset.sum_eq_zero fun κ _ => by
        rw [hzero κ (not_not.mp κ.2)]; simp
    rw [h0, add_zero, ← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hne : (Real.sqrt (hH.eigenvalues (e.symm k)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (hs _).ne'
    field_simp

omit [Fintype m] [DecidableEq n] in
/-- The rows of `R` with `R Rᴴ = diag λ`, normalised by `√λₖ` over the indices with
`λₖ ≠ 0`, are orthonormal. -/
theorem normalizedRows_orthonormal (R : Matrix m n ℂ) (lam : m → ℝ)
    (hRR : R * Rᴴ = diagonal (RCLike.ofReal ∘ lam : m → ℂ)) (hlam : ∀ k, 0 ≤ lam k)
    (k l : {k : m // lam k ≠ 0}) :
    star (fun j => R k j / (Real.sqrt (lam k) : ℂ)) ⬝ᵥ (fun j => R l j / (Real.sqrt (lam l) : ℂ))
      = if k = l then 1 else 0 := by
  classical
  have hRRe : ∀ k l, ∑ j, R k j * star (R l j) = if k = l then (lam k : ℂ) else 0 := by
    intro k l
    have := congrFun (congrFun hRR k) l
    simpa [Matrix.mul_apply, conjTranspose_apply, diagonal_apply] using this
  simp only [dotProduct, Pi.star_apply, star_div₀, Complex.star_def, Complex.conj_ofReal]
  have h1 : ∀ j, (starRingEnd ℂ) (R k j) / (Real.sqrt (lam k) : ℂ) *
      (R l j / (Real.sqrt (lam l) : ℂ)) =
      R l j * star (R k j) / ((Real.sqrt (lam k) : ℂ) * (Real.sqrt (lam l) : ℂ)) := fun j => by
    rw [Complex.star_def]; ring
  simp only [h1, ← Finset.sum_div, hRRe]
  by_cases hkl : k = l
  · subst hkl
    have hne : (lam k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr k.2
    have hsq : (Real.sqrt (lam k) : ℂ) * (Real.sqrt (lam k) : ℂ) = (lam k : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hlam _)]
    simp [hsq, hne]
  · have : (l : m) ≠ k := fun h => hkl (Subtype.ext h).symm
    simp [this, hkl]

/-- **Unitary freedom.** If `N Nᴴ = M Mᴴ`, then `N = M V` for a unitary `V`. -/
theorem exists_unitary_eq_mul_of_mul_conjTranspose_eq (M N : Matrix m n ℂ)
    (h : N * Nᴴ = M * Mᴴ) : ∃ V ∈ unitaryGroup n ℂ, N = M * V := by
  set hH := isHermitian_mul_conjTranspose_self M
  set U : Matrix m m ℂ := (hH.eigenvectorUnitary : Matrix m m ℂ) with hUdef
  set R := star U * M with hR
  set R' := star U * N with hR'
  have hRR : R * Rᴴ = diagonal (RCLike.ofReal ∘ hH.eigenvalues : m → ℂ) :=
    eigenvectorUnitary_star_mul_conj M
  have hRR' : R' * R'ᴴ = diagonal (RCLike.ofReal ∘ hH.eigenvalues : m → ℂ) := by
    rw [← hRR, hR, hR', conjTranspose_mul, conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc N, h]
    simp only [Matrix.mul_assoc]
  have hlam : ∀ k, 0 ≤ hH.eigenvalues k := fun k =>
    (posSemidef_self_mul_conjTranspose M).eigenvalues_nonneg k
  have hzero : ∀ (S : Matrix m n ℂ), S * Sᴴ = diagonal (RCLike.ofReal ∘ hH.eigenvalues : m → ℂ) →
      ∀ k, hH.eigenvalues k = 0 → S k = 0 := by
    intro S hS k hk
    apply row_eq_zero_of_mul_conjTranspose_diag_eq_zero
    rw [hS]; simp [hk]
  let K := {k : m // hH.eigenvalues k ≠ 0}
  let b : K → n → ℂ := fun k j => R k j / (Real.sqrt (hH.eigenvalues k) : ℂ)
  let b' : K → n → ℂ := fun k j => R' k j / (Real.sqrt (hH.eigenvalues k) : ℂ)
  obtain ⟨W, hW, hWb⟩ := exists_unitary_mulVec_eq b b'
    (normalizedRows_orthonormal R _ hRR hlam) (normalizedRows_orthonormal R' _ hRR' hlam)
  have hWW : W * star W = 1 := mem_unitaryGroup_iff.mp hW
  refine ⟨Wᵀ, mem_unitaryGroup_iff'.mpr ?_, ?_⟩
  · rw [star_eq_conjTranspose, conjTranspose_transpose_eq_transpose_conjTranspose,
      ← transpose_mul, ← star_eq_conjTranspose, hWW, transpose_one]
  · have hRV : R' = R * Wᵀ := by
      ext k j
      rw [Matrix.mul_apply]
      simp only [transpose_apply]
      by_cases hk : hH.eigenvalues k = 0
      · rw [hzero R' hRR' k hk, hzero R hRR k hk]; simp
      · have hs : (Real.sqrt (hH.eigenvalues k) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (lt_of_le_of_ne (hlam k) (Ne.symm hk))).ne'
        have := congrFun (hWb ⟨k, hk⟩) j
        simp only [b, b', mulVec, dotProduct] at this
        rw [eq_div_iff hs] at this
        rw [← this, Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        field_simp
    have hN : N = U * R' := by
      rw [hR', ← Matrix.mul_assoc, Unitary.mul_star_self_of_mem (Subtype.prop _), Matrix.one_mul]
    rw [hN, hRV, ← Matrix.mul_assoc, hR, ← Matrix.mul_assoc,
      Unitary.mul_star_self_of_mem (Subtype.prop _), Matrix.one_mul]

end Matrix
