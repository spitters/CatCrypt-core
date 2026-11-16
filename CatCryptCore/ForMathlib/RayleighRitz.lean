/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The Rayleigh–Ritz principle and the Courant–Fischer bound

Let `T` be a symmetric operator on a finite-dimensional inner product space `E` of dimension `n`,
with eigenvalues `λ₀ ≥ λ₁ ≥ ⋯ ≥ λₙ₋₁` (`LinearMap.IsSymmetric.eigenvalues`, sorted in decreasing
order) and orthonormal eigenvector basis `eᵢ`. Then
`re ⟪T v, v⟫ = ∑ᵢ λᵢ ‖⟪eᵢ, v⟫‖²` and `‖v‖² = ∑ᵢ ‖⟪eᵢ, v⟫‖²`, from which:

* (Rayleigh 1877) the infimum of the Rayleigh quotient `re ⟪T x, x⟫ / ‖x‖²` over nonzero `x` is
  the least eigenvalue `λₙ₋₁`, attained at the eigenvector `eₙ₋₁`; the supremum is `λ₀`;
* (Courant 1920, min-max form) the `j`-th smallest eigenvalue `λₙ₋₁₋ⱼ` is the minimum, over the
  subspaces `W` of dimension `j + 1`, of the maximum of the Rayleigh quotient on `W`: every such
  `W` holds a nonzero `w` with `λₙ₋₁₋ⱼ ‖w‖² ≤ re ⟪T w, w⟫`, and the span of the `j + 1` lowest
  eigenvectors attains the bound;
* (Ritz 1909, Cauchy interlacing upper side) for a subspace `V` of dimension `m`, the compression
  `P_V T` of `T` to `V` is symmetric, and its `j`-th smallest eigenvalue is at least the `j`-th
  smallest eigenvalue of `T`, for every `j < m`.

## Main results

* `LinearMap.IsSymmetric.re_inner_apply_self_eq_sum` — the expansion of `re ⟪T v, v⟫`.
* `LinearMap.IsSymmetric.iInf_rayleigh_eq_eigenvalues_last` — the infimum of the Rayleigh
  quotient is the least eigenvalue.
* `LinearMap.IsSymmetric.exists_hasEigenvector_rayleigh_eq_iInf` — it is attained at an
  eigenvector.
* `LinearMap.IsSymmetric.iSup_rayleigh_eq_eigenvalues_zero` — the supremum is the largest
  eigenvalue.
* `LinearMap.IsSymmetric.exists_mem_eigenvalues_rev_le` and
  `LinearMap.IsSymmetric.exists_finrank_eq_forall_le_eigenvalues_rev` — the Courant–Fischer
  min-max characterisation of the `j`-th smallest eigenvalue.
* `LinearMap.IsSymmetric.eigenvalues_rev_le_compression` — the Ritz bound for the compression to
  a subspace.
-/

@[expose] public section

set_option autoImplicit false

open Module Module.End RCLike

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The compression `P_V ∘ T ∘ ι_V : V → V` of an operator `T` to a subspace `V`, with `P_V` the
orthogonal projection onto `V`. -/
noncomputable def compression (T : E →ₗ[𝕜] E) (V : Submodule 𝕜 E) [V.HasOrthogonalProjection] :
    V →ₗ[𝕜] V :=
  (V.orthogonalProjectionOnto : E →ₗ[𝕜] V) ∘ₗ T ∘ₗ V.subtype

/-- The inner product of the compression of `T` to `V` with a vector of `V` is that of `T`. -/
theorem inner_compression_apply (T : E →ₗ[𝕜] E) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (x y : V) :
    ⟪T.compression V x, y⟫ = ⟪T x, y⟫ := by
  simp [compression]

/-- The compression of a symmetric operator is symmetric. -/
theorem IsSymmetric.compression {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] : (T.compression V).IsSymmetric := by
  intro x y
  rw [inner_compression_apply, ← inner_conj_symm x (T.compression V y), inner_compression_apply,
    inner_conj_symm]
  exact hT x y

namespace IsSymmetric

variable [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} {n : ℕ}

/-- The expansion of `re ⟪T v, v⟫` in the eigenvector basis of a symmetric operator:
`re ⟪T v, v⟫ = ∑ᵢ λᵢ ‖⟪eᵢ, v⟫‖²`. -/
theorem re_inner_apply_self_eq_sum (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (v : E) :
    re ⟪T v, v⟫ = ∑ i, hT.eigenvalues hn i * ‖⟪hT.eigenvectorBasis hn i, v⟫‖ ^ 2 := by
  set e := hT.eigenvectorBasis hn
  have hterm : ∀ i, ⟪T v, e i⟫ * ⟪e i, v⟫ =
      ((hT.eigenvalues hn i * ‖⟪e i, v⟫‖ ^ 2 : ℝ) : 𝕜) := by
    intro i
    rw [hT v (e i), hT.apply_eigenvectorBasis, inner_smul_right, ← inner_conj_symm v (e i)]
    grind [RCLike.conj_mul, RCLike.ofReal_mul, RCLike.ofReal_pow]
  rw [← e.sum_inner_mul_inner (T v) v]
  simp only [hterm, map_sum, ofReal_re]

/-- A lower bound `a` on the eigenvalues at the coordinates where `v` is nonzero bounds
`re ⟪T v, v⟫` below by `a ‖v‖²`. -/
theorem mul_norm_sq_le_re_inner_of_coeff (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {a : ℝ}
    (v : E) (h : ∀ i, ⟪hT.eigenvectorBasis hn i, v⟫ ≠ 0 → a ≤ hT.eigenvalues hn i) :
    a * ‖v‖ ^ 2 ≤ re ⟪T v, v⟫ := by
  rw [hT.re_inner_apply_self_eq_sum hn, ← (hT.eigenvectorBasis hn).sum_sq_norm_inner_right v,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h0 : ⟪hT.eigenvectorBasis hn i, v⟫ = 0
  · simp [h0]
  · exact mul_le_mul_of_nonneg_right (h i h0) (by positivity)

/-- An upper bound `a` on the eigenvalues at the coordinates where `v` is nonzero bounds
`re ⟪T v, v⟫` above by `a ‖v‖²`. -/
theorem re_inner_le_mul_norm_sq_of_coeff (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {a : ℝ}
    (v : E) (h : ∀ i, ⟪hT.eigenvectorBasis hn i, v⟫ ≠ 0 → hT.eigenvalues hn i ≤ a) :
    re ⟪T v, v⟫ ≤ a * ‖v‖ ^ 2 := by
  rw [hT.re_inner_apply_self_eq_sum hn, ← (hT.eigenvectorBasis hn).sum_sq_norm_inner_right v,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h0 : ⟪hT.eigenvectorBasis hn i, v⟫ = 0
  · simp [h0]
  · exact mul_le_mul_of_nonneg_right (h i h0) (by positivity)

/-- The least eigenvalue bounds the quadratic form below: `λₙ ‖v‖² ≤ re ⟪T v, v⟫`. -/
theorem eigenvalues_last_mul_norm_sq_le (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n + 1)
    (v : E) : hT.eigenvalues hn (Fin.last n) * ‖v‖ ^ 2 ≤ re ⟪T v, v⟫ :=
  hT.mul_norm_sq_le_re_inner_of_coeff hn v fun i _ =>
    hT.eigenvalues_antitone hn (Fin.le_last i)

/-- The largest eigenvalue bounds the quadratic form above: `re ⟪T v, v⟫ ≤ λ₀ ‖v‖²`. -/
theorem re_inner_le_eigenvalues_zero_mul_norm_sq (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n + 1) (v : E) :
    re ⟪T v, v⟫ ≤ hT.eigenvalues hn 0 * ‖v‖ ^ 2 :=
  hT.re_inner_le_mul_norm_sq_of_coeff hn v fun i _ =>
    hT.eigenvalues_antitone hn (Fin.zero_le i)

/-- The Rayleigh quotient at the `i`-th eigenvector is the `i`-th eigenvalue. -/
theorem rayleigh_eigenvectorBasis (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (i : Fin n) :
    re ⟪T (hT.eigenvectorBasis hn i), hT.eigenvectorBasis hn i⟫ /
      ‖hT.eigenvectorBasis hn i‖ ^ 2 = hT.eigenvalues hn i := by
  simp [inner_smul_left, (hT.eigenvectorBasis hn).orthonormal.1 i]

/-- **Rayleigh's principle**: the infimum of the Rayleigh quotient of a symmetric operator over
the nonzero vectors is its least eigenvalue. -/
theorem iInf_rayleigh_eq_eigenvalues_last (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n + 1) :
    ⨅ x : { x : E // x ≠ 0 }, re ⟪T x, x⟫ / ‖(x : E)‖ ^ 2 = hT.eigenvalues hn (Fin.last n) := by
  set e := hT.eigenvectorBasis hn
  have he : e (Fin.last n) ≠ 0 := e.orthonormal.ne_zero _
  have hlow : ∀ x : { x : E // x ≠ 0 },
      hT.eigenvalues hn (Fin.last n) ≤ re ⟪T x, x⟫ / ‖(x : E)‖ ^ 2 := fun x =>
    (le_div_iff₀ (pow_pos (norm_pos_iff.2 x.2) 2)).2 (hT.eigenvalues_last_mul_norm_sq_le hn x)
  have : Nonempty { x : E // x ≠ 0 } := ⟨⟨_, he⟩⟩
  refine le_antisymm ?_ (le_ciInf hlow)
  calc ⨅ x : { x : E // x ≠ 0 }, re ⟪T x, x⟫ / ‖(x : E)‖ ^ 2
      ≤ re ⟪T (e (Fin.last n)), e (Fin.last n)⟫ / ‖e (Fin.last n)‖ ^ 2 :=
        ciInf_le ⟨_, Set.forall_mem_range.2 hlow⟩ (⟨_, he⟩ : { x : E // x ≠ 0 })
    _ = hT.eigenvalues hn (Fin.last n) := hT.rayleigh_eigenvectorBasis hn _

/-- The infimum of the Rayleigh quotient is attained at an eigenvector whose eigenvalue it is. -/
theorem exists_hasEigenvector_rayleigh_eq_iInf (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n + 1) :
    ∃ x : E, HasEigenvector T (hT.eigenvalues hn (Fin.last n) : 𝕜) x ∧
      re ⟪T x, x⟫ / ‖x‖ ^ 2 = ⨅ y : { y : E // y ≠ 0 }, re ⟪T y, y⟫ / ‖(y : E)‖ ^ 2 := by
  refine ⟨hT.eigenvectorBasis hn (Fin.last n), hT.hasEigenvector_eigenvectorBasis hn _, ?_⟩
  rw [hT.iInf_rayleigh_eq_eigenvalues_last hn, hT.rayleigh_eigenvectorBasis hn]

/-- The supremum of the Rayleigh quotient of a symmetric operator over the nonzero vectors is
its largest eigenvalue. -/
theorem iSup_rayleigh_eq_eigenvalues_zero (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n + 1) :
    ⨆ x : { x : E // x ≠ 0 }, re ⟪T x, x⟫ / ‖(x : E)‖ ^ 2 = hT.eigenvalues hn 0 := by
  set e := hT.eigenvectorBasis hn
  have he : e 0 ≠ 0 := e.orthonormal.ne_zero _
  have hup : ∀ x : { x : E // x ≠ 0 },
      re ⟪T x, x⟫ / ‖(x : E)‖ ^ 2 ≤ hT.eigenvalues hn 0 := fun x =>
    (div_le_iff₀ (pow_pos (norm_pos_iff.2 x.2) 2)).2
      (hT.re_inner_le_eigenvalues_zero_mul_norm_sq hn x)
  have : Nonempty { x : E // x ≠ 0 } := ⟨⟨_, he⟩⟩
  refine le_antisymm (ciSup_le hup) ?_
  calc hT.eigenvalues hn 0 = re ⟪T (e 0), e 0⟫ / ‖e 0‖ ^ 2 :=
        (hT.rayleigh_eigenvectorBasis hn _).symm
    _ ≤ ⨆ x : { x : E // x ≠ 0 }, re ⟪T x, x⟫ / ‖(x : E)‖ ^ 2 :=
        le_ciSup ⟨_, Set.forall_mem_range.2 hup⟩ (⟨_, he⟩ : { x : E // x ≠ 0 })

/-- A vector in the span of the eigenvectors `eₗ`, `l ∈ s`, is orthogonal to `eᵢ` for `i ∉ s`. -/
theorem inner_eigenvectorBasis_eq_zero_of_mem_span (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (s : Finset (Fin n)) {w : E}
    (hw : w ∈ Submodule.span 𝕜 (Set.range fun l : s => hT.eigenvectorBasis hn l))
    {i : Fin n} (hi : i ∉ s) : ⟪hT.eigenvectorBasis hn i, w⟫ = 0 := by
  have hle : Submodule.span 𝕜 (Set.range fun l : s => hT.eigenvectorBasis hn l) ≤
      LinearMap.ker (innerₛₗ 𝕜 (hT.eigenvectorBasis hn i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    have hne : i ≠ l := fun h => hi (h ▸ l.2)
    simpa using (hT.eigenvectorBasis hn).orthonormal.2 hne
  simpa using hle hw

/-- The span of the eigenvectors `eₗ`, `l ∈ s`, has dimension `#s`. -/
theorem finrank_span_eigenvectorBasis (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (s : Finset (Fin n)) :
    finrank 𝕜 (Submodule.span 𝕜 (Set.range fun l : s => hT.eigenvectorBasis hn l)) = s.card := by
  exact (finrank_span_eq_card (b := fun l : s => hT.eigenvectorBasis hn l)
    ((hT.eigenvectorBasis hn).orthonormal.linearIndependent.comp _ Subtype.val_injective)).trans
    (by simp)

/-- **Courant–Fischer**, lower half of the min-max: every subspace `W` of dimension at least
`j + 1` holds a nonzero `w` whose Rayleigh quotient is at least the `j`-th smallest eigenvalue
`λ_{rev j}`. -/
theorem exists_mem_eigenvalues_rev_le (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (W : Submodule 𝕜 E) (j : Fin n) (hW : (j : ℕ) + 1 ≤ finrank 𝕜 W) :
    ∃ w ∈ W, w ≠ 0 ∧ hT.eigenvalues hn j.rev * ‖w‖ ^ 2 ≤ re ⟪T w, w⟫ := by
  set s : Finset (Fin n) := Finset.Iic j.rev
  set U := Submodule.span 𝕜 (Set.range fun l : s => hT.eigenvectorBasis hn l)
  have hU : finrank 𝕜 U = n - j := by
    rw [hT.finrank_span_eigenvectorBasis hn s, Fin.card_Iic, Fin.val_rev]
    omega
  have hnd : ¬ Disjoint W U := by
    intro hd
    have := Submodule.finrank_add_finrank_le_of_disjoint hd
    omega
  obtain ⟨w, hwW, hwU, hw0⟩ : ∃ w, w ∈ W ∧ w ∈ U ∧ w ≠ 0 := by
    by_contra! h
    exact hnd (Submodule.disjoint_def.2 fun w hwW hwU => h w hwW hwU)
  refine ⟨w, hwW, hw0, hT.mul_norm_sq_le_re_inner_of_coeff hn w fun i hi => ?_⟩
  have hij : i ≤ j.rev := by
    by_contra hlt
    exact hi (hT.inner_eigenvectorBasis_eq_zero_of_mem_span hn s hwU (by simpa [s] using hlt))
  exact hT.eigenvalues_antitone hn hij

/-- **Courant–Fischer**, upper half of the min-max: the span of the `j + 1` lowest eigenvectors
is a subspace of dimension `j + 1` on which the Rayleigh quotient is at most the `j`-th smallest
eigenvalue `λ_{rev j}`. -/
theorem exists_finrank_eq_forall_le_eigenvalues_rev (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (j : Fin n) :
    ∃ W : Submodule 𝕜 E, finrank 𝕜 W = (j : ℕ) + 1 ∧
      ∀ w ∈ W, re ⟪T w, w⟫ ≤ hT.eigenvalues hn j.rev * ‖w‖ ^ 2 := by
  set s : Finset (Fin n) := Finset.Ici j.rev
  refine ⟨Submodule.span 𝕜 (Set.range fun l : s => hT.eigenvectorBasis hn l), ?_, ?_⟩
  · rw [hT.finrank_span_eigenvectorBasis hn s, Fin.card_Ici, Fin.val_rev]
    omega
  · intro w hw
    refine hT.re_inner_le_mul_norm_sq_of_coeff hn w fun i hi => ?_
    have hij : j.rev ≤ i := by
      by_contra hlt
      exact hi (hT.inner_eigenvectorBasis_eq_zero_of_mem_span hn s hw (by simpa [s] using hlt))
    exact hT.eigenvalues_antitone hn hij

/-- **The Ritz bound** (Cauchy interlacing, upper side): for a subspace `V` of dimension `m`,
the `j`-th smallest eigenvalue of the compression of `T` to `V` is at least the `j`-th smallest
eigenvalue of `T`, for every `j < m`. -/
theorem eigenvalues_rev_le_compression (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (V : Submodule 𝕜 E) {m : ℕ} (hm : finrank 𝕜 V = m) (hmn : m ≤ n) (j : Fin m) :
    hT.eigenvalues hn (Fin.castLE hmn j).rev ≤
      (hT.compression V).eigenvalues hm j.rev := by
  obtain ⟨W, hWdim, hW⟩ := (hT.compression V).exists_finrank_eq_forall_le_eigenvalues_rev hm j
  have hWE : (j : ℕ) + 1 ≤ finrank 𝕜 (W.map V.subtype) := by
    rw [Submodule.finrank_map_subtype_eq, hWdim]
  obtain ⟨w, hwW, hw0, hle⟩ :=
    hT.exists_mem_eigenvalues_rev_le hn (W.map V.subtype) (Fin.castLE hmn j) hWE
  obtain ⟨v, hvW, rfl⟩ := Submodule.mem_map.1 hwW
  have hv := hW v hvW
  rw [inner_compression_apply] at hv
  have hv0 : 0 < ‖(v : E)‖ ^ 2 := pow_pos (norm_pos_iff.2 hw0) 2
  have hnorm : ‖v‖ = ‖(v : E)‖ := rfl
  rw [hnorm] at hv
  have := hle.trans hv
  exact le_of_mul_le_mul_right this hv0

end IsSymmetric

end LinearMap
