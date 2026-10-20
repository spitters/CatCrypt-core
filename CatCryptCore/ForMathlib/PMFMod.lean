/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Probability.Distributions.Uniform

/-!
# Reduction modulo `M` of a uniform value below `N`

The reduction modulo `M` of a uniform value in `Fin N` puts mass at least
`(1 - M/N)·(1/M)` on every residue: each residue has at least `N / M` preimages.

## Main results

* `Fin.div_le_card_filter_mod_eq` — every residue `r < M` has at least `N / M`
  preimages in `Fin N` under reduction modulo `M`
* `PMF.one_sub_mul_uniform_le_map_mod` — the pointwise minorant
  `(1 - M/N)·U_M r ≤ (U_N.map (· mod M)) r`
* `ENNReal.one_sub_div_mul_inv_le` — `(1 - M/N)·(1/M) ≤ c/N` when `N ≤ c·M + M`
* `ENNReal.one_sub_mul_le_pow` — Bernoulli's inequality `1 - m·β ≤ (1 - β)^m`

They belong in `Mathlib/Probability/Distributions/Uniform.lean`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

/-- Reduction modulo `M` from `Fin N` to `Fin M`. -/
def Fin.modTo (N M : ℕ) [NeZero M] (x : Fin N) : Fin M :=
  ⟨x.val % M, Nat.mod_lt _ (NeZero.pos M)⟩

/-- Every residue `r < M` has at least `N / M` preimages in `Fin N` under reduction
modulo `M`: the values `r + M·j` for `j < N / M`. -/
theorem Fin.div_le_card_filter_mod_eq (N M : ℕ) [NeZero M] (r : Fin M) :
    N / M ≤ (Finset.univ.filter fun x : Fin N => Fin.modTo N M x = r).card := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [hN]
  have hlt : ∀ j < N / M, r.val + M * j < N := fun j hj => by
    have h1 : (j + 1) * M ≤ N := (Nat.le_div_iff_mul_le (NeZero.pos M)).mp hj
    have h2 := r.isLt
    nlinarith
  rw [← Finset.card_range (N / M)]
  refine Finset.card_le_card_of_injOn (fun j => (⟨(r.val + M * j) % N, Nat.mod_lt _ hN⟩ : Fin N))
    ?_ ?_
  · intro j hj
    have hj' := hlt j (Finset.mem_range.mp hj)
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    ext
    simp [Fin.modTo, Nat.mod_eq_of_lt hj', Nat.mod_eq_of_lt r.isLt]
  · intro j hj j' hj' h
    have h1 := hlt j (Finset.mem_range.mp hj)
    have h2 := hlt j' (Finset.mem_range.mp hj')
    simp only [Fin.mk.injEq, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h
    exact Nat.eq_of_mul_eq_mul_left (NeZero.pos M) (by omega)

/-- An arithmetic bound: if `N ≤ c·M + M` then `(1 - M/N)·(1/M) ≤ c/N`. -/
theorem ENNReal.one_sub_div_mul_inv_le {N M c : ℕ} (hN : 0 < N) (hM : 0 < M)
    (h : N ≤ c * M + M) :
    (1 - (M : ℝ≥0∞) / N) * (M : ℝ≥0∞)⁻¹ ≤ (c : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹ := by
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by simp; omega
  have hM0 : (M : ℝ≥0∞) ≠ 0 := by simp; omega
  rcases le_or_gt N M with hNM | hMN
  · have h1 : (1 : ℝ≥0∞) ≤ (M : ℝ≥0∞) / N := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hN0) (Or.inl (by simp)), one_mul]
      exact_mod_cast hNM
    simp [tsub_eq_zero_of_le h1]
  · have hsub : N - M ≤ c * M := by omega
    have h1 : 1 - (M : ℝ≥0∞) / N = ((N - M : ℕ) : ℝ≥0∞) / N := by
      rw [ENNReal.natCast_sub, ENNReal.sub_div (fun _ _ => hN0),
        ENNReal.div_self hN0 (by simp)]
    rw [h1]
    calc ((N - M : ℕ) : ℝ≥0∞) / N * (M : ℝ≥0∞)⁻¹
        ≤ ((c * M : ℕ) : ℝ≥0∞) / N * (M : ℝ≥0∞)⁻¹ := by gcongr
      _ = (c : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹ * ((M : ℝ≥0∞) * (M : ℝ≥0∞)⁻¹) := by
          rw [Nat.cast_mul, div_eq_mul_inv]; ring
      _ = (c : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹ := by rw [ENNReal.mul_inv_cancel hM0 (by simp), mul_one]

/-- Bernoulli's inequality with truncated subtraction: `1 - m·β ≤ (1 - β)^m`. -/
theorem ENNReal.one_sub_mul_le_pow (β : ℝ≥0∞) (m : ℕ) : 1 - (m : ℝ≥0∞) * β ≤ (1 - β) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hfin : 1 - (m : ℝ≥0∞) * β ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
    calc 1 - ((m + 1 : ℕ) : ℝ≥0∞) * β = 1 - (m : ℝ≥0∞) * β - β := by
          rw [tsub_tsub, Nat.cast_succ, add_mul, one_mul]
      _ ≤ (1 - (m : ℝ≥0∞) * β) * 1 - (1 - (m : ℝ≥0∞) * β) * β := by
          rw [mul_one]
          exact tsub_le_tsub_left (mul_le_of_le_one_left' tsub_le_self) _
      _ = (1 - (m : ℝ≥0∞) * β) * (1 - β) := (ENNReal.mul_sub fun _ _ => hfin).symm
      _ ≤ (1 - β) ^ m * (1 - β) := by gcongr
      _ = (1 - β) ^ (m + 1) := (pow_succ _ _).symm

namespace PMF

/-- **Reduction modulo `M` of a uniform value.** For `N, M ≥ 1`, the image of the
uniform distribution on `Fin N` under reduction modulo `M` puts mass at least
`(1 - M/N)·(1/M)` on every residue. -/
theorem one_sub_mul_uniform_le_map_mod (N M : ℕ) [NeZero N] [NeZero M] (r : Fin M) :
    (1 - (M : ℝ≥0∞) / N) * PMF.uniformOfFintype (Fin M) r ≤
      (PMF.uniformOfFintype (Fin N)).map (Fin.modTo N M) r := by
  have hcard : (PMF.uniformOfFintype (Fin N)).map (Fin.modTo N M) r =
      ((Finset.univ.filter fun x : Fin N => Fin.modTo N M x = r).card : ℝ≥0∞) *
        (N : ℝ≥0∞)⁻¹ := by
    rw [PMF.map_apply, tsum_fintype]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    simp only [eq_comm]
  rw [hcard, PMF.uniformOfFintype_apply, Fintype.card_fin]
  refine (ENNReal.one_sub_div_mul_inv_le (c := N / M) (NeZero.pos N) (NeZero.pos M) ?_).trans ?_
  · exact (Nat.lt_div_mul_add (NeZero.pos M)).le
  · gcongr
    exact_mod_cast Fin.div_le_card_filter_mod_eq N M r

end PMF
