/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The rotation calculus of `SU(2)`

The group `SU(2)` of `2 × 2` complex unitary matrices of determinant one, written in axis-angle
form: every element is `rot n θ = cos (θ / 2) • 1 - i sin (θ / 2) • (n · σ)` for a unit vector
`n ∈ ℝ³` and an angle `θ ∈ [0, 2π]`, where `n · σ = n₀ X + n₁ Y + n₂ Z` is the combination of the
Pauli matrices. Matrices carry the `ℓ²` operator norm (`Matrix.Norms.L2Operator`).

This is the toolkit of the Solovay–Kitaev theorem (Dawson–Nielsen 2005, §3; Nielsen–Chuang,
Appendix 3).

## Main results

* `SolovayKitaev.exists_rot_eq` — the axis-angle form of an element of `SU(2)`.
* `SolovayKitaev.norm_rot_sub_one` — `‖rot n θ - 1‖ = 2 |sin (θ / 4)|`.
* `SolovayKitaev.conj_rot` — conjugation by `V` rotates the axis by the adjoint map `adSO3 V`.
* `SolovayKitaev.exists_conj_of_trace_eq` — two elements of `SU(2)` with equal traces are
  conjugate in `SU(2)`.

## References

* C. M. Dawson, M. A. Nielsen, *The Solovay–Kitaev algorithm*, Quantum Inf. Comput. 6 (2006).
* M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information*, Appendix 3.
-/

@[expose] public section

set_option autoImplicit false

open Complex Matrix
open scoped Matrix.Norms.L2Operator

namespace SolovayKitaev

/-- The special unitary group `SU(2)` of `2 × 2` complex matrices. -/
abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- The Pauli matrix `X`. -/
def σx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli matrix `Y`. -/
def σy : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- The Pauli matrix `Z`. -/
def σz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Pauli matrices `X`, `Y`, `Z` indexed by `Fin 3`. -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := ![σx, σy, σz]

/-- The combination `n · σ = n₀ X + n₁ Y + n₂ Z` of the Pauli matrices. -/
def pauliVec (n : EuclideanSpace ℝ (Fin 3)) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i, (n i : ℂ) • pauli i

/-- Rotation by `θ` about the axis `n`: `cos (θ / 2) • 1 - i sin (θ / 2) • (n · σ)`. -/
noncomputable def rot (n : EuclideanSpace ℝ (Fin 3)) (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos (θ / 2) : ℂ) • 1 - (I * Real.sin (θ / 2)) • pauliVec n

/-- The adjoint action of `V ∈ SU(2)` on `ℝ³`: the `i`-th component of `adSO3 V n` is
`Re tr (σᵢ V (n · σ) V†) / 2`, so that `V (n · σ) V† = adSO3 V n · σ`. -/
noncomputable def adSO3 (V : SU2) (n : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun i =>
    (trace (pauli i * ((V : Matrix (Fin 2) (Fin 2) ℂ) * pauliVec n * star (V : Matrix _ _ ℂ)))).re
      / 2

/-- The Pauli combination `n · σ` is traceless. -/
theorem trace_pauliVec (n : EuclideanSpace ℝ (Fin 3)) : trace (pauliVec n) = 0 := by
  simp [pauliVec, pauli, σx, σy, σz, Fin.sum_univ_three, trace_fin_two]

/-- The trace of a rotation by `θ` is `2 cos (θ / 2)`. -/
theorem trace_rot (n : EuclideanSpace ℝ (Fin 3)) (θ : ℝ) :
    trace (rot n θ) = 2 * Real.cos (θ / 2) := by
  simp [rot, trace_sub, trace_smul, trace_pauliVec]
  ring

/-- The rotation by angle `0` is the identity. -/
theorem rot_zero (n : EuclideanSpace ℝ (Fin 3)) : rot n 0 = 1 := by
  simp [rot]

private lemma pauliVec_eq (n : EuclideanSpace ℝ (Fin 3)) :
    pauliVec n = !![(n 2 : ℂ), (n 0 : ℂ) - I * (n 1 : ℂ);
      (n 0 : ℂ) + I * (n 1 : ℂ), -(n 2 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliVec, pauli, σx, σy, σz, Fin.sum_univ_three] <;> ring

private lemma sumsq_of_norm {n : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1) :
    n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at hn
  simpa [Fin.sum_univ_three] using hn

private lemma norm_of_sumsq {n : EuclideanSpace ℝ (Fin 3)}
    (h : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) : ‖n‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simpa [Fin.sum_univ_three] using h

private lemma herm_traceless_eq {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : star A = A)
    (ht : trace A = 0) :
    A = pauliVec (WithLp.toLp 2 fun i => (trace (pauli i * A)).re / 2) := by
  rw [pauliVec_eq]
  have h00 := congrFun (congrFun hA 0) 0
  have h01 := congrFun (congrFun hA 0) 1
  have h11 := congrFun (congrFun hA 1) 1
  rw [trace_fin_two] at ht
  simp only [Matrix.star_apply, Complex.star_def, Complex.ext_iff, Complex.conj_re,
    Complex.conj_im] at h00 h01 h11
  have e01 : A 1 0 = (starRingEnd ℂ) (A 0 1) := by
    simpa [Matrix.star_apply] using (congrFun (congrFun hA 1) 0).symm
  have e11 : A 1 1 = -A 0 0 := by linear_combination ht
  have t0 : trace (pauli 0 * A) = A 1 0 + A 0 1 := by
    rw [Matrix.eta_fin_two A]
    simp [pauli, σx, trace_fin_two]
  have t1 : trace (pauli 1 * A) = -I * A 1 0 + I * A 0 1 := by
    rw [Matrix.eta_fin_two A]
    simp [pauli, σy, trace_fin_two]
  have t2 : trace (pauli 2 * A) = A 0 0 - A 1 1 := by
    rw [Matrix.eta_fin_two A]
    simp [pauli, σz, trace_fin_two]
    ring
  obtain ⟨hr0, hi0⟩ := h00
  obtain ⟨hr1, hi1⟩ := h01
  ext i j
  fin_cases i <;> fin_cases j <;> simp [t0, t1, t2, e01, e11, Complex.ext_iff] <;>
    linarith

private lemma star_pauliVec (n : EuclideanSpace ℝ (Fin 3)) : star (pauliVec n) = pauliVec n := by
  rw [pauliVec_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply, Complex.ext_iff]

private lemma star_mul_self (V : SU2) :
    star (V : Matrix (Fin 2) (Fin 2) ℂ) * (V : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp V.2).1

private lemma mul_star_self (V : SU2) :
    (V : Matrix (Fin 2) (Fin 2) ℂ) * star (V : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
  Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp V.2).1

private lemma conj_pauliVec (V : SU2) (n : EuclideanSpace ℝ (Fin 3)) :
    (V : Matrix (Fin 2) (Fin 2) ℂ) * pauliVec n * star (V : Matrix (Fin 2) (Fin 2) ℂ) =
      pauliVec (adSO3 V n) := by
  refine herm_traceless_eq ?_ ?_
  · simp [StarMul.star_mul, star_pauliVec, Matrix.mul_assoc]
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, star_mul_self, Matrix.one_mul, trace_pauliVec]

private lemma det_pauliVec (m : EuclideanSpace ℝ (Fin 3)) :
    (pauliVec m).det = -((m 0 ^ 2 + m 1 ^ 2 + m 2 ^ 2 : ℝ) : ℂ) := by
  rw [pauliVec_eq, Matrix.det_fin_two_of]
  push_cast
  linear_combination (m 1 : ℂ) ^ 2 * Complex.I_sq

private lemma det_star_mul (V : SU2) :
    ((V : Matrix (Fin 2) (Fin 2) ℂ).det = 1) :=
  (Matrix.mem_specialUnitaryGroup_iff.mp V.2).2

private lemma sumsq_aux (n : EuclideanSpace ℝ (Fin 3)) :
    ‖n‖ ^ 2 = n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three]

private lemma gram_rot_sub_one {n : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1) (θ : ℝ) :
    star (rot n θ - 1) * (rot n θ - 1) =
      ((2 - 2 * Real.cos (θ / 2) : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h := sumsq_of_norm hn
  have hC : ((n 0 : ℝ) : ℂ) ^ 2 + ((n 1 : ℝ) : ℂ) ^ 2 + ((n 2 : ℝ) : ℂ) ^ 2 = 1 := by
    simpa using congrArg (fun x : ℝ => (x : ℂ)) h
  have hs : ((Real.sin (θ / 2) : ℝ) : ℂ) ^ 2 + ((Real.cos (θ / 2) : ℝ) : ℂ) ^ 2 = 1 := by
    simp
  clear h hn
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, pauliVec_eq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
      -Complex.ofReal_cos, -Complex.ofReal_sin, Complex.conj_ofReal] <;>
    grind [Complex.I_sq, div_eq_mul_inv]

private lemma exists_angle (x : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 2 * Real.pi ∧ Real.cos (θ / 2) = x ∧
      Real.sin (θ / 2) = Real.sqrt (1 - x ^ 2) := by
  refine ⟨2 * Real.arccos x, by linarith [Real.arccos_nonneg x],
    by linarith [Real.arccos_le_pi x], ?_, ?_⟩
  · rw [mul_div_cancel_left₀ _ two_ne_zero]
    exact Real.cos_arccos h1 h2
  · rw [mul_div_cancel_left₀ _ two_ne_zero]
    exact Real.sin_arccos x

private lemma exists_rot_of_entries (a b : ℂ)
    (h : a.re ^ 2 + a.im ^ 2 + b.re ^ 2 + b.im ^ 2 = 1) :
    ∃ (n : EuclideanSpace ℝ (Fin 3)) (θ : ℝ), ‖n‖ = 1 ∧ 0 ≤ θ ∧ θ ≤ 2 * Real.pi ∧
      !![a, b; -(starRingEnd ℂ) b, (starRingEnd ℂ) a] = rot n θ := by
  have hx1 : -1 ≤ a.re := by nlinarith [sq_nonneg a.im, sq_nonneg b.re, sq_nonneg b.im]
  have hx2 : a.re ≤ 1 := by nlinarith [sq_nonneg a.im, sq_nonneg b.re, sq_nonneg b.im]
  obtain ⟨θ, hθ0, hθ1, hc, hs⟩ := exists_angle a.re hx1 hx2
  have hs2 : Real.sqrt (1 - a.re ^ 2) ^ 2 = a.im ^ 2 + b.re ^ 2 + b.im ^ 2 := by
    rw [Real.sq_sqrt (by nlinarith [sq_nonneg a.im, sq_nonneg b.re, sq_nonneg b.im])]
    linarith
  by_cases h0 : Real.sqrt (1 - a.re ^ 2) = 0
  · rw [h0] at hs2
    have p1 := sq_nonneg a.im
    have p2 := sq_nonneg b.re
    have p3 := sq_nonneg b.im
    have hai : a.im = 0 := by nlinarith
    have hbr : b.re = 0 := by nlinarith
    have hbi : b.im = 0 := by nlinarith
    refine ⟨WithLp.toLp 2 ![0, 0, 1], θ, ?_, hθ0, hθ1, ?_⟩
    · exact norm_of_sumsq (by simp)
    · have ha : a = (a.re : ℂ) := Complex.ext (by simp) (by simp [hai])
      have hb : b = 0 := Complex.ext (by simp [hbr]) (by simp [hbi])
      rw [hb, ha]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [rot, pauliVec_eq, hs, hc, h0, -Complex.ofReal_cos, -Complex.ofReal_sin]
  · generalize Real.sqrt (1 - a.re ^ 2) = s at *
    refine ⟨WithLp.toLp 2 ![-b.im / s, -b.re / s, -a.im / s], θ, ?_, hθ0, hθ1, ?_⟩
    · refine norm_of_sumsq ?_
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, div_pow, neg_sq]
      field_simp
      linarith
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [rot, pauliVec_eq, hs, hc, Fin.zero_eta, Fin.isValue, Fin.mk_one,
          Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one] <;>
        apply Complex.ext <;> simp <;> field_simp

private lemma pauliVec_mul_self {n : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1) :
    pauliVec n * pauliVec n = 1 := by
  have h := sumsq_of_norm hn
  have hC : ((n 0 : ℝ) : ℂ) ^ 2 + ((n 1 : ℝ) : ℂ) ^ 2 + ((n 2 : ℝ) : ℂ) ^ 2 = 1 := by
    simpa using congrArg (fun x : ℝ => (x : ℂ)) h
  clear h hn
  rw [pauliVec_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    grind [Complex.I_sq]

private lemma pauliVec_anticomm (n m : EuclideanSpace ℝ (Fin 3)) :
    pauliVec n * pauliVec m + pauliVec m * pauliVec n =
      ((2 * (n 0 * m 0 + n 1 * m 1 + n 2 * m 2) : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [pauliVec_eq, pauliVec_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp <;>
    grind [Complex.I_sq]

private lemma det_one_add_fin_two (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (1 + X).det = 1 + X.trace + X.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, trace_fin_two]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, Fin.isValue,
    zero_ne_one, not_false_eq_true, one_ne_zero, zero_add]
  ring

private lemma exists_conj_vec {n m : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    (hd : n 0 * m 0 + n 1 * m 1 + n 2 * m 2 ≠ -1) :
    ∃ S : SU2, (S : Matrix (Fin 2) (Fin 2) ℂ) * pauliVec n * star (S : Matrix (Fin 2) (Fin 2) ℂ) =
      pauliVec m := by
  have hn' := sumsq_of_norm hn
  have hm' := sumsq_of_norm hm
  obtain ⟨d, hdd⟩ : ∃ d : ℝ, d = n 0 * m 0 + n 1 * m 1 + n 2 * m 2 := ⟨_, rfl⟩
  rw [← hdd] at hd
  have hge : -1 ≤ d := by
    nlinarith [sq_nonneg (n 0 + m 0), sq_nonneg (n 1 + m 1), sq_nonneg (n 2 + m 2)]
  have hpos : 0 < 2 + 2 * d := by
    have := lt_of_le_of_ne hge (Ne.symm hd)
    linarith
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 2 = 2 + 2 * d :=
    ⟨Real.sqrt (2 + 2 * d), Real.sqrt_pos.mpr hpos, Real.sq_sqrt hpos.le⟩
  have hN := pauliVec_mul_self hn
  have hM := pauliVec_mul_self hm
  have hanti := pauliVec_anticomm n m
  rw [← hdd] at hanti
  have hMS : pauliVec m * (1 + pauliVec m * pauliVec n) =
      (1 + pauliVec m * pauliVec n) * pauliVec n := by
    rw [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, hM, Matrix.mul_assoc, hN]
    simp only [Matrix.mul_one, Matrix.one_mul]
    exact add_comm _ _
  have hstar0 : star (1 + pauliVec m * pauliVec n) = 1 + pauliVec n * pauliVec m := by
    rw [star_add, star_one, StarMul.star_mul, star_pauliVec, star_pauliVec]
  have hgram : star (1 + pauliVec m * pauliVec n) * (1 + pauliVec m * pauliVec n) =
      ((r : ℂ) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    have e : ((r : ℂ) ^ 2) = 2 + ((2 * d : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, hr]; push_cast; ring
    rw [hstar0, e, add_smul, two_smul]
    calc (1 + pauliVec n * pauliVec m) * (1 + pauliVec m * pauliVec n)
        = 1 + (pauliVec n * pauliVec m + pauliVec m * pauliVec n) +
            pauliVec n * (pauliVec m * pauliVec m) * pauliVec n := by
          noncomm_ring
      _ = _ := by rw [hM, Matrix.mul_one, hN, hanti]; abel
  have hdet : (1 + pauliVec m * pauliVec n).det = (r : ℂ) ^ 2 := by
    have htr : (pauliVec m * pauliVec n).trace = ((2 * d : ℝ) : ℂ) := by
      have := congrArg Matrix.trace hanti
      rw [Matrix.trace_add, Matrix.trace_mul_comm (pauliVec m), Matrix.trace_smul,
        Matrix.trace_one] at this
      simp only [Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul] at this
      linear_combination this / 2 + Matrix.trace_mul_comm (pauliVec m) (pauliVec n)
    rw [det_one_add_fin_two, htr, Matrix.det_mul, det_pauliVec, det_pauliVec, hn', hm']
    rw [← Complex.ofReal_pow, hr]; push_cast; ring
  generalize 1 + pauliVec m * pauliVec n = S0 at *
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
  have hinv : (r : ℂ)⁻¹ * (r : ℂ)⁻¹ * (r : ℂ) ^ 2 = 1 := by field_simp
  have hstarS : star ((r : ℂ)⁻¹ • S0) = (r : ℂ)⁻¹ • star S0 := by
    rw [star_smul]; simp
  have h1 : star ((r : ℂ)⁻¹ • S0) * ((r : ℂ)⁻¹ • S0) = 1 := by
    rw [hstarS, Matrix.smul_mul, Matrix.mul_smul, hgram, smul_smul, smul_smul, hinv, one_smul]
  have hdetS : ((r : ℂ)⁻¹ • S0).det = 1 := by
    rw [Matrix.det_smul, hdet]
    simp only [Fintype.card_fin]
    field_simp
  have hSmem : (r : ℂ)⁻¹ • S0 ∈ specialUnitaryGroup (Fin 2) ℂ :=
    Matrix.mem_specialUnitaryGroup_iff.mpr ⟨⟨h1, mul_eq_one_comm.mp h1⟩, hdetS⟩
  refine ⟨⟨_, hSmem⟩, ?_⟩
  change ((r : ℂ)⁻¹ • S0) * pauliVec n * star ((r : ℂ)⁻¹ • S0) = pauliVec m
  have hMS' : pauliVec m * ((r : ℂ)⁻¹ • S0) = ((r : ℂ)⁻¹ • S0) * pauliVec n := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hMS]
  rw [← hMS', Matrix.mul_assoc, mul_eq_one_comm.mp h1, Matrix.mul_one]

private lemma exists_conj_vec_all {n m : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1)
    (hm : ‖m‖ = 1) :
    ∃ S : SU2, (S : Matrix (Fin 2) (Fin 2) ℂ) * pauliVec n * star (S : Matrix (Fin 2) (Fin 2) ℂ) =
      pauliVec m := by
  by_cases hd : n 0 * m 0 + n 1 * m 1 + n 2 * m 2 = -1
  swap
  · exact exists_conj_vec hn hm hd
  have hn' := sumsq_of_norm hn
  have hm' := sumsq_of_norm hm
  have q0 := sq_nonneg (n 0 + m 0)
  have q1 := sq_nonneg (n 1 + m 1)
  have q2 := sq_nonneg (n 2 + m 2)
  have e0 : m 0 = -n 0 := by nlinarith
  have e1 : m 1 = -n 1 := by nlinarith
  obtain ⟨w, hw, hwn, hwm⟩ : ∃ w : EuclideanSpace ℝ (Fin 3), ‖w‖ = 1 ∧
      n 0 * w 0 + n 1 * w 1 + n 2 * w 2 ≠ -1 ∧ w 0 * m 0 + w 1 * m 1 + w 2 * m 2 ≠ -1 := by
    by_cases h0 : n 0 = 1 ∨ n 0 = -1
    · have h1 : n 1 = 0 := by
        rcases h0 with h0 | h0 <;> rw [h0] at hn' <;> nlinarith [sq_nonneg (n 1), sq_nonneg (n 2)]
      refine ⟨WithLp.toLp 2 ![0, 1, 0], norm_of_sumsq (by simp), ?_, ?_⟩ <;> simp [h1, e1]
    · push Not at h0
      refine ⟨WithLp.toLp 2 ![1, 0, 0], norm_of_sumsq (by simp), ?_, ?_⟩
      · simpa using h0.2
      · simpa [e0] using h0.1
  obtain ⟨S1, h1⟩ := exists_conj_vec hn hw hwn
  obtain ⟨S2, h2⟩ := exists_conj_vec hw hm hwm
  refine ⟨S2 * S1, ?_⟩
  change ((S2 : Matrix (Fin 2) (Fin 2) ℂ) * (S1 : Matrix (Fin 2) (Fin 2) ℂ)) * pauliVec n *
    star ((S2 : Matrix (Fin 2) (Fin 2) ℂ) * (S1 : Matrix (Fin 2) (Fin 2) ℂ)) = pauliVec m
  rw [StarMul.star_mul, ← h2, ← h1]
  simp only [Matrix.mul_assoc]

/-- A rotation about a unit axis lies in `SU(2)`. -/
theorem rot_mem_specialUnitaryGroup {n : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1) (θ : ℝ) :
    rot n θ ∈ specialUnitaryGroup (Fin 2) ℂ := by
  have h := sumsq_of_norm hn
  have hc := Real.sin_sq_add_cos_sq (θ / 2)
  have hC : ((n 0 : ℝ) : ℂ) ^ 2 + ((n 1 : ℝ) : ℂ) ^ 2 + ((n 2 : ℝ) : ℂ) ^ 2 = 1 := by
    simpa using congrArg (fun x : ℝ => (x : ℂ)) h
  have hs : ((Real.sin (θ / 2) : ℝ) : ℂ) ^ 2 + ((Real.cos (θ / 2) : ℝ) : ℂ) ^ 2 = 1 := by
    simp
  clear h hc hn
  rw [mem_specialUnitaryGroup_iff]
  have h1 : star (rot n θ) * rot n θ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rot, pauliVec_eq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
        -Complex.ofReal_cos, -Complex.ofReal_sin, Complex.conj_ofReal] <;>
      grind [Complex.I_sq, div_eq_mul_inv]
  refine ⟨⟨h1, mul_eq_one_comm.mp h1⟩, ?_⟩
  · simp only [rot, pauliVec_eq, Matrix.det_fin_two]
    simp [-Complex.ofReal_cos, -Complex.ofReal_sin]
    grind [Complex.I_sq, div_eq_mul_inv]

/-- **Axis-angle form.** Every element of `SU(2)` is a rotation by an angle `θ ∈ [0, 2π]` about
a unit axis. -/
theorem exists_rot_eq (U : SU2) :
    ∃ (n : EuclideanSpace ℝ (Fin 3)) (θ : ℝ), ‖n‖ = 1 ∧ 0 ≤ θ ∧ θ ≤ 2 * Real.pi ∧
      (U : Matrix (Fin 2) (Fin 2) ℂ) = rot n θ := by
  have hadj : star (U : Matrix (Fin 2) (Fin 2) ℂ) = (U : Matrix (Fin 2) (Fin 2) ℂ).adjugate := by
    calc star (U : Matrix (Fin 2) (Fin 2) ℂ)
        = star (U : Matrix (Fin 2) (Fin 2) ℂ) *
            ((U : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ).adjugate) := by
          rw [Matrix.mul_adjugate, det_star_mul, one_smul, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, star_mul_self, Matrix.one_mul]
  have e00 := congrFun (congrFun hadj 0) 0
  have e10 := congrFun (congrFun hadj 0) 1
  simp only [Matrix.star_apply, Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.star_def] at e00 e10
  have hn := congrFun (congrFun (mul_star_self U) 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply_eq,
    Complex.star_def, Complex.mul_conj] at hn
  have hn' := congrArg Complex.re hn
  simp only [Complex.add_re, Complex.normSq_apply] at hn'
  obtain ⟨n, θ, h1, h2, h3, h4⟩ := exists_rot_of_entries
    ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 1) (by
    simp only [Complex.ofReal_re, Complex.one_re] at hn'
    linarith)
  refine ⟨n, θ, h1, h2, h3, ?_⟩
  rw [← h4]
  have e11 : (U : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
      (starRingEnd ℂ) ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := e00.symm
  have e1 : (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0 =
      -(starRingEnd ℂ) ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 1) := by
    have := congrArg (starRingEnd ℂ) e10
    simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e11, e1]

/-- The distance of a rotation by `θ` from the identity is `2 |sin (θ / 4)|`. -/
theorem norm_rot_sub_one {n : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1) (θ : ℝ) :
    ‖rot n θ - 1‖ = 2 * |Real.sin (θ / 4)| := by
  have hcos : 2 - 2 * Real.cos (θ / 2) = (2 * |Real.sin (θ / 4)|) ^ 2 := by
    have e : θ / 2 = 2 * (θ / 4) := by ring
    rw [mul_pow, sq_abs, e, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (θ / 4)]
  have hnorm := CStarRing.norm_star_mul_self (x := rot n θ - 1)
  rw [gram_rot_sub_one hn, norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    hcos, abs_of_nonneg (by positivity)] at hnorm
  have h2 : ‖rot n θ - 1‖ ^ 2 = (2 * |Real.sin (θ / 4)|) ^ 2 := by rw [sq, ← hnorm]
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp h2

/-- The adjoint action preserves the Euclidean norm. -/
theorem norm_adSO3 (V : SU2) (n : EuclideanSpace ℝ (Fin 3)) : ‖adSO3 V n‖ = ‖n‖ := by
  have hdet : (pauliVec (adSO3 V n)).det = (pauliVec n).det := by
    rw [← conj_pauliVec, Matrix.det_mul, Matrix.det_mul, det_star_mul,
      Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, det_star_mul]
    simp
  rw [det_pauliVec, det_pauliVec, neg_inj, Complex.ofReal_inj] at hdet
  have h1 := sumsq_aux (adSO3 V n)
  have h2 := sumsq_aux n
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), h1, h2, hdet]

/-- Conjugation by `V ∈ SU(2)` rotates the axis of a rotation by the adjoint map. -/
theorem conj_rot (V : SU2) (n : EuclideanSpace ℝ (Fin 3)) (θ : ℝ) :
    (V : Matrix (Fin 2) (Fin 2) ℂ) * rot n θ * star (V : Matrix (Fin 2) (Fin 2) ℂ) =
      rot (adSO3 V n) θ := by
  simp only [rot, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, mul_star_self, conj_pauliVec]

/-- Two elements of `SU(2)` with equal traces are conjugate in `SU(2)`. -/
theorem exists_conj_of_trace_eq {U U' : SU2}
    (h : trace (U : Matrix (Fin 2) (Fin 2) ℂ) = trace (U' : Matrix (Fin 2) (Fin 2) ℂ)) :
    ∃ S : SU2, U' = S * U * star S := by
  obtain ⟨n, θ, hn, h0, h1, hU⟩ := exists_rot_eq U
  obtain ⟨n', θ', hn', h0', h1', hU'⟩ := exists_rot_eq U'
  rw [hU, hU', trace_rot, trace_rot] at h
  have hcos : Real.cos (θ / 2) = Real.cos (θ' / 2) := by
    exact_mod_cast mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0) h
  have hθ : θ = θ' := by
    have := Real.injOn_cos ⟨by linarith, by linarith [Real.pi_pos]⟩
      ⟨by linarith, by linarith [Real.pi_pos]⟩ hcos
    linarith
  subst hθ
  obtain ⟨S, hS⟩ := exists_conj_vec_all hn hn'
  refine ⟨S, Subtype.ext ?_⟩
  change (U' : Matrix (Fin 2) (Fin 2) ℂ) = (S : Matrix (Fin 2) (Fin 2) ℂ) *
    (U : Matrix (Fin 2) (Fin 2) ℂ) * star (S : Matrix (Fin 2) (Fin 2) ℂ)
  rw [hU, hU']
  simp only [rot, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, mul_star_self, hS]

end SolovayKitaev
