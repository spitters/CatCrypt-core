/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Instances.Complex
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Quantum Instruments and the QComp Monad

This file defines `QComp d α`, a quantum computation monad parameterized by
Hilbert space dimension `d`, and proves it forms a `LawfulMonad`.

## Mathematical model

A quantum instrument on a `d`-dimensional system with outcomes in `α` is a
family `{E_a}_{a∈α}` of CP linear maps on `d×d` complex matrices, with
`∑_a E_a` sub-trace-preserving (missing trace = abort probability).

## Sorry inventory (0 remaining)

All proof obligations are discharged. The operator norm bounds `subTP_opNorm_le`
and `instrument_l1_le` are proved via Hermitian shift decomposition:
1. For Hermitian H: shift H + d‖H‖·I to PSD, bound via `psd_norm_le_trace` + sub-TP
2. For general M: decompose M = H₁ + (-i)·H₂ (Hermitian parts), triangle inequality
3. Bound: C(d) = 2d(2d+1) for both single-branch and instrument L1 norms
-/

@[expose] public section

open scoped Matrix ComplexOrder ENNReal Matrix.Norms.Elementwise
open Matrix Classical

noncomputable section

namespace CatCrypt.Quantum

variable {d : ℕ} {α β γ δ : Type}

/-! ## Helper: trace of PSD is non-negative -/

theorem trace_re_nonneg_of_psd {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) : 0 ≤ ρ.trace.re := by
  unfold Matrix.trace Matrix.diag
  rw [show (∑ x : Fin d, ρ x x).re = ∑ x : Fin d, (ρ x x).re from
    map_sum Complex.reAddGroupHom _ _]
  exact Finset.sum_nonneg fun i _ => (Complex.nonneg_iff.mp (hρ.diag_nonneg)).1

/-! ## Density Matrices -/

structure DensityMatrix (d : ℕ) where
  val : Matrix (Fin d) (Fin d) ℂ
  psd : val.PosSemidef
  tr_one : val.trace = 1

/-! ## QComp Definition -/

structure QComp (d : ℕ) (α : Type) where
  branch : α → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
  branch_psd : ∀ a (ρ : Matrix (Fin d) (Fin d) ℂ), ρ.PosSemidef →
    (branch a ρ).PosSemidef
  branch_summable : ∀ (ρ : Matrix (Fin d) (Fin d) ℂ),
    Summable (fun a => branch a ρ)
  branch_stp : ∀ (ρ : Matrix (Fin d) (Fin d) ℂ), ρ.PosSemidef →
    (∑' a, (branch a ρ).trace).re ≤ ρ.trace.re

/-! ## Extensional Equality -/

@[ext]
theorem QComp.ext {I J : QComp d α}
    (h : ∀ a, I.branch a = J.branch a) : I = J := by
  cases I; cases J; congr 1; funext a; exact h a

theorem QComp.ext_fun {I J : QComp d α}
    (h : ∀ a (ρ : Matrix (Fin d) (Fin d) ℂ), I.branch a ρ = J.branch a ρ) :
    I = J :=
  QComp.ext (fun a => LinearMap.ext (h a))

/-! ## Pure -/

def QComp.qpure (a : α) : QComp d α where
  branch a' := if a' = a then LinearMap.id else 0
  branch_psd a' ρ hρ := by
    split_ifs with h <;> simp_all [Matrix.PosSemidef.zero]
  branch_summable ρ := by
    suffices h : Summable (fun a' => if a' = a then ρ else (0 : Matrix (Fin d) (Fin d) ℂ)) by
      refine h.congr ?_
      intro a'
      split_ifs <;> simp
    apply summable_of_ne_finset_zero (s := {a})
    intro b hb
    simp only [Finset.mem_singleton] at hb
    simp [hb]
  branch_stp ρ _ := by
    have heq : (fun a' => ((if a' = a then
        (LinearMap.id : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
        else 0) ρ).trace) =
        (fun a' => if a' = a then ρ.trace else 0) := by
      funext a'; split_ifs <;> simp
    simp only [heq, tsum_ite_eq a (fun _ => ρ.trace)]
    exact le_refl _

/-! ## Fail -/

def QComp.qfail : QComp d α where
  branch _ := 0
  branch_psd _ ρ _ := by
    change (0 : Matrix (Fin d) (Fin d) ℂ).PosSemidef
    exact Matrix.PosSemidef.zero
  branch_summable ρ := by
    change Summable (fun _ : α => (0 : Matrix (Fin d) (Fin d) ℂ))
    exact summable_zero
  branch_stp ρ hρ := by
    change (∑' (_ : α), (0 : Matrix (Fin d) (Fin d) ℂ).trace).re ≤ ρ.trace.re
    simp only [Matrix.trace_zero, tsum_zero, Complex.zero_re]
    exact trace_re_nonneg_of_psd hρ

/-! ## Summability Infrastructure for PSD Matrices -/

/-- Cauchy–Schwarz for PSD matrices: `|M i j|² ≤ (M i i).re * (M j j).re`.
    Proved via non-negative determinant of the 2×2 principal submatrix. -/
theorem psd_cauchy_schwarz {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.PosSemidef)
    (i j : Fin d) : Complex.normSq (M i j) ≤ (M i i).re * (M j j).re := by
  have hN : (M.submatrix (![i, j]) (![i, j])).PosSemidef := hM.submatrix _
  have hdet_nn : 0 ≤ (M.submatrix (![i, j]) (![i, j])).det := hN.det_nonneg
  have hdet_eq : (M.submatrix (![i, j]) (![i, j])).det =
      M i i * M j j - M i j * M j i := by
    rw [Matrix.det_fin_two]
    simp [Matrix.submatrix_apply]
  have hconj : M j i = starRingEnd ℂ (M i j) := by
    have := congr_fun (congr_fun hM.isHermitian j) i
    simp [conjTranspose_apply] at this; exact this.symm
  have hii_im : (M i i).im = 0 := by
    have := congr_fun (congr_fun hM.isHermitian i) i
    simp [conjTranspose_apply] at this; exact Complex.conj_eq_iff_im.mp this
  have hjj_im : (M j j).im = 0 := by
    have := congr_fun (congr_fun hM.isHermitian j) j
    simp [conjTranspose_apply] at this; exact Complex.conj_eq_iff_im.mp this
  rw [hdet_eq, hconj, Complex.mul_conj] at hdet_nn
  have hre := (Complex.nonneg_iff.mp hdet_nn).1
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  have hprod_re : (M i i * M j j).re = (M i i).re * (M j j).re := by
    simp [Complex.mul_re, hii_im, hjj_im]
  linarith

/-- Entry norm bound for PSD matrices: `‖M i j‖ ≤ trace(M).re`. -/
theorem psd_entry_norm_le_trace {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.PosSemidef)
    (i j : Fin d) : ‖M i j‖ ≤ M.trace.re := by
  have hdiag_nn : ∀ k, 0 ≤ (M k k).re :=
    fun k => (Complex.nonneg_iff.mp (hM.diag_nonneg)).1
  have htrace_re : M.trace.re = ∑ k : Fin d, (M k k).re := by
    unfold Matrix.trace Matrix.diag; exact map_sum Complex.reAddGroupHom _ _
  have htrace_nn : 0 ≤ M.trace.re := by
    rw [htrace_re]; exact Finset.sum_nonneg fun k _ => hdiag_nn k
  have hcs := psd_cauchy_schwarz hM i j
  have hai : (M i i).re ≤ M.trace.re := by
    rw [htrace_re]; exact Finset.single_le_sum (fun k _ => hdiag_nn k) (Finset.mem_univ i)
  have haj : (M j j).re ≤ M.trace.re := by
    rw [htrace_re]; exact Finset.single_le_sum (fun k _ => hdiag_nn k) (Finset.mem_univ j)
  have hab_le : (M i i).re * (M j j).re ≤ M.trace.re ^ 2 := by
    calc (M i i).re * (M j j).re ≤ M.trace.re * M.trace.re :=
          mul_le_mul hai haj (hdiag_nn j) htrace_nn
      _ = M.trace.re ^ 2 := (sq M.trace.re).symm
  have h_sq_le : ‖M i j‖ ^ 2 ≤ M.trace.re ^ 2 := by
    calc ‖M i j‖ ^ 2 = Complex.normSq (M i j) := Complex.sq_norm (M i j)
      _ ≤ (M i i).re * (M j j).re := hcs
      _ ≤ M.trace.re ^ 2 := hab_le
  nlinarith [norm_nonneg (M i j), sq_nonneg (M.trace.re - ‖M i j‖)]

/-- For PSD matrices, the sup-norm is bounded by the trace.
    Uses `psd_cauchy_schwarz` (2×2 principal minor determinant) and `Matrix.norm_le_iff`. -/
theorem psd_norm_le_trace {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.PosSemidef) :
    ‖M‖ ≤ M.trace.re := by
  have htrace_nn : 0 ≤ M.trace.re := by
    unfold Matrix.trace Matrix.diag
    rw [show (∑ x : Fin d, M x x).re = ∑ x : Fin d, (M x x).re from
      map_sum Complex.reAddGroupHom _ _]
    exact Finset.sum_nonneg fun i _ => (Complex.nonneg_iff.mp (hM.diag_nonneg)).1
  rw [Matrix.norm_le_iff htrace_nn]
  exact fun i j => psd_entry_norm_le_trace hM i j

/-- A family of PSD matrices with summable traces is summable (in the product/norm topology). -/
theorem psd_summable_of_trace_summable {f : α → Matrix (Fin d) (Fin d) ℂ}
    (hpsd : ∀ a, (f a).PosSemidef)
    (htrace : Summable (fun a => (f a).trace.re)) :
    Summable f :=
  summable_norm_iff.mp
    (htrace.of_nonneg_of_le (fun _ => norm_nonneg _) (fun a => psd_norm_le_trace (hpsd a)))

/-- Entry-wise summability from matrix summability. -/
private theorem summable_entry {f : α → Matrix (Fin d) (Fin d) ℂ}
    (hf : Summable f) (i j : Fin d) : Summable (fun a => f a i j) :=
  Pi.summable.mp (Pi.summable.mp hf i) j

/-- Entry-wise tsum for summable matrix families. -/
private theorem tsum_entry {f : α → Matrix (Fin d) (Fin d) ℂ}
    (hf : Summable f) (i j : Fin d) :
    (∑' a, f a) i j = ∑' a, f a i j := by
  have h1 : (∑' a, f a) i = ∑' a, f a i := tsum_apply hf
  have h2 : (∑' a, f a i) j = ∑' a, f a i j := tsum_apply (Pi.summable.mp hf i)
  exact (congr_fun h1 j).trans h2

/-- Tsum of Hermitian matrices is Hermitian. -/
private theorem tsum_isHermitian {f : α → Matrix (Fin d) (Fin d) ℂ}
    (hH : ∀ a, (f a).IsHermitian) (hf : Summable f) :
    (∑' a, f a).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply]
  rw [tsum_entry hf j i, tsum_entry hf i j, tsum_star]
  congr 1; ext a
  exact congr_fun (congr_fun (hH a) i) j

/-- Tsum of PSD matrices is PSD (summable family). -/
theorem tsum_posSemidef {f : α → Matrix (Fin d) (Fin d) ℂ}
    (hpsd : ∀ a, (f a).PosSemidef) (hf : Summable f) :
    (∑' a, f a).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨tsum_isHermitian (fun a => (hpsd a).isHermitian) hf, fun x => ?_⟩
  -- Show: star x ⬝ᵥ (∑' a, f a) *ᵥ x = ∑' a, star x ⬝ᵥ f a *ᵥ x, then use tsum_nonneg
  suffices h : star x ⬝ᵥ (∑' a, f a) *ᵥ x = ∑' a, star x ⬝ᵥ f a *ᵥ x by
    rw [h]; exact tsum_nonneg (fun a => (posSemidef_iff_dotProduct_mulVec.mp (hpsd a)).2 x)
  -- Push the quadratic form through the tsum using finite-sum/tsum interchange
  have hentry : ∀ i j, Summable (fun a => f a i j) := summable_entry hf
  have hentry_mul : ∀ i j, Summable (fun a => f a i j * x j) :=
    fun i j => (hentry i j).mul_right _
  have hrow : ∀ i, Summable (fun a => ∑ j : Fin d, f a i j * x j) :=
    fun i => summable_sum fun j _ => hentry_mul i j
  simp only [dotProduct, mulVec]
  simp_rw [tsum_entry hf]
  simp_rw [← tsum_mul_right]
  simp_rw [show ∀ i, ∑ j : Fin d, ∑' a, f a i j * x j =
      ∑' a, ∑ j : Fin d, f a i j * x j from fun i => by
    rw [show (∑ j : Fin d, ∑' a, f a i j * x j) =
        (∑ j ∈ Finset.univ, ∑' a, (fun j' a' => f a' i j' * x j') j a) from by simp]
    rw [← Summable.tsum_finsetSum (fun j _ => hentry_mul i j)]]
  simp_rw [← tsum_mul_left]
  rw [show (∑ i : Fin d, ∑' a, star x i * ∑ j : Fin d, f a i j * x j) =
      (∑ i ∈ Finset.univ, ∑' a,
        (fun i' a' => star x i' * ∑ j : Fin d, f a' i' j * x j) i a) from by simp]
  rw [← Summable.tsum_finsetSum (fun i _ => (hrow i).mul_left _)]

/-- Trace commutes with tsum for summable matrix families. -/
theorem trace_tsum {f : α → Matrix (Fin d) (Fin d) ℂ} (hf : Summable f) :
    (∑' a, f a).trace = ∑' a, (f a).trace := by
  unfold Matrix.trace Matrix.diag
  rw [show (∑ j : Fin d, (∑' a, f a) j j) =
      (∑ j : Fin d, ∑' a, f a j j) from by
    congr 1; ext j; exact tsum_entry hf j j]
  rw [show (∑ j ∈ Finset.univ, ∑' a, (fun j' a' => f a' j' j') j a) =
      (∑ j : Fin d, ∑' a, f a j j) from by simp]
  rw [← Summable.tsum_finsetSum (fun j _ => summable_entry hf j j)]

/-- The trace, as a ContinuousLinearMap from matrices to ℂ. -/
def traceCLM (d : ℕ) : Matrix (Fin d) (Fin d) ℂ →L[ℂ] ℂ :=
  (traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap

/-- Summability of traces from summability of matrices. -/
theorem trace_summable {f : α → Matrix (Fin d) (Fin d) ℂ} (hf : Summable f) :
    Summable (fun a => (f a).trace) :=
  (traceCLM d).summable hf

/-- Summability of trace real parts from summability of matrices. -/
theorem trace_re_summable {f : α → Matrix (Fin d) (Fin d) ℂ} (hf : Summable f) :
    Summable (fun a => (f a).trace.re) :=
  (trace_summable hf).map Complex.reAddGroupHom Complex.continuous_re

/-! ## Operator Norm Bounds for Instruments

Proved bounds for completely positive sub-trace-preserving (sub-TP) maps:

* `single_stp_re`: A single branch of a sub-TP instrument has trace ≤ input trace.
* `subTP_opNorm_le`: `‖L(M)‖ ≤ 2d(2d+1) · ‖M‖` for a single branch.
* `instrument_l1_le`: `∑ᵦ ‖Lᵦ(M)‖ ≤ 2d(2d+1) · ‖M‖` for all branches combined.

**Proof structure** (Hermitian shift decomposition):
For PSD input M: L(M) is PSD with trace ≤ trace(M), so ‖L(M)‖ ≤ trace(M) ≤ d·‖M‖.
For Hermitian H: shift H + d‖H‖·I to make PSD, use triangle inequality → d(2d+1)·‖H‖.
For general M: decompose M = H₁ + (-i)H₂ with ‖Hₖ‖ ≤ ‖M‖ → 2d(2d+1)·‖M‖.
-/

/-- Single branch sub-TP: trace of one branch ≤ trace of input, for PSD input. -/
private lemma single_stp_re
    {α : Type}
    (branch : α → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (hpsd : ∀ a (ρ : Matrix (Fin d) (Fin d) ℂ), ρ.PosSemidef → (branch a ρ).PosSemidef)
    (hsum : ∀ (ρ : Matrix (Fin d) (Fin d) ℂ), Summable (fun a => branch a ρ))
    (hstp : ∀ (ρ : Matrix (Fin d) (Fin d) ℂ), ρ.PosSemidef →
      (∑' a, (branch a ρ).trace).re ≤ ρ.trace.re)
    (b : α) (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef) :
    (branch b M).trace.re ≤ M.trace.re := by
  calc (branch b M).trace.re
      ≤ ∑' a, (branch a M).trace.re :=
        (trace_re_summable (hsum M)).le_tsum b
          (fun j _ => trace_re_nonneg_of_psd (hpsd j M hM))
    _ = (∑' a, (branch a M).trace).re :=
        (Complex.re_tsum (trace_summable (hsum M))).symm
    _ ≤ M.trace.re := hstp M hM

private lemma QComp.single_stp (I : QComp d α) (b : α)
    (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef) :
    (I.branch b M).trace.re ≤ M.trace.re :=
  single_stp_re I.branch I.branch_psd I.branch_summable I.branch_stp b M hM

/-- For PSD-preserving sub-TP map L and PSD input M, ‖L(M)‖ ≤ trace(M).re.
    Proof: L(M) is PSD, so ‖L(M)‖ ≤ trace(L(M)).re ≤ trace(M).re. -/
private theorem subTP_psd_norm_le
    {d : ℕ}
    (L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hpsd : ∀ (M : Matrix (Fin d) (Fin d) ℂ), M.PosSemidef → (L M).PosSemidef)
    (hstp : ∀ (M : Matrix (Fin d) (Fin d) ℂ), M.PosSemidef → (L M).trace.re ≤ M.trace.re)
    (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef) :
    ‖L M‖ ≤ M.trace.re :=
  le_trans (psd_norm_le_trace (hpsd M hM)) (hstp M hM)

/-- Quadratic form bound via Cauchy-Schwarz: `|⟨x, Mx⟩| ≤ d · ‖M‖ · ‖x‖²`. -/
private lemma norm_quadratic_form_le {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) :
    ‖star x ⬝ᵥ M *ᵥ x‖ ≤ ↑d * ‖M‖ * ∑ i : Fin d, ‖x i‖ ^ 2 := by
  simp only [dotProduct, mulVec, star]
  calc ‖∑ i, (starRingEnd ℂ) (x i) * ∑ j, M i j * x j‖
      ≤ ∑ i, ‖(starRingEnd ℂ) (x i) * ∑ j, M i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖x i‖ * (‖M‖ * ∑ j, ‖x j‖) := by
        apply Finset.sum_le_sum; intro i _
        rw [norm_mul, Complex.norm_conj]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        calc ‖∑ j, M i j * x j‖
            ≤ ∑ j, ‖M i j * x j‖ := norm_sum_le _ _
          _ = ∑ j, ‖M i j‖ * ‖x j‖ := by congr 1; ext j; exact norm_mul _ _
          _ ≤ ∑ j, ‖M‖ * ‖x j‖ := Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_right (norm_entry_le_entrywise_sup_norm M) (norm_nonneg _)
          _ = ‖M‖ * ∑ j, ‖x j‖ := by rw [Finset.mul_sum]
    _ ≤ ↑d * ‖M‖ * ∑ i : Fin d, ‖x i‖ ^ 2 := by
        have h1 : ∑ i : Fin d, ‖x i‖ * (‖M‖ * ∑ j : Fin d, ‖x j‖) =
            ‖M‖ * (∑ i : Fin d, ‖x i‖) ^ 2 := by
          rw [sq]; simp_rw [mul_comm (‖M‖) _, ← Finset.sum_mul]; ring
        rw [h1]
        have h2 := @sq_sum_le_card_mul_sum_sq _ ℝ _ _ _ _
          (s := Finset.univ) (f := fun i => ‖x i‖)
        simp at h2
        calc ‖M‖ * (∑ i : Fin d, ‖x i‖) ^ 2
            ≤ ‖M‖ * (↑d * ∑ i : Fin d, ‖x i‖ ^ 2) :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
          _ = ↑d * ‖M‖ * ∑ i : Fin d, ‖x i‖ ^ 2 := by ring

/-- Hermitian quadratic form is real: `Im(⟨x, Hx⟩) = 0` for Hermitian H.
    Proved via involution pairing: terms (i,j) and (j,i) contribute conjugate values. -/
private lemma hermitian_quadratic_im_zero {d : ℕ}
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) (x : Fin d → ℂ) :
    (star x ⬝ᵥ H *ᵥ x).im = 0 := by
  simp only [dotProduct, mulVec]
  show (∑ i : Fin d, (star x) i * ∑ j : Fin d, H i j * x j).im = 0
  rw [show (∑ i : Fin d, (star x) i * ∑ j : Fin d, H i j * x j).im =
    ∑ i : Fin d, ((star x) i * ∑ j : Fin d, H i j * x j).im from
    map_sum Complex.imAddGroupHom _ _]
  simp_rw [Finset.mul_sum,
    show ∀ i : Fin d, (∑ j : Fin d, (star x) i * (H i j * x j)).im =
      ∑ j : Fin d, ((star x) i * (H i j * x j)).im from
      fun i => map_sum Complex.imAddGroupHom _ _]
  rw [← Finset.sum_product']
  let σ : Fin d × Fin d → Fin d × Fin d := fun p => (p.2, p.1)
  apply Finset.sum_involution (fun a _ => σ a)
  · intro ⟨i, j⟩ _
    set z := (star x) i * (H i j * x j)
    suffices heq : ((star x) j * (H j i * x i)) = starRingEnd ℂ z by
      rw [heq, Complex.conj_im, add_neg_cancel]
    rw [map_mul, show (starRingEnd ℂ) ((star x) i) = x i from star_star (x i),
      map_mul, show (starRingEnd ℂ) (H i j) = H j i from congr_fun (congr_fun hH j) i]
    show (starRingEnd ℂ) (x j) * (H j i * x i) = x i * (H j i * (starRingEnd ℂ) (x j))
    ring
  · intro ⟨i, j⟩ _ hne heq
    apply hne
    have : i = j := (Prod.mk.inj heq).2
    subst this
    show ((star x) i * (H i i * x i)).im = 0
    change ((starRingEnd ℂ) (x i) * (H i i * x i)).im = 0
    rw [show (starRingEnd ℂ) (x i) * (H i i * x i) = H i i * ((starRingEnd ℂ) (x i) * x i)
      from by ring, Complex.normSq_eq_conj_mul_self.symm]
    have hii_real : (H i i).im = 0 :=
      Complex.conj_eq_iff_im.mp (congr_fun (congr_fun hH i) i)
    simp [Complex.mul_im, hii_real]
  · intro ⟨i, j⟩ _
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  · intro ⟨i, j⟩ _; rfl

/-- Hermitian shift to PSD: for Hermitian H, `H + c·I` is PSD when `c ≥ d·‖H‖`.
    Uses `norm_quadratic_form_le` for the lower bound on the quadratic form. -/
private lemma hermitian_shift_psd {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) (c : ℝ) (hc : ↑d * ‖H‖ ≤ c) :
    (H + (↑c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · have : ((↑c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)).IsHermitian := by
      show ((↑c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ))ᴴ = (↑c : ℂ) • 1
      rw [conjTranspose_smul, isHermitian_one]; congr 1; exact Complex.conj_ofReal c
    exact hH.add this
  · intro x
    rw [add_mulVec, dotProduct_add,
      show ((↑c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ x = (↑c : ℂ) • x from by
        rw [smul_mulVec (↑c : ℂ) 1 x, one_mulVec],
      dotProduct_smul]
    have hxx_eq : star x ⬝ᵥ x = ↑(∑ i : Fin d, ‖x i‖ ^ 2 : ℝ) := by
      simp only [dotProduct]; rw [Complex.ofReal_sum]
      congr 1; ext i
      change (starRingEnd ℂ) (x i) * x i = ↑(‖x i‖ ^ 2)
      rw [Complex.normSq_eq_conj_mul_self.symm, Complex.sq_norm]
    rw [hxx_eq]
    set S := ∑ i : Fin d, ‖x i‖ ^ 2
    have hS_nn : (0 : ℝ) ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hqf_im := hermitian_quadratic_im_zero H hH x
    have hqf_re_bound : -(↑d * ‖H‖ * S) ≤ (star x ⬝ᵥ H *ᵥ x).re := by
      have hle := norm_quadratic_form_le H x
      calc -(↑d * ‖H‖ * S) ≤ -‖star x ⬝ᵥ H *ᵥ x‖ := neg_le_neg hle
        _ ≤ -|Complex.re (star x ⬝ᵥ H *ᵥ x)| := neg_le_neg (Complex.abs_re_le_norm _)
        _ ≤ (star x ⬝ᵥ H *ᵥ x).re := neg_abs_le _
    have hcS_re : ((↑c : ℂ) * (↑S : ℂ)).re = c * S := by simp
    have hcS_im : ((↑c : ℂ) * (↑S : ℂ)).im = 0 := by simp
    rw [Complex.nonneg_iff, smul_eq_mul] at *
    exact ⟨by rw [Complex.add_re, hcS_re]; linarith [mul_le_mul_of_nonneg_right hc hS_nn],
           by rw [Complex.add_im, hcS_im]; linarith⟩

/-- `trace(M).re ≤ d · ‖M‖` for any `d×d` complex matrix. -/
private lemma trace_re_le_dim_mul_norm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) :
    M.trace.re ≤ ↑d * ‖M‖ := by
  unfold Matrix.trace Matrix.diag
  rw [show (∑ x : Fin d, M x x).re = ∑ x : Fin d, (M x x).re from
    map_sum Complex.reAddGroupHom _ _]
  calc ∑ i : Fin d, (M i i).re
      ≤ ∑ i : Fin d, ‖M i i‖ := Finset.sum_le_sum fun i _ => Complex.re_le_norm _
    _ ≤ ∑ i : Fin d, ‖M‖ := Finset.sum_le_sum fun i _ => norm_entry_le_entrywise_sup_norm M
    _ = ↑d * ‖M‖ := by simp [Finset.sum_const, nsmul_eq_mul]

private lemma trace_one_re {d : ℕ} :
    (1 : Matrix (Fin d) (Fin d) ℂ).trace.re = (↑d : ℝ) := by
  simp [Matrix.trace, Matrix.diag, Finset.sum_const, nsmul_eq_mul]

private lemma trace_add_smul_one_re {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (c : ℝ) :
    (H + (↑c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)).trace.re =
    H.trace.re + c * ↑d := by
  rw [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  have : (1 : Matrix (Fin d) (Fin d) ℂ).trace = (↑d : ℂ) := by
    simp [Matrix.trace, Matrix.diag, Finset.sum_const, nsmul_eq_mul]
  rw [this]; simp

set_option maxHeartbeats 400000 in
/-- Core Hermitian bound: `‖L(H)‖ ≤ d(2d+1)·‖H‖` for Hermitian H and sub-TP L.
    Uses shift trick: L(H) = L(H+c·I) - c·L(I) where c = d·‖H‖. -/
private lemma hermitian_norm_bound {d : ℕ}
    (L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hpsd : ∀ (M : Matrix (Fin d) (Fin d) ℂ), M.PosSemidef → (L M).PosSemidef)
    (hstp : ∀ (M : Matrix (Fin d) (Fin d) ℂ), M.PosSemidef → (L M).trace.re ≤ M.trace.re)
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    ‖L H‖ ≤ ↑d * (2 * ↑d + 1) * ‖H‖ := by
  set c := (↑d : ℝ) * ‖H‖ with hc_def
  have hc_nn : 0 ≤ c := mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hdecomp : L H = L (H + (↑c : ℂ) • 1) - (↑c : ℂ) • L 1 := by
    rw [map_add, map_smul]; simp
  rw [hdecomp]
  have hpsd_shift := hermitian_shift_psd hH c le_rfl
  have hpsd_one : (1 : Matrix (Fin d) (Fin d) ℂ).PosSemidef := PosSemidef.one
  calc ‖L (H + (↑c : ℂ) • 1) - (↑c : ℂ) • L 1‖
      ≤ ‖L (H + (↑c : ℂ) • 1)‖ + ‖(↑c : ℂ) • L 1‖ := norm_sub_le _ _
    _ ≤ ‖L (H + (↑c : ℂ) • 1)‖ + c * ‖L 1‖ := by
        rw [norm_smul, Complex.norm_of_nonneg (by exact_mod_cast hc_nn)]
    _ ≤ (H + (↑c : ℂ) • 1).trace.re + c * (1 : Matrix (Fin d) (Fin d) ℂ).trace.re := by
        gcongr
        · exact le_trans (psd_norm_le_trace (hpsd _ hpsd_shift)) (hstp _ hpsd_shift)
        · exact le_trans (psd_norm_le_trace (hpsd 1 hpsd_one)) (hstp 1 hpsd_one)
    _ ≤ ↑d * ‖H‖ + c * ↑d + c * ↑d := by
        rw [trace_add_smul_one_re, trace_one_re]
        linarith [trace_re_le_dim_mul_norm H]
    _ = ↑d * (2 * ↑d + 1) * ‖H‖ := by rw [hc_def]; ring

set_option maxHeartbeats 400000 in
/-- L1 Hermitian bound for instruments: `∑ᵦ ‖Lᵦ(H)‖ ≤ d(2d+1)·‖H‖`. -/
private lemma hermitian_l1_bound {d : ℕ} {β : Type}
    (branch : β → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (hpsd : ∀ b (M : Matrix (Fin d) (Fin d) ℂ), M.PosSemidef → (branch b M).PosSemidef)
    (hsum : ∀ (M : Matrix (Fin d) (Fin d) ℂ), Summable (fun b => branch b M))
    (hstp : ∀ (M : Matrix (Fin d) (Fin d) ℂ), M.PosSemidef →
      (∑' b, (branch b M).trace).re ≤ M.trace.re)
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    ∑' b, ‖branch b H‖ ≤ ↑d * (2 * ↑d + 1) * ‖H‖ := by
  set c := (↑d : ℝ) * ‖H‖ with hc_def
  have hc_nn : 0 ≤ c := mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hpsd_shift := hermitian_shift_psd hH c le_rfl
  have hpsd_one : (1 : Matrix (Fin d) (Fin d) ℂ).PosSemidef := PosSemidef.one
  -- branch b H = branch b (H + c·I) - c · branch b I
  have hdecomp : ∀ b, branch b H = branch b (H + (↑c : ℂ) • 1) - (↑c : ℂ) • branch b 1 := by
    intro b; rw [map_add, map_smul]; simp
  -- ‖branch b H‖ ≤ ‖branch b (H+c·I)‖ + c·‖branch b I‖
  have hle : ∀ b, ‖branch b H‖ ≤ ‖branch b (H + (↑c : ℂ) • 1)‖ + c * ‖branch b 1‖ := by
    intro b; rw [hdecomp b]
    calc ‖branch b (H + (↑c : ℂ) • 1) - (↑c : ℂ) • branch b 1‖
        ≤ ‖branch b (H + (↑c : ℂ) • 1)‖ + ‖(↑c : ℂ) • branch b 1‖ := norm_sub_le _ _
      _ = ‖branch b (H + (↑c : ℂ) • 1)‖ + c * ‖branch b 1‖ := by
          rw [norm_smul, Complex.norm_of_nonneg (by exact_mod_cast hc_nn)]
  -- Summability of the bounding terms
  have hsum_shift := summable_norm_iff.mpr (hsum (H + (↑c : ℂ) • 1))
  have hsum_one := summable_norm_iff.mpr (hsum 1)
  calc ∑' b, ‖branch b H‖
      ≤ ∑' b, (‖branch b (H + (↑c : ℂ) • 1)‖ + c * ‖branch b 1‖) :=
        Summable.tsum_le_tsum hle (summable_norm_iff.mpr (hsum H)) (hsum_shift.add (hsum_one.mul_left c))
    _ = (∑' b, ‖branch b (H + (↑c : ℂ) • 1)‖) + c * (∑' b, ‖branch b 1‖) := by
        rw [Summable.tsum_add hsum_shift (hsum_one.mul_left c), tsum_mul_left]
    _ ≤ (H + (↑c : ℂ) • 1).trace.re + c * (1 : Matrix (Fin d) (Fin d) ℂ).trace.re := by
        gcongr
        · exact instrument_psd_l1_le branch hpsd hsum hstp _ hpsd_shift
        · exact instrument_psd_l1_le branch hpsd hsum hstp 1 hpsd_one
    _ ≤ ↑d * ‖H‖ + c * ↑d + c * ↑d := by
        rw [trace_add_smul_one_re, trace_one_re]
        linarith [trace_re_le_dim_mul_norm H]
    _ = ↑d * (2 * ↑d + 1) * ‖H‖ := by rw [hc_def]; ring
  where
    /-- For instrument branches and PSD input M, ∑ᵦ ‖branch b M‖ ≤ trace(M).re. -/
    instrument_psd_l1_le
        (branch : β → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
        (hpsd : ∀ b (M : Matrix (Fin d) (Fin d) ℂ), M.PosSemidef → (branch b M).PosSemidef)
        (hsum : ∀ (M : Matrix (Fin d) (Fin d) ℂ), Summable (fun b => branch b M))
        (hstp : ∀ (M : Matrix (Fin d) (Fin d) ℂ), M.PosSemidef →
          (∑' b, (branch b M).trace).re ≤ M.trace.re)
        (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef) :
        ∑' b, ‖branch b M‖ ≤ M.trace.re :=
      calc ∑' b, ‖branch b M‖
          ≤ ∑' b, (branch b M).trace.re :=
            Summable.tsum_le_tsum (fun b => psd_norm_le_trace (hpsd b M hM))
              (summable_norm_iff.mpr (hsum M)) (trace_re_summable (hsum M))
        _ = (∑' b, (branch b M).trace).re :=
            (Complex.re_tsum (trace_summable (hsum M))).symm
        _ ≤ M.trace.re := hstp M hM

/-- Hermitian decomposition helper: `‖(2⁻¹)‖ * 2 = 1` for complex inverse of 2. -/
private lemma inv2_norm_mul_2 : ‖(2 : ℂ)⁻¹‖ * 2 = 1 := by
  have h : (2 : ℂ)⁻¹ = ↑((2 : ℝ)⁻¹) := by push_cast; norm_num
  rw [h, Complex.norm_of_nonneg (by positivity)]; norm_num

/-- Uniform operator norm bound for a single branch of a PSD-preserving sub-TP map.
    Every such map L satisfies `‖L(M)‖ ≤ C(d) · ‖M‖` where `C(d) = 2d(2d+1)`.
    Proved via Hermitian shift decomposition. -/
private def subTP_opNorm_bound (d : ℕ) : ℝ := 2 * ↑d * (2 * ↑d + 1)
set_option maxHeartbeats 800000 in
private theorem subTP_opNorm_le
    {d : ℕ}
    (L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hpsd : ∀ (M : Matrix (Fin d) (Fin d) ℂ), M.PosSemidef → (L M).PosSemidef)
    (hstp : ∀ (M : Matrix (Fin d) (Fin d) ℂ), M.PosSemidef → (L M).trace.re ≤ M.trace.re)
    (M : Matrix (Fin d) (Fin d) ℂ) :
    ‖L M‖ ≤ subTP_opNorm_bound d * ‖M‖ := by
  -- Decompose M = H₁ + (-i)·H₂ where H₁, H₂ are Hermitian with ‖Hₖ‖ ≤ ‖M‖
  set H₁ : Matrix (Fin d) (Fin d) ℂ := (2 : ℂ)⁻¹ • (M + Mᴴ)
  set H₂ : Matrix (Fin d) (Fin d) ℂ := Complex.I • ((2 : ℂ)⁻¹ • (M - Mᴴ))
  have hH₁_herm : H₁.IsHermitian := by
    show ((2 : ℂ)⁻¹ • (M + Mᴴ))ᴴ = (2 : ℂ)⁻¹ • (M + Mᴴ)
    rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]; simp; abel
  have hH₂_herm : H₂.IsHermitian := by
    show (Complex.I • ((2 : ℂ)⁻¹ • (M - Mᴴ)))ᴴ = Complex.I • ((2 : ℂ)⁻¹ • (M - Mᴴ))
    rw [conjTranspose_smul, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose,
      Complex.star_def, Complex.conj_I,
      show (starRingEnd ℂ) ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ from by rw [map_inv₀, map_ofNat]]
    simp only [neg_smul, smul_sub]; abel
  have hdecomp : L M = L H₁ + (-Complex.I) • L H₂ := by
    rw [← map_smul, ← map_add]; congr 1
    show M = (2 : ℂ)⁻¹ • (M + Mᴴ) + (-Complex.I) • (Complex.I • ((2 : ℂ)⁻¹ • (M - Mᴴ)))
    rw [smul_smul, show (-Complex.I) * Complex.I = 1 from by rw [neg_mul, Complex.I_mul_I]; simp,
      one_smul, ← smul_add,
      show M + Mᴴ + (M - Mᴴ) = (2 : ℂ) • M from by rw [two_smul]; abel,
      smul_smul, inv_mul_cancel₀ (two_ne_zero)]; simp
  have hH₁_norm : ‖H₁‖ ≤ ‖M‖ :=
    calc ‖H₁‖ = ‖(2 : ℂ)⁻¹‖ * ‖M + Mᴴ‖ := norm_smul _ _
      _ ≤ ‖(2 : ℂ)⁻¹‖ * (‖M‖ + ‖Mᴴ‖) := by gcongr; exact norm_add_le _ _
      _ = ‖(2 : ℂ)⁻¹‖ * 2 * ‖M‖ := by rw [norm_conjTranspose]; ring
      _ = ‖M‖ := by rw [inv2_norm_mul_2, one_mul]
  have hH₂_norm : ‖H₂‖ ≤ ‖M‖ :=
    calc ‖H₂‖ = ‖(2 : ℂ)⁻¹‖ * ‖M - Mᴴ‖ := by
          show ‖Complex.I • ((2 : ℂ)⁻¹ • (M - Mᴴ))‖ = _
          rw [norm_smul, Complex.norm_I, one_mul, norm_smul]
      _ ≤ ‖(2 : ℂ)⁻¹‖ * (‖M‖ + ‖Mᴴ‖) := by gcongr; exact norm_sub_le _ _
      _ = ‖(2 : ℂ)⁻¹‖ * 2 * ‖M‖ := by rw [norm_conjTranspose]; ring
      _ = ‖M‖ := by rw [inv2_norm_mul_2, one_mul]
  rw [hdecomp]
  calc ‖L H₁ + (-Complex.I) • L H₂‖
      ≤ ‖L H₁‖ + ‖(-Complex.I) • L H₂‖ := norm_add_le _ _
    _ = ‖L H₁‖ + ‖L H₂‖ := by rw [norm_smul]; simp [Complex.norm_I]
    _ ≤ ↑d * (2 * ↑d + 1) * ‖H₁‖ + ↑d * (2 * ↑d + 1) * ‖H₂‖ :=
        add_le_add (hermitian_norm_bound L hpsd hstp H₁ hH₁_herm)
          (hermitian_norm_bound L hpsd hstp H₂ hH₂_herm)
    _ = ↑d * (2 * ↑d + 1) * (‖H₁‖ + ‖H₂‖) := by ring
    _ ≤ ↑d * (2 * ↑d + 1) * (‖M‖ + ‖M‖) := by gcongr
    _ = subTP_opNorm_bound d * ‖M‖ := by simp only [subTP_opNorm_bound]; ring

/-- For instrument branches and PSD input M, ∑ᵦ ‖branch b M‖ ≤ trace(M).re. -/
private theorem instrument_psd_l1_le
    {d : ℕ} {β : Type}
    (branch : β → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (hpsd : ∀ b (M : Matrix (Fin d) (Fin d) ℂ), M.PosSemidef → (branch b M).PosSemidef)
    (hsum : ∀ (M : Matrix (Fin d) (Fin d) ℂ), Summable (fun b => branch b M))
    (hstp : ∀ (M : Matrix (Fin d) (Fin d) ℂ), M.PosSemidef →
      (∑' b, (branch b M).trace).re ≤ M.trace.re)
    (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef) :
    ∑' b, ‖branch b M‖ ≤ M.trace.re := by
  calc ∑' b, ‖branch b M‖
      ≤ ∑' b, (branch b M).trace.re :=
        Summable.tsum_le_tsum (fun b => psd_norm_le_trace (hpsd b M hM))
          (summable_norm_iff.mpr (hsum M)) (trace_re_summable (hsum M))
    _ = (∑' b, (branch b M).trace).re :=
        (Complex.re_tsum (trace_summable (hsum M))).symm
    _ ≤ M.trace.re := hstp M hM

/-- Total L1-norm bound for all branches of an instrument.
    `∑ᵦ ‖Lᵦ(M)‖ ≤ C(d) · ‖M‖` where `C(d) = 2d(2d+1)`.
    Proved via Hermitian shift decomposition, same as `subTP_opNorm_le`. -/
private def instrument_l1_bound (d : ℕ) : ℝ := subTP_opNorm_bound d
set_option maxHeartbeats 800000 in
private theorem instrument_l1_le
    {d : ℕ} {β : Type}
    (branch : β → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (hpsd : ∀ b (M : Matrix (Fin d) (Fin d) ℂ), M.PosSemidef → (branch b M).PosSemidef)
    (hsum : ∀ (M : Matrix (Fin d) (Fin d) ℂ), Summable (fun b => branch b M))
    (hstp : ∀ (M : Matrix (Fin d) (Fin d) ℂ), M.PosSemidef →
      (∑' b, (branch b M).trace).re ≤ M.trace.re)
    (M : Matrix (Fin d) (Fin d) ℂ) :
    ∑' b, ‖branch b M‖ ≤ instrument_l1_bound d * ‖M‖ := by
  -- Decompose M = H₁ + (-i)·H₂ where H₁, H₂ are Hermitian with ‖Hₖ‖ ≤ ‖M‖
  set H₁ : Matrix (Fin d) (Fin d) ℂ := (2 : ℂ)⁻¹ • (M + Mᴴ)
  set H₂ : Matrix (Fin d) (Fin d) ℂ := Complex.I • ((2 : ℂ)⁻¹ • (M - Mᴴ))
  have hH₁_herm : H₁.IsHermitian := by
    show ((2 : ℂ)⁻¹ • (M + Mᴴ))ᴴ = (2 : ℂ)⁻¹ • (M + Mᴴ)
    rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]; simp; abel
  have hH₂_herm : H₂.IsHermitian := by
    show (Complex.I • ((2 : ℂ)⁻¹ • (M - Mᴴ)))ᴴ = Complex.I • ((2 : ℂ)⁻¹ • (M - Mᴴ))
    rw [conjTranspose_smul, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose,
      Complex.star_def, Complex.conj_I,
      show (starRingEnd ℂ) ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ from by rw [map_inv₀, map_ofNat]]
    simp only [neg_smul, smul_sub]; abel
  -- M = H₁ + (-i)·H₂
  have hM_eq : ∀ b, branch b M = branch b H₁ + (-Complex.I) • branch b H₂ := by
    intro b
    rw [← map_smul, ← map_add]; congr 1
    show M = (2 : ℂ)⁻¹ • (M + Mᴴ) + (-Complex.I) • (Complex.I • ((2 : ℂ)⁻¹ • (M - Mᴴ)))
    rw [smul_smul, show (-Complex.I) * Complex.I = 1 from by rw [neg_mul, Complex.I_mul_I]; simp,
      one_smul, ← smul_add,
      show M + Mᴴ + (M - Mᴴ) = (2 : ℂ) • M from by rw [two_smul]; abel,
      smul_smul, inv_mul_cancel₀ (two_ne_zero)]; simp
  have hH₁_norm : ‖H₁‖ ≤ ‖M‖ :=
    calc ‖H₁‖ = ‖(2 : ℂ)⁻¹‖ * ‖M + Mᴴ‖ := norm_smul _ _
      _ ≤ ‖(2 : ℂ)⁻¹‖ * (‖M‖ + ‖Mᴴ‖) := by gcongr; exact norm_add_le _ _
      _ = ‖(2 : ℂ)⁻¹‖ * 2 * ‖M‖ := by rw [norm_conjTranspose]; ring
      _ = ‖M‖ := by rw [inv2_norm_mul_2, one_mul]
  have hH₂_norm : ‖H₂‖ ≤ ‖M‖ :=
    calc ‖H₂‖ = ‖(2 : ℂ)⁻¹‖ * ‖M - Mᴴ‖ := by
          show ‖Complex.I • ((2 : ℂ)⁻¹ • (M - Mᴴ))‖ = _
          rw [norm_smul, Complex.norm_I, one_mul, norm_smul]
      _ ≤ ‖(2 : ℂ)⁻¹‖ * (‖M‖ + ‖Mᴴ‖) := by gcongr; exact norm_sub_le _ _
      _ = ‖(2 : ℂ)⁻¹‖ * 2 * ‖M‖ := by rw [norm_conjTranspose]; ring
      _ = ‖M‖ := by rw [inv2_norm_mul_2, one_mul]
  -- ‖branch b M‖ ≤ ‖branch b H₁‖ + ‖branch b H₂‖
  have hle : ∀ b, ‖branch b M‖ ≤ ‖branch b H₁‖ + ‖branch b H₂‖ := by
    intro b; rw [hM_eq b]
    calc ‖branch b H₁ + (-Complex.I) • branch b H₂‖
        ≤ ‖branch b H₁‖ + ‖(-Complex.I) • branch b H₂‖ := norm_add_le _ _
      _ = ‖branch b H₁‖ + ‖branch b H₂‖ := by rw [norm_smul]; simp [Complex.norm_I]
  calc ∑' b, ‖branch b M‖
      ≤ ∑' b, (‖branch b H₁‖ + ‖branch b H₂‖) :=
        Summable.tsum_le_tsum hle (summable_norm_iff.mpr (hsum M))
          ((summable_norm_iff.mpr (hsum H₁)).add (summable_norm_iff.mpr (hsum H₂)))
    _ = (∑' b, ‖branch b H₁‖) + (∑' b, ‖branch b H₂‖) :=
        Summable.tsum_add (summable_norm_iff.mpr (hsum H₁)) (summable_norm_iff.mpr (hsum H₂))
    _ ≤ ↑d * (2 * ↑d + 1) * ‖H₁‖ + ↑d * (2 * ↑d + 1) * ‖H₂‖ :=
        add_le_add (hermitian_l1_bound branch hpsd hsum hstp H₁ hH₁_herm)
          (hermitian_l1_bound branch hpsd hsum hstp H₂ hH₂_herm)
    _ = ↑d * (2 * ↑d + 1) * (‖H₁‖ + ‖H₂‖) := by ring
    _ ≤ ↑d * (2 * ↑d + 1) * (‖M‖ + ‖M‖) := by gcongr
    _ = instrument_l1_bound d * ‖M‖ := by simp only [instrument_l1_bound, subTP_opNorm_bound]; ring

/-! ## Bind -/

set_option maxHeartbeats 400000 in
theorem QComp.bind_summable (I : QComp d α) (f : α → QComp d β)
    (b : β) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Summable (fun a => (f a).branch b (I.branch a ρ)) :=
  Summable.of_norm_bounded
    (g := fun a => subTP_opNorm_bound d * ‖I.branch a ρ‖)
    ((summable_norm_iff (E := Matrix (Fin d) (Fin d) ℂ)).mpr
      (I.branch_summable ρ) |>.hasSum.mul_left (subTP_opNorm_bound d) |>.summable)
    (fun a => subTP_opNorm_le ((f a).branch b)
      (fun M hM => (f a).branch_psd b M hM)
      (fun M hM => (f a).single_stp b M hM)
      (I.branch a ρ))

set_option maxHeartbeats 400000 in
/-- Joint summability of the uncurried family for Fubini in `qbind_assoc`. -/
theorem QComp.bind_summable_uncurry (I : QComp d α) (f : α → QComp d β)
    (g : β → QComp d γ) (c : γ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Summable (Function.uncurry fun a b =>
      (g b).branch c ((f a).branch b (I.branch a ρ))) := by
  -- Norm bound per (a,b): ‖F(a,b)‖ ≤ C · ‖(f a).branch b (I.branch a ρ)‖
  have hF_le : ∀ (p : α × β),
      ‖(Function.uncurry fun a b => (g b).branch c ((f a).branch b (I.branch a ρ))) p‖ ≤
      subTP_opNorm_bound d * ‖(f p.1).branch p.2 (I.branch p.1 ρ)‖ :=
    fun ⟨a, b⟩ => subTP_opNorm_le ((g b).branch c)
      (fun M hM => (g b).branch_psd c M hM)
      (fun M hM => (g b).single_stp c M hM)
      ((f a).branch b (I.branch a ρ))
  -- Intermediate norm family is summable over the product (via summable_prod_of_nonneg)
  have hG_norm_summable : Summable (fun (p : α × β) =>
      ‖(f p.1).branch p.2 (I.branch p.1 ρ)‖) := by
    rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
    exact ⟨fun a => summable_norm_iff.mpr ((f a).branch_summable (I.branch a ρ)),
      Summable.of_nonneg_of_le
        (fun a => tsum_nonneg (fun b => norm_nonneg _))
        (fun a => instrument_l1_le (f a).branch (f a).branch_psd
          (f a).branch_summable (f a).branch_stp (I.branch a ρ))
        ((summable_norm_iff (E := Matrix (Fin d) (Fin d) ℂ)).mpr
          (I.branch_summable ρ) |>.hasSum.mul_left (instrument_l1_bound d) |>.summable)⟩
  -- Summable by comparison with the bounding function
  exact Summable.of_norm_bounded
    (g := fun p => subTP_opNorm_bound d * ‖(f p.1).branch p.2 (I.branch p.1 ρ)‖)
    (hG_norm_summable.hasSum.mul_left (subTP_opNorm_bound d) |>.summable)
    hF_le

set_option maxHeartbeats 400000 in
/-- Joint summability of the (a,b)-family (without the outer g), used for
branch_summable and for `qbind` reasoning (e.g. `localOp₁` functoriality). -/
theorem QComp.bind_uncurry_summable (I : QComp d α) (f : α → QComp d β)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Summable (Function.uncurry fun a b => (f a).branch b (I.branch a ρ)) := by
  rw [show (Function.uncurry fun a b => (f a).branch b (I.branch a ρ)) =
      (fun (p : α × β) => (f p.1).branch p.2 (I.branch p.1 ρ)) from rfl]
  exact summable_norm_iff.mp
    ((summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
      ⟨fun a => summable_norm_iff.mpr ((f a).branch_summable (I.branch a ρ)),
       Summable.of_nonneg_of_le
        (fun a => tsum_nonneg (fun b => norm_nonneg _))
        (fun a => instrument_l1_le (f a).branch (f a).branch_psd
          (f a).branch_summable (f a).branch_stp (I.branch a ρ))
        ((summable_norm_iff (E := Matrix (Fin d) (Fin d) ℂ)).mpr
          (I.branch_summable ρ) |>.hasSum.mul_left (instrument_l1_bound d) |>.summable)⟩)

def QComp.qbind (I : QComp d α) (f : α → QComp d β) : QComp d β where
  branch b :=
    { toFun := fun ρ => ∑' a, (f a).branch b (I.branch a ρ)
      map_add' := fun ρ₁ ρ₂ => by
        simp only [map_add]
        exact (bind_summable I f b ρ₁).tsum_add (bind_summable I f b ρ₂)
      map_smul' := fun c ρ => by
        simp only [map_smul]
        exact tsum_const_smul'' c
    }
  branch_psd b ρ hρ :=
    tsum_posSemidef
      (fun a => (f a).branch_psd b _ (I.branch_psd a ρ hρ))
      (bind_summable I f b ρ)
  branch_summable ρ := by
    -- From the joint (a,b)-summability, swap to get the b-marginal.
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    have huncurry := bind_uncurry_summable I f ρ
    -- Swap: Summable (fun (b, a) => (f a).branch b (I.branch a ρ))
    have hswap : Summable (fun p : β × α =>
        (f p.2).branch p.1 (I.branch p.2 ρ)) := by
      have : Summable ((fun p : α × β => (f p.1).branch p.2 (I.branch p.1 ρ)) ∘
          (Equiv.prodComm β α)) := by
        rw [show (fun p : α × β => (f p.1).branch p.2 (I.branch p.1 ρ)) =
            Function.uncurry (fun a b => (f a).branch b (I.branch a ρ)) from rfl]
        exact (Equiv.prodComm β α).summable_iff.mpr huncurry
      simp only [Equiv.prodComm_apply, Function.comp_def] at this
      exact this
    -- b-marginal: Summable (fun b => ∑' a, ...)
    exact hswap.prod
  branch_stp ρ hρ := by
    -- Push trace through inner tsum:
    have htrace_inner : ∀ b, (∑' a, (f a).branch b (I.branch a ρ)).trace =
        ∑' a, ((f a).branch b (I.branch a ρ)).trace := fun b =>
      trace_tsum (bind_summable I f b ρ)
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    simp_rw [htrace_inner]
    -- Swap sums via Fubini for the trace family:
    -- ∑' b, ∑' a, g(a,b) = ∑' a, ∑' b, g(a,b) where g(a,b) = trace((f a).branch b (...))
    have htrace_uncurry : Summable (Function.uncurry fun a b =>
        ((f a).branch b (I.branch a ρ)).trace) :=
      trace_summable (bind_uncurry_summable I f ρ)
    rw [htrace_uncurry.tsum_comm'
      (fun a => trace_summable ((f a).branch_summable (I.branch a ρ)))
      (fun b => trace_summable (bind_summable I f b ρ))]
    -- Goal: (∑' a, ∑' b, ((f a).branch b (I.branch a ρ)).trace).re ≤ ρ.trace.re
    -- = (∑' a, (∑' b, (f a).branch b (I.branch a ρ)).trace).re
    -- where the inner sum uses trace_tsum backwards.
    conv_lhs =>
      arg 1; arg 1; ext a
      rw [(trace_tsum ((f a).branch_summable (I.branch a ρ))).symm]
    -- Now: (∑' a, (∑' b, (f a).branch b (I.branch a ρ)).trace).re ≤ ρ.trace.re
    -- Apply .re via reCLM, then use (f a).branch_stp and I.branch_stp
    have hfa_stp : ∀ a, (∑' b, (f a).branch b (I.branch a ρ)).trace.re ≤
        (I.branch a ρ).trace.re := by
      intro a
      rw [trace_tsum ((f a).branch_summable (I.branch a ρ))]
      exact (f a).branch_stp (I.branch a ρ) (I.branch_psd a ρ hρ)
    have houter_summable : Summable (fun a =>
        (∑' b, (f a).branch b (I.branch a ρ)).trace) := by
      have : Summable (fun a => ∑' b, (f a).branch b (I.branch a ρ)) := by
        have huncurry := bind_uncurry_summable I f ρ
        exact huncurry.prod
      exact trace_summable this
    rw [Complex.re_tsum houter_summable]
    calc ∑' a, (∑' b, (f a).branch b (I.branch a ρ)).trace.re
        ≤ ∑' a, (I.branch a ρ).trace.re :=
          Summable.tsum_le_tsum hfa_stp
            (houter_summable.map Complex.reAddGroupHom Complex.continuous_re)
            (trace_re_summable (I.branch_summable ρ))
      _ = (∑' a, (I.branch a ρ).trace).re :=
          (Complex.re_tsum (trace_summable (I.branch_summable ρ))).symm
      _ ≤ ρ.trace.re := I.branch_stp ρ hρ

/-! ## Monad Laws -/

theorem QComp.qpure_qbind (a : α) (f : α → QComp d β) :
    QComp.qbind (QComp.qpure a) f = f a := by
  apply QComp.ext_fun; intro b ρ
  show ∑' a', (f a').branch b ((QComp.qpure a).branch a' ρ) = (f a).branch b ρ
  simp only [QComp.qpure]
  rw [tsum_eq_single a (fun a' ha' => by simp [ha', map_zero])]
  simp

theorem QComp.qbind_qpure (I : QComp d α) :
    QComp.qbind I QComp.qpure = I := by
  apply QComp.ext_fun; intro b ρ
  show ∑' a, (QComp.qpure a).branch b (I.branch a ρ) = I.branch b ρ
  simp only [QComp.qpure]
  rw [tsum_eq_single b (fun a ha => by simp [Ne.symm ha])]
  simp

theorem QComp.qbind_assoc (I : QComp d α) (f : α → QComp d β)
    (g : β → QComp d γ) :
    QComp.qbind (QComp.qbind I f) g =
    QComp.qbind I (fun a => QComp.qbind (f a) g) := by
  apply QComp.ext_fun; intro c ρ
  show ∑' b, (g b).branch c (∑' a, (f a).branch b (I.branch a ρ)) =
       ∑' a, ∑' b, (g b).branch c ((f a).branch b (I.branch a ρ))
  have hdist : ∀ b', (g b').branch c (∑' a, (f a).branch b' (I.branch a ρ)) =
      ∑' a, (g b').branch c ((f a).branch b' (I.branch a ρ)) :=
    fun b' => ContinuousLinearMap.map_tsum ((g b').branch c).toContinuousLinearMap
      (QComp.bind_summable I f b' ρ)
  simp_rw [hdist]
  exact (QComp.bind_summable_uncurry I f g c ρ).tsum_comm'
    (fun a => QComp.bind_summable (f a) g c (I.branch a ρ))
    (fun b => (QComp.bind_summable I f b ρ).map ((g b).branch c).toContinuousLinearMap
      ((g b).branch c).toContinuousLinearMap.continuous)

/-! ## Monad Instance -/

instance : Monad (QComp d) where
  pure := QComp.qpure
  bind := QComp.qbind

instance : LawfulMonad (QComp d) := LawfulMonad.mk'
  (id_map := fun m => QComp.qbind_qpure m)
  (pure_bind := fun a f => QComp.qpure_qbind a f)
  (bind_assoc := fun m f g => QComp.qbind_assoc m f g)

/-! ## Bind with Fail -/

theorem QComp.qbind_fail (c : QComp d α) :
    QComp.qbind c (fun _ => (QComp.qfail : QComp d β)) = QComp.qfail := by
  apply QComp.ext_fun; intro b ρ
  show ∑' a, ((0 : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (c.branch a ρ)) = 0
  simp only [LinearMap.zero_apply, tsum_zero]

theorem QComp.qfail_qbind (f : α → QComp d β) :
    QComp.qbind (QComp.qfail : QComp d α) f = QComp.qfail := by
  apply QComp.ext_fun; intro b ρ
  show ∑' a, (f a).branch b (QComp.qfail.branch a ρ) = 0
  simp only [QComp.qfail, LinearMap.zero_apply, map_zero, tsum_zero]

/-! ## Parallel Composition on Sum -/

def QComp.mapSum (f : α → QComp d β) (g : γ → QComp d δ) :
    (α ⊕ γ) → QComp d (β ⊕ δ)
  | .inl a => QComp.qbind (f a) (fun b => QComp.qpure (.inl b))
  | .inr c => QComp.qbind (g c) (fun d' => QComp.qpure (.inr d'))

theorem QComp.mapSum_inl (f : α → QComp d β) (g : γ → QComp d δ) (a : α) :
    QComp.mapSum f g (.inl a) = f a >>= fun b => pure (.inl b) := rfl

theorem QComp.mapSum_inr (f : α → QComp d β) (g : γ → QComp d δ) (c : γ) :
    QComp.mapSum f g (.inr c) = g c >>= fun d' => pure (.inr d') := rfl

theorem QComp.mapSum_pure_pure :
    QComp.mapSum (QComp.qpure : α → QComp d α)
      (QComp.qpure : β → QComp d β) = QComp.qpure := by
  funext x; cases x with
  | inl a => exact QComp.qpure_qbind a _
  | inr b => exact QComp.qpure_qbind b _

theorem QComp.mapSum_pure_kleisli (f : β → QComp d γ) (g : γ → QComp d δ) :
    (fun x : α ⊕ β => QComp.mapSum QComp.qpure f x >>=
      QComp.mapSum QComp.qpure g) =
    QComp.mapSum QComp.qpure (fun b => f b >>= g) := by
  funext x; cases x with
  | inl a =>
    -- Both sides reduce to qpure (.inl a) via mapSum + qpure_qbind
    show QComp.qbind (QComp.mapSum QComp.qpure f (.inl a))
      (QComp.mapSum QComp.qpure g) = _
    simp only [QComp.mapSum]
    rw [QComp.qpure_qbind, QComp.qpure_qbind]; rfl
  | inr b =>
    -- LHS: bind(bind(f b)(pure ∘ inr))(mapSum pure g)
    -- = bind(f b)(fun c => bind(pure(inr c))(mapSum pure g))  [assoc]
    -- = bind(f b)(fun c => mapSum pure g (inr c))  [pure_bind]
    -- = bind(f b)(fun c => bind(g c)(pure ∘ inr))  [mapSum def]
    -- = bind(f b >>= g)(pure ∘ inr)  [assoc]
    -- = RHS
    show QComp.qbind (QComp.mapSum QComp.qpure f (.inr b))
      (QComp.mapSum QComp.qpure g) =
      QComp.qbind (QComp.qbind (f b) g) (fun d' => QComp.qpure (.inr d'))
    simp only [QComp.mapSum]
    rw [QComp.qbind_assoc]
    conv_rhs => rw [QComp.qbind_assoc]
    congr 1; funext c
    rw [QComp.qpure_qbind]; rfl

/-! ## Probability and Distance Helpers -/

/-- Probability of outcome `true` for `I : QComp d Bool` at state `ρ`. -/
def prTrue_Q (I : QComp d Bool) (ρ : DensityMatrix d) : ℝ≥0∞ :=
  ENNReal.ofReal ((I.branch true ρ.val).trace.re)

def absDiff (a b : ℝ≥0∞) : ℝ≥0∞ := (a - b) ⊔ (b - a)

theorem absDiff_self (a : ℝ≥0∞) : absDiff a a = 0 := by
  simp [absDiff, tsub_self]

theorem absDiff_comm (a b : ℝ≥0∞) : absDiff a b = absDiff b a := by
  simp [absDiff, max_comm]

theorem absDiff_triangle (a b c : ℝ≥0∞) :
    absDiff a c ≤ absDiff a b + absDiff b c := by
  simp only [absDiff]
  apply max_le
  · calc a - c ≤ (a - b) + (b - c) := tsub_le_tsub_add_tsub
      _ ≤ ((a - b) ⊔ (b - a)) + ((b - c) ⊔ (c - b)) :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
  · calc c - a ≤ (c - b) + (b - a) := tsub_le_tsub_add_tsub
      _ ≤ ((c - b) ⊔ (b - c)) + ((b - a) ⊔ (a - b)) :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
      _ = ((a - b) ⊔ (b - a)) + ((b - c) ⊔ (c - b)) := by
        rw [max_comm (c - b), max_comm (b - a), add_comm]

theorem weighted_bound {ι : Type} (w f g : ι → ℝ≥0∞) (ε : ℝ≥0∞)
    (hfg : ∀ i, f i ≤ g i + ε) (hw : ∑' i, w i ≤ 1) :
    ∑' i, w i * f i ≤ (∑' i, w i * g i) + ε := by
  calc ∑' i, w i * f i
      ≤ ∑' i, w i * (g i + ε) := by
        apply ENNReal.tsum_le_tsum; intro i; exact mul_le_mul_right (hfg i) _
    _ = ∑' i, (w i * g i + w i * ε) := by
        congr 1; funext i; exact mul_add (w i) (g i) ε
    _ = (∑' i, w i * g i) + ∑' i, w i * ε := ENNReal.tsum_add
    _ = (∑' i, w i * g i) + (∑' i, w i) * ε := by
        congr 1; exact ENNReal.tsum_mul_right
    _ ≤ (∑' i, w i * g i) + 1 * ε := by
        gcongr
    _ = (∑' i, w i * g i) + ε := by rw [one_mul]

/-- `absDiff a b ≤ ε` iff both `a ≤ b + ε` and `b ≤ a + ε`. -/
theorem absDiff_le_iff {a b ε : ℝ≥0∞} :
    absDiff a b ≤ ε ↔ (a ≤ b + ε ∧ b ≤ a + ε) := by
  constructor
  · intro h
    constructor
    · have : a - b ≤ ε := le_trans (le_max_left _ _) h
      calc a ≤ a - b + b := le_tsub_add
        _ ≤ ε + b := by gcongr
        _ = b + ε := add_comm _ _
    · have : b - a ≤ ε := le_trans (le_max_right _ _) h
      calc b ≤ b - a + a := le_tsub_add
        _ ≤ ε + a := by gcongr
        _ = a + ε := add_comm _ _
  · intro ⟨hab, hba⟩
    simp only [absDiff]
    apply max_le
    · exact tsub_le_iff_right.mpr (by rwa [add_comm])
    · exact tsub_le_iff_right.mpr (by rwa [add_comm])

/-- PSD matrix with zero trace is the zero matrix (wrapper for Mathlib). -/
private theorem psd_zero_of_trace_zero {M : Matrix (Fin d) (Fin d) ℂ}
    (hM : M.PosSemidef) (htr : M.trace = 0) : M = 0 :=
  hM.trace_eq_zero_iff.mp htr

/-- Imaginary part of the trace of a Hermitian matrix is zero. -/
theorem trace_im_zero_of_hermitian {M : Matrix (Fin d) (Fin d) ℂ}
    (hH : M.IsHermitian) : M.trace.im = 0 := by
  unfold Matrix.trace Matrix.diag
  rw [show (∑ x : Fin d, M x x).im = ∑ x : Fin d, (M x x).im from
    map_sum Complex.imAddGroupHom _ _]
  apply Finset.sum_eq_zero; intro i _
  exact Complex.conj_eq_iff_im.mp (congr_fun (congr_fun hH i) i)

set_option maxHeartbeats 800000 in
/-- Weighted average bound for prTrue_Q under qbind.
    The core technical lemma: post-composition with ε-close continuations
    preserves the ε bound on prTrue_Q, for any shared prefix `c`. -/
theorem absDiff_prTrue_Q_qbind_le {α : Type} (c : QComp d α)
    (k₁ k₂ : α → QComp d Bool)
    (ρ : DensityMatrix d) (ε : ℝ≥0∞)
    (hk : ∀ a (ρ' : DensityMatrix d),
      absDiff (prTrue_Q (k₁ a) ρ') (prTrue_Q (k₂ a) ρ') ≤ ε) :
    absDiff (prTrue_Q (QComp.qbind c k₁) ρ)
            (prTrue_Q (QComp.qbind c k₂) ρ) ≤ ε := by
  -- Summability facts
  have hsum₁ : Summable (fun a => (k₁ a).branch true (c.branch a ρ.val)) :=
    QComp.bind_summable c k₁ true ρ.val
  have hsum₂ : Summable (fun a => (k₂ a).branch true (c.branch a ρ.val)) :=
    QComp.bind_summable c k₂ true ρ.val
  -- Unfold prTrue_Q of qbind to tsum of component traces
  have eq₁ : prTrue_Q (QComp.qbind c k₁) ρ =
      ENNReal.ofReal (∑' a, ((k₁ a).branch true (c.branch a ρ.val)).trace.re) := by
    simp only [prTrue_Q, QComp.qbind, LinearMap.coe_mk, AddHom.coe_mk]
    congr 1; rw [trace_tsum hsum₁, Complex.re_tsum (trace_summable hsum₁)]
  have eq₂ : prTrue_Q (QComp.qbind c k₂) ρ =
      ENNReal.ofReal (∑' a, ((k₂ a).branch true (c.branch a ρ.val)).trace.re) := by
    simp only [prTrue_Q, QComp.qbind, LinearMap.coe_mk, AddHom.coe_mk]
    congr 1; rw [trace_tsum hsum₂, Complex.re_tsum (trace_summable hsum₂)]
  rw [eq₁, eq₂]
  -- Each intermediate state c.branch a ρ.val is PSD
  have hσ_psd : ∀ a, (c.branch a ρ.val).PosSemidef :=
    fun a => c.branch_psd a ρ.val ρ.psd
  -- Each term is non-negative
  have hnn₁ : ∀ a, 0 ≤ ((k₁ a).branch true (c.branch a ρ.val)).trace.re :=
    fun a => trace_re_nonneg_of_psd ((k₁ a).branch_psd true _ (hσ_psd a))
  have hnn₂ : ∀ a, 0 ≤ ((k₂ a).branch true (c.branch a ρ.val)).trace.re :=
    fun a => trace_re_nonneg_of_psd ((k₂ a).branch_psd true _ (hσ_psd a))
  -- Convert to ENNReal tsum
  rw [ENNReal.ofReal_tsum_of_nonneg hnn₁ (trace_re_summable hsum₁),
      ENNReal.ofReal_tsum_of_nonneg hnn₂ (trace_re_summable hsum₂)]
  -- Suffices to show both ≤ directions
  rw [absDiff_le_iff]
  -- Weight function: w(a) = ofReal(trace(c.branch a ρ.val).re)
  -- Weights sum to ≤ 1 (from sub-TP of c and trace(ρ) = 1)
  have hw_sum : ∑' a, ENNReal.ofReal (c.branch a ρ.val).trace.re ≤ 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun a => trace_re_nonneg_of_psd (hσ_psd a))
      (trace_re_summable (c.branch_summable ρ.val))]
    calc ENNReal.ofReal (∑' a, (c.branch a ρ.val).trace.re)
        = ENNReal.ofReal (∑' a, (c.branch a ρ.val).trace).re := by
          congr 1; exact (Complex.re_tsum (trace_summable (c.branch_summable ρ.val))).symm
      _ ≤ ENNReal.ofReal ρ.val.trace.re :=
          ENNReal.ofReal_le_ofReal (c.branch_stp ρ.val ρ.psd)
      _ = 1 := by rw [ρ.tr_one]; simp
  -- Per-component bound: for each a, need both directions with weight w(a) * ε
  have hcomp : ∀ a,
      ENNReal.ofReal ((k₁ a).branch true (c.branch a ρ.val)).trace.re ≤
      ENNReal.ofReal ((k₂ a).branch true (c.branch a ρ.val)).trace.re +
        ENNReal.ofReal (c.branch a ρ.val).trace.re * ε ∧
      ENNReal.ofReal ((k₂ a).branch true (c.branch a ρ.val)).trace.re ≤
      ENNReal.ofReal ((k₁ a).branch true (c.branch a ρ.val)).trace.re +
        ENNReal.ofReal (c.branch a ρ.val).trace.re * ε := by
    intro a
    by_cases htr : (c.branch a ρ.val).trace = 0
    · -- Zero trace: c.branch a ρ.val = 0, all terms vanish
      have hzero : c.branch a ρ.val = 0 := psd_zero_of_trace_zero (hσ_psd a) htr
      simp [hzero, map_zero, Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero]
    · -- Non-zero trace: normalize to density matrix
      have him : (c.branch a ρ.val).trace.im = 0 :=
        trace_im_zero_of_hermitian (hσ_psd a).isHermitian
      have htr_re_pos : 0 < (c.branch a ρ.val).trace.re := by
        rcases lt_or_eq_of_le (trace_re_nonneg_of_psd (hσ_psd a)) with h | h
        · exact h
        · exact absurd (Complex.ext h.symm him) htr
      set t := (c.branch a ρ.val).trace.re
      have ht_ne : (↑t : ℂ) ≠ 0 := by
        simp; exact ne_of_gt htr_re_pos
      -- Normalized matrix ρ'_val = (↑t⁻¹ : ℂ) • c.branch a ρ.val
      have hρ'_psd : ((↑t⁻¹ : ℂ) • c.branch a ρ.val).PosSemidef :=
        (hσ_psd a).smul (by
          rw [Complex.nonneg_iff]
          exact ⟨le_of_lt (inv_pos_of_pos htr_re_pos), by simp⟩)
      have htr_eq : (c.branch a ρ.val).trace = (↑t : ℂ) :=
        Complex.ext_iff.mpr ⟨rfl, by simpa using him⟩
      have hρ'_tr : ((↑t⁻¹ : ℂ) • c.branch a ρ.val).trace = 1 := by
        rw [Matrix.trace_smul, htr_eq,
          show (↑t⁻¹ : ℂ) = (↑t : ℂ)⁻¹ from by push_cast; ring]
        exact inv_mul_cancel₀ ht_ne
      set ρ' : DensityMatrix d :=
        ⟨(↑t⁻¹ : ℂ) • c.branch a ρ.val, hρ'_psd, hρ'_tr⟩
      -- Linearity: c.branch a ρ.val = (↑t : ℂ) • ρ'.val
      have hσ_eq : c.branch a ρ.val = (↑t : ℂ) • ρ'.val := by
        show c.branch a ρ.val = (↑t : ℂ) • ((↑t⁻¹ : ℂ) • c.branch a ρ.val)
        rw [smul_smul,
          show (↑t : ℂ) * (↑t⁻¹ : ℂ) = 1 from by
            rw [show (↑t⁻¹ : ℂ) = (↑t : ℂ)⁻¹ from by push_cast; ring]
            exact mul_inv_cancel₀ ht_ne]
        simp
      -- Scale factorization: (ki a).branch true (c.branch a ρ.val) = ↑t • (ki a).branch true ρ'.val
      -- This follows from hσ_eq and linearity of (ki a).branch true
      have hscale_mat : ∀ (ki : α → QComp d Bool),
          (ki a).branch true (c.branch a ρ.val) =
          (↑t : ℂ) • (ki a).branch true ρ'.val := by
        intro ki; rw [hσ_eq]; exact map_smul _ _ _
      have hscale : ∀ (ki : α → QComp d Bool),
          ((ki a).branch true (c.branch a ρ.val)).trace.re =
          t * ((ki a).branch true ρ'.val).trace.re := by
        intro ki
        rw [hscale_mat ki, Matrix.trace_smul]
        simp
      -- Apply hk to the normalized state
      have hk_a := absDiff_le_iff.mp (hk a ρ')
      -- Unfold prTrue_Q in hk_a to get ENNReal.ofReal form
      change ENNReal.ofReal ((k₁ a).branch true ρ'.val).trace.re ≤
          ENNReal.ofReal ((k₂ a).branch true ρ'.val).trace.re + ε ∧
        ENNReal.ofReal ((k₂ a).branch true ρ'.val).trace.re ≤
          ENNReal.ofReal ((k₁ a).branch true ρ'.val).trace.re + ε at hk_a
      constructor
      · rw [hscale k₁, hscale k₂,
            ENNReal.ofReal_mul (le_of_lt htr_re_pos),
            ENNReal.ofReal_mul (le_of_lt htr_re_pos), ← mul_add]
        exact mul_le_mul_right hk_a.1 _
      · rw [hscale k₁, hscale k₂,
            ENNReal.ofReal_mul (le_of_lt htr_re_pos),
            ENNReal.ofReal_mul (le_of_lt htr_re_pos), ← mul_add]
        exact mul_le_mul_right hk_a.2 _
  -- Assemble: ∑ f ≤ ∑ g + ε (both directions) using weighted sum bound
  have assemble : ∀ (f g : α → ℝ≥0∞),
      (∀ a, f a ≤ g a + ENNReal.ofReal (c.branch a ρ.val).trace.re * ε) →
      (∑' a, f a ≤ (∑' a, g a) + ε) := by
    intro f g hfg
    calc ∑' a, f a
        ≤ ∑' a, (g a + ENNReal.ofReal (c.branch a ρ.val).trace.re * ε) :=
          ENNReal.tsum_le_tsum hfg
      _ = (∑' a, g a) + ∑' a, ENNReal.ofReal (c.branch a ρ.val).trace.re * ε :=
          ENNReal.tsum_add
      _ = (∑' a, g a) + (∑' a, ENNReal.ofReal (c.branch a ρ.val).trace.re) * ε := by
          congr 1; exact ENNReal.tsum_mul_right
      _ ≤ (∑' a, g a) + 1 * ε := by gcongr
      _ = (∑' a, g a) + ε := by rw [one_mul]
  exact ⟨assemble _ _ (fun a => (hcomp a).1), assemble _ _ (fun a => (hcomp a).2)⟩

/-! ## Smart Constructor: Kraus Operator QComp -/

/-- Build a QComp from Kraus operators over a `Fintype` index.
    Given measurement operators `M : α → Matrix` with completeness `∑ M†M = I`,
    each branch maps `ρ ↦ M(a) ρ M(a)†`.
    Automatically proves PSD preservation, summability, and trace preservation. -/
def QComp.ofKraus [Fintype α] (M : α → Matrix (Fin d) (Fin d) ℂ)
    (h_complete : ∑ a, (M a)ᴴ * M a = 1) : QComp d α where
  branch a := {
    toFun := fun ρ => M a * ρ * (M a)ᴴ
    map_add' := fun ρ₁ ρ₂ => by simp [mul_add, add_mul]
    map_smul' := fun c ρ => by
      show M a * (c • ρ) * (M a)ᴴ = c • (M a * ρ * (M a)ᴴ)
      simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  }
  branch_psd a ρ hρ := hρ.mul_mul_conjTranspose_same (M a)
  branch_summable ρ :=
    summable_of_ne_finset_zero (s := Finset.univ)
      (fun a ha => absurd (Finset.mem_univ a) ha)
  branch_stp ρ _ := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [tsum_fintype]
    conv_lhs => arg 1; arg 2; ext a; rw [trace_mul_cycle]
    rw [show ∑ a : α, ((M a)ᴴ * M a * ρ).trace =
      ((∑ a : α, (M a)ᴴ * M a) * ρ).trace from by
      rw [Finset.sum_mul, trace_sum]]
    rw [h_complete, Matrix.one_mul]

/-- `QComp.ofKraus` branch unfolds to conjugation. -/
@[simp]
theorem QComp.ofKraus_branch [Fintype α] (M : α → Matrix (Fin d) (Fin d) ℂ)
    (h : ∑ a, (M a)ᴴ * M a = 1) (a : α) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (QComp.ofKraus M h).branch a ρ = M a * ρ * (M a)ᴴ := rfl

end CatCrypt.Quantum
