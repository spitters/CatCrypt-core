/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCMonad.QDistHub
public import CatCryptCore.Quantum.HelstromPriors

/-!
# The quantum distances as trace norms

For instruments `C₁ C₂ : QComp d β` with finitely many outcomes, write
`X_b = C₁ᵇ ρ - C₂ᵇ ρ` for the difference of the output branches at an input state `ρ`.
This file computes the distances of `QDistHub` in terms of the trace norms of the `X_b`.

* `abs_sum_effect_trace_le` and `exists_effect_abs_sum_trace_eq`: over families of
  effects `E_b`, the maximum of `|∑_b Re tr(E_b X_b)|` is
  `(∑_b ‖X_b‖₁ + |∑_b Re tr X_b|) / 2`.
* D7, `qdist_const_eq`: `qdist` of constant families is the supremum over input states of
  `(∑_b ‖X_b‖₁ + |∑_b Re tr X_b|) / 2`.
* D7', `qdist_const_eq_of_tp`: for trace-preserving instruments the trace term vanishes,
  and `qdist` is the supremum of half the trace norm of the classical-quantum output.
* D7'', `qdist_unit_eq_iSup_traceDist`: for channels, `qdist` is the supremum over inputs
  of the trace distance of the outputs.
* `qdist_eq_iSup_traceNorm`: the Kleisli form, a supremum over inputs and states.
* D8, `qdistDiamond_const_eq`: the diamond distance is the supremum over reference
  dimensions `r` and states on `d * r` of the same expression for `localOp₁`.
* `localOp₁_tp`: `localOp₁` of a trace-preserving instrument is trace preserving.
* D8', `qdistDiamond_const_eq_of_tp`: for trace-preserving completely positive
  instruments, the diamond distance is `½ sup_r ‖(Φ₁ - Φ₂) ⊗ id_r‖₁` in its
  supremum-over-ancilla form.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCMonad.QDistTrace

open CatCrypt.Quantum
open CatCrypt.Quantum.TensorProduct
open CatCrypt.Quantum.HelstromPriors
open CatCrypt.Crypto.UCMonad.DiamondNorm
open CatCrypt.Crypto.UCMonad.QIndistDiamond
open CatCrypt.Crypto.UCMonad.QDistHub
open UCMonad.QuantumUC
open scoped ENNReal ComplexOrder Matrix

variable {d : ℕ} {α β : Type}

/-- The difference of two output branches at a state is Hermitian. -/
theorem outHerm (C₁ C₂ : QComp d β) (ρ : DensityMatrix d) (b : β) :
    (C₁.branch b ρ.val - C₂.branch b ρ.val).IsHermitian :=
  (C₁.branch_psd b _ ρ.psd).isHermitian.sub (C₂.branch_psd b _ ρ.psd).isHermitian

/-! ## Families of effects against Hermitian families -/

section Effects

variable {n : Type} [Fintype n] [DecidableEq n] [Fintype β]

/-- For effects `E_b` and Hermitian `X_b`,
`|∑_b Re tr(E_b X_b)| ≤ (∑_b ‖X_b‖₁ + |∑_b Re tr X_b|) / 2`. -/
theorem abs_sum_effect_trace_le (X : β → Matrix n n ℂ) (hX : ∀ b, (X b).IsHermitian)
    (E : β → Matrix n n ℂ) (hE : ∀ b, IsEffect (E b)) :
    |∑ b, (E b * X b).trace.re| ≤
      (∑ b, traceNormH (X b) (hX b) + |∑ b, (X b).trace.re|) / 2 := by
  have hup : ∑ b, (E b * X b).trace.re ≤
      (∑ b, (X b).trace.re + ∑ b, traceNormH (X b) (hX b)) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_le_sum fun b _ => effect_trace_le_half_trace_add (X b) (hX b) (E b) (hE b)
  have hlo : -∑ b, (E b * X b).trace.re ≤
      (-∑ b, (X b).trace.re + ∑ b, traceNormH (X b) (hX b)) / 2 := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
      Finset.sum_div]
    refine Finset.sum_le_sum fun b _ => ?_
    have h := effect_trace_le_half_trace_add (-X b) (hX b).neg (E b) (hE b)
    rwa [traceNormH_neg (X b) (hX b), Matrix.mul_neg, Matrix.trace_neg, Matrix.trace_neg,
      Complex.neg_re, Complex.neg_re] at h
  rw [abs_le]
  constructor <;> linarith [le_abs_self (∑ b, (X b).trace.re),
    neg_abs_le (∑ b, (X b).trace.re)]

/-- The bound of `abs_sum_effect_trace_le` is attained by a family of effects. -/
theorem exists_effect_abs_sum_trace_eq (X : β → Matrix n n ℂ) (hX : ∀ b, (X b).IsHermitian) :
    ∃ (E : β → Matrix n n ℂ) (_ : ∀ b, IsEffect (E b)),
      |∑ b, (E b * X b).trace.re| =
        (∑ b, traceNormH (X b) (hX b) + |∑ b, (X b).trace.re|) / 2 := by
  have hS : 0 ≤ ∑ b, traceNormH (X b) (hX b) :=
    Finset.sum_nonneg fun b _ => traceNormH_nonneg (X b) (hX b)
  choose P hP hPeq using fun b => exists_effect_trace_eq_half_trace_add (X b) (hX b)
  choose N hN hNeq using fun b => exists_effect_trace_eq_half_trace_add (-X b) (hX b).neg
  by_cases hT : 0 ≤ ∑ b, (X b).trace.re
  · refine ⟨P, hP, ?_⟩
    rw [Finset.sum_congr rfl fun b _ => hPeq b, ← Finset.sum_div, Finset.sum_add_distrib,
      abs_of_nonneg hT, abs_of_nonneg]
    · ring
    · linarith
  · have hT' := not_le.mp hT
    refine ⟨N, hN, ?_⟩
    have h : ∀ b, (N b * X b).trace.re =
        -((-(X b).trace.re + traceNormH (X b) (hX b)) / 2) := by
      intro b
      have hb := hNeq b
      rw [traceNormH_neg (X b) (hX b), Matrix.mul_neg, Matrix.trace_neg, Matrix.trace_neg,
        Complex.neg_re, Complex.neg_re] at hb
      linarith
    rw [Finset.sum_congr rfl fun b _ => h b, Finset.sum_neg_distrib, abs_neg,
      ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_neg_distrib, abs_of_neg hT',
      abs_of_nonneg]
    · ring
    · linarith

end Effects

/-! ## Acceptance traces of measured composites -/

/-- The accept trace of `C` followed by the measurements of effects `F_b` is
`∑_b Re tr(F_b C_b Y)`. -/
theorem trace_re_qbind_effectMeas [Fintype β] (C : QComp d β) (F : β → Matrix (Fin d) (Fin d) ℂ)
    (hF : ∀ b, IsEffect (F b)) (Y : Matrix (Fin d) (Fin d) ℂ) :
    ((C.qbind fun b => effectMeas (F b) (hF b)).branch true Y).trace.re =
      ∑ b, (F b * C.branch b Y).trace.re := by
  rw [trace_qbind_true, tsum_fintype, Complex.re_sum]
  exact Finset.sum_congr rfl fun b _ => by rw [trace_effectMeas_true]

private theorem absDiff_ofReal_eq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    absDiff (ENNReal.ofReal x) (ENNReal.ofReal y) = ENNReal.ofReal |x - y| := by
  rw [absDiff, ← ENNReal.ofReal_sub x hy, ← ENNReal.ofReal_sub y hx, ← ENNReal.ofReal_max,
    abs_eq_max_neg, neg_sub]

/-- The distinguishing advantage of the measurements of effects `F_b` between `C₁` and
`C₂` at `ρ` is `|∑_b Re tr(F_b X_b)|`. -/
theorem absDiff_prTrue_effectMeas [Fintype β] (C₁ C₂ : QComp d β)
    (F : β → Matrix (Fin d) (Fin d) ℂ) (hF : ∀ b, IsEffect (F b)) (ρ : DensityMatrix d) :
    absDiff (prTrue_Q (C₁.qbind fun b => effectMeas (F b) (hF b)) ρ)
        (prTrue_Q (C₂.qbind fun b => effectMeas (F b) (hF b)) ρ) =
      ENNReal.ofReal |∑ b, (F b * (C₁.branch b ρ.val - C₂.branch b ρ.val)).trace.re| := by
  unfold prTrue_Q
  rw [absDiff_ofReal_eq (trace_re_nonneg_of_psd (QComp.branch_psd _ true _ ρ.psd))
    (trace_re_nonneg_of_psd (QComp.branch_psd _ true _ ρ.psd)),
    trace_re_qbind_effectMeas, trace_re_qbind_effectMeas, ← Finset.sum_sub_distrib]
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

/-! ## D7 and its corollaries -/

/-- D7: `qdist` of constant families with finitely many outcomes is the supremum over
input states of `(∑_b ‖X_b‖₁ + |∑_b Re tr X_b|) / 2`. -/
theorem qdist_const_eq [Fintype β] (C₁ C₂ : QComp d β) :
    qdist (fun _ : Unit => C₁) (fun _ => C₂) =
      ⨆ ρ : DensityMatrix d, ENNReal.ofReal
        ((∑ b, traceNormH (C₁.branch b ρ.val - C₂.branch b ρ.val) (outHerm C₁ C₂ ρ b)
          + |∑ b, (C₁.branch b ρ.val - C₂.branch b ρ.val).trace.re|) / 2) := by
  apply le_antisymm
  · simp only [qdist]
    refine iSup_le fun D => iSup_le fun _ => iSup_le fun ρ => ?_
    rw [prTrue_Q_qbind_congr C₁ D (effectDist D) (trace_effectDist_true D),
      prTrue_Q_qbind_congr C₂ D (effectDist D) (trace_effectDist_true D)]
    refine le_iSup_of_le ρ ?_
    exact (absDiff_prTrue_effectMeas C₁ C₂ (fun b => dualMap ((D b).branch true) 1)
      (fun b => isEffect_dualMap_branch (D b)) ρ).trans_le
      (ENNReal.ofReal_le_ofReal (abs_sum_effect_trace_le _ (outHerm C₁ C₂ ρ) _
        fun b => isEffect_dualMap_branch (D b)))
  · refine iSup_le fun ρ => ?_
    obtain ⟨F, hF, hEq⟩ := exists_effect_abs_sum_trace_eq _ (outHerm C₁ C₂ ρ)
    refine le_iSup_of_le (fun b => effectMeas (F b) (hF b)) (le_iSup_of_le () ?_)
    refine le_iSup_of_le ρ ?_
    exact (congrArg ENNReal.ofReal hEq.symm).le.trans (absDiff_prTrue_effectMeas C₁ C₂ F hF ρ).ge

/-- D7': for trace-preserving instruments, `qdist` of constant families is the supremum
over input states of half the trace norm of the classical-quantum output difference. -/
theorem qdist_const_eq_of_tp [Fintype β] (C₁ C₂ : QComp d β)
    (h₁ : ∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef → ∑ b, (C₁.branch b ρ).trace = ρ.trace)
    (h₂ : ∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef → ∑ b, (C₂.branch b ρ).trace = ρ.trace) :
    qdist (fun _ : Unit => C₁) (fun _ => C₂) =
      ⨆ ρ : DensityMatrix d, ENNReal.ofReal
        ((1 / 2 : ℝ) * ∑ b, traceNormH (C₁.branch b ρ.val - C₂.branch b ρ.val)
          (outHerm C₁ C₂ ρ b)) := by
  rw [qdist_const_eq]
  refine iSup_congr fun ρ => ?_
  have hT : ∑ b, (C₁.branch b ρ.val - C₂.branch b ρ.val).trace.re = 0 := by
    simp only [Matrix.trace_sub, Complex.sub_re, Finset.sum_sub_distrib, ← Complex.re_sum,
      h₁ _ ρ.psd, h₂ _ ρ.psd, sub_self]
  rw [hT, abs_zero, add_zero]
  ring_nf

/-- D7'': for channels, `qdist` of constant families is the supremum over input states
of the trace distance of the outputs. -/
theorem qdist_unit_eq_iSup_traceDist (C₁ C₂ : QComp d Unit)
    (h₁ : ∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef → (C₁.branch () ρ).trace = ρ.trace)
    (h₂ : ∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef → (C₂.branch () ρ).trace = ρ.trace) :
    qdist (fun _ : Unit => C₁) (fun _ => C₂) =
      ⨆ ρ : DensityMatrix d, ENNReal.ofReal
        (traceDist (C₁.branch () ρ.val) (C₂.branch () ρ.val)
          (C₁.branch_psd () _ ρ.psd) (C₂.branch_psd () _ ρ.psd) (outHerm C₁ C₂ ρ ())) := by
  rw [qdist_const_eq_of_tp C₁ C₂ (fun ρ hρ => by simpa using h₁ ρ hρ)
    (fun ρ hρ => by simpa using h₂ ρ hρ)]
  simp only [Fintype.sum_unique, traceDist]

/-- The Kleisli form of D7: `qdist` of families with finitely many outcomes is the
supremum over inputs and states of `(∑_b ‖X_b‖₁ + |∑_b Re tr X_b|) / 2`. -/
theorem qdist_eq_iSup_traceNorm [Fintype β] (f g : α → QComp d β) :
    qdist f g = ⨆ (a : α) (ρ : DensityMatrix d), ENNReal.ofReal
      ((∑ b, traceNormH ((f a).branch b ρ.val - (g a).branch b ρ.val) (outHerm (f a) (g a) ρ b)
        + |∑ b, ((f a).branch b ρ.val - (g a).branch b ρ.val).trace.re|) / 2) := by
  rw [qdist_eq_iSup_const]
  exact iSup_congr fun a => qdist_const_eq (f a) (g a)

/-! ## D8 and D8' -/

/-- D8: the diamond distance of constant families is the supremum over reference
dimensions `r` and states on `d * r` of the D7 expression for `localOp₁`. -/
theorem qdistDiamond_const_eq [Fintype β] (C₁ C₂ : QComp d β)
    (hc₁ : ∀ b, IsCPMap (C₁.branch b)) (hc₂ : ∀ b, IsCPMap (C₂.branch b)) :
    qdistDiamond (fun _ : Unit => C₁) (fun _ => C₂)
        (QIndistDiamond.constCP C₁ hc₁) (QIndistDiamond.constCP C₂ hc₂) =
      ⨆ (r : ℕ) (ρ : DensityMatrix (d * r)), ENNReal.ofReal
        ((∑ b, traceNormH ((localOp₁ (d₂ := r) C₁ hc₁).branch b ρ.val
              - (localOp₁ (d₂ := r) C₂ hc₂).branch b ρ.val)
            (outHerm (localOp₁ C₁ hc₁) (localOp₁ C₂ hc₂) ρ b)
          + |∑ b, ((localOp₁ (d₂ := r) C₁ hc₁).branch b ρ.val
              - (localOp₁ (d₂ := r) C₂ hc₂).branch b ρ.val).trace.re|) / 2) := by
  unfold qdistDiamond withRef
  exact iSup_congr fun r => qdist_const_eq (localOp₁ (d₂ := r) C₁ hc₁) (localOp₁ C₂ hc₂)

/-- `localOp₁` of a trace-preserving instrument is trace preserving. -/
theorem localOp₁_tp [Fintype β] {r : ℕ} (C : QComp d β) (hc : ∀ b, IsCPMap (C.branch b))
    (h : ∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef → ∑ b, (C.branch b ρ).trace = ρ.trace)
    (σ : Matrix (Fin (d * r)) (Fin (d * r)) ℂ) (hσ : σ.PosSemidef) :
    ∑ b, ((localOp₁ (d₂ := r) C hc).branch b σ).trace = σ.trace := by
  have hb : ∀ b, ((localOp₁ (d₂ := r) C hc).branch b σ).trace =
      ∑ k : Fin r, (C.branch b (extractBlock σ k k)).trace :=
    fun b => trace_localOp₁_fun C b σ
  rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun k _ => h _ (extractBlock_diag_psd σ hσ k)]
  exact sum_extractBlock_diag_trace σ

/-- D8': for trace-preserving completely positive instruments, the diamond distance of
constant families is the supremum over reference dimensions and states of half the trace
norm of the output difference of the reference-extended instruments. -/
theorem qdistDiamond_const_eq_of_tp [Fintype β] (C₁ C₂ : QComp d β)
    (hc₁ : ∀ b, IsCPMap (C₁.branch b)) (hc₂ : ∀ b, IsCPMap (C₂.branch b))
    (h₁ : ∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef → ∑ b, (C₁.branch b ρ).trace = ρ.trace)
    (h₂ : ∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef → ∑ b, (C₂.branch b ρ).trace = ρ.trace) :
    qdistDiamond (fun _ : Unit => C₁) (fun _ => C₂)
        (QIndistDiamond.constCP C₁ hc₁) (QIndistDiamond.constCP C₂ hc₂) =
      ⨆ (r : ℕ) (ρ : DensityMatrix (d * r)), ENNReal.ofReal ((1 / 2 : ℝ) *
        ∑ b, traceNormH ((localOp₁ (d₂ := r) C₁ hc₁).branch b ρ.val
          - (localOp₁ (d₂ := r) C₂ hc₂).branch b ρ.val) (outHerm _ _ ρ b)) := by
  unfold qdistDiamond withRef
  exact iSup_congr fun r => qdist_const_eq_of_tp (localOp₁ (d₂ := r) C₁ hc₁) (localOp₁ C₂ hc₂)
    (localOp₁_tp C₁ hc₁ h₁) (localOp₁_tp C₂ hc₂ h₂)

end CatCrypt.Crypto.UCMonad.QDistTrace
