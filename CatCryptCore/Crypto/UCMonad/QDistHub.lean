/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCMonad.CPCompUC
public import CatCryptCore.Crypto.UCMonad.QIndistDiamond
public import CatCryptCore.Quantum.QRHL
public import CatCryptCore.Quantum.CPCompMonad
public import CatCryptCore.Quantum.QPullback
public import QuantumFoundations.ForMathlib.Analysis.Matrix.PosSemidef

/-!
# Relations between the quantum distances

This file relates the distances between quantum programs of the core.

* The accept branch of a distinguisher `D : QComp d Bool` has the effect
  `E = Φ†(1)` of its accept map `Φ`: `tr(Φ Y) = tr(E Y)`
  (`trace_branch_eq_dual`), and `E` is an effect (`isEffect_dualMap_branch`).
* `effectMeas E hE` is the two-outcome measurement of an effect `E`, with Kraus
  operators `K`, `K'` where `Kᴴ K = E` and `K'ᴴ K' = 1 - E`; its branches are
  completely positive (`effectMeas_branch_isCPMap`) and its accept trace is
  `tr(E Y)` (`trace_effectMeas_true`).
* D1, `qIndist_iff_qdist_le`: `QRHL.qIndist` is a bound on `qdist` of the
  constant families.
* D2, `qdist_eq_iSup_const`: `qdist` of Kleisli families is the supremum over
  inputs of `qdist` of the constant families.
* D3, `qdist_eq_qdistCP`: restricting the distinguishers of `qdist` to
  completely positive ones does not change the distance, since each
  distinguisher has the same acceptance probabilities as the measurement of
  its accept effects.
* D4, `qdist_le_qdistDiamond`: the diamond distance bounds `qdist`.
* D5, `cpSdist_eq_qdist`: `cpSdist` is `qdist` of the underlying instruments.
* D6, `qIndist_of_qIndistDiamond`, and `cpSdist_const_le_cpDist`: the diamond
  bounds transfer to `qIndist` and to `cpSdist`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCMonad.QDistHub

open CatCrypt.Quantum
open CatCrypt.Crypto.UCMonad.DiamondNorm
open CatCrypt.Crypto.UCMonad.DiamondDominates
open CatCrypt.Crypto.UCMonad.CPCompUC
open CatCrypt.Crypto.UCMonad.QIndistDiamond
open UCMonad.QuantumUC
open scoped ENNReal ComplexOrder Matrix MatrixOrder

variable {d : ℕ} {α β : Type}

/-! ## The effect of a distinguisher -/

/-- The effect of the accept branch: `tr(Φ Y) = tr(E Y)` with `E = Φ†(1)`. -/
theorem trace_branch_eq_dual (D : QComp d Bool) (Y : Matrix (Fin d) (Fin d) ℂ) :
    ((D.branch true) Y).trace = (dualMap (D.branch true) 1 * Y).trace := by
  rw [dual_spec, Matrix.one_mul]

/-- The dual of the accept branch at `1` is an effect. -/
theorem isEffect_dualMap_branch (D : QComp d Bool) :
    IsEffect (dualMap (D.branch true) 1) := by
  have hpos : (dualMap (D.branch true) 1).PosSemidef :=
    dual_positive_of_positive (D.branch true) (fun A hA => D.branch_psd true A hA) 1
      Matrix.PosSemidef.one
  refine ⟨hpos, Matrix.IsHermitian.posSemidef_of_trace_mul_re_nonneg
    (Matrix.isHermitian_one.sub hpos.isHermitian) fun ρ hρ => ?_⟩
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul, ← trace_branch_eq_dual,
    Complex.sub_re]
  have hstp := D.branch_stp ρ hρ
  rw [tsum_fintype, Fintype.sum_bool, Complex.add_re] at hstp
  have hfalse := trace_re_nonneg_of_psd (D.branch_psd false ρ hρ)
  linarith

/-! ## The measurement of an effect -/

/-- A Kraus operator of a positive semidefinite matrix `E`: a matrix `K` with
`Kᴴ * K = E`. -/
noncomputable def effectKraus (E : Matrix (Fin d) (Fin d) ℂ) (hE : E.PosSemidef) :
    Matrix (Fin d) (Fin d) ℂ :=
  Classical.choose (CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hE.nonneg)

/-- `effectKraus E hE` is a square root of `E` in the form `Kᴴ * K = E`. -/
theorem effectKraus_spec (E : Matrix (Fin d) (Fin d) ℂ) (hE : E.PosSemidef) :
    (effectKraus E hE)ᴴ * effectKraus E hE = E := by
  have h := Classical.choose_spec (CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hE.nonneg)
  rw [Matrix.star_eq_conjTranspose] at h
  exact h.symm

/-- The two-outcome measurement of an effect `E`: outcome `true` has the Kraus
operator `effectKraus E`, outcome `false` the Kraus operator `effectKraus (1 - E)`. -/
noncomputable def effectMeas (E : Matrix (Fin d) (Fin d) ℂ) (hE : IsEffect E) : QComp d Bool :=
  Measurement.measureOps
    { op := fun b => if b then effectKraus E hE.1 else effectKraus (1 - E) hE.2
      completeness := by
        rw [Fintype.sum_bool]
        simp only [ite_true, Bool.false_eq_true, ite_false, effectKraus_spec]
        abel }

/-- The branches of the measurement of an effect are completely positive. -/
theorem effectMeas_branch_isCPMap (E : Matrix (Fin d) (Fin d) ℂ) (hE : IsEffect E)
    (b : Bool) : IsCPMap ((effectMeas E hE).branch b) :=
  Measurement.measureOps_branch_isCPMap _ b

/-- The accept branch of the measurement of `E` has trace `tr(E Y)`. -/
theorem trace_effectMeas_true (E : Matrix (Fin d) (Fin d) ℂ) (hE : IsEffect E)
    (Y : Matrix (Fin d) (Fin d) ℂ) :
    ((effectMeas E hE).branch true Y).trace = (E * Y).trace := by
  change (effectKraus E hE.1 * Y * (effectKraus E hE.1)ᴴ).trace = _
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, effectKraus_spec]

/-! ## Acceptance probabilities of a composite -/

/-- The trace of the accept branch of `C >>= D` is the sum of the traces of the
accept branches of `D b` at the outputs of `C`. -/
theorem trace_qbind_true (C : QComp d β) (D : β → QComp d Bool)
    (Y : Matrix (Fin d) (Fin d) ℂ) :
    ((C.qbind D).branch true Y).trace = ∑' b, ((D b).branch true (C.branch b Y)).trace :=
  trace_tsum (QComp.bind_summable C D true Y)

/-- Two distinguishers whose accept branches have the same traces give a
composite the same acceptance probability. -/
theorem prTrue_Q_qbind_congr (C : QComp d β) (D D' : β → QComp d Bool)
    (h : ∀ b Y, ((D b).branch true Y).trace = ((D' b).branch true Y).trace)
    (ρ : DensityMatrix d) :
    prTrue_Q (C.qbind D) ρ = prTrue_Q (C.qbind D') ρ := by
  simp only [prTrue_Q, trace_qbind_true, h]

/-- The completely positive distinguisher with the accept effects of `D`. -/
noncomputable def effectDist (D : β → QComp d Bool) : β → QComp d Bool :=
  fun b => effectMeas (dualMap ((D b).branch true) 1) (isEffect_dualMap_branch (D b))

/-- `effectDist D` is a completely positive channel. -/
theorem effectDist_isCPChannel (D : β → QComp d Bool) : IsCPChannel (effectDist D) :=
  fun _ c => effectMeas_branch_isCPMap _ _ c

/-- `D` and `effectDist D` have accept branches with the same traces. -/
theorem trace_effectDist_true (D : β → QComp d Bool) (b : β) (Y : Matrix (Fin d) (Fin d) ℂ) :
    ((D b).branch true Y).trace = ((effectDist D b).branch true Y).trace := by
  rw [effectDist, trace_effectMeas_true, trace_branch_eq_dual]

/-! ## D1 and D2 -/

/-- D1: `qIndist` is a bound on `qdist` of the constant families. -/
theorem qIndist_iff_qdist_le (C₁ C₂ : QComp d α) (ε : ℝ≥0∞) :
    QRHL.qIndist C₁ C₂ ε ↔ qdist (fun _ : Unit => C₁) (fun _ => C₂) ≤ ε := by
  simp only [QRHL.qIndist, qdist, iSup_le_iff, forall_const]

/-- D2: `qdist` is the supremum over inputs of `qdist` of the constant families. -/
theorem qdist_eq_iSup_const (f g : α → QComp d β) :
    qdist f g = ⨆ a, qdist (fun _ : Unit => f a) (fun _ => g a) := by
  simp only [qdist, iSup_unique]
  exact iSup_comm

/-! ## D3: completely positive distinguishers suffice -/

/-- `qdistCP` is at most `qdist`. -/
theorem qdistCP_le_qdist (f g : α → QComp d β) : qdistCP f g ≤ qdist f g :=
  iSup_mono fun _ => iSup_le fun _ => le_rfl

/-- `qdist` is at most `qdistCP`: each distinguisher is replaced by `effectDist`. -/
theorem qdist_le_qdistCP (f g : α → QComp d β) : qdist f g ≤ qdistCP f g := by
  refine iSup_le fun D => iSup_le fun a => iSup_le fun ρ => ?_
  rw [prTrue_Q_qbind_congr (f a) D (effectDist D) (trace_effectDist_true D),
    prTrue_Q_qbind_congr (g a) D (effectDist D) (trace_effectDist_true D)]
  exact le_iSup_of_le (effectDist D) (le_iSup_of_le (effectDist_isCPChannel D)
    (le_iSup_of_le a (le_iSup_of_le ρ le_rfl)))

/-- D3: completely positive distinguishers give the same distance. -/
theorem qdist_eq_qdistCP (f g : α → QComp d β) : qdist f g = qdistCP f g :=
  le_antisymm (qdist_le_qdistCP f g) (qdistCP_le_qdist f g)

/-! ## D4, D5, D6 -/

/-- D4: the diamond distance bounds `qdist`. -/
theorem qdist_le_qdistDiamond (f g : α → QComp d β) (hf : IsCPChannel f)
    (hg : IsCPChannel g) : qdist f g ≤ qdistDiamond f g hf hg := by
  rw [qdist_eq_qdistCP]
  exact qdistCP_le_qdistDiamond f g hf hg

/-- D5: `cpSdist` is `qdist` of the underlying instruments. -/
theorem cpSdist_eq_qdist (f g : α → CPComp d β) :
    cpSdist f g = qdist (fun a => (f a).toQComp) (fun a => (g a).toQComp) := by
  rw [cpSdist_eq_qdistCP, qdist_eq_qdistCP]

/-- D6: diamond indistinguishability implies `qIndist` at the same bound. -/
theorem qIndist_of_qIndistDiamond {C₁ C₂ : QComp d α} {ε : ℝ≥0∞}
    {hc₁ : ∀ a, IsCPMap (C₁.branch a)} {hc₂ : ∀ a, IsCPMap (C₂.branch a)}
    (h : qIndistDiamond C₁ C₂ hc₁ hc₂ ε) : QRHL.qIndist C₁ C₂ ε :=
  (qIndist_iff_qdist_le C₁ C₂ ε).2
    (le_trans (qdist_le_qdistDiamond _ _ (constCP C₁ hc₁) (constCP C₂ hc₂)) h)

/-- The diamond distance `cpDist` of two instruments bounds `cpSdist` of the
constant families. -/
theorem cpSdist_const_le_cpDist (p q : CPComp d α) :
    cpSdist (fun _ : Unit => p) (fun _ => q) ≤ ReactiveUC.cpDist p q :=
  cpSdist_le_qdistDiamond _ _

end CatCrypt.Crypto.UCMonad.QDistHub
