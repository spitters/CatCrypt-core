/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Refinement.RRelWRPQuantumUpTo
public import CatCryptCore.Refinement.WRPLevelsQuantum
public import CatCryptCore.Quantum.CPMap
public import QuantumFoundations.ForMathlib.Analysis.Matrix.PosSemidef

/-!
# Squares of quantum channels up to an error

A square of channels of grade `ε` has the channel `a` on top, the channel `c` at the bottom and
identity vertical arrows; it states that `c` refines `a` up to `ε` on expectations of effects
(`ChannelWRP.ChannelRefinesUpTo ε c a`). Grades are elements of the monoid `([0, ∞], +)`.

Squares of grade `ε` form a `([0, ∞], +)`-graded double category over the category of channels
under sequencing: identity squares have grade `0`, vertical pasting adds grades, horizontal
pasting (sequencing) adds grades, and a square of grade `ε` is a square of every larger grade.

Horizontal pasting uses the Heisenberg picture. The expectation of an effect `E` after a channel
`Φ` is the expectation of the effect `Φ†(E)` before it (`effectExp_channelState`), and `Φ†`
sends effects to effects since `Φ` is positive and does not increase the trace
(`isEffect_dualMap_branch`).

Every exact square of `WRPLevelsQuantum` is a square of grade `0`. A square of grade `0` states
that the output of `c` dominates that of `a` in the Loewner order; when the top channel `a` is
trace preserving, the square of grade `0` is exactly the exact square.

## Main definitions

* `GSq ε a c`: the square of grade `ε` with top `a` and bottom `c`.

## Main results

* `GSq.id`: identity squares have grade `0`.
* `GSq.vcomp`: vertical pasting adds grades.
* `GSq.hcomp`: horizontal pasting, the sequence of the tops and of the bottoms, adds grades.
* `GSq.mono`: squares are monotone in the grade.
* `GSq.of_sq`, `GSq.zero_iff_sq`: exact squares are squares of grade `0`, and conversely when
  the top channel is trace preserving.
* `effectExp_channelState`, `isEffect_dualMap_branch`: the Heisenberg picture of a channel.

## Search words

graded double category, approximate refinement, quantum channel, error, sequencing, horizontal
composition, vertical composition, Heisenberg picture, dual channel, effect
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CatCrypt.Quantum CatCrypt.Refinement.ChannelWRP
  CatCrypt.Refinement.WRPLevelsQuantum
open scoped Matrix ComplexOrder MatrixOrder ENNReal Matrix.Norms.L2Operator

noncomputable section

namespace CatCrypt.Refinement.WRPGraded

variable {d : ℕ}

/-! ## The Heisenberg picture of a channel

The lemmas of this section are about `QComp`, `dualMap` and `effectExp` only; they belong in
`RRelWRPQuantumUpTo.lean`. -/

/-- A channel does not increase the trace of a state. -/
theorem channelState_trace_le (I : QComp d Unit) (ρ : PSDState d) :
    (channelState I ρ).1.trace.re ≤ ρ.1.trace.re := by
  have h := I.branch_stp ρ.1 ρ.2
  rwa [tsum_fintype, Fintype.sum_unique] at h

/-- The expectation of an effect after a channel is the expectation of its Heisenberg dual
before the channel. -/
theorem effectExp_channelState (I : QComp d Unit) (E : Matrix (Fin d) (Fin d) ℂ)
    (ρ : PSDState d) :
    effectExp E (channelState I ρ) = effectExp (dualMap (I.branch ()) E) ρ := by
  unfold effectExp
  rw [dual_spec]
  rfl

/-- The Heisenberg dual of a channel sends effects to effects. -/
theorem isEffect_dualMap_branch (I : QComp d Unit) {E : Matrix (Fin d) (Fin d) ℂ}
    (hE : IsEffect E) : IsEffect (dualMap (I.branch ()) E) := by
  have hpos : (dualMap (I.branch ()) E).PosSemidef :=
    dual_positive_of_positive (I.branch ()) (fun A hA => I.branch_psd () A hA) E hE.1
  refine ⟨hpos, Matrix.IsHermitian.posSemidef_of_trace_mul_re_nonneg
    (Matrix.isHermitian_one.sub hpos.isHermitian) fun ρ hρ => ?_⟩
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul, dual_spec, Complex.sub_re]
  have h1 := hE.2.trace_mul_re_nonneg (I.branch_psd () ρ hρ)
  have h2 := channelState_trace_le I ⟨ρ, hρ⟩
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul, Complex.sub_re] at h1
  change ((I.branch ()) ρ).trace.re ≤ ρ.trace.re at h2
  linarith

/-- A positive semidefinite matrix scaled by `(‖σ‖ + 1)⁻¹` is an effect. -/
theorem isEffect_smul_inv_norm_add_one {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : σ.PosSemidef) :
    IsEffect ((‖σ‖ + 1)⁻¹ • σ) := by
  have hs : (0 : ℝ) ≤ (‖σ‖ + 1)⁻¹ := by positivity
  have hpos : ((‖σ‖ + 1)⁻¹ • σ).PosSemidef := hσ.smul hs
  refine ⟨hpos, Matrix.le_iff.mp ((CStarAlgebra.norm_le_one_iff_of_nonneg _
    (Matrix.nonneg_iff_posSemidef.mpr hpos)).mp ?_)⟩
  rw [norm_smul, Real.norm_of_nonneg hs, inv_mul_le_iff₀ (by positivity), mul_one]
  linarith

/-! ## Squares up to an error -/

/-- The square of grade `ε` with the channel `a` on top, the channel `c` at the bottom and
identity vertical arrows: `c` refines `a` up to `ε`. -/
def GSq (ε : ℝ≥0∞) (a c : QComp d Unit) : Prop :=
  ChannelRefinesUpTo ε c a

/-- Identity squares have grade `0`. -/
theorem GSq.id (a : QComp d Unit) : GSq 0 a a :=
  ChannelRefinesUpTo.refl 0 a

/-- Squares are monotone in the grade. -/
theorem GSq.mono {ε ε' : ℝ≥0∞} {a c : QComp d Unit} (h : GSq ε a c) (hε : ε ≤ ε') :
    GSq ε' a c :=
  ChannelRefinesUpTo.mono h hε

/-- Vertical pasting adds grades. -/
theorem GSq.vcomp {ε₁ ε₂ : ℝ≥0∞} {a b c : QComp d Unit} (h₁ : GSq ε₁ a b)
    (h₂ : GSq ε₂ b c) : GSq (ε₁ + ε₂) a c :=
  ChannelRefinesUpTo.trans h₂ h₁

/-- Horizontal pasting adds grades: the sequence of the bottoms refines the sequence of the
tops up to the sum of the errors. -/
theorem GSq.hcomp {ε₁ ε₂ : ℝ≥0∞} {a₁ c₁ a₂ c₂ : QComp d Unit} (h₁ : GSq ε₁ a₁ c₁)
    (h₂ : GSq ε₂ a₂ c₂) :
    GSq (ε₁ + ε₂) (a₁ >>= fun _ => a₂) (c₁ >>= fun _ => c₂) := by
  rw [GSq, channelRefinesUpTo_iff]
  intro E hE ρ hρ
  rw [channelState_seq, channelState_seq]
  have hρ₁ : (channelState a₁ ρ).1.trace.re ≤ 1 := (channelState_trace_le a₁ ρ).trans hρ
  have step₂ := channelRefinesUpTo_iff.1 h₂ E hE (channelState a₁ ρ) hρ₁
  have step₁ := channelRefinesUpTo_iff.1 h₁ _ (isEffect_dualMap_branch c₂ hE) ρ hρ
  change effectExp E (channelState a₂ (channelState a₁ ρ)) ≤
    effectExp E (channelState c₂ (channelState a₁ ρ)) + ε₂ at step₂
  change effectExp (dualMap (c₂.branch ()) E) (channelState a₁ ρ) ≤
    effectExp (dualMap (c₂.branch ()) E) (channelState c₁ ρ) + ε₁ at step₁
  rw [← effectExp_channelState, ← effectExp_channelState] at step₁
  calc effectExp E (channelState a₂ (channelState a₁ ρ))
      ≤ effectExp E (channelState c₂ (channelState a₁ ρ)) + ε₂ := step₂
    _ ≤ effectExp E (channelState c₂ (channelState c₁ ρ)) + ε₁ + ε₂ := by gcongr
    _ = effectExp E (channelState c₂ (channelState c₁ ρ)) + (ε₁ + ε₂) := by rw [add_assoc]

/-! ## Grade `0` and the exact squares -/

/-- Every exact square of channels along identity vertical arrows is a square of grade `0`. -/
theorem GSq.of_sq {a c : QComp d Unit}
    (h : WRPLevels.Sq (channelFamily d) (a := chanObj d) (b := chanObj d) (.mk a)
      (𝟙 (chanObj d)) (𝟙 (chanObj d)) (.mk c)) : GSq 0 a c := by
  rw [(sq_id_iff a c).1 h]
  exact GSq.id c

/-- A square of grade `0` whose top channel is trace preserving is an equality of channels. -/
theorem GSq.eq_of_zero {a c : QComp d Unit} (htp : IsTP (a.branch ())) (h : GSq 0 a c) :
    a = c := by
  have hsub : ∀ ρ : PSDState d, ρ.1.trace.re ≤ 1 → a.branch () ρ.1 = c.branch () ρ.1 := by
    intro ρ hρ
    have hN : (c.branch () ρ.1 - a.branch () ρ.1).PosSemidef := by
      refine Matrix.IsHermitian.posSemidef_of_trace_mul_re_nonneg
        ((c.branch_psd () _ ρ.2).isHermitian.sub (a.branch_psd () _ ρ.2).isHermitian)
        fun σ hσ => ?_
      have hE := isEffect_smul_inv_norm_add_one hσ
      have hs : (0 : ℝ) < (‖σ‖ + 1)⁻¹ := by positivity
      have key := channelRefinesUpTo_iff.1 h _ hE ρ hρ
      rw [add_zero] at key
      change effectExp _ (channelState a ρ) ≤ effectExp _ (channelState c ρ) at key
      unfold effectExp at key
      change ENNReal.ofReal ((_ • σ) * a.branch () ρ.1).trace.re ≤
        ENNReal.ofReal ((_ • σ) * c.branch () ρ.1).trace.re at key
      rw [ENNReal.ofReal_le_ofReal_iff (hE.1.trace_mul_re_nonneg (c.branch_psd () _ ρ.2))]
        at key
      rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_smul,
        Complex.smul_re, Complex.smul_re] at key
      have key' := (mul_le_mul_iff_of_pos_left hs).mp key
      rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, Matrix.trace_mul_comm (c.branch () _),
        Matrix.trace_mul_comm (a.branch () _)]
      linarith
    have htr : (c.branch () ρ.1 - a.branch () ρ.1).trace = 0 := by
      have hc := channelState_trace_le c ρ
      change (c.branch () ρ.1).trace.re ≤ ρ.1.trace.re at hc
      have ha := congrArg Complex.re (htp ρ.1)
      obtain ⟨h0re, h0im⟩ := Complex.nonneg_iff.mp hN.trace_nonneg
      apply Complex.ext
      · rw [Matrix.trace_sub, Complex.sub_re] at h0re ⊢
        simp only [Complex.zero_re]
        linarith
      · exact h0im.symm
    exact (sub_eq_zero.mp (hN.trace_eq_zero_iff.mp htr)).symm
  refine channelState_injective (funext fun ρ => Subtype.ext ?_)
  change a.branch () ρ.1 = c.branch () ρ.1
  have h0 := trace_re_nonneg_of_psd ρ.2
  have ht : (0 : ℝ) < (ρ.1.trace.re + 1)⁻¹ := inv_pos.mpr (by linarith)
  have key := hsub ⟨_, ρ.2.smul ht.le⟩ (by
    change ((_ : ℝ) • ρ.1).trace.re ≤ 1
    rw [Matrix.trace_smul, Complex.smul_re, smul_eq_mul, inv_mul_le_iff₀ (by linarith), mul_one]
    linarith)
  change a.branch () ((_ : ℝ) • ρ.1) = c.branch () ((_ : ℝ) • ρ.1) at key
  rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower] at key
  exact smul_right_injective _ ht.ne' key

/-- When the top channel is trace preserving, the squares of grade `0` are the exact squares of
`WRPLevelsQuantum`. -/
theorem GSq.zero_iff_sq {a c : QComp d Unit} (htp : IsTP (a.branch ())) :
    GSq 0 a c ↔ WRPLevels.Sq (channelFamily d) (a := chanObj d) (b := chanObj d) (.mk a)
      (𝟙 (chanObj d)) (𝟙 (chanObj d)) (.mk c) :=
  ⟨fun h => (sq_id_iff a c).2 (GSq.eq_of_zero htp h), GSq.of_sq⟩

end CatCrypt.Refinement.WRPGraded
