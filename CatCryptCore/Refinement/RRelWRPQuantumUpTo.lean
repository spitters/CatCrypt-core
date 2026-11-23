/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Refinement.RRelWRPQuantum
public import CatCryptCore.Quantum.UnitaryChannel
public import CatCryptCore.Quantum.TraceNorm
public import CatCryptCore.ForMathlib.Matrix.TraceNormConj
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import QuantumFoundations.Pure.Vector

/-!
# Refinement of quantum channels up to an error

A quantum computation with one outcome is observed through the expectations of effects: for an
effect `E` (`0 ≤ E ≤ 1`) and a state `ρ`, the observation is `tr(E ρ)` in `ℝ≥0∞`. The weakest
precondition of the computation at this observation is its precomposition with the channel
(`instWPChannel`). Refinement of `a` by `c` up to `ε` states that for every effect and every
state of trace at most `1` the expectation under `a` is at most the expectation under `c` plus
`ε`.

Two unitary channels whose matrices are within `ε` in the `ℓ²` operator norm refine each other
up to `2ε`, since `‖U ρ Uᴴ - V ρ Vᴴ‖₁ ≤ 2 ‖U - V‖ tr ρ` for contractions `U`, `V` and positive
semidefinite `ρ` (`Matrix.traceNorm_mul_mul_conjTranspose_sub_le`). A global phase of the
matrix does not change the channel (`UnitaryChannel.unitaryChannel_eq_of_val_eq_smul`), so the
bound holds also when `U` is within `ε` of `e^{iφ} V`. Refinements up to `ε₁` and `ε₂` compose to
`ε₁ + ε₂`.

## Main definitions

* `effectExp E ρ`: the expectation `tr(E ρ)` of the effect `E` at the state `ρ`.
* `ChannelRefinesUpTo ε c a`: refinement of `a` by `c` up to `ε` on expectations of effects.

## Main results

* `unitaryChannel_refinesUpTo_of_norm_sub_le`: unitary channels of matrices within `ε` refine
  each other up to `2ε`; `unitaryChannel_refinesUpTo_both_of_norm_sub_le` gives both directions.
* `unitaryChannel_refinesUpTo_of_norm_sub_smul_le`: the same with a global phase.
* `ChannelRefinesUpTo.trans`: refinements up to errors compose additively.
* `ChannelRefines.refinesUpTo`: exact refinement is refinement up to every error.

## Search words

quantum channel, unitary channel, effect, expectation, approximate refinement, error, operator
norm, trace norm, perturbation, global phase, circuit optimizer, weakest precondition
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum CatCrypt.Quantum.UnitaryChannel RefinementWP
open Std.WP (WP wp)
open scoped Matrix ComplexOrder MatrixOrder ENNReal Matrix.Norms.L2Operator

noncomputable section

namespace CatCrypt.Refinement.ChannelWRP

variable {d : ℕ}

/-! ## Expectations of effects and refinement up to an error -/

/-- The expectation `tr(E ρ)` of the effect `E` at the state `ρ`, in `ℝ≥0∞`. -/
def effectExp (E : Matrix (Fin d) (Fin d) ℂ) (ρ : PSDState d) : ℝ≥0∞ :=
  ENNReal.ofReal (E * ρ.1).trace.re

/-- `c` refines `a` up to `ε` on expectations of effects: for every effect `E` and every state
`ρ` of trace at most `1`, the weakest precondition of `a` at the expectation of `E` is at most
that of `c` plus `ε`. -/
def ChannelRefinesUpTo (ε : ℝ≥0∞) (c a : QComp d Unit) : Prop :=
  ∀ E : Matrix (Fin d) (Fin d) ℂ, IsEffect E → ∀ ρ : PSDState d, ρ.1.trace.re ≤ 1 →
    wp a (fun _ => effectExp E) () ρ ≤ wp c (fun _ => effectExp E) () ρ + ε

/-- The unfolding lemma of `ChannelRefinesUpTo` at the states after the channels. -/
theorem channelRefinesUpTo_iff {ε : ℝ≥0∞} {c a : QComp d Unit} :
    ChannelRefinesUpTo ε c a ↔
      ∀ E : Matrix (Fin d) (Fin d) ℂ, IsEffect E → ∀ ρ : PSDState d, ρ.1.trace.re ≤ 1 →
        effectExp E (channelState a ρ) ≤ effectExp E (channelState c ρ) + ε :=
  Iff.rfl

/-- A computation refines itself up to every error. -/
theorem ChannelRefinesUpTo.refl (ε : ℝ≥0∞) (c : QComp d Unit) : ChannelRefinesUpTo ε c c :=
  fun _ _ _ _ => le_self_add

/-- Refinement up to an error is monotone in the error. -/
theorem ChannelRefinesUpTo.mono {ε ε' : ℝ≥0∞} {c a : QComp d Unit}
    (h : ChannelRefinesUpTo ε c a) (hε : ε ≤ ε') : ChannelRefinesUpTo ε' c a :=
  fun E hE ρ hρ => (h E hE ρ hρ).trans (by gcongr)

/-- **Refinements up to errors compose additively**, along the identity. -/
theorem ChannelRefinesUpTo.trans {ε₁ ε₂ : ℝ≥0∞} {c b a : QComp d Unit}
    (h₂ : ChannelRefinesUpTo ε₂ c b) (h₁ : ChannelRefinesUpTo ε₁ b a) :
    ChannelRefinesUpTo (ε₁ + ε₂) c a :=
  fun E hE ρ hρ => (h₁ E hE ρ hρ).trans <| by
    rw [add_comm ε₁, ← add_assoc]
    gcongr
    exact h₂ E hE ρ hρ

/-- Exact refinement along the identity gives refinement up to every error. -/
theorem ChannelRefines.refinesUpTo {c a : QComp d Unit} (h : ChannelRefines c a)
    (ε : ℝ≥0∞) : ChannelRefinesUpTo ε c a := by
  rw [channelRefines_iff] at h
  subst h
  exact ChannelRefinesUpTo.refl ε a

/-! ## Unitary channels within an error -/

/-- A unitary matrix has `ℓ²` operator norm at most `1`. -/
theorem norm_unitary_le_one (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ‖(U : Matrix (Fin d) (Fin d) ℂ)‖ ≤ 1 :=
  Quantum.l2_opNorm_le_one_of_mem_unitaryGroup U.2

/-- An effect has `ℓ²` operator norm at most `1`. -/
theorem norm_le_one_of_isEffect {n : Type} [Fintype n] [DecidableEq n] {E : Matrix n n ℂ}
    (hE : IsEffect E) : ‖E‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg E (Matrix.nonneg_iff_posSemidef.mpr hE.1)).mpr
    (Matrix.le_iff.mpr hE.2)

/-- Conjugations by contractions within `ε` move the expectation of an effect at a state of
trace at most `1` by at most `2ε`. -/
theorem effectExp_conjugate_le {U V : Matrix (Fin d) (Fin d) ℂ} (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1)
    {ε : ℝ} (h : ‖U - V‖ ≤ ε) {E : Matrix (Fin d) (Fin d) ℂ} (hE : IsEffect E)
    (ρ : PSDState d) (hρ : ρ.1.trace.re ≤ 1) :
    ENNReal.ofReal (E * conjugate U ρ.1).trace.re ≤
      ENNReal.ofReal (E * conjugate V ρ.1).trace.re + ENNReal.ofReal (2 * ε) := by
  have h1 := Matrix.re_trace_mul_le_add_traceNorm_sub (norm_le_one_of_isEffect hE)
    (conjugate U ρ.1) (conjugate V ρ.1)
  have h2 := Matrix.traceNorm_mul_mul_conjTranspose_sub_le hU hV ρ.2
  have htr : 0 ≤ ρ.1.trace.re := by
    rw [← ρ.2.traceNorm_eq]; exact Matrix.traceNorm_nonneg _
  have h3 : 2 * ‖U - V‖ * ρ.1.trace.re ≤ 2 * ε := by
    have := mul_le_mul h hρ htr ((norm_nonneg (U - V)).trans h)
    linarith
  refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
  simp only [conjugate_apply] at h1
  grind

/-- **Unitary channels within `ε` refine each other up to `2ε`**: if `‖U - V‖ ≤ ε` in the
`ℓ²` operator norm, the channel of `V` refines that of `U` up to `2ε`. -/
theorem unitaryChannel_refinesUpTo_of_norm_sub_le {U V : Matrix.unitaryGroup (Fin d) ℂ}
    {ε : ℝ} (h : ‖(U : Matrix (Fin d) (Fin d) ℂ) - V‖ ≤ ε) :
    ChannelRefinesUpTo (ENNReal.ofReal (2 * ε)) (unitaryChannel V) (unitaryChannel U) := by
  rw [channelRefinesUpTo_iff]
  intro E hE ρ hρ
  exact effectExp_conjugate_le (norm_unitary_le_one U) (norm_unitary_le_one V) h hE ρ hρ

/-- Unitary channels within `ε` refine each other up to `2ε`, in both directions. -/
theorem unitaryChannel_refinesUpTo_both_of_norm_sub_le {U V : Matrix.unitaryGroup (Fin d) ℂ}
    {ε : ℝ} (h : ‖(U : Matrix (Fin d) (Fin d) ℂ) - V‖ ≤ ε) :
    ChannelRefinesUpTo (ENNReal.ofReal (2 * ε)) (unitaryChannel V) (unitaryChannel U) ∧
      ChannelRefinesUpTo (ENNReal.ofReal (2 * ε)) (unitaryChannel U) (unitaryChannel V) :=
  ⟨unitaryChannel_refinesUpTo_of_norm_sub_le h,
    unitaryChannel_refinesUpTo_of_norm_sub_le (by rwa [norm_sub_rev])⟩

/-- **A global phase does not change the bound**: if `‖U - c V‖ ≤ ε` for a scalar `c` of
modulus `1` (for instance `c = e^{iφ}`), the unitary channels of `U` and `V` refine each other
up to `2ε`. -/
theorem unitaryChannel_refinesUpTo_of_norm_sub_smul_le {U V : Matrix.unitaryGroup (Fin d) ℂ}
    {c : ℂ} (hc : ‖c‖ = 1) {ε : ℝ}
    (h : ‖(U : Matrix (Fin d) (Fin d) ℂ) - c • (V : Matrix (Fin d) (Fin d) ℂ)‖ ≤ ε) :
    ChannelRefinesUpTo (ENNReal.ofReal (2 * ε)) (unitaryChannel V) (unitaryChannel U) ∧
      ChannelRefinesUpTo (ENNReal.ofReal (2 * ε)) (unitaryChannel U) (unitaryChannel V) := by
  have hcc : c * (starRingEnd ℂ) c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; norm_num
  have hconj : conjugate (c • (V : Matrix (Fin d) (Fin d) ℂ)) = conjugate V :=
    conjugate_smul_unit c hcc _
  have hcV : ‖c • (V : Matrix (Fin d) (Fin d) ℂ)‖ ≤ 1 := by
    rw [norm_smul, hc, one_mul]; exact norm_unitary_le_one V
  constructor
  · intro E hE ρ hρ
    have := effectExp_conjugate_le (norm_unitary_le_one U) hcV h hE ρ hρ
    rw [hconj] at this
    exact this
  · intro E hE ρ hρ
    have := effectExp_conjugate_le hcV (norm_unitary_le_one U)
      (ε := ε) (by rwa [norm_sub_rev]) hE ρ hρ
    rw [hconj] at this
    exact this

end CatCrypt.Refinement.ChannelWRP
