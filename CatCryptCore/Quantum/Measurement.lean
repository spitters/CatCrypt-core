/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.Instrument
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Quantum Measurement as QComp

Defines POVMs and projective measurements as QComp instruments.

## Main Definitions

* `POVM` — positive operator-valued measure: family of PSD matrices summing to I
* `measurePOVM` — construct a QComp from a POVM
* `projectiveMeasure` — special case with orthogonal projectors
* `bornRule` — Born rule: probability of outcome `a` is `tr(E_a ρ)`

## Mathematical Background

A POVM `{E_a}` on a `d`-dimensional system with outcomes in `α` satisfies:
- Each `E_a` is positive semidefinite
- `∑_a E_a = I` (resolution of identity)

The associated instrument has branch `E_a(ρ) = √E_a · ρ · √E_a` (Lüders rule).
For simplicity, we define a general measurement instrument where each branch
is `ρ ↦ M_a ρ M_a†` with `∑_a M_a† M_a = I`.

## References

* Watrous — The Theory of Quantum Information, §2.3
* Nielsen & Chuang — Quantum Computation and Quantum Information, §2.2.6
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix Classical

noncomputable section

namespace CatCrypt.Quantum.Measurement

variable {d : ℕ} {α : Type}

/-! ## POVM -/

/-- A POVM (positive operator-valued measure) on a `d`-dimensional system.

    A family of PSD matrices indexed by outcomes, summing to the identity. -/
structure POVM (d : ℕ) (α : Type) [Fintype α] where
  effect : α → Matrix (Fin d) (Fin d) ℂ
  effect_psd : ∀ a, (effect a).PosSemidef
  sum_eq_one : ∑ a, effect a = 1

/-! ## Measurement Operators -/

/-- Measurement operators: a family `{M_a}` with `∑_a M_a† M_a = I`.

    The associated POVM is `E_a = M_a† M_a`.
    The post-measurement state (unnormalized) is `M_a ρ M_a†`. -/
structure MeasurementOps (d : ℕ) (α : Type) [Fintype α] where
  op : α → Matrix (Fin d) (Fin d) ℂ
  completeness : ∑ a, (op a)ᴴ * op a = 1

/-- Construct a QComp from measurement operators.

    Branch `a` maps `ρ ↦ M_a ρ M_a†`.
    This is a (finitely-branching) quantum instrument. -/
def measureOps [Fintype α] (M : MeasurementOps d α) : QComp d α where
  branch a := {
    toFun := fun ρ => M.op a * ρ * (M.op a)ᴴ
    map_add' := fun ρ₁ ρ₂ => by simp [mul_add, add_mul]
    map_smul' := fun c ρ => by
      show M.op a * (c • ρ) * (M.op a)ᴴ = c • (M.op a * ρ * (M.op a)ᴴ)
      simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  }
  branch_psd a ρ hρ := hρ.mul_mul_conjTranspose_same (M.op a)
  branch_summable ρ := by
    exact summable_of_ne_finset_zero (s := Finset.univ)
      (fun a ha => absurd (Finset.mem_univ a) ha)
  branch_stp ρ hρ := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [tsum_fintype]
    conv_lhs => arg 1; arg 2; ext a; rw [trace_mul_cycle]
    rw [show ∑ a : α, ((M.op a)ᴴ * M.op a * ρ).trace =
      ((∑ a : α, (M.op a)ᴴ * M.op a) * ρ).trace from by
      rw [Finset.sum_mul, trace_sum]]
    rw [M.completeness, Matrix.one_mul]

/-! ## Projective Measurement -/

/-- Projective measurement: measurement operators that are orthogonal projectors.

    Each `P_a` satisfies `P_a² = P_a` and `P_a† = P_a`, and `∑ P_a = I`. -/
structure ProjectiveMeasurement (d : ℕ) (α : Type) [Fintype α] extends
    MeasurementOps d α where
  self_adjoint : ∀ a, (op a)ᴴ = op a
  idempotent : ∀ a, op a * op a = op a

/-- Projective measurement as QComp. -/
def projectiveMeasure [Fintype α] (P : ProjectiveMeasurement d α) :
    QComp d α :=
  measureOps P.toMeasurementOps

/-! ## Born Rule -/

/-- Born rule: the probability of outcome `a` when measuring state `ρ`
    with POVM `{E_a}` is `tr(E_a ρ)`. -/
def bornProb [Fintype α] (E : POVM d α) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (a : α) : ℂ :=
  (E.effect a * ρ).trace

/-- Born probabilities sum to `tr(ρ)`. -/
theorem bornProb_sum [Fintype α] (E : POVM d α)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    ∑ a, bornProb E ρ a = ρ.trace := by
  simp only [bornProb]
  rw [show ∑ a : α, (E.effect a * ρ).trace =
    ((∑ a : α, E.effect a) * ρ).trace from by
    rw [Finset.sum_mul, trace_sum]]
  rw [E.sum_eq_one, Matrix.one_mul]

end CatCrypt.Quantum.Measurement
