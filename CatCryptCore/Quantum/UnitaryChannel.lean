/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.Instrument
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Unitary Channels for QComp

Unitary evolution `ρ ↦ U ρ U*` as a QComp operation with deterministic
outcome (type `Unit`).

## Main Definitions

* `unitaryChannel U` — QComp from a unitary matrix: `ρ ↦ U ρ U*`
* `unitaryChannel_compose` — `apply(U) >>= apply(V) = apply(V * U)`

## Mathematical Background

A unitary channel `Φ_U(ρ) = U ρ U†` is:
- Completely positive (single Kraus operator U)
- Trace-preserving: `tr(U ρ U†) = tr(ρ)` (by cyclicity of trace)
- Deterministic: single branch with outcome `()`

## References

* Watrous — The Theory of Quantum Information, §2.2
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix Classical

noncomputable section

namespace CatCrypt.Quantum.UnitaryChannel

variable {d : ℕ}

/-- Conjugation by a matrix: `ρ ↦ U ρ U*ᴴ` as a linear map. -/
def conjugate (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun ρ := U * ρ * Uᴴ
  map_add' ρ₁ ρ₂ := by simp [mul_add, add_mul]
  map_smul' c ρ := by
    show U * (c • ρ) * Uᴴ = c • (U * ρ * Uᴴ)
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

@[grind =]
theorem conjugate_apply (U ρ : Matrix (Fin d) (Fin d) ℂ) :
    conjugate U ρ = U * ρ * Uᴴ := rfl

/-- Unitary channel: `ρ ↦ U ρ U†` as a deterministic QComp.

    Since there is exactly one outcome `()`, this is trace-preserving
    (not just sub-trace-preserving). -/
def unitaryChannel (U : Matrix.unitaryGroup (Fin d) ℂ) : QComp d Unit where
  branch _ := conjugate (U : Matrix (Fin d) (Fin d) ℂ)
  branch_psd _ ρ hρ := by
    simp only [conjugate_apply]
    exact hρ.mul_mul_conjTranspose_same (U : Matrix (Fin d) (Fin d) ℂ)
  branch_summable ρ := by
    exact summable_of_ne_finset_zero (s := {()})
      (fun b hb => by simp at hb)
  branch_stp ρ hρ := by
    have htrace : (conjugate (U : Matrix (Fin d) (Fin d) ℂ) ρ).trace = ρ.trace := by
      rw [conjugate_apply, trace_mul_cycle]
      have hU := UnitaryGroup.star_mul_self U
      simp only [star_eq_conjTranspose] at hU
      rw [hU, Matrix.one_mul]
    rw [tsum_eq_single () (fun b hb => absurd rfl hb), htrace]

/-- Composing two unitary channels = channel of product.

    `apply(U) >>= (fun _ => apply(V)) = apply(V * U)` -/
theorem unitaryChannel_compose
    (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    QComp.qbind (unitaryChannel U) (fun _ => unitaryChannel V) =
      unitaryChannel (V * U) := by
  apply QComp.ext_fun; intro () ρ
  show ∑' (_ : Unit), conjugate (V : Matrix _ _ ℂ) (conjugate (U : Matrix _ _ ℂ) ρ) =
    conjugate ((V * U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix _ _ ℂ) ρ
  rw [tsum_eq_single () (fun b hb => absurd rfl hb)]
  simp only [conjugate_apply, UnitaryGroup.mul_val, Matrix.conjTranspose_mul]
  simp only [← Matrix.mul_assoc]

end CatCrypt.Quantum.UnitaryChannel
