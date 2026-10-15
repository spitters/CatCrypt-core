/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.CPMap

/-!
# Functoriality of the Heisenberg dual

`dualMap Φ` (`CatCryptCore.Quantum.CPMap`) is the dual of a linear map on
matrices with respect to the Hilbert–Schmidt pairing, `tr(Φ†(A) B) = tr(A Φ(B))`
(`dual_spec`). This module proves that the dual is a contravariant monoid
morphism on such maps.

## Main results

* `ext_of_trace_mul` — matrices are separated by their traces against all
  matrices.
* `dualMap_id`, `dualMap_zero` — the dual of the identity is the identity and
  the dual of zero is zero.
* `dualMap_comp` — `(Φ ∘ Ψ)† = Ψ† ∘ Φ†`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrices are separated by traces against all matrices. -/
theorem ext_of_trace_mul {X Y : Matrix ι ι ℂ}
    (h : ∀ B : Matrix ι ι ℂ, (X * B).trace = (Y * B).trace) : X = Y := by
  ext i j
  have hu := h (matUnit j i)
  rwa [trace_mul_matUnit, trace_mul_matUnit] at hu

/-- The dual of the identity map is the identity. -/
@[simp] theorem dualMap_id :
    dualMap (LinearMap.id : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) = LinearMap.id := by
  refine LinearMap.ext fun A => ext_of_trace_mul fun B => ?_
  rw [dual_spec]
  rfl

/-- The dual of the zero map is zero. -/
@[simp] theorem dualMap_zero :
    dualMap (0 : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) = 0 := by
  refine LinearMap.ext fun A => ext_of_trace_mul fun B => ?_
  rw [dual_spec]
  simp

/-- The dual reverses composition: `(Φ ∘ Ψ)† = Ψ† ∘ Φ†`. -/
theorem dualMap_comp (Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) :
    dualMap (Φ ∘ₗ Ψ) = dualMap Ψ ∘ₗ dualMap Φ := by
  refine LinearMap.ext fun A => ext_of_trace_mul fun B => ?_
  rw [dual_spec, LinearMap.comp_apply, LinearMap.comp_apply, dual_spec, dual_spec]

end CatCrypt.Quantum
