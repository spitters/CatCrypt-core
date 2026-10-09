/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Complex.Basic

/-!
# Positive semidefinite complex matrices: closedness; a bound on the real part

Mathlib candidates. `Matrix.isClosed_posSemidef` belongs in
`Mathlib/Topology/Instances/Matrix.lean` (or a topology section of
`Mathlib/LinearAlgebra/Matrix/PosDef.lean`); `Complex.re_le_sqrt_of_normSq_le`
belongs in `Mathlib/Analysis/Complex/Norm.lean`.

## Main results

* `Matrix.isClosed_posSemidef` — the positive semidefinite `d × d` complex
  matrices form a closed set.
* `Complex.re_le_sqrt_of_normSq_le` — `Re z ≤ √c` whenever `|z|² ≤ c`.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder

namespace Matrix

/-- The PSD matrices form a closed set. -/
theorem isClosed_posSemidef {d : ℕ} :
    IsClosed {A : Matrix (Fin d) (Fin d) ℂ | A.PosSemidef} := by
  have h : {A : Matrix (Fin d) (Fin d) ℂ | A.PosSemidef} =
      {A | Aᴴ = A} ∩ ⋂ x : Fin d → ℂ, {A | 0 ≤ star x ⬝ᵥ A *ᵥ x} := by
    ext A
    simp [posSemidef_iff_dotProduct_mulVec, IsHermitian]
  rw [h]
  exact (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter
    (isClosed_iInter fun x => isClosed_le continuous_const
      (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)))

end Matrix

namespace Complex

/-- The real part of a complex number is at most the square root of any
    upper bound on its squared modulus. -/
theorem re_le_sqrt_of_normSq_le {z : ℂ} {c : ℝ} (h : Complex.normSq z ≤ c) :
    z.re ≤ Real.sqrt c :=
  calc z.re ≤ ‖z‖ := Complex.re_le_norm z
    _ = Real.sqrt (Complex.normSq z) := Complex.norm_def z
    _ ≤ Real.sqrt c := Real.sqrt_le_sqrt h

end Complex
