/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.UnitaryChannel
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The standard quantum-accessible oracle over `QComp`

The standard oracle for a function `H : X → Y` is the unitary
`|x, y⟩ ↦ |x, y + H x⟩` on the query register `X ⊗ Y`. Its register form places
the function itself in a third register: `|x, y, G⟩ ↦ |x, y + G x, G⟩` on
`X ⊗ Y ⊗ (X → Y)`, so that a uniform superposition over `G` in the third
register is the quantum random oracle. Both are permutation matrices, and every
result here is obtained from the permutation (`Equiv.Perm`) rather than from
matrix entries.

## Main definitions

* `stdOraclePerm H` — the permutation `(x, y) ↦ (x, y + H x)` of `X × Y`
* `stdOracleRegPerm` — the permutation `(x, y, G) ↦ (x, y + G x, G)` of
  `X × Y × (X → Y)`
* `permUnitary σ` — the permutation matrix `e_k ↦ e_{σ k}` as an element of the
  unitary group
* `stdOracleFixedG m n H`, `stdOracleRegG m n` — the two unitaries over
  `Fin (m * n)` and `Fin (m * (n * n ^ m))` for `X = Fin m`, `Y = Fin n`
* `stdOracleFixed H`, `stdOracleReg` — the instances at `X = Y = Fin 2`
  (dimensions `4` and `16`)
* `stdOracleFixedQ H`, `stdOracleRegQ` — the same as unitary channels in
  `QComp 4 Unit` and `QComp 16 Unit`

## Main results

* `permMatrix_mem_unitaryGroup` — a permutation matrix is unitary
* `permUnitary_mulVec_single` — `permUnitary σ` maps the basis ket `e_k` to
  `e_{σ k}`
* `stdOracleFixed_unitary`, `stdOracleReg_unitary` — unitarity of the two
  oracles
* `stdOracleFixed_ket`, `stdOracleReg_ket` — the action on basis kets,
  `|x, y⟩ ↦ |x, y + H x⟩` and `|x, y, G⟩ ↦ |x, y + G x, G⟩`
* `stdOracleRegPerm_fin2_involutive` — the register permutation at
  `X = Y = Fin 2` is an involution, checked by `decide` at dimension 16 as a
  static pin of the index encoding

## The representation

The matrix of each oracle is `permMatrixHom` of an `Equiv.Perm`, and unitarity
and the ket action are proved once for every permutation
(`permMatrix_mem_unitaryGroup`, `permUnitary_mulVec_single`), so
`stdOracleFixedG_unitary`, `stdOracleRegG_unitary`, `stdOracleFixedG_ket` and
`stdOracleRegG_ket` hold at every `m` and `n` without reducing a matrix. An
entry evaluation or a `decide` over the index type visits all `m · n · n ^ m`
basis states; the only such check in this module is
`stdOracleRegPerm_fin2_involutive`, at dimension 16. The register form over
`Fin (m * (n * n ^ m))` and the per-function form `stdOracleFixedQ H` follow the
design of Heidler–Unruh (CPP 2025) in Isabelle over an abstract `ell2` type,
with the purification `∑_G |G⟩` introduced in proofs and never evaluated.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder
open Matrix

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The permutations -/

section Perm

variable {X Y : Type} [AddGroup Y]

/-- The permutation `(x, y) ↦ (x, y + H x)` of the query register `X × Y`. -/
def stdOraclePerm (H : X → Y) : Equiv.Perm (X × Y) where
  toFun p := (p.1, p.2 + H p.1)
  invFun p := (p.1, p.2 - H p.1)
  left_inv p := by simp
  right_inv p := by simp

/-- The permutation `(x, y, G) ↦ (x, y + G x, G)` of `X × Y × (X → Y)`: the
    standard oracle controlled by the function register. -/
def stdOracleRegPerm : Equiv.Perm (X × Y × (X → Y)) where
  toFun p := (p.1, p.2.1 + p.2.2 p.1, p.2.2)
  invFun p := (p.1, p.2.1 - p.2.2 p.1, p.2.2)
  left_inv p := by simp
  right_inv p := by simp

@[simp]
theorem stdOraclePerm_apply (H : X → Y) (x : X) (y : Y) :
    stdOraclePerm H (x, y) = (x, y + H x) := rfl

@[simp]
theorem stdOracleRegPerm_apply (x : X) (y : Y) (G : X → Y) :
    stdOracleRegPerm (x, y, G) = (x, y + G x, G) := rfl

end Perm

/-! ## Permutation matrices as unitaries -/

section PermUnitary

variable {n : Type} [Fintype n] [DecidableEq n]

/-- A permutation matrix is unitary. -/
theorem permMatrix_mem_unitaryGroup (σ : Equiv.Perm n) :
    σ.permMatrix ℂ ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
    ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

/-- The permutation matrix sending the basis ket `e_k` to `e_{σ k}`, as an
    element of the unitary group. Its underlying matrix is
    `Matrix.permMatrixHom σ = σ⁻¹.permMatrix ℂ`. -/
def permUnitary (σ : Equiv.Perm n) : Matrix.unitaryGroup n ℂ :=
  ⟨Matrix.permMatrixHom σ, by
    rw [Matrix.permMatrixHom_apply]; exact permMatrix_mem_unitaryGroup σ⁻¹⟩

@[simp]
theorem permUnitary_val (σ : Equiv.Perm n) :
    (permUnitary σ : Matrix n n ℂ) = σ⁻¹.permMatrix ℂ := rfl

/-- `permUnitary σ` maps the basis ket `e_k` to `e_{σ k}`. -/
theorem permUnitary_mulVec_single (σ : Equiv.Perm n) (k : n) :
    (permUnitary σ : Matrix n n ℂ) *ᵥ Pi.single k 1 = Pi.single (σ k) 1 := by
  rw [permUnitary_val, Matrix.permMatrix_mulVec]
  funext i
  simp [Pi.single_apply, Equiv.symm_apply_eq]

end PermUnitary

/-! ## Index equivalences for `X = Fin m`, `Y = Fin n` -/

/-- Row-major index of the query register `Fin m × Fin n` in `Fin (m * n)`. -/
def fixedIndex (m n : ℕ) : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv

/-- Row-major index of `Fin m × Fin n × (Fin m → Fin n)` in
    `Fin (m * (n * n ^ m))`, with the function register encoded by
    `finFunctionFinEquiv`. -/
def regIndex (m n : ℕ) : Fin m × Fin n × (Fin m → Fin n) ≃ Fin (m * (n * n ^ m)) :=
  ((Equiv.refl (Fin m)).prodCongr ((Equiv.refl (Fin n)).prodCongr finFunctionFinEquiv)).trans
    (((Equiv.refl (Fin m)).prodCongr finProdFinEquiv).trans finProdFinEquiv)

/-! ## The oracles over `Fin m`, `Fin n` -/

section FinOracles

variable (m n : ℕ) [NeZero n]

/-- The standard oracle for `H : Fin m → Fin n` on `Fin (m * n)`:
    `|x, y⟩ ↦ |x, y + H x⟩`. -/
def stdOracleFixedG (H : Fin m → Fin n) : Matrix (Fin (m * n)) (Fin (m * n)) ℂ :=
  permUnitary ((fixedIndex m n).permCongr (stdOraclePerm H))

/-- The register oracle on `Fin (m * (n * n ^ m))`: `|x, y, G⟩ ↦ |x, y + G x, G⟩`. -/
def stdOracleRegG : Matrix (Fin (m * (n * n ^ m))) (Fin (m * (n * n ^ m))) ℂ :=
  permUnitary ((regIndex m n).permCongr stdOracleRegPerm)

theorem stdOracleFixedG_unitary (H : Fin m → Fin n) :
    stdOracleFixedG m n H ∈ Matrix.unitaryGroup (Fin (m * n)) ℂ :=
  (permUnitary _).property

theorem stdOracleRegG_unitary :
    stdOracleRegG m n ∈ Matrix.unitaryGroup (Fin (m * (n * n ^ m))) ℂ :=
  (permUnitary _).property

/-- `stdOracleFixedG` on the basis ket `|x, y⟩`. -/
theorem stdOracleFixedG_ket (H : Fin m → Fin n) (x : Fin m) (y : Fin n) :
    stdOracleFixedG m n H *ᵥ Pi.single (fixedIndex m n (x, y)) 1 =
      Pi.single (fixedIndex m n (x, y + H x)) 1 := by
  unfold stdOracleFixedG
  rw [permUnitary_mulVec_single]
  simp [Equiv.permCongr_apply]

/-- `stdOracleRegG` on the basis ket `|x, y, G⟩`. -/
theorem stdOracleRegG_ket (x : Fin m) (y : Fin n) (G : Fin m → Fin n) :
    stdOracleRegG m n *ᵥ Pi.single (regIndex m n (x, y, G)) 1 =
      Pi.single (regIndex m n (x, y + G x, G)) 1 := by
  unfold stdOracleRegG
  rw [permUnitary_mulVec_single]
  simp [Equiv.permCongr_apply]

end FinOracles

/-! ## The instances at `X = Y = Fin 2` -/

/-- The standard oracle for `H : Fin 2 → Fin 2` on `Fin 4`, index `x * 2 + y`. -/
def stdOracleFixed (H : Fin 2 → Fin 2) : Matrix (Fin 4) (Fin 4) ℂ :=
  stdOracleFixedG 2 2 H

/-- The register oracle at `X = Y = Fin 2` on `Fin 16`. -/
def stdOracleReg : Matrix (Fin 16) (Fin 16) ℂ :=
  stdOracleRegG 2 2

theorem stdOracleFixed_unitary (H : Fin 2 → Fin 2) :
    stdOracleFixed H ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
  stdOracleFixedG_unitary 2 2 H

theorem stdOracleReg_unitary :
    stdOracleReg ∈ Matrix.unitaryGroup (Fin 16) ℂ :=
  stdOracleRegG_unitary 2 2

theorem stdOracleFixed_ket (H : Fin 2 → Fin 2) (x y : Fin 2) :
    stdOracleFixed H *ᵥ Pi.single (fixedIndex 2 2 (x, y)) 1 =
      Pi.single (fixedIndex 2 2 (x, y + H x)) 1 :=
  stdOracleFixedG_ket 2 2 H x y

theorem stdOracleReg_ket (x y : Fin 2) (G : Fin 2 → Fin 2) :
    stdOracleReg *ᵥ Pi.single (regIndex 2 2 (x, y, G)) 1 =
      Pi.single (regIndex 2 2 (x, y + G x, G)) 1 :=
  stdOracleRegG_ket 2 2 x y G

/-! ## The oracles as instruments -/

/-- The standard oracle for `H` as the unitary channel `ρ ↦ U ρ Uᴴ` on `QComp 4`. -/
def stdOracleFixedQ (H : Fin 2 → Fin 2) : QComp 4 Unit :=
  UnitaryChannel.unitaryChannel ⟨stdOracleFixed H, stdOracleFixed_unitary H⟩

/-- The register oracle as the unitary channel `ρ ↦ U ρ Uᴴ` on `QComp 16`. -/
def stdOracleRegQ : QComp 16 Unit :=
  UnitaryChannel.unitaryChannel ⟨stdOracleReg, stdOracleReg_unitary⟩

/-! ## Reduction checks

The permutations are computable, so `decide` evaluates them on every basis
state. Each check is a static pin of the index encoding: the register oracle
over `Fin 2` outputs is an involution, since `y + G x + G x = y` in `Fin 2`.
-/

/-- The register permutation at `X = Y = Fin 2` is an involution on `Fin 16`. -/
theorem stdOracleRegPerm_fin2_involutive :
    ∀ k : Fin 16, ((regIndex 2 2).permCongr stdOracleRegPerm)
      (((regIndex 2 2).permCongr stdOracleRegPerm) k) = k := by
  decide

end CatCrypt.Quantum.QROM
