/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.PermUnitaryCore
public import Mathlib.Data.BitVec

/-!
# Laws of the standard oracle

This module proves the algebraic laws of the quantum-accessible oracles of
`OracleRegisterProbe` and `SemiClassicalOracle`: the XOR oracle is a
self-inverse, self-adjoint permutation unitary; the additive standard oracle
for `H` is undone by the oracle for `-H`; a `0`-query adversary's run does not
depend on the oracle; and the oracle framed by a reference register is a
unitary with the expected action on basis kets.

## Main definitions

* `xorOraclePerm H` — the permutation `(x, y) ↦ (x, y ^^^ H x)` of
  `X × BitVec k`
* `xorIndex m k` — the row-major index of `Fin m × BitVec k` in
  `Fin (m * 2 ^ k)`
* `xorOracle m k H` — the XOR oracle `|x, y⟩ ↦ |x, y ⊕ H x⟩` as an element of
  the unitary group of `Fin (m * 2 ^ k)`

## Main results

* `xorOracle_ket` — the action `|x, y⟩ ↦ |x, y ⊕ H x⟩` on basis kets
* `xorOracle_mul_self` — two XOR queries to the same `H` compose to the
  identity
* `xorOracle_conjTranspose` — the XOR oracle is self-adjoint
* `stdOraclePerm_add`, `stdOraclePerm_neg_mul` — the additive oracle
  permutation is a homomorphism in `H`, and `H ↦ -H` inverts it
* `stdOracleFixedG_neg_mul`, `oracleU_neg_mul` — the query to `-H` undoes a
  query to `H`, on the query register and on the total register
* `run_eq_of_zero_query`, `prOut_eq_of_zero_query` — a `0`-query adversary
  has the same run, and the same acceptance probability, for every oracle
* `oracleU_mem_unitaryGroup`, `oracleU_ket` — the oracle framed by the
  reference register `Fin w` is unitary and maps `|x, y, z⟩` to
  `|x, y + H x, z⟩`
* `xorOracle_kron_one_ket` — the XOR oracle framed by a reference register
  maps `|x, y, z⟩` to `|x, y ⊕ H x, z⟩`
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Products and adjoints of permutation unitaries -/

section PermLaws

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The matrix product of two permutation unitaries is the permutation unitary
    of the product permutation. -/
theorem permUnitary_val_mul (σ τ : Equiv.Perm ι) :
    (permUnitary σ : Matrix ι ι ℂ) * (permUnitary τ : Matrix ι ι ℂ) =
      (permUnitary (σ * τ) : Matrix ι ι ℂ) := by
  rw [← permUnitary_mul]
  rfl

/-- The permutation unitary of an involution squares to the identity. -/
theorem permUnitary_mul_self_of_involutive (σ : Equiv.Perm ι)
    (hσ : Function.Involutive σ) :
    (permUnitary σ : Matrix ι ι ℂ) * (permUnitary σ : Matrix ι ι ℂ) = 1 := by
  have h : σ * σ = 1 := Equiv.ext fun k => hσ k
  rw [permUnitary_val_mul, h, permUnitary_one]
  rfl

/-- The permutation unitary of an involution is self-adjoint. -/
theorem permUnitary_conjTranspose_of_involutive (σ : Equiv.Perm ι)
    (hσ : Function.Involutive σ) :
    (permUnitary σ : Matrix ι ι ℂ)ᴴ = (permUnitary σ : Matrix ι ι ℂ) := by
  calc (permUnitary σ : Matrix ι ι ℂ)ᴴ
      = (permUnitary σ : Matrix ι ι ℂ)ᴴ *
          ((permUnitary σ : Matrix ι ι ℂ) * (permUnitary σ : Matrix ι ι ℂ)) := by
        rw [permUnitary_mul_self_of_involutive σ hσ, Matrix.mul_one]
    _ = (permUnitary σ : Matrix ι ι ℂ) := by
        rw [← Matrix.mul_assoc, star_permUnitary_mul, Matrix.one_mul]

end PermLaws

/-! ## The XOR oracle -/

section Xor

variable {X : Type} {k : ℕ}

/-- The permutation `(x, y) ↦ (x, y ^^^ H x)` of `X × BitVec k`. -/
def xorOraclePerm (H : X → BitVec k) : Equiv.Perm (X × BitVec k) where
  toFun p := (p.1, p.2 ^^^ H p.1)
  invFun p := (p.1, p.2 ^^^ H p.1)
  left_inv p := by simp [BitVec.xor_assoc]
  right_inv p := by simp [BitVec.xor_assoc]

@[simp]
theorem xorOraclePerm_apply (H : X → BitVec k) (x : X) (y : BitVec k) :
    xorOraclePerm H (x, y) = (x, y ^^^ H x) := rfl

/-- The XOR oracle permutation is an involution. -/
theorem xorOraclePerm_involutive (H : X → BitVec k) :
    Function.Involutive (xorOraclePerm H) := fun p => by
  simp [xorOraclePerm, BitVec.xor_assoc]

end Xor

section XorFin

variable (m k : ℕ)

/-- Row-major index of `Fin m × BitVec k` in `Fin (m * 2 ^ k)`, with the value
    register encoded by `BitVec.equivFin`. -/
def xorIndex : Fin m × BitVec k ≃ Fin (m * 2 ^ k) :=
  ((Equiv.refl (Fin m)).prodCongr BitVec.equivFin.toEquiv).trans finProdFinEquiv

/-- The XOR oracle for `H : Fin m → BitVec k` on `Fin (m * 2 ^ k)`:
    `|x, y⟩ ↦ |x, y ⊕ H x⟩`. -/
def xorOracle (H : Fin m → BitVec k) : Matrix.unitaryGroup (Fin (m * 2 ^ k)) ℂ :=
  permUnitary ((xorIndex m k).permCongr (xorOraclePerm H))

/-- The transported XOR oracle permutation is an involution. -/
theorem xorIndex_permCongr_involutive (H : Fin m → BitVec k) :
    Function.Involutive ((xorIndex m k).permCongr (xorOraclePerm H)) := fun i => by
  simp [Equiv.permCongr_apply, xorOraclePerm_involutive H _]

/-- `xorOracle` on the basis ket `|x, y⟩` is the basis ket `|x, y ⊕ H x⟩`. -/
theorem xorOracle_ket (H : Fin m → BitVec k) (x : Fin m) (y : BitVec k) :
    (xorOracle m k H : Matrix (Fin (m * 2 ^ k)) (Fin (m * 2 ^ k)) ℂ) *ᵥ
        Pi.single (xorIndex m k (x, y)) 1 =
      Pi.single (xorIndex m k (x, y ^^^ H x)) 1 := by
  unfold xorOracle
  rw [permUnitary_mulVec_single]
  simp [Equiv.permCongr_apply]

/-- Two XOR queries to the same function compose to the identity. -/
theorem xorOracle_mul_self (H : Fin m → BitVec k) :
    xorOracle m k H * xorOracle m k H = 1 := by
  apply Subtype.ext
  exact permUnitary_mul_self_of_involutive _ (xorIndex_permCongr_involutive m k H)

/-- The XOR oracle is self-adjoint. -/
theorem xorOracle_conjTranspose (H : Fin m → BitVec k) :
    (xorOracle m k H : Matrix (Fin (m * 2 ^ k)) (Fin (m * 2 ^ k)) ℂ)ᴴ =
      (xorOracle m k H : Matrix (Fin (m * 2 ^ k)) (Fin (m * 2 ^ k)) ℂ) :=
  permUnitary_conjTranspose_of_involutive _ (xorIndex_permCongr_involutive m k H)

end XorFin

/-! ## Inverse queries to the additive oracle -/

section Additive

variable {X Y : Type} [AddGroup Y]

/-- The additive oracle permutation is a homomorphism in the function:
    the oracle for `G + H` is the oracle for `G` followed by the oracle for
    `H`. -/
theorem stdOraclePerm_add (H G : X → Y) :
    stdOraclePerm (G + H) = stdOraclePerm H * stdOraclePerm G :=
  Equiv.ext fun p => by simp [stdOraclePerm, Equiv.Perm.mul_apply, add_assoc]

/-- The oracle for `-H` undoes the oracle for `H`. -/
theorem stdOraclePerm_neg_mul (H : X → Y) :
    stdOraclePerm (-H) * stdOraclePerm H = 1 :=
  Equiv.ext fun p => by simp [stdOraclePerm, Equiv.Perm.mul_apply]

variable (m n w : ℕ) [NeZero n]

/-- A query to `-H` after a query to `H` restores the query register. -/
theorem stdOracleFixedG_neg_mul (H : Fin m → Fin n) :
    stdOracleFixedG m n (-H) * stdOracleFixedG m n H = 1 := by
  unfold stdOracleFixedG
  have h1 : (fixedIndex m n).permCongr (1 : Equiv.Perm (Fin m × Fin n)) = 1 :=
    Equiv.ext fun k => by simp [Equiv.permCongr_apply]
  rw [permUnitary_val_mul, ← Equiv.permCongr_mul, stdOraclePerm_neg_mul, h1, permUnitary_one]
  rfl

/-- A query to `-H` after a query to `H` restores the total register. -/
theorem oracleU_neg_mul (H : Fin m → Fin n) :
    oracleU m n w (-H) * oracleU m n w H = 1 := by
  apply Subtype.ext
  change stdOracleFixedG m n (-H) ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℂ) *
      (stdOracleFixedG m n H ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℂ)) = 1
  rw [kronecker_mul_kronecker, stdOracleFixedG_neg_mul, Matrix.one_mul, kronecker_one_one]

end Additive

/-! ## Zero-query adversaries -/

section ZeroQuery

variable {m n w : ℕ} [NeZero n]

/-- The run of a `0`-query adversary is the same for every oracle. -/
theorem run_eq_of_zero_query (A : QAdv m n w 0) (H H' : Fin m → Fin n) :
    run A H = run A H' := by
  rw [run, run, oracleChain, oracleChain]

/-- A `0`-query adversary outputs `1` with the same probability for every
    oracle. -/
theorem prOut_eq_of_zero_query (A : QAdv m n w 0) (H H' : Fin m → Fin n) :
    prOut A H = prOut A H' := by
  unfold prOut
  rw [run_eq_of_zero_query A H H']

end ZeroQuery

/-! ## The oracle framed by a reference register -/

section Framed

variable (m n w : ℕ) [NeZero n]

/-- The oracle `stdOracleFixedG H ⊗ₖ 1` framed by the reference register
    `Fin w` is unitary. -/
theorem oracleU_mem_unitaryGroup (H : Fin m → Fin n) :
    stdOracleFixedG m n H ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℂ) ∈
      Matrix.unitaryGroup (Fin (m * n * w)) ℂ :=
  (oracleU m n w H).property

/-- The framed oracle maps the basis ket `|x, y, z⟩` to `|x, y + H x, z⟩`,
    leaving the reference register `z` unchanged. -/
theorem oracleU_ket (H : Fin m → Fin n) (x : Fin m) (y : Fin n) (z : Fin w) :
    (oracleU m n w H : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) *ᵥ
        Pi.single (oracleIndex m n w ((x, y), z)) 1 =
      Pi.single (oracleIndex m n w ((x, y + H x), z)) 1 := by
  rw [oracleU_eq_permUnitary, permUnitary_mulVec_single, oraclePerm_apply]

variable (k : ℕ)

/-- The XOR oracle framed by the reference register `Fin w` is unitary. -/
theorem xorOracle_kron_one_mem_unitaryGroup (H : Fin m → BitVec k) :
    (xorOracle m k H : Matrix (Fin (m * 2 ^ k)) (Fin (m * 2 ^ k)) ℂ) ⊗ₖ
        (1 : Matrix (Fin w) (Fin w) ℂ) ∈ Matrix.unitaryGroup (Fin (m * 2 ^ k * w)) ℂ :=
  kronecker_mem_unitaryGroup (xorOracle m k H).property
    (Matrix.mem_unitaryGroup_iff.mpr (by simp))

/-- The XOR oracle framed by the reference register `Fin w` maps the basis ket
    `|x, y, z⟩` to `|x, y ⊕ H x, z⟩`. -/
theorem xorOracle_kron_one_ket (H : Fin m → BitVec k) (x : Fin m) (y : BitVec k)
    (z : Fin w) :
    ((xorOracle m k H : Matrix (Fin (m * 2 ^ k)) (Fin (m * 2 ^ k)) ℂ) ⊗ₖ
        (1 : Matrix (Fin w) (Fin w) ℂ)) *ᵥ
        Pi.single (finProdEquiv (m * 2 ^ k) w (xorIndex m k (x, y), z)) 1 =
      Pi.single (finProdEquiv (m * 2 ^ k) w (xorIndex m k (x, y ^^^ H x), z)) 1 := by
  have h1 : (1 : Matrix (Fin w) (Fin w) ℂ) =
      (permUnitary (1 : Equiv.Perm (Fin w)) : Matrix (Fin w) (Fin w) ℂ) := by simp
  rw [h1, xorOracle, permUnitary_kron, permUnitary_mulVec_single]
  simp [Equiv.permCongr_apply, Equiv.prodCongr_apply]

end Framed

end CatCrypt.Quantum.QROM
