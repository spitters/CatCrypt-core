/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.SemiClassicalOracle
public import CatCryptCore.Quantum.KroneckerPSD

/-!
# The sampled oracle is the oracle with the function in a register

A `q`-query adversary `A : QAdv m n w q` run against the standard oracle for a
function `H : Fin m → Fin n` sampled uniformly accepts with probability
`(n ^ m)⁻¹ ∑_H prOut A H`. This module proves that the same probability is
obtained from one run in which the function is held in a table register
`Fin (n ^ m)`: the table register is initialised to the uniform mixture
`(n ^ m)⁻¹ ∑_H |H⟩⟨H|`, every oracle call is the register oracle
`stdOracleRegG` (`|x, y, G⟩ ↦ |x, y + G x, G⟩`) tensored with the identity on
the work register, and the adversary's unitaries and final projector act as
`· ⊗ₖ 1` on the table register.

The total register is `Fin (m * n * w * n ^ m)`: the adversary register
`Fin (m * n * w)` of `SemiClassicalOracle` first and the table register last, so
that adversary operations are `U ⊗ₖ 1` at the type `TensorProduct.kronecker`
produces. The register oracle is `stdOracleRegG m n ⊗ₖ 1_w` reindexed along
`regReindex`, which moves the table index next to the query register.

## Main definitions

* `tableIndex m n` — the index `Fin m → Fin n ≃ Fin (n ^ m)` of the table register
* `totIndex m n w` — the index of the total register,
  `((x, y), z), G ↦ Fin (m * n * w * n ^ m)`
* `regReindex m n w` — the equivalence between the total register and the
  index space `Fin (m * (n * n ^ m) * w)` of `stdOracleRegG m n ⊗ₖ 1_w`
* `oracleRegU m n w`, `oracleRegQ m n w` — the register oracle on the total
  register, as a unitary and as a unitary channel
* `tableLiftU t U` — the unitary `U ⊗ₖ 1_t`
* `tableProj m n G` — the projector `|G⟩⟨G|` on the table register
* `tableMix m n` — the uniform mixture `(n ^ m)⁻¹ ∑_G |G⟩⟨G|`
* `runReg A`, `initReg A`, `prOutReg A` — the run of `A` against the register
  oracle, its initial state `A.init ⊗ₖ tableMix`, and its acceptance probability

## Main results

* `oracleRegU_mul_one_kronecker_tableProj` — the register oracle is block
  diagonal in the table basis: on the block `G` it is `oracleU m n w G ⊗ₖ 1`
* `oracleRegU_conj_kronecker_tableProj` — conjugating `X ⊗ₖ |G⟩⟨G|` by the
  register oracle conjugates `X` by the oracle for `G`
* `oracleChain_reg_branch` — the register chain maps `X ⊗ₖ |G⟩⟨G|` to the
  chain for `G` applied to `X`, tensored with `|G⟩⟨G|`
* `prOutReg_eq_avg_prOut` — `prOutReg A = (n ^ m)⁻¹ ∑_H prOut A H`
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix Classical CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
  CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.Measurement

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Index equivalences -/

section Index

variable (m n w : ℕ)

/-- The index of the table register: `G ↦ Fin (n ^ m)` through
    `finFunctionFinEquiv`. -/
def tableIndex : (Fin m → Fin n) ≃ Fin (n ^ m) := finFunctionFinEquiv

/-- The index of the total register `((x, y), z), G`: the adversary register
    `Fin (m * n * w)` first, the table register `Fin (n ^ m)` last. -/
def totIndex : ((Fin m × Fin n) × Fin w) × (Fin m → Fin n) ≃ Fin (m * n * w * n ^ m) :=
  ((((fixedIndex m n).prodCongr (Equiv.refl (Fin w))).trans (finProdEquiv (m * n) w)).prodCongr
    (tableIndex m n)).trans (finProdEquiv (m * n * w) (n ^ m))

/-- The index of `stdOracleRegG m n ⊗ₖ 1_w`: `(x, y, G), z`. -/
def regWorkIndex : (Fin m × Fin n × (Fin m → Fin n)) × Fin w ≃ Fin (m * (n * n ^ m) * w) :=
  ((regIndex m n).prodCongr (Equiv.refl (Fin w))).trans (finProdEquiv (m * (n * n ^ m)) w)

/-- The rearrangement `((x, y), z), G ↦ (x, y, G), z`. -/
def regShuffle :
    ((Fin m × Fin n) × Fin w) × (Fin m → Fin n) ≃
      (Fin m × Fin n × (Fin m → Fin n)) × Fin w where
  toFun p := ((p.1.1.1, p.1.1.2, p.2), p.1.2)
  invFun p := (((p.1.1, p.1.2.1), p.2), p.1.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The equivalence between the total register and the index space of
    `stdOracleRegG m n ⊗ₖ 1_w`. -/
def regReindex : Fin (m * n * w * n ^ m) ≃ Fin (m * (n * n ^ m) * w) :=
  (totIndex m n w).symm.trans ((regShuffle m n w).trans (regWorkIndex m n w))

theorem finProdEquiv_symm_totIndex (p : ((Fin m × Fin n) × Fin w) × (Fin m → Fin n)) :
    (finProdEquiv (m * n * w) (n ^ m)).symm (totIndex m n w p) =
      (finProdEquiv (m * n) w (fixedIndex m n p.1.1, p.1.2), tableIndex m n p.2) := by
  simp [totIndex]
  rfl

theorem regReindex_totIndex (p : ((Fin m × Fin n) × Fin w) × (Fin m → Fin n)) :
    regReindex m n w (totIndex m n w p) =
      finProdEquiv (m * (n * n ^ m)) w (regIndex m n (p.1.1.1, p.1.1.2, p.2), p.1.2) := by
  simp [regReindex, regWorkIndex, regShuffle]

end Index

/-! ## Unitaries under reindexing and tensoring -/

section Unitary

/-- Reindexing a unitary along an equivalence gives a unitary. -/
theorem submatrix_equiv_mem_unitaryGroup {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {A : Matrix κ κ ℂ} (hA : A ∈ Matrix.unitaryGroup κ ℂ)
    (e : ι ≃ κ) : A.submatrix e e ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose] at hA ⊢
  rw [conjTranspose_submatrix, submatrix_mul_equiv, hA, submatrix_one_equiv]

/-- The unitary `U ⊗ₖ 1_t`. -/
def tableLiftU {d : ℕ} (t : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.unitaryGroup (Fin (d * t)) ℂ :=
  ⟨(U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (1 : Matrix (Fin t) (Fin t) ℂ),
    kronecker_mem_unitaryGroup U.property (Matrix.mem_unitaryGroup_iff.mpr (by simp))⟩

@[simp]
theorem tableLiftU_val {d : ℕ} (t : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (tableLiftU t U : Matrix (Fin (d * t)) (Fin (d * t)) ℂ) =
      (U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (1 : Matrix (Fin t) (Fin t) ℂ) := rfl

/-- Conjugation by `V ⊗ₖ 1` acts on the first factor. -/
theorem kronecker_one_conj {d t : ℕ} (V X : Matrix (Fin d) (Fin d) ℂ)
    (E : Matrix (Fin t) (Fin t) ℂ) :
    (V ⊗ₖ (1 : Matrix (Fin t) (Fin t) ℂ)) * (X ⊗ₖ E) *
        (V ⊗ₖ (1 : Matrix (Fin t) (Fin t) ℂ))ᴴ =
      (V * X * Vᴴ) ⊗ₖ E := by
  rw [conjTranspose_kronecker, conjTranspose_one, kronecker_mul_kronecker,
    kronecker_mul_kronecker, Matrix.one_mul, Matrix.mul_one]

end Unitary

/-! ## The register oracle on the total register -/

section RegOracle

variable (m n w : ℕ) [NeZero n]

/-- The register oracle on the total register: `stdOracleRegG m n ⊗ₖ 1_w`
    reindexed along `regReindex`, so that it acts as
    `|((x, y), z), G⟩ ↦ |((x, y + G x), z), G⟩`. -/
def oracleRegU : Matrix.unitaryGroup (Fin (m * n * w * n ^ m)) ℂ :=
  ⟨(stdOracleRegG m n ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℂ)).submatrix
      (regReindex m n w) (regReindex m n w),
    submatrix_equiv_mem_unitaryGroup
      (kronecker_mem_unitaryGroup (stdOracleRegG_unitary m n)
        (Matrix.mem_unitaryGroup_iff.mpr (by simp))) _⟩

/-- The register oracle as a unitary channel on the total register. -/
def oracleRegQ : QComp (m * n * w * n ^ m) Unit :=
  unitaryChannel (oracleRegU m n w)

/-- The projector `|G⟩⟨G|` on the table register. -/
def tableProj (G : Fin m → Fin n) : Matrix (Fin (n ^ m)) (Fin (n ^ m)) ℂ :=
  Matrix.single (tableIndex m n G) (tableIndex m n G) 1

/-- The uniform mixture `(n ^ m)⁻¹ ∑_G |G⟩⟨G|` on the table register. -/
def tableMix : Matrix (Fin (n ^ m)) (Fin (n ^ m)) ℂ :=
  ((n : ℂ) ^ m)⁻¹ • ∑ G : Fin m → Fin n, tableProj m n G

/-- The entry of `stdOracleRegG` between two basis kets. -/
theorem stdOracleRegG_apply_regIndex (p p' : Fin m × Fin n × (Fin m → Fin n)) :
    stdOracleRegG m n (regIndex m n p) (regIndex m n p') =
      if p = stdOracleRegPerm p' then 1 else 0 := by
  obtain ⟨x, y, G⟩ := p'
  have := congrFun (stdOracleRegG_ket m n x y G) (regIndex m n p)
  rw [Matrix.mulVec_single_one] at this
  refine this.trans ?_
  rw [Pi.single_apply]
  exact if_congr (by simp) rfl rfl

/-- The entry of `stdOracleFixedG` between two basis kets. -/
theorem stdOracleFixedG_apply_fixedIndex_pair (H : Fin m → Fin n) (p p' : Fin m × Fin n) :
    stdOracleFixedG m n H (fixedIndex m n p) (fixedIndex m n p') =
      if p = stdOraclePerm H p' then 1 else 0 := by
  obtain ⟨x, y⟩ := p'
  have := congrFun (stdOracleFixedG_ket m n H x y) (fixedIndex m n p)
  rw [Matrix.mulVec_single_one] at this
  refine this.trans ?_
  rw [Pi.single_apply]
  exact if_congr (by simp) rfl rfl

omit [NeZero n] in
/-- `1 ⊗ₖ |G⟩⟨G|` is diagonal, with entry `1` exactly on the table index `G`. -/
theorem one_kronecker_tableProj (G : Fin m → Fin n) :
    (1 : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) ⊗ₖ tableProj m n G =
      Matrix.diagonal (fun k =>
        if ((finProdEquiv (m * n * w) (n ^ m)).symm k).2 = tableIndex m n G then 1 else 0) := by
  ext i j
  simp only [kronecker_apply, tableProj, Matrix.single_apply, Matrix.one_apply,
    Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp [eq_comm]
  · have : ¬(((finProdEquiv (m * n * w) (n ^ m)).symm i).1 =
        ((finProdEquiv (m * n * w) (n ^ m)).symm j).1 ∧
      ((finProdEquiv (m * n * w) (n ^ m)).symm i).2 =
        ((finProdEquiv (m * n * w) (n ^ m)).symm j).2) := by
      intro ⟨h1, h2⟩
      exact h ((finProdEquiv _ _).symm.injective (Prod.ext h1 h2))
    rcases not_and_or.mp this with h1 | h2
    · simp [h, h1]
    · have h3 : ¬(tableIndex m n G = ((finProdEquiv (m * n * w) (n ^ m)).symm i).2 ∧
          tableIndex m n G = ((finProdEquiv (m * n * w) (n ^ m)).symm j).2) :=
        fun h3 => h2 (h3.1.symm.trans h3.2)
      simp [h, h3]

/-- The register oracle is block diagonal in the table basis: on the block of
    `G` it is the oracle for `G` on the adversary register. -/
theorem oracleRegU_mul_one_kronecker_tableProj (G : Fin m → Fin n) :
    (oracleRegU m n w : Matrix _ _ ℂ) *
        ((1 : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) ⊗ₖ tableProj m n G) =
      ((oracleU m n w G : Matrix _ _ ℂ) ⊗ₖ (1 : Matrix (Fin (n ^ m)) (Fin (n ^ m)) ℂ)) *
        ((1 : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) ⊗ₖ tableProj m n G) := by
  rw [one_kronecker_tableProj]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal]
  obtain ⟨⟨⟨⟨x, y⟩, z⟩, G₁⟩, rfl⟩ := (totIndex m n w).surjective i
  obtain ⟨⟨⟨⟨x', y'⟩, z'⟩, G₂⟩, rfl⟩ := (totIndex m n w).surjective j
  simp only [finProdEquiv_symm_totIndex, EmbeddingLike.apply_eq_iff_eq]
  split_ifs with hG
  · subst hG
    simp only [oracleRegU, regReindex_totIndex, submatrix_apply, kronecker_apply,
      Equiv.symm_apply_apply, stdOracleRegG_apply_regIndex, oracleU_val,
      finProdEquiv_symm_totIndex, stdOracleFixedG_apply_fixedIndex_pair, Matrix.one_apply,
      stdOracleRegPerm_apply, stdOraclePerm_apply, Prod.mk.injEq,
      EmbeddingLike.apply_eq_iff_eq]
    split_ifs <;> simp_all
  · simp

/-- Conjugating `X ⊗ₖ |G⟩⟨G|` by the register oracle conjugates `X` by the
    oracle for `G`. -/
theorem oracleRegU_conj_kronecker_tableProj (G : Fin m → Fin n)
    (X : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (oracleRegU m n w : Matrix _ _ ℂ) * (X ⊗ₖ tableProj m n G) *
        (oracleRegU m n w : Matrix _ _ ℂ)ᴴ =
      ((oracleU m n w G : Matrix _ _ ℂ) * X * (oracleU m n w G : Matrix _ _ ℂ)ᴴ) ⊗ₖ
        tableProj m n G := by
  set P : Matrix (Fin (m * n * w * n ^ m)) (Fin (m * n * w * n ^ m)) ℂ :=
    (1 : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) ⊗ₖ tableProj m n G with hPdef
  have hE : tableProj m n G * tableProj m n G = tableProj m n G := by
    simp [tableProj, Matrix.single_mul_single_same]
  have hP : Pᴴ = P := by
    simp [hPdef, conjTranspose_kronecker, tableProj, Matrix.conjTranspose_single]
  have hX : X ⊗ₖ tableProj m n G = P * (X ⊗ₖ tableProj m n G) * P := by
    rw [hPdef, kronecker_mul_kronecker, kronecker_mul_kronecker, Matrix.one_mul,
      Matrix.mul_one, hE, hE]
  have hO := oracleRegU_mul_one_kronecker_tableProj m n w G
  rw [← hPdef] at hO
  set W : Matrix (Fin (m * n * w * n ^ m)) (Fin (m * n * w * n ^ m)) ℂ :=
    (oracleU m n w G : Matrix _ _ ℂ) ⊗ₖ (1 : Matrix (Fin (n ^ m)) (Fin (n ^ m)) ℂ)
    with hWdef
  calc (oracleRegU m n w : Matrix _ _ ℂ) * (X ⊗ₖ tableProj m n G) *
          (oracleRegU m n w : Matrix _ _ ℂ)ᴴ
      = ((oracleRegU m n w : Matrix _ _ ℂ) * P) * (X ⊗ₖ tableProj m n G) *
          ((oracleRegU m n w : Matrix _ _ ℂ) * P)ᴴ := by
        rw [conjTranspose_mul, hP]
        conv_lhs => rw [hX]
        simp only [Matrix.mul_assoc]
    _ = (W * P) * (X ⊗ₖ tableProj m n G) * (W * P)ᴴ := by
        rw [hO]
    _ = W * (P * (X ⊗ₖ tableProj m n G) * P) * Wᴴ := by
        rw [conjTranspose_mul, hP]
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [← hX, hWdef, kronecker_one_conj]

/-- The register chain maps `X ⊗ₖ |G⟩⟨G|` to the chain for the oracle of `G`
    applied to `X`, tensored with `|G⟩⟨G|`. -/
theorem oracleChain_reg_branch (G : Fin m → Fin n) (k : ℕ)
    (V : Fin (k + 1) → Matrix.unitaryGroup (Fin (m * n * w)) ℂ)
    (X : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (oracleChain (oracleRegQ m n w) k (fun i => tableLiftU (n ^ m) (V i))).branch ()
        (X ⊗ₖ tableProj m n G) =
      (oracleChain (oracleQ m n w G) k V).branch () X ⊗ₖ tableProj m n G := by
  induction k generalizing X with
  | zero =>
    simp only [oracleChain, unitaryChannel_branch_apply, tableLiftU_val, kronecker_one_conj]
  | succ k ih =>
    simp only [oracleChain]
    rw [qbind_unit_branch, qbind_unit_branch, qbind_unit_branch, qbind_unit_branch]
    rw [unitaryChannel_branch_apply, unitaryChannel_branch_apply, tableLiftU_val, kronecker_one_conj]
    rw [oracleRegQ, oracleQ, unitaryChannel_branch_apply, unitaryChannel_branch_apply,
      oracleRegU_conj_kronecker_tableProj]
    exact ih (Fin.tail V) _

end RegOracle

/-! ## The run against the register oracle -/

section RunReg

variable {m n w q : ℕ} [NeZero n]

/-- The final projector of `A` tensored with the identity on the table register. -/
def QAdv.finalReg (A : QAdv m n w q) :
    Matrix (Fin (m * n * w * n ^ m)) (Fin (m * n * w * n ^ m)) ℂ :=
  A.final ⊗ₖ (1 : Matrix (Fin (n ^ m)) (Fin (n ^ m)) ℂ)

omit [NeZero n] in
theorem QAdv.finalReg_conjTranspose (A : QAdv m n w q) : A.finalRegᴴ = A.finalReg := by
  rw [QAdv.finalReg, conjTranspose_kronecker, conjTranspose_one, A.final_conjTranspose]

omit [NeZero n] in
theorem QAdv.finalReg_mul_self (A : QAdv m n w q) : A.finalReg * A.finalReg = A.finalReg := by
  rw [QAdv.finalReg, kronecker_mul_kronecker, A.final_mul_self, Matrix.mul_one]

/-- The final measurement of `A` on the total register. -/
def QAdv.measureReg (A : QAdv m n w q) : QComp (m * n * w * n ^ m) Bool :=
  measProj A.finalReg A.finalReg_conjTranspose A.finalReg_mul_self

/-- The run of `A` against the register oracle:
    `U₀ ⊗ 1 ; O_reg ; U₁ ⊗ 1 ; … ; O_reg ; U_q ⊗ 1 ; measure (final ⊗ 1)`. -/
def runReg (A : QAdv m n w q) : QComp (m * n * w * n ^ m) Bool :=
  QComp.qbind (oracleChain (oracleRegQ m n w) q (fun i => tableLiftU (n ^ m) (A.U i)))
    fun _ => A.measureReg

omit [NeZero n] in
theorem tableMix_eq :
    tableMix m n = ((n : ℂ) ^ m)⁻¹ • (1 : Matrix (Fin (n ^ m)) (Fin (n ^ m)) ℂ) := by
  rw [tableMix]
  congr 1
  ext i j
  rw [Matrix.sum_apply, ← (tableIndex m n).symm.sum_comp]
  by_cases h : i = j
  · subst h; simp [tableProj, Matrix.single_apply]
  · simp [tableProj, Matrix.single_apply, h]

omit [NeZero n] in
theorem tableProj_trace (G : Fin m → Fin n) : (tableProj m n G).trace = 1 := by
  simp [tableProj]

omit [NeZero n] in
theorem tableMix_posSemidef : (tableMix (n := n) m).PosSemidef := by
  rw [tableMix_eq]
  refine Matrix.PosSemidef.one.smul ?_
  have : ((n : ℂ) ^ m)⁻¹ = (((n : ℝ) ^ m)⁻¹ : ℝ) := by push_cast; rfl
  rw [this]
  exact Complex.zero_le_real.mpr (by positivity)

theorem tableMix_trace : (tableMix (n := n) m).trace = 1 := by
  rw [tableMix_eq, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
  push_cast
  exact inv_mul_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne n)))

/-- The initial state of the register run: `A.init ⊗ₖ tableMix`. -/
def initReg (A : QAdv m n w q) : DensityMatrix (m * n * w * n ^ m) :=
  ⟨A.init.val ⊗ₖ tableMix m n, QHL.kronecker_posSemidef A.init.psd tableMix_posSemidef, by
    rw [TensorProduct.trace_kronecker, A.init.tr_one, tableMix_trace, one_mul]⟩

/-- The probability that the register run outputs `1`. -/
def prOutReg (A : QAdv m n w q) : ℝ≥0∞ :=
  prTrue_Q (runReg A) (initReg A)

/-- On `X ⊗ₖ |G⟩⟨G|` the `true` branch of the register run is the `true` branch
    of the run for `G` on `X`, tensored with `|G⟩⟨G|`. -/
theorem runReg_branch_true (A : QAdv m n w q) (G : Fin m → Fin n)
    (X : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (runReg A).branch true (X ⊗ₖ tableProj m n G) =
      (run A G).branch true X ⊗ₖ tableProj m n G := by
  rw [runReg, run, qbind_unit_branch, qbind_unit_branch, oracleChain_reg_branch,
    QAdv.measureReg, QAdv.measure, measProj_branch_true, measProj_branch_true, QAdv.finalReg,
    kronecker_one_conj]

/-- The sampled oracle equals the oracle with the function held in a register:
    the acceptance probability of the register run is the average over `H` of
    the acceptance probability against the standard oracle for `H`. -/
theorem prOutReg_eq_avg_prOut (A : QAdv m n w q) :
    prOutReg A = ((n : ℝ≥0∞) ^ m)⁻¹ * ∑ H : Fin m → Fin n, prOut A H := by
  have hnn : ∀ H : Fin m → Fin n, 0 ≤ ((run A H).branch true A.init.val).trace.re := fun H =>
    (Complex.nonneg_iff.mp ((run A H).branch_psd true _ A.init.psd).trace_nonneg).1
  have hc : ((n : ℂ) ^ m)⁻¹ = (((n : ℝ) ^ m)⁻¹ : ℝ) := by push_cast; rfl
  have hsplit : A.init.val ⊗ₖ tableMix m n =
      ∑ G : Fin m → Fin n, ((n : ℂ) ^ m)⁻¹ • (A.init.val ⊗ₖ tableProj m n G) := by
    have hs : ∀ (c : ℂ) (B : Matrix (Fin (n ^ m)) (Fin (n ^ m)) ℂ),
        c • (A.init.val ⊗ₖ B) = (c • A.init.val) ⊗ₖ B := by
      intro c B; ext i j; simp [kronecker_apply, mul_assoc]
    rw [tableMix, ← smul_kronecker_eq_kronecker_smul]
    simp_rw [hs]
    rw [kronecker_finset_sum_right]
  unfold prOutReg prOut prTrue_Q
  rw [show (initReg A).val = A.init.val ⊗ₖ tableMix m n from rfl, hsplit, map_sum]
  simp only [map_smul, runReg_branch_true, trace_sum, trace_smul, TensorProduct.trace_kronecker,
    tableProj_trace, mul_one, smul_eq_mul, hc, Complex.re_sum, Complex.re_ofReal_mul]
  rw [ENNReal.ofReal_sum_of_nonneg (fun H _ => mul_nonneg (by positivity) (hnn H)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_inv_of_pos (pow_pos (Nat.cast_pos.mpr (NeZero.pos n)) m),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]

end RunReg

end CatCrypt.Quantum.QROM
