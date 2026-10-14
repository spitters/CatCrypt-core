/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.OracleRegisterMixture
public import CatCryptCore.Quantum.QROM.O2HTheorem

/-!
# The compressed oracle

Zhandry's compressed oracle (CRYPTO 2019) for a `q`-query adversary
`A : QAdv m n w q` and a uniformly random function `H : Fin m → Fin n`. The
function is held in a register, the oracle acts on that register, and the
random choice of `H` becomes the initial state of the register:

* the purified standard oracle holds the function table in the register
  `Fin (n ^ m)` of `OracleRegisterMixture`, initialised to the uniform
  superposition `(n ^ m)^{-1/2} ∑_G |G⟩`;
* the compressed oracle holds a database `D : Fin m → Fin (n + 1)` in the
  register `Fin ((n + 1) ^ m)`, each entry a value `y < n` or the empty symbol
  `⊥ = n`, initialised to the empty database. One call decompresses the
  database, applies the standard oracle to it, and compresses it again.

Decompression of one entry is the reflection `1 - |u⟩⟨u|` with
`u = |⊥⟩ - n^{-1/2} ∑_{y < n} |y⟩`; it exchanges `|⊥⟩` with the uniform
superposition. Decompression of the database applies it to every entry, so it
sends the empty database to the uniform superposition over the databases with
no `⊥` entry.

Both runs reduce to one identity: against a block-diagonal oracle
`∑ₖ O_{f k} ⊗ |k⟩⟨k|`, a table register in state `σ` gives the acceptance
probability `∑ₖ σ k k · prOut A (f k)` (`prTrue_runLift_tableOracleU`). The
adversary's operations act on the other registers, so conjugating the oracle
by decompression is the same as decompressing the initial state
(`prTrue_runLift_conj`).

## Main definitions

* `blockU V` — the block-diagonal unitary `∑ₖ V k ⊗ₖ |k⟩⟨k|`
* `runLift t O A` — the run of `A` against an oracle `O` on the register
  `Fin (m * n * w * t)`, the adversary acting as `· ⊗ₖ 1_t`
* `tableOracleU f` — the oracle that applies the standard oracle for `f k` on
  the table block `k`
* `tablePure m n`, `initPure A`, `prOutPure A` — the uniform superposition on
  the table register and the acceptance probability of the purified run
* `decompEntry n`, `decompDB m n`, `decompDBU m n` — decompression of one entry
  and of the database
* `stdDbU m n w`, `decompU m n w`, `cmpOracleU m n w` — the standard oracle on
  the database register (`⊥` read as `0`), decompression on the total register,
  and the compressed oracle `decompUᴴ * stdDbU * decompU`
* `dbEmpty m n`, `initCmp A`, `runCmp A`, `prOutCmp A` — the empty database and
  the compressed run with its acceptance probability

## Main results

* `chainOp_blockU` — the chain around a block-diagonal oracle is block diagonal
* `prTrue_runLift_tableOracleU` — the acceptance probability against
  `tableOracleU f` from `ρ ⊗ σ` is `∑ₖ σ k k · prOut A (f k)`
* `oracleRegU_eq_tableOracleU` — the register oracle of `OracleRegisterMixture`
  is `tableOracleU` of the table index
* `prOutPure_eq_avg_prOut`, `prOutPure_eq_prOutReg` — the purified standard
  oracle gives `(n ^ m)⁻¹ ∑_H prOut A H`, the value of the uniform mixture
* `prTrue_runLift_conj` — conjugating the oracle by `1 ⊗ D` equals replacing
  the table state `σ` by `D σ Dᴴ`
* `decompEntry_mem_unitaryGroup`, `decompEntry_apply_last`,
  `decompDB_mul_conjTranspose`, `decompDB_apply_empty`
* `prOutCmp_eq_avg_prOut` — the compressed oracle from the empty database gives
  `(n ^ m)⁻¹ ∑_H prOut A H`
* `prOut_compressed_eq` — `prOutCmp A = prOutPure A` for every adversary `A`
* `prOutCmp_eq_prOutReg` — `prOutCmp A = prOutReg A`

## References

* [Zhandry — How to Record Quantum Queries, and Applications to Quantum
  Indifferentiability, CRYPTO 2019]
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix Classical CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
  CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.Measurement

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Block-diagonal operators on a table register -/

section Block

variable {d t : ℕ}

theorem sum_single_diag_one : ∑ k : Fin t, Matrix.single k k (1 : ℂ) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.sum_apply, Matrix.single_apply]
  · simp [Matrix.sum_apply, Matrix.single_apply, h]

theorem kronecker_zero_right (X : Matrix (Fin d) (Fin d) ℂ) :
    X ⊗ₖ (0 : Matrix (Fin t) (Fin t) ℂ) = 0 := by
  ext i j
  simp [kronecker_apply]

/-- `X ⊗ₖ 1` is the block-diagonal operator with every block `X`. -/
theorem kronecker_one_eq_sum_single (X : Matrix (Fin d) (Fin d) ℂ) :
    X ⊗ₖ (1 : Matrix (Fin t) (Fin t) ℂ) = ∑ k, X ⊗ₖ Matrix.single k k 1 := by
  rw [kronecker_finset_sum_right, sum_single_diag_one]

/-- The product of two block-diagonal operators is block diagonal, with the
    blockwise products as blocks. -/
theorem sum_kronecker_single_mul (X Y : Fin t → Matrix (Fin d) (Fin d) ℂ) :
    (∑ k, X k ⊗ₖ Matrix.single k k 1) * (∑ j, Y j ⊗ₖ Matrix.single j j 1) =
      ∑ k, (X k * Y k) ⊗ₖ Matrix.single k k 1 := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single k]
  · rw [kronecker_mul_kronecker, Matrix.single_mul_single_same, mul_one]
  · intro j _ hj
    rw [kronecker_mul_kronecker, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hj),
      kronecker_zero_right]
  · simp

theorem conjTranspose_sum_kronecker_single (X : Fin t → Matrix (Fin d) (Fin d) ℂ) :
    (∑ k, X k ⊗ₖ Matrix.single k k 1)ᴴ = ∑ k, (X k)ᴴ ⊗ₖ Matrix.single k k 1 := by
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [conjTranspose_kronecker, Matrix.conjTranspose_single, star_one]

/-- A block-diagonal operator with unitary blocks is unitary. -/
theorem sum_kronecker_single_mem_unitaryGroup (V : Fin t → Matrix.unitaryGroup (Fin d) ℂ) :
    (∑ k, (V k : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Matrix.single k k 1) ∈
      Matrix.unitaryGroup (Fin (d * t)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_sum_kronecker_single,
    sum_kronecker_single_mul]
  simp_rw [show ∀ k, (V k : Matrix (Fin d) (Fin d) ℂ) * (V k : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1
    from fun k => Matrix.mem_unitaryGroup_iff.mp (V k).prop]
  rw [← kronecker_one_eq_sum_single, kronecker_one_one]

/-- The block-diagonal unitary `∑ₖ V k ⊗ |k⟩⟨k|`: the operator `V k` applied
    to the first register, controlled on the basis state `k` of the second. -/
def blockU (V : Fin t → Matrix.unitaryGroup (Fin d) ℂ) : Matrix.unitaryGroup (Fin (d * t)) ℂ :=
  ⟨∑ k, (V k : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Matrix.single k k 1,
    sum_kronecker_single_mem_unitaryGroup V⟩

theorem blockU_val (V : Fin t → Matrix.unitaryGroup (Fin d) ℂ) :
    (blockU V : Matrix (Fin (d * t)) (Fin (d * t)) ℂ) =
      ∑ k, (V k : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Matrix.single k k 1 := rfl

/-- The chain of lifted unitaries around a block-diagonal oracle is block
    diagonal, with the chain for the oracle `V k` as the block `k`. -/
theorem chainOp_blockU (V : Fin t → Matrix.unitaryGroup (Fin d) ℂ) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    chainOp (blockU V : Matrix (Fin (d * t)) (Fin (d * t)) ℂ) q (fun i => tableLiftU t (U i)) =
      ∑ k, chainOp (V k : Matrix (Fin d) (Fin d) ℂ) q U ⊗ₖ Matrix.single k k 1 := by
  induction q with
  | zero => simp only [chainOp, tableLiftU_val, kronecker_one_eq_sum_single]
  | succ q ih =>
    simp only [chainOp]
    rw [show (Fin.tail fun i => tableLiftU t (U i)) = fun i => tableLiftU t (Fin.tail U i)
      from rfl, ih, blockU_val, tableLiftU_val, kronecker_one_eq_sum_single,
      sum_kronecker_single_mul, sum_kronecker_single_mul]

/-- The trace of `P_k σ P_j` for the basis projectors `P_k = |k⟩⟨k|`. -/
theorem trace_single_mul_mul_single (σ : Matrix (Fin t) (Fin t) ℂ) (k j : Fin t) :
    (Matrix.single k k (1 : ℂ) * σ * Matrix.single j j 1).trace =
      if k = j then σ k k else 0 := by
  rw [Matrix.single_mul_mul_single, one_mul, mul_one]
  split_ifs with h
  · subst h; simp
  · exact Matrix.trace_single_eq_of_ne _ _ _ h

/-- `ρ ⊗ₖ σ` as a density matrix. -/
def kronDM (ρ : DensityMatrix d) (σ : DensityMatrix t) : DensityMatrix (d * t) :=
  ⟨ρ.val ⊗ₖ σ.val, QHL.kronecker_posSemidef ρ.psd σ.psd, by
    rw [TensorProduct.trace_kronecker, ρ.tr_one, σ.tr_one, one_mul]⟩

theorem kronDM_val (ρ : DensityMatrix d) (σ : DensityMatrix t) :
    (kronDM ρ σ).val = ρ.val ⊗ₖ σ.val := rfl

end Block

/-! ## The run with a table register -/

section RunLift

variable {m n w q : ℕ}

/-- The final projector of `A` tensored with the identity on a register `Fin t`. -/
def QAdv.finalLift (t : ℕ) (A : QAdv m n w q) :
    Matrix (Fin (m * n * w * t)) (Fin (m * n * w * t)) ℂ :=
  A.final ⊗ₖ (1 : Matrix (Fin t) (Fin t) ℂ)

theorem QAdv.finalLift_conjTranspose (t : ℕ) (A : QAdv m n w q) :
    (A.finalLift t)ᴴ = A.finalLift t := by
  rw [QAdv.finalLift, conjTranspose_kronecker, conjTranspose_one, A.final_conjTranspose]

theorem QAdv.finalLift_mul_self (t : ℕ) (A : QAdv m n w q) :
    A.finalLift t * A.finalLift t = A.finalLift t := by
  rw [QAdv.finalLift, kronecker_mul_kronecker, A.final_mul_self, Matrix.mul_one]

/-- The final measurement of `A` on the register `Fin (m * n * w * t)`. -/
def QAdv.measureLift (t : ℕ) (A : QAdv m n w q) : QComp (m * n * w * t) Bool :=
  measProj (A.finalLift t) (QAdv.finalLift_conjTranspose t A) (QAdv.finalLift_mul_self t A)

/-- The run of `A` against an oracle `O` on the register `Fin (m * n * w * t)`,
    the adversary's unitaries and final projector acting as `· ⊗ₖ 1_t`:
    `U₀ ⊗ 1 ; O ; U₁ ⊗ 1 ; … ; O ; U_q ⊗ 1 ; measure (final ⊗ 1)`. -/
def runLift (t : ℕ) (O : Matrix.unitaryGroup (Fin (m * n * w * t)) ℂ) (A : QAdv m n w q) :
    QComp (m * n * w * t) Bool :=
  QComp.qbind (oracleChain (unitaryChannel O) q (fun i => tableLiftU t (A.U i))) fun _ =>
    A.measureLift t

/-- The `true` branch of `runLift` is conjugation by `(final ⊗ 1) * chainOp`. -/
theorem runLift_branch_true (t : ℕ) (O : Matrix.unitaryGroup (Fin (m * n * w * t)) ℂ)
    (A : QAdv m n w q) (ρ : Matrix (Fin (m * n * w * t)) (Fin (m * n * w * t)) ℂ) :
    (runLift t O A).branch true ρ =
      (A.finalLift t * chainOp (O : Matrix _ _ ℂ) q (fun i => tableLiftU t (A.U i))) * ρ *
        (A.finalLift t * chainOp (O : Matrix _ _ ℂ) q (fun i => tableLiftU t (A.U i)))ᴴ := by
  unfold runLift QAdv.measureLift
  rw [qbind_unit_branch, measProj_branch_true, oracleChain_unitaryChannel_branch,
    QAdv.finalLift_conjTranspose, conjTranspose_mul, QAdv.finalLift_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- Against a block-diagonal oracle, the trace of the `true` branch on `ρ ⊗ₖ σ`
    is the sum over the blocks `k` of `σ k k` times the trace for the oracle
    `V k` on `ρ`. -/
theorem trace_runLift_blockU {t : ℕ} (V : Fin t → Matrix.unitaryGroup (Fin (m * n * w)) ℂ)
    (A : QAdv m n w q) (ρ : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ)
    (σ : Matrix (Fin t) (Fin t) ℂ) :
    ((runLift t (blockU V) A).branch true (ρ ⊗ₖ σ)).trace =
      ∑ k, σ k k * ((A.final * chainOp (V k : Matrix _ _ ℂ) q A.U) * ρ *
        (A.final * chainOp (V k : Matrix _ _ ℂ) q A.U)ᴴ).trace := by
  rw [runLift_branch_true, chainOp_blockU, QAdv.finalLift, kronecker_one_eq_sum_single,
    sum_kronecker_single_mul, conjTranspose_sum_kronecker_single, Finset.sum_mul,
    Finset.sum_mul, trace_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, trace_sum, Finset.sum_eq_single k]
  · rw [kronecker_mul_kronecker, kronecker_mul_kronecker, TensorProduct.trace_kronecker,
      trace_single_mul_mul_single, if_pos rfl, mul_comm]
  · intro j _ hj
    rw [kronecker_mul_kronecker, kronecker_mul_kronecker, TensorProduct.trace_kronecker,
      trace_single_mul_mul_single, if_neg (Ne.symm hj), mul_zero]
  · simp

variable [NeZero n]

/-- The table-register oracle that applies the oracle for `f k` on the block `k`. -/
def tableOracleU {t : ℕ} (f : Fin t → Fin m → Fin n) :
    Matrix.unitaryGroup (Fin (m * n * w * t)) ℂ :=
  blockU fun k => oracleU m n w (f k)

/-- Against `tableOracleU f`, the trace of the `true` branch on `ρ ⊗ₖ σ` is the
    `σ`-diagonal weighted sum of the traces of the standard runs for `f k`. -/
theorem trace_runLift_tableOracleU {t : ℕ} (f : Fin t → Fin m → Fin n) (A : QAdv m n w q)
    (ρ : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) (σ : Matrix (Fin t) (Fin t) ℂ) :
    ((runLift t (tableOracleU (w := w) f) A).branch true (ρ ⊗ₖ σ)).trace =
      ∑ k, σ k k * ((run A (f k)).branch true ρ).trace := by
  rw [tableOracleU, trace_runLift_blockU]
  simp only [run_branch_true, runOp]

/-- Against `tableOracleU f` with the table register in a state `σ`, the
    acceptance probability is `∑ₖ σ k k · prOut A (f k)`. -/
theorem prTrue_runLift_tableOracleU {t : ℕ} (f : Fin t → Fin m → Fin n) (A : QAdv m n w q)
    (σ : DensityMatrix t) :
    prTrue_Q (runLift t (tableOracleU (w := w) f) A) (kronDM A.init σ) =
      ∑ k, ENNReal.ofReal (σ.val k k).re * prOut A (f k) := by
  have hσ : ∀ k, 0 ≤ σ.val k k := fun k => σ.psd.diag_nonneg
  have hnn : ∀ H : Fin m → Fin n, 0 ≤ ((run A H).branch true A.init.val).trace.re := fun H =>
    (Complex.nonneg_iff.mp ((run A H).branch_psd true _ A.init.psd).trace_nonneg).1
  unfold prOut prTrue_Q
  rw [kronDM_val, trace_runLift_tableOracleU, Complex.re_sum]
  have hre : ∀ k, (σ.val k k * ((run A (f k)).branch true A.init.val).trace).re =
      (σ.val k k).re * ((run A (f k)).branch true A.init.val).trace.re := by
    intro k
    rw [Complex.mul_re, ← (Complex.nonneg_iff.mp (hσ k)).2, zero_mul, sub_zero]
  simp only [hre]
  rw [ENNReal.ofReal_sum_of_nonneg fun k _ =>
    mul_nonneg (Complex.nonneg_iff.mp (hσ k)).1 (hnn (f k))]
  exact Finset.sum_congr rfl fun k _ => ENNReal.ofReal_mul (Complex.nonneg_iff.mp (hσ k)).1

end RunLift

/-! ## The purified standard oracle -/

section Purified

variable (m n : ℕ)

/-- The uniform superposition `(n ^ m)^{-1/2} ∑_G |G⟩` on the table register. -/
def tableUniformVec : Fin (n ^ m) → ℂ := fun _ => ((Real.sqrt ((n : ℝ) ^ m))⁻¹ : ℝ)

theorem tableUniformVec_mul_star (k : Fin (n ^ m)) :
    tableUniformVec m n k * star (tableUniformVec m n k) = ((((n : ℝ) ^ m)⁻¹ : ℝ) : ℂ) := by
  rw [tableUniformVec, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (by positivity)]

variable [NeZero n]

/-- The pure state of the uniform superposition on the table register. -/
def tablePure : DensityMatrix (n ^ m) where
  val := vecMulVec (tableUniformVec m n) (star (tableUniformVec m n))
  psd := posSemidef_vecMulVec_self_star _
  tr_one := by
    simp only [Matrix.trace, Matrix.diag, vecMulVec_apply, Pi.star_apply,
      tableUniformVec_mul_star, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    exact mul_inv_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne n)))

theorem tablePure_diag_re (k : Fin (n ^ m)) :
    ((tablePure m n).val k k).re = ((n : ℝ) ^ m)⁻¹ := by
  simp only [tablePure, vecMulVec_apply, Pi.star_apply, tableUniformVec_mul_star,
    Complex.ofReal_re]

variable {m n} {w q : ℕ}

/-- The register oracle of `OracleRegisterMixture` is the table oracle of the
    table index: `∑_G O_G ⊗ |G⟩⟨G|`. -/
theorem oracleRegU_eq_tableOracleU :
    oracleRegU m n w = tableOracleU (w := w) (tableIndex m n).symm := by
  apply Subtype.ext
  rw [tableOracleU, blockU_val]
  have hP : ∑ G : Fin m → Fin n, tableProj m n G = 1 := by
    rw [← sum_single_diag_one, ← (tableIndex m n).sum_comp]
    rfl
  calc (oracleRegU m n w : Matrix _ _ ℂ)
      = (oracleRegU m n w : Matrix _ _ ℂ) *
          ((1 : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) ⊗ₖ
            (1 : Matrix (Fin (n ^ m)) (Fin (n ^ m)) ℂ)) := by
        rw [kronecker_one_one, Matrix.mul_one]
    _ = ∑ G : Fin m → Fin n, (oracleRegU m n w : Matrix _ _ ℂ) *
          ((1 : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) ⊗ₖ tableProj m n G) := by
        rw [← Finset.mul_sum, kronecker_finset_sum_right, hP]
    _ = ∑ G : Fin m → Fin n, (oracleU m n w G : Matrix _ _ ℂ) ⊗ₖ tableProj m n G := by
        refine Finset.sum_congr rfl fun G _ => ?_
        rw [oracleRegU_mul_one_kronecker_tableProj, kronecker_mul_kronecker, Matrix.mul_one,
          Matrix.one_mul]
    _ = _ := by
        rw [← (tableIndex m n).sum_comp]
        simp only [Equiv.symm_apply_apply, tableProj]

/-- The register run of `OracleRegisterMixture` is `runLift` against the
    register oracle. -/
theorem runReg_eq_runLift (A : QAdv m n w q) :
    runReg A = runLift (n ^ m) (oracleRegU m n w) A := rfl

/-- The initial state of the purified run: `A.init` tensored with the uniform
    superposition on the table register. -/
def initPure (A : QAdv m n w q) : DensityMatrix (m * n * w * n ^ m) :=
  kronDM A.init (tablePure m n)

/-- The acceptance probability of the run against the purified standard oracle:
    the register oracle with the table register in the uniform superposition. -/
def prOutPure (A : QAdv m n w q) : ℝ≥0∞ :=
  prTrue_Q (runReg A) (initPure A)

/-- The purified standard oracle gives the average over `H` of the acceptance
    probability against the standard oracle for `H`. -/
theorem prOutPure_eq_avg_prOut (A : QAdv m n w q) :
    prOutPure A = ((n : ℝ≥0∞) ^ m)⁻¹ * ∑ H : Fin m → Fin n, prOut A H := by
  rw [prOutPure, runReg_eq_runLift, oracleRegU_eq_tableOracleU, initPure,
    prTrue_runLift_tableOracleU]
  simp only [tablePure_diag_re]
  rw [← Finset.mul_sum, (tableIndex m n).symm.sum_comp,
    ENNReal.ofReal_inv_of_pos (pow_pos (Nat.cast_pos.mpr (NeZero.pos n)) m),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]

/-- The purified standard oracle and the uniform mixture in the table register
    give the same acceptance probability. -/
theorem prOutPure_eq_prOutReg (A : QAdv m n w q) : prOutPure A = prOutReg A := by
  rw [prOutPure_eq_avg_prOut, prOutReg_eq_avg_prOut]

end Purified

/-! ## Conjugating the oracle by a unitary on the table register -/

section Conj

variable {d t : ℕ}

/-- The unitary `1_d ⊗ₖ D` acting on the second factor. -/
def oneKronU (d : ℕ) (D : Matrix.unitaryGroup (Fin t) ℂ) : Matrix.unitaryGroup (Fin (d * t)) ℂ :=
  ⟨(1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (D : Matrix (Fin t) (Fin t) ℂ),
    kronecker_mem_unitaryGroup (Matrix.mem_unitaryGroup_iff.mpr (by simp)) D.prop⟩

theorem oneKronU_val (d : ℕ) (D : Matrix.unitaryGroup (Fin t) ℂ) :
    (oneKronU d D : Matrix (Fin (d * t)) (Fin (d * t)) ℂ) =
      (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (D : Matrix (Fin t) (Fin t) ℂ) := rfl

/-- `D σ Dᴴ` as a density matrix. -/
def conjDM (D : Matrix.unitaryGroup (Fin t) ℂ) (σ : DensityMatrix t) : DensityMatrix t :=
  ⟨(D : Matrix (Fin t) (Fin t) ℂ) * σ.val * (D : Matrix (Fin t) (Fin t) ℂ)ᴴ,
    σ.psd.mul_mul_conjTranspose_same _, by
    rw [Matrix.trace_mul_cycle, ← star_eq_conjTranspose,
      Matrix.mem_unitaryGroup_iff'.mp D.prop, Matrix.one_mul, σ.tr_one]⟩

theorem conjDM_val (D : Matrix.unitaryGroup (Fin t) ℂ) (σ : DensityMatrix t) :
    (conjDM D σ).val =
      (D : Matrix (Fin t) (Fin t) ℂ) * σ.val * (D : Matrix (Fin t) (Fin t) ℂ)ᴴ := rfl

/-- Conjugating the oracle by a unitary `V` that commutes with every adversary
    unitary conjugates the whole chain by `V`. -/
theorem chainOp_conj (O V : Matrix (Fin d) (Fin d) ℂ) (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1)
    (q : ℕ) (W : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (hW : ∀ i, V * (W i : Matrix (Fin d) (Fin d) ℂ) = (W i : Matrix (Fin d) (Fin d) ℂ) * V) :
    chainOp (Vᴴ * O * V) q W = Vᴴ * chainOp O q W * V := by
  induction q with
  | zero =>
    simp only [chainOp]
    rw [Matrix.mul_assoc, ← hW 0, ← Matrix.mul_assoc, hV, Matrix.one_mul]
  | succ q ih =>
    simp only [chainOp]
    rw [ih (Fin.tail W) (fun i => hW i.succ)]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V Vᴴ, hV', Matrix.one_mul, hW 0]

theorem trace_conj_conj (M V X : Matrix (Fin d) (Fin d) ℂ) (hV' : V * Vᴴ = 1) :
    ((Vᴴ * M * V) * X * (Vᴴ * M * V)ᴴ).trace = (M * (V * X * Vᴴ) * Mᴴ).trace := by
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [hV', Matrix.mul_one]

variable {m n w q : ℕ}

/-- Running against `(1 ⊗ D)ᴴ O (1 ⊗ D)` from `ρ ⊗ σ` accepts with the same
    probability as running against `O` from `ρ ⊗ D σ Dᴴ`. -/
theorem prTrue_runLift_conj (O : Matrix.unitaryGroup (Fin (m * n * w * t)) ℂ)
    (D : Matrix.unitaryGroup (Fin t) ℂ) (A : QAdv m n w q) (ρ : DensityMatrix (m * n * w))
    (σ : DensityMatrix t) :
    prTrue_Q (runLift t (star (oneKronU (m * n * w) D) * O * oneKronU (m * n * w) D) A)
        (kronDM ρ σ) =
      prTrue_Q (runLift t O A) (kronDM ρ (conjDM D σ)) := by
  set V : Matrix (Fin (m * n * w * t)) (Fin (m * n * w * t)) ℂ :=
    ↑(oneKronU (m * n * w) D) with hVdef
  have hV : Vᴴ * V = 1 := by
    rw [← star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp (oneKronU _ D).prop
  have hV' : V * Vᴴ = 1 := by
    rw [← star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp (oneKronU _ D).prop
  have hW : ∀ i, V * (tableLiftU t (A.U i) : Matrix _ _ ℂ) =
      (tableLiftU t (A.U i) : Matrix _ _ ℂ) * V := by
    intro i
    rw [hVdef, oneKronU_val, tableLiftU_val, kronecker_mul_kronecker, kronecker_mul_kronecker,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  have hF : V * A.finalLift t = A.finalLift t * V := by
    rw [hVdef, oneKronU_val, QAdv.finalLift, kronecker_mul_kronecker, kronecker_mul_kronecker,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  have hcoe : ((star (oneKronU (m * n * w) D) * O * oneKronU (m * n * w) D :
      Matrix.unitaryGroup (Fin (m * n * w * t)) ℂ) : Matrix _ _ ℂ) = Vᴴ * (O : Matrix _ _ ℂ) * V := by
    rw [hVdef, ← star_eq_conjTranspose]; rfl
  have hX : V * (kronDM ρ σ).val * Vᴴ = (kronDM ρ (conjDM D σ)).val := by
    rw [kronDM_val, kronDM_val, conjDM_val, hVdef, oneKronU_val, conjTranspose_kronecker,
      conjTranspose_one, kronecker_mul_kronecker, kronecker_mul_kronecker, Matrix.one_mul,
      Matrix.mul_one]
  unfold prTrue_Q
  rw [runLift_branch_true, runLift_branch_true, hcoe, chainOp_conj _ V hV hV' q _ hW]
  have hM : A.finalLift t * (Vᴴ * chainOp (O : Matrix _ _ ℂ) q (fun i => tableLiftU t (A.U i)) * V) =
      Vᴴ * (A.finalLift t * chainOp (O : Matrix _ _ ℂ) q (fun i => tableLiftU t (A.U i))) * V := by
    have hF' : A.finalLift t * Vᴴ = Vᴴ * A.finalLift t := by
      have := congrArg (fun M => Vᴴ * M * Vᴴ) hF
      simp only [Matrix.mul_assoc] at this
      rw [hV', Matrix.mul_one, ← Matrix.mul_assoc, hV, Matrix.one_mul] at this
      exact this
    simp only [← Matrix.mul_assoc]
    rw [hF']
  rw [hM, trace_conj_conj _ _ _ hV', hX]

end Conj

/-! ## Decompression of one database entry -/

section Entry

variable (n : ℕ)

/-- The uniform superposition `n^{-1/2} ∑_{y < n} |y⟩` in the entry register
    `Fin (n + 1)`, whose last basis state `n` is the empty symbol `⊥`. -/
def entryUniform : Fin (n + 1) → ℂ := fun y => if (y : ℕ) < n then ((Real.sqrt n)⁻¹ : ℝ) else 0

/-- The vector `|⊥⟩ - ∑_{y < n} n^{-1/2} |y⟩`. -/
def entryDiff : Fin (n + 1) → ℂ := Pi.single (Fin.last n) 1 - entryUniform n

/-- Decompression of one entry: the reflection `1 - |u⟩⟨u|` for
    `u = |⊥⟩ - entryUniform n`. It exchanges `|⊥⟩` with the uniform
    superposition and fixes their orthogonal complement; it is its own inverse,
    so it is also the compression map. -/
def decompEntry : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  1 - vecMulVec (entryDiff n) (star (entryDiff n))

theorem entryUniform_mul_star (y : Fin (n + 1)) :
    entryUniform n y * star (entryUniform n y) =
      (((if (y : ℕ) < n then (n : ℝ)⁻¹ else 0 : ℝ)) : ℂ) := by
  unfold entryUniform
  split_ifs
  · rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (Nat.cast_nonneg n)]
  · simp

theorem star_entryDiff_dotProduct [NeZero n] : star (entryDiff n) ⬝ᵥ entryDiff n = 2 := by
  simp only [dotProduct, Fin.sum_univ_castSucc, entryDiff, Pi.sub_apply, Pi.star_apply,
    Pi.single_apply, Fin.castSucc_ne_last, if_false, if_true, entryUniform, Fin.val_castSucc,
    Fin.is_lt, Fin.val_last, lt_irrefl]
  rw [zero_sub, sub_zero, star_neg, neg_mul_neg, star_one, one_mul, Complex.star_def,
    Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg n),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne n))]
  norm_num

theorem decompEntry_conjTranspose : (decompEntry n)ᴴ = decompEntry n := by
  rw [decompEntry, conjTranspose_sub, conjTranspose_one, conjTranspose_vecMulVec, star_star]

theorem decompEntry_mul_self [NeZero n] : decompEntry n * decompEntry n = 1 := by
  rw [decompEntry, sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    vecMulVec_mul_vecMulVec, star_entryDiff_dotProduct, vecMulVec_smul, two_smul]
  abel

theorem decompEntry_mem_unitaryGroup [NeZero n] :
    decompEntry n ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, decompEntry_conjTranspose,
    decompEntry_mul_self]

/-- Decompression sends `|⊥⟩` to the uniform superposition. -/
theorem decompEntry_apply_last (y : Fin (n + 1)) :
    decompEntry n y (Fin.last n) = entryUniform n y := by
  simp [decompEntry, entryDiff, entryUniform, vecMulVec_apply, Matrix.one_apply, Pi.single_apply]

end Entry

/-! ## The database register and the compressed oracle -/

section Database

variable (m n : ℕ)

/-- The index of the database register: a database `D : Fin m → Fin (n + 1)`
    holds at each input either a value `y < n` or the empty symbol `⊥ = n`. -/
def dbIndex : (Fin m → Fin (n + 1)) ≃ Fin ((n + 1) ^ m) := finFunctionFinEquiv

/-- Decompression of the whole database: `decompEntry` on every entry,
    `⟨D|Dec|D'⟩ = ∏ₓ ⟨D x|decompEntry|D' x⟩`. -/
def decompDB : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ :=
  Matrix.of fun i j => ∏ x, decompEntry n ((dbIndex m n).symm i x) ((dbIndex m n).symm j x)

theorem decompDB_mul_conjTranspose [NeZero n] : decompDB m n * (decompDB m n)ᴴ = 1 := by
  have hD : ∀ a b : Fin (n + 1),
      ∑ y, decompEntry n a y * star (decompEntry n b y) = if a = b then 1 else 0 := by
    intro a b
    have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp
      (decompEntry_mem_unitaryGroup n)) a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  ext i j
  rw [Matrix.mul_apply, ← (dbIndex m n).sum_comp]
  simp only [decompDB, Matrix.conjTranspose_apply, Matrix.of_apply, Equiv.symm_apply_apply,
    star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun x y =>
    decompEntry n ((dbIndex m n).symm i x) y * star (decompEntry n ((dbIndex m n).symm j x) y))]
  simp only [hD, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]
    have : ∃ x, (dbIndex m n).symm i x ≠ (dbIndex m n).symm j x := by
      by_contra hc
      exact h ((dbIndex m n).symm.injective
        (funext fun x => not_not.mp fun hx => hc ⟨x, hx⟩))
    obtain ⟨x, hx⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ x) (if_neg hx)

/-- Decompression of the database as a unitary. -/
def decompDBU [NeZero n] : Matrix.unitaryGroup (Fin ((n + 1) ^ m)) ℂ :=
  ⟨decompDB m n, Matrix.mem_unitaryGroup_iff.mpr (by
    rw [star_eq_conjTranspose]; exact decompDB_mul_conjTranspose m n)⟩

/-- The index of the empty database, every entry holding `⊥`. -/
def dbEmptyIdx : Fin ((n + 1) ^ m) := dbIndex m n fun _ => Fin.last n

/-- Decompressing the empty database gives the uniform superposition over the
    databases with no `⊥` entry. -/
theorem decompDB_apply_empty (i : Fin ((n + 1) ^ m)) :
    decompDB m n i (dbEmptyIdx m n) = ∏ x, entryUniform n ((dbIndex m n).symm i x) := by
  simp only [decompDB, dbEmptyIdx, Matrix.of_apply, Equiv.symm_apply_apply,
    decompEntry_apply_last]

/-- The pure state of the empty database. -/
def dbEmpty : DensityMatrix ((n + 1) ^ m) where
  val := vecMulVec (Pi.single (dbEmptyIdx m n) 1) (star (Pi.single (dbEmptyIdx m n) 1))
  psd := posSemidef_vecMulVec_self_star _
  tr_one := by
    rw [trace_vecMulVec]
    simp [dotProduct, Pi.single_apply]

variable [NeZero n]

/-- An entry read as a value: `y < n` is itself, `⊥` is read as `0`. -/
def truncEntry (y : Fin (n + 1)) : Fin n := if h : (y : ℕ) < n then ⟨y, h⟩ else 0

theorem truncEntry_castSucc (y : Fin n) : truncEntry n y.castSucc = y := by
  simp [truncEntry]

/-- The function a database index holds, with `⊥` entries read as `0`. -/
def dbFun (k : Fin ((n + 1) ^ m)) : Fin m → Fin n := fun x => truncEntry n ((dbIndex m n).symm k x)

variable (w : ℕ)

/-- The standard oracle on the database register:
    `|x, y, z, D⟩ ↦ |x, y + D x, z, D⟩`, with `⊥` entries read as `0`. -/
def stdDbU : Matrix.unitaryGroup (Fin (m * n * w * (n + 1) ^ m)) ℂ :=
  tableOracleU (w := w) (dbFun m n)

/-- Decompression of the database register on the total register. -/
def decompU : Matrix.unitaryGroup (Fin (m * n * w * (n + 1) ^ m)) ℂ :=
  oneKronU (m * n * w) (decompDBU m n)

/-- The compressed oracle: decompress the database, apply the standard oracle,
    compress the database. -/
def cmpOracleU : Matrix.unitaryGroup (Fin (m * n * w * (n + 1) ^ m)) ℂ :=
  star (decompU m n w) * stdDbU m n w * decompU m n w

variable {m n w} {q : ℕ}

/-- The initial state of the compressed run: `A.init` tensored with the empty
    database. -/
def initCmp (A : QAdv m n w q) : DensityMatrix (m * n * w * (n + 1) ^ m) :=
  kronDM A.init (dbEmpty m n)

/-- The run of `A` against the compressed oracle. -/
def runCmp (A : QAdv m n w q) : QComp (m * n * w * (n + 1) ^ m) Bool :=
  runLift ((n + 1) ^ m) (cmpOracleU m n w) A

/-- The acceptance probability of `A` against the compressed oracle, from the
    empty database. -/
def prOutCmp (A : QAdv m n w q) : ℝ≥0∞ :=
  prTrue_Q (runCmp A) (initCmp A)

theorem conjDM_dbEmpty_diag_re (k : Fin ((n + 1) ^ m)) :
    ((conjDM (decompDBU m n) (dbEmpty m n)).val k k).re =
      ∏ x, (if (((dbIndex m n).symm k x : Fin (n + 1)) : ℕ) < n then (n : ℝ)⁻¹ else 0) := by
  rw [conjDM_val]
  simp only [dbEmpty, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, vecMulVec_apply,
    Matrix.mulVec_single_one]
  have hrow : ∀ M : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ,
      (star (Pi.single (dbEmptyIdx m n) (1 : ℂ)) ᵥ* Mᴴ) k = star (M k (dbEmptyIdx m n)) :=
    fun M => by simp [vecMul, dotProduct, Pi.single_apply, conjTranspose_apply]
  simp only [hrow, Matrix.col_apply]
  change (decompDB m n k (dbEmptyIdx m n) * star (decompDB m n k (dbEmptyIdx m n))).re = _
  rw [decompDB_apply_empty, star_prod, ← Finset.prod_mul_distrib]
  simp only [entryUniform_mul_star]
  rw [← Complex.ofReal_prod, Complex.ofReal_re]

/-- The compressed oracle from the empty database gives the average over `H`
    of the acceptance probability against the standard oracle for `H`. -/
theorem prOutCmp_eq_avg_prOut (A : QAdv m n w q) :
    prOutCmp A = ((n : ℝ≥0∞) ^ m)⁻¹ * ∑ H : Fin m → Fin n, prOut A H := by
  rw [prOutCmp, runCmp, cmpOracleU, decompU, initCmp, prTrue_runLift_conj, stdDbU,
    prTrue_runLift_tableOracleU]
  simp only [conjDM_dbEmpty_diag_re]
  rw [← (dbIndex m n).sum_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.mul_sum]
  symm
  refine Fintype.sum_of_injective (fun H x => (H x).castSucc)
    (fun H H' h => funext fun x => Fin.castSucc_injective n (congrFun h x)) _ _ ?_ ?_
  · intro D hD
    have : ∃ x, ¬ (((D x : Fin (n + 1)) : ℕ) < n) := by
      by_contra hc
      exact hD ⟨fun x => ⟨D x, not_not.mp fun hx => hc ⟨x, hx⟩⟩, funext fun x => Fin.ext rfl⟩
    obtain ⟨x, hx⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ x) (if_neg hx), ENNReal.ofReal_zero, zero_mul]
  · intro H
    simp only [Fin.val_castSucc, Fin.is_lt, if_true, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [show dbFun m n (dbIndex m n fun x => (H x).castSucc) = H from
      funext fun x => by simp [dbFun, truncEntry_castSucc]]
    rw [ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr (NeZero.pos n)), ENNReal.ofReal_natCast,
      ENNReal.inv_pow]

/-- The compressed oracle from the empty database and the purified standard
    oracle give the same acceptance probability, for every adversary. -/
theorem prOut_compressed_eq (A : QAdv m n w q) : prOutCmp A = prOutPure A := by
  rw [prOutCmp_eq_avg_prOut, prOutPure_eq_avg_prOut]

/-- The compressed oracle from the empty database and the uniform mixture in the
    table register give the same acceptance probability. -/
theorem prOutCmp_eq_prOutReg (A : QAdv m n w q) : prOutCmp A = prOutReg A := by
  rw [prOut_compressed_eq, prOutPure_eq_prOutReg]

end Database

end CatCrypt.Quantum.QROM
