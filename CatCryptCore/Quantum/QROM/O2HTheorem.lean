/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.SemiClassicalOracle
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The semi-classical one-way-to-hiding theorem

The one-way-to-hiding inequality of Ambainis–Hamburg–Unruh (CRYPTO 2019,
Theorem 1) for the `q`-query adversary `QAdv` of `SemiClassicalOracle`, with a
pure initial state. The standard run and the `Find = false` branch of the
semi-classical run are rank one, with vectors given by operator products
(`runOp`, `scOp`); the difference of the two vectors telescopes over the
queries into a sum of projected intermediate states, whose squared norms sum to
`Pr[Find]`; Cauchy–Schwarz over the `q` queries and the norm-square inequality
`|‖a‖² − ‖b‖²| ≤ 2‖a − b‖` give the bound.

## Main definitions

* `nrm v` — the Euclidean norm of `v : Fin d → ℂ`, through `EuclideanSpace`
* `chainOp O q U` — the operator `U_q O U_{q-1} ⋯ O U_0` of `oracleChain`
* `scStates O' Π q U ψ` — the states before each query of the chain with the
  projected oracle `O'`, from the initial vector `ψ`
* `runOp A H`, `scOp A H S`, `scState A H S ψ` — the same for an adversary,
  with the standard oracle and with `U_H (1 − Π_S)`
* `prOutNoFind A H S` — the probability that the semi-classical run outputs `1`
  and `Find` does not occur

## Main results

* `run_branch_true_pure`, `prOut_eq_nrm_sq` — the standard run on a pure
  state, as a rank-one state and as a squared norm
* `scChain_branch_false_eq`, `prOutNoFind_eq_nrm_sq` — the `Find = false`
  branch of the semi-classical run, as a rank-one state and as a squared norm
* `scChain_trace_add`, `prFind_eq_sum` — the semi-classical chain is trace
  preserving, and `Pr[Find]` is the sum of the squared norms of the projected
  intermediate states
* `nrm_chainOp_sub_le`, `sum_le_sqrt_card_mul_sum_sq` — the telescoping bound
  and Cauchy–Schwarz
* `o2h_semiclassical` — `|Pr[out = 1 : H] − Pr[out = 1 ∧ ¬Find : H \ S]| ≤ 2 √(q · Pr[Find])`
* `o2h` — `|Pr[out = 1 : H] − Pr[out = 1 : H']| ≤ 4 √(q · Pr[Find])` for `H`,
  `H'` agreeing outside `S`
* `o2h_extraction_of_QAdv` — the squared form `≤ (4q)² · Pr[Find]`, comparable
  to `Quantum.O2H.O2HExtraction`

## The adversary class and the constants

The adversary has a pure initial state (`A.init = ψψ†`), applies the oracle `q`
times between `q + 1` unitaries, and ends with one projective measurement. The
bounds are `2√(q · P_find)` against the `Find = false` branch and
`4√(q · P_find)` between two functions. Since `q` counts oracle applications,
these are at least as tight as the `d + 1` form of Ambainis–Hamburg–Unruh.

## References

* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], Theorem 1
* [Heidler, Unruh — Formalizing the O2H Lemma, CPP 2025]
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal InnerProductSpace
open Matrix Classical CatCrypt.Quantum CatCrypt.Quantum.UnitaryChannel
  CatCrypt.Quantum.Measurement

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The Euclidean norm on `Fin d → ℂ` -/

section Norm

variable {d : ℕ}

/-- The Euclidean norm of a vector, through `EuclideanSpace ℂ (Fin d)`. -/
def nrm (v : Fin d → ℂ) : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin d))‖

theorem nrm_nonneg (v : Fin d → ℂ) : 0 ≤ nrm v := norm_nonneg _

@[simp]
theorem nrm_zero : nrm (0 : Fin d → ℂ) = 0 := by
  simp [nrm]

/-- The self pairing `v ⬝ᵥ star v` is the squared norm. -/
theorem dotProduct_star_self (v : Fin d → ℂ) :
    v ⬝ᵥ star v = ((nrm v ^ 2 : ℝ) : ℂ) := by
  rw [← EuclideanSpace.inner_toLp_toLp, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

theorem nrm_eq_of_dotProduct_eq {v w : Fin d → ℂ} (h : v ⬝ᵥ star v = w ⬝ᵥ star w) :
    nrm v = nrm w := by
  rw [dotProduct_star_self, dotProduct_star_self] at h
  exact (sq_eq_sq₀ (nrm_nonneg v) (nrm_nonneg w)).mp (by exact_mod_cast h)

theorem abs_nrm_sub_nrm_le (a b : Fin d → ℂ) : |nrm a - nrm b| ≤ nrm (a - b) := by
  unfold nrm
  rw [WithLp.toLp_sub]
  exact abs_norm_sub_norm_le _ _

theorem nrm_add_le (a b : Fin d → ℂ) : nrm (a + b) ≤ nrm a + nrm b := by
  unfold nrm
  rw [WithLp.toLp_add]
  exact norm_add_le _ _

/-- `|‖a‖² − ‖b‖²| ≤ ‖a − b‖ (‖a‖ + ‖b‖)`. -/
theorem abs_nrm_sq_sub_nrm_sq_le (a b : Fin d → ℂ) :
    |nrm a ^ 2 - nrm b ^ 2| ≤ nrm (a - b) * (nrm a + nrm b) := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (nrm_nonneg a) (nrm_nonneg b)), mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_nrm_sub_nrm_le a b)
    (add_nonneg (nrm_nonneg a) (nrm_nonneg b))

/-- The pairing of two images under matrices, pulled back to the argument. -/
theorem mulVec_dotProduct_star_mulVec (A B : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
    (A *ᵥ v) ⬝ᵥ star (B *ᵥ v) = ((Bᴴ * A) *ᵥ v) ⬝ᵥ star v := by
  rw [star_mulVec, dotProduct_comm, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec,
    dotProduct_comm]

/-- A unitary preserves the norm. -/
theorem nrm_mulVec_of_mem_unitaryGroup {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (v : Fin d → ℂ) : nrm (U *ᵥ v) = nrm v := by
  apply nrm_eq_of_dotProduct_eq
  rw [mulVec_dotProduct_star_mulVec, ← star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff'.mp hU, one_mulVec]

/-- Pythagoras for an orthogonal projector: `‖Pv‖² + ‖(1 − P)v‖² = ‖v‖²`. -/
theorem nrm_sq_proj_add_nrm_sq_one_sub_proj {P : Matrix (Fin d) (Fin d) ℂ}
    (hI : P * P = P) (hH : Pᴴ = P) (v : Fin d → ℂ) :
    nrm (P *ᵥ v) ^ 2 + nrm ((1 - P) *ᵥ v) ^ 2 = nrm v ^ 2 := by
  have h1 : (P *ᵥ v) ⬝ᵥ star (P *ᵥ v) = (P *ᵥ v) ⬝ᵥ star v := by
    rw [mulVec_dotProduct_star_mulVec, hH, hI]
  have h2 : ((1 - P) *ᵥ v) ⬝ᵥ star ((1 - P) *ᵥ v) = ((1 - P) *ᵥ v) ⬝ᵥ star v := by
    rw [mulVec_dotProduct_star_mulVec, conjTranspose_sub, conjTranspose_one, hH]
    congr 2
    simp only [sub_mul, mul_sub, one_mul, mul_one, hI]
    abel
  have h3 : (P *ᵥ v) ⬝ᵥ star v + ((1 - P) *ᵥ v) ⬝ᵥ star v = v ⬝ᵥ star v := by
    rw [← add_dotProduct, ← add_mulVec, add_sub_cancel, one_mulVec]
  have := h3
  rw [← h1, ← h2, dotProduct_star_self, dotProduct_star_self, dotProduct_star_self] at this
  exact_mod_cast this

/-- An orthogonal projector is a contraction. -/
theorem nrm_proj_mulVec_le {P : Matrix (Fin d) (Fin d) ℂ}
    (hI : P * P = P) (hH : Pᴴ = P) (v : Fin d → ℂ) : nrm (P *ᵥ v) ≤ nrm v := by
  have h := nrm_sq_proj_add_nrm_sq_one_sub_proj hI hH v
  rw [← pow_le_pow_iff_left₀ (nrm_nonneg _) (nrm_nonneg _) two_ne_zero]
  nlinarith [sq_nonneg (nrm ((1 - P) *ᵥ v))]

/-- Cauchy–Schwarz for a finite sum of non-negative reals:
    `∑ f ≤ √(card · ∑ f²)`. -/
theorem sum_le_sqrt_card_mul_sum_sq {ι : Type} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    ∑ i, f i ≤ Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, f i ^ 2) := by
  rw [Real.le_sqrt (Finset.sum_nonneg fun i _ => hf i)
    (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _))]
  have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := f)
  simpa [Finset.card_univ] using this

/-- Conjugating a rank-one state by `X` is the rank-one state of `X ψ`. -/
theorem mul_vecMulVec_star_mul_conjTranspose (X : Matrix (Fin d) (Fin d) ℂ) (ψ : Fin d → ℂ) :
    X * vecMulVec ψ (star ψ) * Xᴴ = vecMulVec (X *ᵥ ψ) (star (X *ᵥ ψ)) := by
  rw [mul_vecMulVec, vecMulVec_mul, star_mulVec]

/-- The trace of a conjugated rank-one state is the squared norm of `X ψ`. -/
theorem trace_mul_vecMulVec_star_mul_conjTranspose (X : Matrix (Fin d) (Fin d) ℂ)
    (ψ : Fin d → ℂ) :
    (X * vecMulVec ψ (star ψ) * Xᴴ).trace = ((nrm (X *ᵥ ψ) ^ 2 : ℝ) : ℂ) := by
  rw [mul_vecMulVec_star_mul_conjTranspose, trace_vecMulVec, dotProduct_star_self]

/-- Conjugation by a unitary preserves the trace. -/
theorem trace_mul_mul_conjTranspose_of_mem_unitaryGroup {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    (U * X * Uᴴ).trace = X.trace := by
  rw [trace_mul_cycle, ← star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hU, one_mul]

/-- `tr (P ρ P) = tr (P ρ)` for an idempotent `P`. -/
theorem trace_proj_mul_mul_proj {P : Matrix (Fin d) (Fin d) ℂ} (hI : P * P = P)
    (ρ : Matrix (Fin d) (Fin d) ℂ) : (P * ρ * P).trace = (P * ρ).trace := by
  rw [trace_mul_cycle, hI]

end Norm

/-! ## Branch identities for `qbind` -/

section Branch

variable {d : ℕ} {α β : Type}

/-- The branch of a bind is the sum over the intermediate outcomes. -/
theorem qbind_branch_apply (I : QComp d α) (f : α → QComp d β) (b : β)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (QComp.qbind I f).branch b ρ = ∑' a, (f a).branch b (I.branch a ρ) := rfl

/-- Post-composing with `qpure` leaves each branch unchanged. -/
theorem qbind_qpure_branch (I : QComp d α) (b : α) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (QComp.qbind I fun a => QComp.qpure a).branch b ρ = I.branch b ρ := by
  rw [show (fun a => (QComp.qpure a : QComp d α)) = QComp.qpure from rfl, QComp.qbind_qpure]

end Branch

/-! ## The operator products of the chains -/

section Chain

variable {d : ℕ}

/-- The operator `U_q O U_{q-1} ⋯ O U_0` of `oracleChain`, for a matrix `O` in
    place of the oracle. -/
def chainOp (O : Matrix (Fin d) (Fin d) ℂ) :
    (q : ℕ) → (Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) → Matrix (Fin d) (Fin d) ℂ
  | 0, U => U 0
  | q + 1, U => chainOp O q (Fin.tail U) * O * U 0

theorem chainOp_succ_mulVec (O : Matrix (Fin d) (Fin d) ℂ) (q : ℕ)
    (U : Fin (q + 2) → Matrix.unitaryGroup (Fin d) ℂ) (ψ : Fin d → ℂ) :
    chainOp O (q + 1) U *ᵥ ψ = chainOp O q (Fin.tail U) *ᵥ (O *ᵥ ((U 0 : Matrix _ _ ℂ) *ᵥ ψ)) := by
  simp only [chainOp, mulVec_mulVec, Matrix.mul_assoc]

/-- The `Unit` chain of a unitary channel is conjugation by `chainOp`. -/
theorem oracleChain_unitaryChannel_branch (O : Matrix.unitaryGroup (Fin d) ℂ) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (oracleChain (unitaryChannel O) q U).branch () ρ =
      chainOp (O : Matrix _ _ ℂ) q U * ρ * (chainOp (O : Matrix _ _ ℂ) q U)ᴴ := by
  induction q generalizing ρ with
  | zero => simp only [oracleChain, chainOp, unitaryChannel_branch_apply]
  | succ q ih =>
    simp only [oracleChain, qbind_unit_branch, unitaryChannel_branch_apply, ih, chainOp,
      conjTranspose_mul, Matrix.mul_assoc]

/-- A chain of contractions is a contraction. -/
theorem nrm_chainOp_mulVec_le (O : Matrix (Fin d) (Fin d) ℂ)
    (hO : ∀ v, nrm (O *ᵥ v) ≤ nrm v) (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (ψ : Fin d → ℂ) : nrm (chainOp O q U *ᵥ ψ) ≤ nrm ψ := by
  induction q generalizing ψ with
  | zero => exact (nrm_mulVec_of_mem_unitaryGroup (U 0).prop ψ).le
  | succ q ih =>
    rw [chainOp_succ_mulVec]
    refine (ih (Fin.tail U) _).trans ((hO _).trans ?_)
    exact (nrm_mulVec_of_mem_unitaryGroup (U 0).prop ψ).le

/-- A chain of unitaries preserves the norm. -/
theorem nrm_chainOp_mulVec_eq (O : Matrix (Fin d) (Fin d) ℂ)
    (hO : ∀ v, nrm (O *ᵥ v) = nrm v) (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (ψ : Fin d → ℂ) : nrm (chainOp O q U *ᵥ ψ) = nrm ψ := by
  induction q generalizing ψ with
  | zero => exact nrm_mulVec_of_mem_unitaryGroup (U 0).prop ψ
  | succ q ih =>
    rw [chainOp_succ_mulVec, ih, hO, nrm_mulVec_of_mem_unitaryGroup (U 0).prop]

/-- The states before each query of the chain with the projected oracle `O'`:
    `θ₀ = U₀ ψ` and `θ_{i+1}` is the state of the tail chain from `O' θ₀`. -/
def scStates (O' : Matrix (Fin d) (Fin d) ℂ) :
    (q : ℕ) → (Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) → (Fin d → ℂ) → Fin q → (Fin d → ℂ)
  | 0, _, _ => fun i => i.elim0
  | q + 1, U, ψ =>
    Fin.cons ((U 0 : Matrix _ _ ℂ) *ᵥ ψ)
      (scStates O' q (Fin.tail U) (O' *ᵥ ((U 0 : Matrix _ _ ℂ) *ᵥ ψ)))

/-- Norm bookkeeping of the projected chain: the squared norm of the final
    state plus the squared norms of the projected intermediate states is the
    squared norm of the initial state. -/
theorem nrm_sq_chainOp_add_sum_nrm_sq_scStates {O P : Matrix (Fin d) (Fin d) ℂ}
    (hO : O ∈ Matrix.unitaryGroup (Fin d) ℂ) (hI : P * P = P) (hH : Pᴴ = P) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (ψ : Fin d → ℂ) :
    nrm (chainOp (O * (1 - P)) q U *ᵥ ψ) ^ 2 +
      ∑ i, nrm (P *ᵥ scStates (O * (1 - P)) q U ψ i) ^ 2 = nrm ψ ^ 2 := by
  induction q generalizing ψ with
  | zero =>
    simp only [chainOp, scStates, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
      nrm_mulVec_of_mem_unitaryGroup (U 0).prop]
  | succ q ih =>
    rw [chainOp_succ_mulVec, Fin.sum_univ_succ]
    simp only [scStates, Fin.cons_zero, Fin.cons_succ]
    have h := ih (Fin.tail U) ((O * (1 - P)) *ᵥ ((U 0 : Matrix _ _ ℂ) *ᵥ ψ))
    have h2 : nrm ((O * (1 - P)) *ᵥ ((U 0 : Matrix _ _ ℂ) *ᵥ ψ)) =
        nrm ((1 - P) *ᵥ ((U 0 : Matrix _ _ ℂ) *ᵥ ψ)) := by
      rw [← mulVec_mulVec, nrm_mulVec_of_mem_unitaryGroup hO]
    have h3 := nrm_sq_proj_add_nrm_sq_one_sub_proj hI hH ((U 0 : Matrix _ _ ℂ) *ᵥ ψ)
    rw [nrm_mulVec_of_mem_unitaryGroup (U 0).prop ψ] at h3
    rw [h2] at h
    linarith

/-- The telescoping bound: the difference between the standard and the
    projected chain on `ψ` is at most the sum of the norms of the projected
    intermediate states. -/
theorem nrm_chainOp_sub_le {O : Matrix (Fin d) (Fin d) ℂ} (P : Matrix (Fin d) (Fin d) ℂ)
    (hO : O ∈ Matrix.unitaryGroup (Fin d) ℂ) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (ψ : Fin d → ℂ) :
    nrm (chainOp O q U *ᵥ ψ - chainOp (O * (1 - P)) q U *ᵥ ψ) ≤
      ∑ i, nrm (P *ᵥ scStates (O * (1 - P)) q U ψ i) := by
  induction q generalizing ψ with
  | zero => simp [chainOp]
  | succ q ih =>
    rw [chainOp_succ_mulVec, chainOp_succ_mulVec, Fin.sum_univ_succ]
    simp only [scStates, Fin.cons_zero, Fin.cons_succ]
    set x := O *ᵥ ((U 0 : Matrix _ _ ℂ) *ᵥ ψ)
    set y := (O * (1 - P)) *ᵥ ((U 0 : Matrix _ _ ℂ) *ᵥ ψ)
    have hxy : x - y = O *ᵥ (P *ᵥ ((U 0 : Matrix _ _ ℂ) *ᵥ ψ)) := by
      simp only [x, y, ← mulVec_mulVec, sub_mulVec, one_mulVec, mulVec_sub, sub_sub_cancel]
    have hsplit : chainOp O q (Fin.tail U) *ᵥ x - chainOp (O * (1 - P)) q (Fin.tail U) *ᵥ y =
        chainOp O q (Fin.tail U) *ᵥ (x - y) +
          (chainOp O q (Fin.tail U) *ᵥ y - chainOp (O * (1 - P)) q (Fin.tail U) *ᵥ y) := by
      rw [mulVec_sub]; abel
    rw [hsplit]
    refine (nrm_add_le _ _).trans (add_le_add ?_ (ih (Fin.tail U) y))
    rw [hxy, nrm_chainOp_mulVec_eq O (nrm_mulVec_of_mem_unitaryGroup hO),
      nrm_mulVec_of_mem_unitaryGroup hO]

end Chain

/-! ## Trace preservation of the semi-classical chain -/

section TracePreserving

variable {d : ℕ}

theorem scChain_succ_branch_true (O : QComp d Bool) (q : ℕ)
    (U : Fin (q + 2) → Matrix.unitaryGroup (Fin d) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (scChain O (q + 1) U).branch true ρ =
      (scChain O q (Fin.tail U)).branch true
          (O.branch true ((U 0 : Matrix _ _ ℂ) * ρ * (U 0 : Matrix _ _ ℂ)ᴴ)) +
        (scChain O q (Fin.tail U)).branch false
          (O.branch true ((U 0 : Matrix _ _ ℂ) * ρ * (U 0 : Matrix _ _ ℂ)ᴴ)) +
        (scChain O q (Fin.tail U)).branch true
          (O.branch false ((U 0 : Matrix _ _ ℂ) * ρ * (U 0 : Matrix _ _ ℂ)ᴴ)) := by
  simp only [scChain]
  rw [qbind_unit_branch, qbind_bool_branch, unitaryChannel_branch_apply]
  simp only [qbind_branch_apply, tsum_fintype, Fintype.sum_bool, qpure_branch_apply]
  simp
  abel

theorem scChain_succ_branch_false (O : QComp d Bool) (q : ℕ)
    (U : Fin (q + 2) → Matrix.unitaryGroup (Fin d) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (scChain O (q + 1) U).branch false ρ =
      (scChain O q (Fin.tail U)).branch false
        (O.branch false ((U 0 : Matrix _ _ ℂ) * ρ * (U 0 : Matrix _ _ ℂ)ᴴ)) := by
  simp only [scChain]
  rw [qbind_unit_branch, qbind_bool_branch, unitaryChannel_branch_apply]
  simp only [qbind_branch_apply, tsum_fintype, Fintype.sum_bool, qpure_branch_apply]
  simp

/-- The semi-classical chain of a trace-preserving `Bool` oracle is trace
    preserving. -/
theorem scChain_trace_add (O : QComp d Bool)
    (hO : ∀ σ, (O.branch true σ).trace + (O.branch false σ).trace = σ.trace) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    ((scChain O q U).branch true ρ).trace + ((scChain O q U).branch false ρ).trace = ρ.trace := by
  induction q generalizing ρ with
  | zero =>
    simp only [scChain, qbind_unit_branch, qpure_branch_apply, unitaryChannel_branch_apply]
    simp [trace_mul_mul_conjTranspose_of_mem_unitaryGroup (U 0).prop]
  | succ q ih =>
    rw [scChain_succ_branch_true, scChain_succ_branch_false, trace_add, trace_add]
    have hf := ih (Fin.tail U) (O.branch false ((U 0 : Matrix _ _ ℂ) * ρ * (U 0 : Matrix _ _ ℂ)ᴴ))
    have ht := ih (Fin.tail U) (O.branch true ((U 0 : Matrix _ _ ℂ) * ρ * (U 0 : Matrix _ _ ℂ)ᴴ))
    have hU := trace_mul_mul_conjTranspose_of_mem_unitaryGroup (U 0).prop ρ
    have h := hO ((U 0 : Matrix _ _ ℂ) * ρ * (U 0 : Matrix _ _ ℂ)ᴴ)
    linear_combination hf + ht + h + hU

end TracePreserving

/-! ## The adversary's runs on a pure state -/

section Adv

variable {m n w q : ℕ} [NeZero n]

/-- The operator `U_q O_H U_{q-1} ⋯ O_H U_0` of the standard run. -/
def runOp (A : QAdv m n w q) (H : Fin m → Fin n) : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ :=
  chainOp (oracleU m n w H : Matrix _ _ ℂ) q A.U

/-- The operator `U_q O_H (1 − Π_S) U_{q-1} ⋯ O_H (1 − Π_S) U_0` of the
    `Find = false` branch of the semi-classical run. -/
def scOp (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m)) :
    Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ :=
  chainOp ((oracleU m n w H : Matrix _ _ ℂ) * (1 - projS m n w S)) q A.U

/-- The state before the `i`-th query of the `Find = false` branch, from the
    initial vector `ψ`. -/
def scState (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m))
    (ψ : Fin (m * n * w) → ℂ) : Fin q → (Fin (m * n * w) → ℂ) :=
  scStates ((oracleU m n w H : Matrix _ _ ℂ) * (1 - projS m n w S)) q A.U ψ

/-- The probability that the semi-classical run outputs `1` and `Find` does
    not occur. -/
def prOutNoFind (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m)) : ℝ≥0∞ :=
  prTrue_Q (QComp.qbind (runSC A H S) fun p => QComp.qpure (p.1 && !p.2)) A.init

/-- The `true` branch of the standard run is conjugation by `final * runOp`. -/
theorem run_branch_true (A : QAdv m n w q) (H : Fin m → Fin n)
    (ρ : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (run A H).branch true ρ = (A.final * runOp A H) * ρ * (A.final * runOp A H)ᴴ := by
  unfold run QAdv.measure oracleQ runOp
  rw [qbind_unit_branch, measProj_branch_true, oracleChain_unitaryChannel_branch,
    A.final_conjTranspose, conjTranspose_mul, A.final_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- The `false` branch of the semi-classical chain is conjugation by the
    projected chain operator. -/
theorem scChain_branch_false_eq (H : Fin m → Fin n) (S : Finset (Fin m)) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin (m * n * w)) ℂ)
    (ρ : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (scChain (scOracleQ m n w H S) q U).branch false ρ =
      chainOp ((oracleU m n w H : Matrix _ _ ℂ) * (1 - projS m n w S)) q U * ρ *
        (chainOp ((oracleU m n w H : Matrix _ _ ℂ) * (1 - projS m n w S)) q U)ᴴ := by
  induction q generalizing ρ with
  | zero =>
    simp only [scChain, qbind_unit_branch, qpure_branch_apply, unitaryChannel_branch_apply,
      chainOp]
    simp
  | succ q ih =>
    rw [scChain_succ_branch_false, scOracleQ_branch_false, ih]
    simp only [chainOp, conjTranspose_mul, conjTranspose_sub, conjTranspose_one,
      projS_conjTranspose, Matrix.mul_assoc]

/-- The semi-classical oracle is trace preserving. -/
theorem scOracleQ_trace_add (H : Fin m → Fin n) (S : Finset (Fin m))
    (σ : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    ((scOracleQ m n w H S).branch true σ).trace + ((scOracleQ m n w H S).branch false σ).trace =
      σ.trace := by
  have hP : (1 - projS m n w S) * (1 - projS m n w S) = 1 - projS m n w S := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, projS_mul_self]; abel
  rw [scOracleQ_branch_true, scOracleQ_branch_false,
    trace_mul_mul_conjTranspose_of_mem_unitaryGroup (oracleU m n w H).prop,
    trace_mul_mul_conjTranspose_of_mem_unitaryGroup (oracleU m n w H).prop,
    trace_proj_mul_mul_proj (projS_mul_self m n w S), trace_proj_mul_mul_proj hP, ← trace_add,
    ← add_mul, add_sub_cancel, one_mul]

/-- The branch of the semi-classical run at `(out, f)`: the final measurement
    at `out` after the chain's branch at `f`. -/
theorem runSC_branch_apply (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m))
    (out f : Bool) (ρ : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (runSC A H S).branch (out, f) ρ =
      A.measure.branch out ((scChain (scOracleQ m n w H S) q A.U).branch f ρ) := by
  unfold runSC
  simp only [qbind_branch_apply, tsum_fintype, Fintype.sum_bool, qpure_branch_apply]
  cases out <;> cases f <;> simp

omit [NeZero n] in
/-- The final measurement is trace preserving. -/
theorem measure_trace_add (A : QAdv m n w q) (σ : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (A.measure.branch true σ).trace + (A.measure.branch false σ).trace = σ.trace := by
  have hP : (1 - A.final) * (1 - A.final) = 1 - A.final := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, A.final_mul_self]; abel
  unfold QAdv.measure
  rw [measProj_branch_true, measProj_branch_false, A.final_conjTranspose, conjTranspose_sub,
    conjTranspose_one, A.final_conjTranspose, trace_proj_mul_mul_proj A.final_mul_self,
    trace_proj_mul_mul_proj hP, ← trace_add, ← add_mul, add_sub_cancel, one_mul]

/-- `Pr[Find]` is the trace of the `true` branch of the semi-classical chain. -/
theorem prFind_eq_trace (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m)) :
    prFind A H S =
      ENNReal.ofReal ((scChain (scOracleQ m n w H S) q A.U).branch true A.init.val).trace.re := by
  unfold prFind prTrue_Q
  simp only [qbind_branch_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool,
    qpure_branch_apply, runSC_branch_apply]
  simp only [Bool.true_eq_false, ↓reduceIte, add_zero, trace_add]
  rw [measure_trace_add]

/-- `Pr[out = 1 ∧ ¬Find]` is the trace of the final projector applied to the
    `false` branch of the semi-classical chain. -/
theorem prOutNoFind_eq_trace (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m)) :
    prOutNoFind A H S =
      ENNReal.ofReal (A.final * (scChain (scOracleQ m n w H S) q A.U).branch false A.init.val *
        A.final).trace.re := by
  unfold prOutNoFind prTrue_Q
  simp only [qbind_branch_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool,
    qpure_branch_apply, runSC_branch_apply]
  simp only [Bool.and_self, Bool.not_true, Bool.and_false, Bool.false_and, Bool.not_false,
    Bool.true_eq_false, ↓reduceIte, zero_add, add_zero]
  unfold QAdv.measure
  rw [measProj_branch_true, A.final_conjTranspose]

omit [NeZero n] in
/-- The initial vector of a pure initial state has norm one. -/
theorem nrm_eq_one_of_init (A : QAdv m n w q) {ψ : Fin (m * n * w) → ℂ}
    (hpure : A.init.val = vecMulVec ψ (star ψ)) : nrm ψ = 1 := by
  have h := A.init.tr_one
  rw [hpure, trace_vecMulVec, dotProduct_star_self] at h
  have h' : nrm ψ ^ 2 = 1 ^ 2 := by rw [one_pow]; exact_mod_cast h
  exact (sq_eq_sq₀ (nrm_nonneg ψ) zero_le_one).mp h'

/-- The standard run on a pure state: `Pr[out = 1] = ‖M (runOp ψ)‖²`. -/
theorem prOut_eq_nrm_sq (A : QAdv m n w q) (H : Fin m → Fin n) {ψ : Fin (m * n * w) → ℂ}
    (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    prOut A H = ENNReal.ofReal (nrm (A.final *ᵥ (runOp A H *ᵥ ψ)) ^ 2) := by
  unfold prOut prTrue_Q
  rw [run_branch_true, hpure, trace_mul_vecMulVec_star_mul_conjTranspose, Complex.ofReal_re,
    mulVec_mulVec]

/-- The `Find = false` branch on a pure state: `Pr[out = 1 ∧ ¬Find] = ‖M (scOp ψ)‖²`. -/
theorem prOutNoFind_eq_nrm_sq (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m))
    {ψ : Fin (m * n * w) → ℂ} (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    prOutNoFind A H S = ENNReal.ofReal (nrm (A.final *ᵥ (scOp A H S *ᵥ ψ)) ^ 2) := by
  rw [prOutNoFind_eq_trace, scChain_branch_false_eq, hpure]
  have : A.final * (chainOp ((oracleU m n w H : Matrix _ _ ℂ) * (1 - projS m n w S)) q A.U *
      vecMulVec ψ (star ψ) *
      (chainOp ((oracleU m n w H : Matrix _ _ ℂ) * (1 - projS m n w S)) q A.U)ᴴ) * A.final =
      (A.final * scOp A H S) * vecMulVec ψ (star ψ) * (A.final * scOp A H S)ᴴ := by
    rw [conjTranspose_mul, A.final_conjTranspose]
    unfold scOp
    simp only [Matrix.mul_assoc]
  rw [this, trace_mul_vecMulVec_star_mul_conjTranspose, Complex.ofReal_re, mulVec_mulVec]

/-- `Pr[Find]` on a pure state is the sum over the queries of the squared norms
    of the projected intermediate states. -/
theorem prFind_eq_sum (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m))
    {ψ : Fin (m * n * w) → ℂ} (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    prFind A H S = ENNReal.ofReal (∑ i, nrm (projS m n w S *ᵥ scState A H S ψ i) ^ 2) := by
  rw [prFind_eq_trace, hpure]
  congr 1
  have htp := scChain_trace_add (scOracleQ m n w H S) (scOracleQ_trace_add H S) q A.U
    (vecMulVec ψ (star ψ))
  rw [scChain_branch_false_eq, trace_mul_vecMulVec_star_mul_conjTranspose,
    trace_vecMulVec, dotProduct_star_self] at htp
  have hpy : ((nrm (chainOp ((oracleU m n w H : Matrix _ _ ℂ) * (1 - projS m n w S)) q A.U *ᵥ ψ)
      ^ 2 : ℝ) : ℂ) + ((∑ i, nrm (projS m n w S *ᵥ scState A H S ψ i) ^ 2 : ℝ) : ℂ) =
      ((nrm ψ ^ 2 : ℝ) : ℂ) := by
    unfold scState
    exact_mod_cast nrm_sq_chainOp_add_sum_nrm_sq_scStates (oracleU m n w H).prop
      (projS_mul_self m n w S) (projS_conjTranspose m n w S) q A.U ψ
  have hre : ((scChain (scOracleQ m n w H S) q A.U).branch true (vecMulVec ψ (star ψ))).trace =
      ((∑ i, nrm (projS m n w S *ᵥ scState A H S ψ i) ^ 2 : ℝ) : ℂ) := by
    linear_combination htp - hpy
  rw [hre, Complex.ofReal_re]

/-- `Pr[out = 1 ∧ ¬Find]` and `Pr[Find]` are the same for two functions that
    agree outside `S`, on the operator level. -/
theorem scOp_congr (A : QAdv m n w q) (H H' : Fin m → Fin n) (S : Finset (Fin m))
    (hHH' : ∀ x, x ∉ S → H x = H' x) : scOp A H S = scOp A H' S := by
  unfold scOp
  rw [oracleU_mul_one_sub_projS H H' S hHH']

theorem scState_congr (A : QAdv m n w q) (H H' : Fin m → Fin n) (S : Finset (Fin m))
    (hHH' : ∀ x, x ∉ S → H x = H' x) (ψ : Fin (m * n * w) → ℂ) :
    scState A H S ψ = scState A H' S ψ := by
  unfold scState
  rw [oracleU_mul_one_sub_projS H H' S hHH']

end Adv

/-! ## The O2H inequality -/

section O2H

variable {m n w q : ℕ} [NeZero n]

/-- The real-valued core: `|‖M R ψ‖² − ‖M S ψ‖²| ≤ 2 √(q · ∑ᵢ ‖Π θᵢ‖²)` for a
    unit vector `ψ`. -/
theorem abs_nrm_sq_sub_le_sqrt (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m))
    {ψ : Fin (m * n * w) → ℂ} (hψ : nrm ψ = 1) :
    |nrm (A.final *ᵥ (runOp A H *ᵥ ψ)) ^ 2 - nrm (A.final *ᵥ (scOp A H S *ᵥ ψ)) ^ 2| ≤
      2 * Real.sqrt ((q : ℝ) * ∑ i, nrm (projS m n w S *ᵥ scState A H S ψ i) ^ 2) := by
  have hI := A.final_mul_self
  have hH := A.final_conjTranspose
  have hO := (oracleU m n w H).prop
  have hPI := projS_mul_self m n w S
  have hPH := projS_conjTranspose m n w S
  set a := A.final *ᵥ (runOp A H *ᵥ ψ)
  set b := A.final *ᵥ (scOp A H S *ᵥ ψ)
  have ha : nrm a ≤ 1 := by
    calc nrm a ≤ nrm (runOp A H *ᵥ ψ) := nrm_proj_mulVec_le hI hH _
      _ = 1 := by
        unfold runOp
        rw [nrm_chainOp_mulVec_eq _ (nrm_mulVec_of_mem_unitaryGroup hO), hψ]
  have hb : nrm b ≤ 1 := by
    calc nrm b ≤ nrm (scOp A H S *ᵥ ψ) := nrm_proj_mulVec_le hI hH _
      _ ≤ 1 := by
        unfold scOp
        rw [← hψ]
        refine nrm_chainOp_mulVec_le _ (fun v => ?_) q A.U ψ
        rw [← mulVec_mulVec, nrm_mulVec_of_mem_unitaryGroup hO]
        exact nrm_proj_mulVec_le (P := 1 - projS m n w S)
          (by simp only [sub_mul, mul_sub, one_mul, mul_one, hPI]; abel)
          (by rw [conjTranspose_sub, conjTranspose_one, hPH]) v
  have hab : nrm (a - b) ≤ ∑ i, nrm (projS m n w S *ᵥ scState A H S ψ i) := by
    calc nrm (a - b) = nrm (A.final *ᵥ (runOp A H *ᵥ ψ - scOp A H S *ᵥ ψ)) := by
          simp only [a, b, mulVec_sub]
      _ ≤ nrm (runOp A H *ᵥ ψ - scOp A H S *ᵥ ψ) := nrm_proj_mulVec_le hI hH _
      _ ≤ _ := nrm_chainOp_sub_le (projS m n w S) hO q A.U ψ
  have hcs := sum_le_sqrt_card_mul_sum_sq (fun i => nrm (projS m n w S *ᵥ scState A H S ψ i))
    (fun i => nrm_nonneg _)
  rw [Fintype.card_fin] at hcs
  calc |nrm a ^ 2 - nrm b ^ 2| ≤ nrm (a - b) * (nrm a + nrm b) := abs_nrm_sq_sub_nrm_sq_le a b
    _ ≤ nrm (a - b) * 2 := mul_le_mul_of_nonneg_left (by linarith) (nrm_nonneg _)
    _ ≤ (∑ i, nrm (projS m n w S *ᵥ scState A H S ψ i)) * 2 := by gcongr
    _ ≤ Real.sqrt ((q : ℝ) * ∑ i, nrm (projS m n w S *ᵥ scState A H S ψ i) ^ 2) * 2 := by
        gcongr
    _ = _ := by ring

/-- `absDiff` of two `ofReal`s is at most `ofReal` of the absolute difference. -/
theorem absDiff_ofReal_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    absDiff (ENNReal.ofReal x) (ENNReal.ofReal y) ≤ ENNReal.ofReal |x - y| := by
  unfold absDiff
  apply max_le
  · rw [← ENNReal.ofReal_sub x hy]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  · rw [← ENNReal.ofReal_sub y hx, abs_sub_comm]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)

/-- `ofReal (2 √(q · F)) = 2 (q · ofReal F)^(1/2)` for `0 ≤ F`. -/
theorem ofReal_two_mul_sqrt {F : ℝ} (hF : 0 ≤ F) :
    ENNReal.ofReal (2 * Real.sqrt ((q : ℝ) * F)) =
      2 * ((q : ℝ≥0∞) * ENNReal.ofReal F) ^ (1 / 2 : ℝ) := by
  rw [ENNReal.ofReal_mul (by norm_num), Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hF) (by norm_num),
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]

/-- The semi-classical one-way-to-hiding bound (Ambainis–Hamburg–Unruh,
    CRYPTO 2019, Theorem 1, the `Pr[out = 1 ∧ ¬Find]` form) for a pure initial
    state:
    `|Pr[out = 1 : A^H] − Pr[out = 1 ∧ ¬Find : A^{H \ S}]| ≤ 2 √(q · Pr[Find])`.

    References: Ambainis, Hamburg, Unruh, "Quantum security proofs using
    semi-classical oracles", CRYPTO 2019, ePrint 2018/904, Theorem 1. The
    paper's constant is the query depth; the constant here is the number of
    queries `q`, which coincides with the depth for the sequential adversary
    `QAdv`. -/
theorem o2h_semiclassical (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m))
    {ψ : Fin (m * n * w) → ℂ} (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    absDiff (prOut A H) (prOutNoFind A H S) ≤
      2 * ((q : ℝ≥0∞) * prFind A H S) ^ (1 / 2 : ℝ) := by
  rw [prOut_eq_nrm_sq A H hpure, prOutNoFind_eq_nrm_sq A H S hpure, prFind_eq_sum A H S hpure,
    ← ofReal_two_mul_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  refine (absDiff_ofReal_le (sq_nonneg _) (sq_nonneg _)).trans (ENNReal.ofReal_le_ofReal ?_)
  exact abs_nrm_sq_sub_le_sqrt A H S (nrm_eq_one_of_init A hpure)

/-- `Pr[out = 1 ∧ ¬Find]` is the same for two functions that agree outside `S`. -/
theorem prOutNoFind_congr (A : QAdv m n w q) (H H' : Fin m → Fin n) (S : Finset (Fin m))
    (hHH' : ∀ x, x ∉ S → H x = H' x) {ψ : Fin (m * n * w) → ℂ}
    (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    prOutNoFind A H S = prOutNoFind A H' S := by
  rw [prOutNoFind_eq_nrm_sq A H S hpure, prOutNoFind_eq_nrm_sq A H' S hpure,
    scOp_congr A H H' S hHH']

/-- `Pr[Find]` is the same for two functions that agree outside `S`. -/
theorem prFind_congr (A : QAdv m n w q) (H H' : Fin m → Fin n) (S : Finset (Fin m))
    (hHH' : ∀ x, x ∉ S → H x = H' x) {ψ : Fin (m * n * w) → ℂ}
    (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    prFind A H S = prFind A H' S := by
  rw [prFind_eq_sum A H S hpure, prFind_eq_sum A H' S hpure, scState_congr A H H' S hHH']

/-- The one-way-to-hiding bound between two functions that agree outside `S`,
    for a pure initial state:
    `|Pr[out = 1 : A^H] − Pr[out = 1 : A^{H'}]| ≤ 4 √(q · Pr[Find])`.

    References: Ambainis, Hamburg, Unruh, "Quantum security proofs using
    semi-classical oracles", CRYPTO 2019, ePrint 2018/904, Theorem 1 (the
    two-function form, obtained from `o2h_semiclassical` applied to `H` and
    `H'`); the constant `q` is the query count in place of the paper's query
    depth. -/
theorem o2h (A : QAdv m n w q) (H H' : Fin m → Fin n) (S : Finset (Fin m))
    (hHH' : ∀ x, x ∉ S → H x = H' x) {ψ : Fin (m * n * w) → ℂ}
    (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    absDiff (prOut A H) (prOut A H') ≤ 4 * ((q : ℝ≥0∞) * prFind A H S) ^ (1 / 2 : ℝ) := by
  calc absDiff (prOut A H) (prOut A H')
      ≤ absDiff (prOut A H) (prOutNoFind A H S) + absDiff (prOutNoFind A H S) (prOut A H') :=
        absDiff_triangle _ _ _
    _ = absDiff (prOut A H) (prOutNoFind A H S) +
          absDiff (prOut A H') (prOutNoFind A H' S) := by
        rw [absDiff_comm (prOutNoFind A H S), prOutNoFind_congr A H H' S hHH' hpure]
    _ ≤ 2 * ((q : ℝ≥0∞) * prFind A H S) ^ (1 / 2 : ℝ) +
          2 * ((q : ℝ≥0∞) * prFind A H' S) ^ (1 / 2 : ℝ) :=
        add_le_add (o2h_semiclassical A H S hpure) (o2h_semiclassical A H' S hpure)
    _ = 4 * ((q : ℝ≥0∞) * prFind A H S) ^ (1 / 2 : ℝ) := by
        rw [← prFind_congr A H H' S hHH' hpure]; ring

/-- The squared form of `o2h`: `|Pr[out = 1 : A^H] − Pr[out = 1 : A^{H'}]|² ≤ (4q)² · Pr[Find]`,
    the shape of `Quantum.O2H.O2HExtraction` with constant `4q` in place of `2q`. -/
theorem o2h_extraction_of_QAdv (A : QAdv m n w q) (H H' : Fin m → Fin n) (S : Finset (Fin m))
    (hHH' : ∀ x, x ∉ S → H x = H' x) {ψ : Fin (m * n * w) → ℂ}
    (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    absDiff (prOut A H) (prOut A H') ^ 2 ≤ (4 * (q : ℝ≥0∞)) ^ 2 * prFind A H S := by
  have h := o2h A H H' S hHH' hpure
  have hsq : (((q : ℝ≥0∞) * prFind A H S) ^ (1 / 2 : ℝ)) ^ 2 = (q : ℝ≥0∞) * prFind A H S := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  calc absDiff (prOut A H) (prOut A H') ^ 2
      ≤ (4 * ((q : ℝ≥0∞) * prFind A H S) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left' h 2
    _ = 4 ^ 2 * ((q : ℝ≥0∞) * prFind A H S) := by rw [mul_pow, hsq]
    _ ≤ (4 * (q : ℝ≥0∞)) ^ 2 * prFind A H S := by
        rcases Nat.eq_zero_or_pos q with hq | hq
        · subst hq; simp
        · rw [mul_pow, mul_assoc]
          gcongr
          calc (q : ℝ≥0∞) = (q : ℝ≥0∞) * 1 := (mul_one _).symm
            _ ≤ (q : ℝ≥0∞) * q := by gcongr; exact_mod_cast hq
            _ = (q : ℝ≥0∞) ^ 2 := (sq _).symm

end O2H

end CatCrypt.Quantum.QROM
