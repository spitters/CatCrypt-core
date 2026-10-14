/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.O2HTheorem
public import CatCryptCore.Quantum.QROM.PermUnitaryCore

/-!
# Search in a semi-classical oracle: `Pr[Find]` against measuring a random query

The `Find` probability of the semi-classical run of a `q`-query adversary is at
most `4` times the sum over the queries `j` of the probability that the query
register of the plain run, measured before query `j`, lies in the punctured
set (Ambainis–Hamburg–Unruh, CRYPTO 2019, Theorem 2). The proof is the
potential argument of that paper: with `Ψ'_i` the plain state and `Ψ_i` the
`Find = false` state before query `i`, the potential
`3 ‖Ψ'_i‖² − 4 Re⟨Ψ'_i, Ψ_i⟩ + ‖Ψ_i‖²` starts at `0`, grows by at most
`4 ‖Π U_i Ψ'_i‖²` at each query, and dominates `‖Ψ'_i‖² − ‖Ψ_i‖²`, which at the
end is `Pr[Find]`.

The statements are about an arbitrary adversary `QAdv m n w q` and oracle
`H : Fin m → Fin n`; no encryption scheme or game appears.

## Main definitions

* `absorbU G q U` — the unitary `U_q O_G U_{q-1} ⋯ O_G U_0`
* `absorbOracle A G` — the `0`-query adversary with the single unitary
  `absorbU G q A.U`, the initial state and the final projector of `A`
* `pot a b` — the potential `3 ‖a‖² − 4 Re⟨a, b⟩ + ‖b‖²`
* `prefixU A H j`, `plainState A H ψ` — the operator of the plain run up to
  and including `U_j`, and the plain states before each query
* `prefixAdv A H S j`, `guessProb A H S j` — the `0`-query adversary that runs
  the prefix and measures `projS S`, and its acceptance probability
* `swapXO m n w`, `swapPerm m n w`, `swapU m n w` — the permutation exchanging
  the query factor `Fin m` with the factor `Fin m` of a work register
  `Fin (m * w)`, on pairs, on the total index, and as a unitary

## Main results

* `absorbU_val` — the value of `absorbU` is `chainOp (oracleU G)`
* `prOut_absorbOracle` — the absorbed adversary wins as `A` does against `G`,
  whatever oracle it is run against
* `pot_chainOp_le` — the potential grows by at most `4 ∑ᵢ ‖Π θ'ᵢ‖²` along
  the chains
* `sum_nrm_sq_scStates_le` — `∑ᵢ ‖Π θᵢ‖² ≤ 4 ∑ᵢ ‖Π θ'ᵢ‖²` for the projected
  and the plain intermediate states
* `prFind_le_four_sum_guess` — for a pure initial state,
  `Pr[Find] ≤ 4 ∑ⱼ guessProb A H S j`
* `oPart_swapPerm` — the swap carries the query factor to the output factor

## References

* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], Theorem 2 (Lemma 7)
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Absorbing the oracle into the adversary's unitaries -/

section Absorb

variable {m n w q : ℕ} [NeZero n]

/-- The unitary `U_q O_G U_{q-1} ⋯ O_G U_0` of a `q`-query adversary with the
    standard oracle for `G` at each query. -/
def absorbU (G : Fin m → Fin n) :
    (q : ℕ) → (Fin (q + 1) → Matrix.unitaryGroup (Fin (m * n * w)) ℂ) →
      Matrix.unitaryGroup (Fin (m * n * w)) ℂ
  | 0, U => U 0
  | q + 1, U => absorbU G q (Fin.tail U) * oracleU m n w G * U 0

/-- The value of `absorbU` is the chain operator of the oracle unitary. -/
theorem absorbU_val (G : Fin m → Fin n) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin (m * n * w)) ℂ) :
    (absorbU G q U : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) =
      chainOp (oracleU m n w G : Matrix _ _ ℂ) q U := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [absorbU, chainOp, Submonoid.coe_mul, ih]

/-- The `0`-query adversary with the single unitary `absorbU G q A.U`, the
    initial state and the final projector of `A`. -/
def absorbOracle (A : QAdv m n w q) (G : Fin m → Fin n) : QAdv m n w 0 where
  U _ := absorbU G q A.U
  init := A.init
  final := A.final
  final_conjTranspose := A.final_conjTranspose
  final_mul_self := A.final_mul_self

/-- The run operator of a `0`-query adversary is its unitary, whatever the
    oracle. -/
theorem runOp_zero (A : QAdv m n w 0) (H : Fin m → Fin n) :
    runOp A H = (A.U 0 : Matrix _ _ ℂ) := rfl

/-- The run operator of the absorbed adversary is the run operator of `A`
    against `G`. -/
theorem runOp_absorbOracle (A : QAdv m n w q) (G H : Fin m → Fin n) :
    runOp (absorbOracle A G) H = runOp A G := by
  rw [runOp_zero]
  exact absorbU_val G q A.U

/-- A `0`-query adversary wins with the same probability against every oracle. -/
theorem prOut_zero (A : QAdv m n w 0) (H H' : Fin m → Fin n) : prOut A H = prOut A H' := by
  unfold prOut prTrue_Q
  rw [run_branch_true, run_branch_true, runOp_zero, runOp_zero]

/-- The absorbed adversary wins, against any oracle, with the probability of
    `A` against `G`. -/
theorem prOut_absorbOracle (A : QAdv m n w q) (G H : Fin m → Fin n) :
    prOut (absorbOracle A G) H = prOut A G := by
  unfold prOut prTrue_Q
  rw [run_branch_true, run_branch_true, runOp_absorbOracle]
  simp only [absorbOracle]

end Absorb

/-! ## The pairing and the potential -/

section Potential

variable {d : ℕ}

/-- The pairing of two images under matrices, pulled back to the arguments. -/
theorem mulVec_dotProduct_star_mulVec' (A B : Matrix (Fin d) (Fin d) ℂ) (u v : Fin d → ℂ) :
    (A *ᵥ u) ⬝ᵥ star (B *ᵥ v) = ((Bᴴ * A) *ᵥ u) ⬝ᵥ star v := by
  rw [star_mulVec, dotProduct_comm, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec,
    dotProduct_comm]

/-- The real part of the pairing is symmetric. -/
theorem re_dotProduct_star_comm (u v : Fin d → ℂ) :
    (u ⬝ᵥ star v).re = (v ⬝ᵥ star u).re := by
  rw [dotProduct_star, Complex.star_def, Complex.conj_re]

/-- The real part of the self pairing is the squared norm. -/
theorem re_dotProduct_star_self (v : Fin d → ℂ) : (v ⬝ᵥ star v).re = nrm v ^ 2 := by
  rw [dotProduct_star_self, Complex.ofReal_re]

/-- A unitary preserves the pairing. -/
theorem mulVec_dotProduct_star_mulVec_of_mem_unitaryGroup {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (u v : Fin d → ℂ) :
    (U *ᵥ u) ⬝ᵥ star (U *ᵥ v) = u ⬝ᵥ star v := by
  rw [mulVec_dotProduct_star_mulVec', ← star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hU,
    one_mulVec]

/-- The pairing against a projected vector is the pairing of the projections. -/
theorem dotProduct_star_proj_mulVec {P : Matrix (Fin d) (Fin d) ℂ}
    (hI : P * P = P) (hH : Pᴴ = P) (u v : Fin d → ℂ) :
    u ⬝ᵥ star (P *ᵥ v) = (P *ᵥ u) ⬝ᵥ star (P *ᵥ v) := by
  rw [mulVec_dotProduct_star_mulVec' P P u v, hH, hI]
  nth_rw 1 [← one_mulVec u]
  rw [mulVec_dotProduct_star_mulVec', hH, Matrix.mul_one]

/-- `‖u − v‖² = ‖u‖² − 2 Re⟨u, v⟩ + ‖v‖²`. -/
theorem nrm_sq_sub (u v : Fin d → ℂ) :
    nrm (u - v) ^ 2 = nrm u ^ 2 - 2 * (u ⬝ᵥ star v).re + nrm v ^ 2 := by
  rw [← re_dotProduct_star_self, ← re_dotProduct_star_self, ← re_dotProduct_star_self,
    star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
  simp only [Complex.sub_re]
  rw [re_dotProduct_star_comm v u]
  ring

/-- The potential `3 ‖a‖² − 4 Re⟨a, b⟩ + ‖b‖²`. -/
def pot (a b : Fin d → ℂ) : ℝ := 3 * nrm a ^ 2 - 4 * (a ⬝ᵥ star b).re + nrm b ^ 2

theorem pot_self (a : Fin d → ℂ) : pot a a = 0 := by
  simp only [pot, re_dotProduct_star_self]; ring

/-- The potential dominates the difference of the squared norms. -/
theorem nrm_sq_sub_nrm_sq_le_pot (a b : Fin d → ℂ) : nrm a ^ 2 - nrm b ^ 2 ≤ pot a b := by
  have h := nrm_sq_sub a b
  have h0 := sq_nonneg (nrm (a - b))
  unfold pot
  linarith

/-- The potential is invariant under a common unitary. -/
theorem pot_mulVec_of_mem_unitaryGroup {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (a b : Fin d → ℂ) :
    pot (U *ᵥ a) (U *ᵥ b) = pot a b := by
  simp only [pot, nrm_mulVec_of_mem_unitaryGroup hU, mulVec_dotProduct_star_mulVec_of_mem_unitaryGroup hU]

/-- One query step of the potential: projecting the second argument by `1 − P`
    raises the potential by at most `4 ‖P x‖²`. -/
theorem pot_one_sub_proj_le {P : Matrix (Fin d) (Fin d) ℂ}
    (hI : P * P = P) (hH : Pᴴ = P) (x y : Fin d → ℂ) :
    pot x ((1 - P) *ᵥ y) ≤ pot x y + 4 * nrm (P *ᵥ x) ^ 2 := by
  have hpy := nrm_sq_proj_add_nrm_sq_one_sub_proj hI hH y
  have h0 := sq_nonneg (nrm (P *ᵥ x - (P *ᵥ y - P *ᵥ x)))
  have hsq := nrm_sq_sub (P *ᵥ x) (P *ᵥ y - P *ᵥ x)
  have hsq' := nrm_sq_sub (P *ᵥ y) (P *ᵥ x)
  have hpair : (P *ᵥ x ⬝ᵥ star (P *ᵥ y - P *ᵥ x)).re =
      (x ⬝ᵥ star (P *ᵥ y)).re - nrm (P *ᵥ x) ^ 2 := by
    rw [star_sub, dotProduct_sub, Complex.sub_re, re_dotProduct_star_self,
      dotProduct_star_proj_mulVec hI hH x y]
  have hcomm := re_dotProduct_star_comm (P *ᵥ y) (P *ᵥ x)
  rw [← dotProduct_star_proj_mulVec hI hH x y] at hcomm
  have hlin : (x ⬝ᵥ star ((1 - P) *ᵥ y)).re = (x ⬝ᵥ star y).re - (x ⬝ᵥ star (P *ᵥ y)).re := by
    rw [sub_mulVec, one_mulVec, star_sub, dotProduct_sub, Complex.sub_re]
  unfold pot
  rw [hlin]
  nlinarith

end Potential

/-! ## The potential along the chains -/

section Chain

variable {d : ℕ}

/-- Along the plain chain from `a` and the projected chain from `b`, the
    potential grows by at most `4 ∑ᵢ ‖P θ'ᵢ‖²`, with `θ'ᵢ` the plain states
    before each query. -/
theorem pot_chainOp_le {O P : Matrix (Fin d) (Fin d) ℂ}
    (hO : O ∈ Matrix.unitaryGroup (Fin d) ℂ) (hI : P * P = P) (hH : Pᴴ = P) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (a b : Fin d → ℂ) :
    pot (chainOp O q U *ᵥ a) (chainOp (O * (1 - P)) q U *ᵥ b) ≤
      pot a b + 4 * ∑ i, nrm (P *ᵥ scStates O q U a i) ^ 2 := by
  induction q generalizing a b with
  | zero =>
    simp only [chainOp, scStates, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, add_zero,
      pot_mulVec_of_mem_unitaryGroup (U 0).prop, le_refl]
  | succ q ih =>
    rw [chainOp_succ_mulVec, chainOp_succ_mulVec, Fin.sum_univ_succ]
    simp only [scStates, Fin.cons_zero, Fin.cons_succ]
    refine (ih (Fin.tail U) _ _).trans ?_
    have hstep : pot (O *ᵥ ((U 0 : Matrix _ _ ℂ) *ᵥ a))
        ((O * (1 - P)) *ᵥ ((U 0 : Matrix _ _ ℂ) *ᵥ b)) ≤
        pot a b + 4 * nrm (P *ᵥ ((U 0 : Matrix _ _ ℂ) *ᵥ a)) ^ 2 := by
      rw [← mulVec_mulVec, pot_mulVec_of_mem_unitaryGroup hO,
        ← pot_mulVec_of_mem_unitaryGroup (U 0).prop a b]
      exact pot_one_sub_proj_le hI hH _ _
    linarith

/-- The squared norms of the projected states of the semi-classical chain sum
    to at most `4` times those of the plain chain. -/
theorem sum_nrm_sq_scStates_le {O P : Matrix (Fin d) (Fin d) ℂ}
    (hO : O ∈ Matrix.unitaryGroup (Fin d) ℂ) (hI : P * P = P) (hH : Pᴴ = P) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (ψ : Fin d → ℂ) :
    ∑ i, nrm (P *ᵥ scStates (O * (1 - P)) q U ψ i) ^ 2 ≤
      4 * ∑ i, nrm (P *ᵥ scStates O q U ψ i) ^ 2 := by
  have h1 := nrm_sq_chainOp_add_sum_nrm_sq_scStates hO hI hH q U ψ
  have h2 := nrm_chainOp_mulVec_eq O (nrm_mulVec_of_mem_unitaryGroup hO) q U ψ
  have h3 := nrm_sq_sub_nrm_sq_le_pot (chainOp O q U *ᵥ ψ) (chainOp (O * (1 - P)) q U *ᵥ ψ)
  have h4 := pot_chainOp_le hO hI hH q U ψ ψ
  rw [pot_self] at h4
  rw [h2] at h3
  linarith

/-- The chain of the first `j + 1` unitaries applied to `ψ` is the state before
    query `j`. -/
theorem chainOp_castLE_mulVec (O : Matrix (Fin d) (Fin d) ℂ) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (ψ : Fin d → ℂ) (j : Fin q) :
    chainOp O j (fun i : Fin (j + 1) => U (Fin.castLE (Nat.succ_le_succ j.isLt.le) i)) *ᵥ ψ =
      scStates O q U ψ j := by
  induction q generalizing ψ with
  | zero => exact j.elim0
  | succ q ih =>
    refine Fin.cases ?_ (fun j' => ?_) j
    · simp only [Fin.val_zero, chainOp, scStates, Fin.cons_zero]
      rfl
    · simp only [Fin.val_succ, chainOp_succ_mulVec, scStates, Fin.cons_succ]
      rw [← ih (Fin.tail U) _ j']
      congr 2

end Chain

/-! ## The plain states and the guessing probability of an adversary -/

section Adv

variable {m n w q : ℕ} [NeZero n]

/-- The operator `U_j O_H U_{j-1} ⋯ O_H U_0` of the plain run up to and
    including `U_j`. -/
def prefixU (A : QAdv m n w q) (H : Fin m → Fin n) (j : Fin q) :
    Matrix.unitaryGroup (Fin (m * n * w)) ℂ :=
  absorbU H j (fun i : Fin (j + 1) => A.U (Fin.castLE (Nat.succ_le_succ j.isLt.le) i))

/-- The states of the plain run before each query, from the initial vector `ψ`:
    `θ'_j = U_j O_H ⋯ O_H U_0 ψ`. -/
def plainState (A : QAdv m n w q) (H : Fin m → Fin n) (ψ : Fin (m * n * w) → ℂ) :
    Fin q → (Fin (m * n * w) → ℂ) :=
  scStates (oracleU m n w H : Matrix _ _ ℂ) q A.U ψ

theorem prefixU_mulVec (A : QAdv m n w q) (H : Fin m → Fin n) (ψ : Fin (m * n * w) → ℂ)
    (j : Fin q) : (prefixU A H j : Matrix _ _ ℂ) *ᵥ ψ = plainState A H ψ j := by
  unfold prefixU plainState
  rw [absorbU_val]
  exact chainOp_castLE_mulVec _ q A.U ψ j

/-- The `0`-query adversary that runs the prefix of `A` up to `U_j` against `H`
    and measures `projS S`. -/
def prefixAdv (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m)) (j : Fin q) :
    QAdv m n w 0 where
  U _ := prefixU A H j
  init := A.init
  final := projS m n w S
  final_conjTranspose := projS_conjTranspose m n w S
  final_mul_self := projS_mul_self m n w S

/-- The probability that the query register of the plain run against `H`,
    measured before query `j`, lies in `S`. -/
def guessProb (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m)) (j : Fin q) :
    ℝ≥0∞ :=
  prOut (prefixAdv A H S j) H

/-- On a pure state, `guessProb` is the squared norm of the projected plain
    state. -/
theorem guessProb_eq_nrm_sq (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m))
    (j : Fin q) {ψ : Fin (m * n * w) → ℂ} (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    guessProb A H S j = ENNReal.ofReal (nrm (projS m n w S *ᵥ plainState A H ψ j) ^ 2) := by
  unfold guessProb
  rw [prOut_eq_nrm_sq (prefixAdv A H S j) H hpure, runOp_zero]
  simp only [prefixAdv, prefixU_mulVec]

/-- Search in a semi-classical oracle (Ambainis–Hamburg–Unruh, CRYPTO 2019,
    Theorem 2) for a pure initial state: `Pr[Find] ≤ 4 ∑ⱼ guessProb A H S j`. -/
theorem prFind_le_four_sum_guess (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m))
    {ψ : Fin (m * n * w) → ℂ} (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    prFind A H S ≤ 4 * ∑ j, guessProb A H S j := by
  rw [prFind_eq_sum A H S hpure]
  simp only [guessProb_eq_nrm_sq A H S _ hpure]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _), ← ENNReal.ofReal_ofNat 4,
    ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  unfold scState plainState
  exact sum_nrm_sq_scStates_le (oracleU m n w H).prop (projS_mul_self m n w S)
    (projS_conjTranspose m n w S) q A.U ψ

end Adv

/-! ## The swap of the query factor into the output factor -/

section Swap

variable (m n w : ℕ)

/-- The permutation `((x, y), (o, z)) ↦ ((o, y), (x, z))` of the total register's
    index set, exchanging the query factor with the output factor. -/
def swapXO : Equiv.Perm ((Fin m × Fin n) × (Fin m × Fin w)) where
  toFun p := ((p.2.1, p.1.2), (p.1.1, p.2.2))
  invFun p := ((p.2.1, p.1.2), (p.1.1, p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The row-major index of `((x, y), (o, z))` in the total register
    `Fin (m * n * (m * w))`. -/
def totalIndex : (Fin m × Fin n) × (Fin m × Fin w) ≃ Fin (m * n * (m * w)) :=
  ((finProdEquiv m n).prodCongr (finProdEquiv m w)).trans (finProdEquiv (m * n) (m * w))

/-- The output factor of a total-register index. -/
def oPart (k : Fin (m * n * (m * w))) : Fin m := ((totalIndex m n w).symm k).2.1

/-- The permutation of `Fin (m * n * (m * w))` exchanging the query factor with
    the output factor. -/
def swapPerm : Equiv.Perm (Fin (m * n * (m * w))) :=
  (totalIndex m n w).permCongr (swapXO m n w)

/-- The unitary of `swapPerm`. -/
def swapU : Matrix.unitaryGroup (Fin (m * n * (m * w))) ℂ := permUnitary (swapPerm m n w)

theorem oPart_swapPerm (k : Fin (m * n * (m * w))) :
    oPart m n w (swapPerm m n w k) = xPart m n (m * w) k := by
  simp [oPart, xPart, swapPerm, totalIndex, swapXO, Equiv.permCongr_apply]

/-- The identity tensored with a diagonal matrix is diagonal, with the entry
    read off the second factor of the index. -/
theorem one_kronecker_diagonal {d₁ d₂ : ℕ} (f : Fin d₂ → ℂ) :
    (1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ Matrix.diagonal f =
      Matrix.diagonal (fun k => f ((finProdEquiv d₁ d₂).symm k).2) := by
  ext i j
  simp only [kronecker_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · have : ¬(((finProdEquiv d₁ d₂).symm i).1 = ((finProdEquiv d₁ d₂).symm j).1 ∧
      ((finProdEquiv d₁ d₂).symm i).2 = ((finProdEquiv d₁ d₂).symm j).2) := by
      intro ⟨h1, h2⟩
      exact h ((finProdEquiv d₁ d₂).symm.injective (Prod.ext h1 h2))
    rcases not_and_or.mp this with h1 | h2
    · simp [h, h1]
    · simp [h, h2]

end Swap

end CatCrypt.Quantum.QROM
