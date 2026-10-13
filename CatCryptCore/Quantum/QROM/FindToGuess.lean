/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.QuantumOWCPA
public import CatCryptCore.Quantum.QROM.PermUnitaryCore

/-!
# Search in a semi-classical oracle: `Pr[Find]` against the guessing adversary

The `Find` probability of the semi-classical run is at most `4` times the
probability that the query register of the plain run, measured before a
uniformly chosen query, lies in the punctured set (Ambainis–Hamburg–Unruh,
CRYPTO 2019, Theorem 2). The proof is the potential argument of that paper:
with `Ψ'_i` the plain state and `Ψ_i` the `Find = false` state before query
`i`, the potential `3 ‖Ψ'_i‖² − 4 Re⟨Ψ'_i, Ψ_i⟩ + ‖Ψ_i‖²` starts at `0`, grows
by at most `4 ‖Π U_i Ψ'_i‖²` at each query, and dominates
`‖Ψ'_i‖² − ‖Ψ_i‖²`, which at the end is `Pr[Find]`.

For the T transform this bounds `tFind` by the quantum OW-CPA advantage of the
adversary that runs `A` up to a uniformly chosen query, swaps the query
register into the output register, and outputs it.

## Main definitions

* `pot a b` — the potential `3 ‖a‖² − 4 Re⟨a, b⟩ + ‖b‖²`
* `prefixU A H j`, `plainState A H ψ` — the operator of the plain run up to
  and including `U_j`, and the plain states before each query
* `prefixAdv A H S j`, `guessProb A H S j` — the `0`-query adversary that runs
  the prefix and measures `projS S`, and its acceptance probability
* `swapXO m n w`, `swapU m n w` — the permutation exchanging the query
  factor `Fin m` with the output factor `Fin m` of the work register, and its
  unitary
* `guessReduction eM eR A` — the `QOWAdv` with coins `Fin q × (Fin m → Fin n)`
  that runs the prefix of `A` to a uniform query and swaps the query register
  into the output register

## Main results

* `pot_chainOp_le` — the potential grows by at most `4 ∑ᵢ ‖Π θ'ᵢ‖²` along
  the chains
* `sum_nrm_sq_scStates_le` — `∑ᵢ ‖Π θᵢ‖² ≤ 4 ∑ᵢ ‖Π θ'ᵢ‖²` for the projected
  and the plain intermediate states
* `prFind_le_four_sum_guess` — `Pr[Find] ≤ 4 ∑ⱼ guessProb A H S j`
* `winProj_mul_swapU` — `winProj t * swapU = swapU * projS {t}`
* `prOut_guessReduction` — the reduction at `(j, G)` wins with `guessProb` of
  `A` against `G` at `{t}` and `j`
* `tFind_le_qOwcpa` — `tFind P A ≤ 4 q · qOwcpaAdvantage P (guessReduction A)`
* `tOw_le_qOwcpa_two` — the T transform in the QROM with both reductions
  named

## Scope

Pure initial state, as in `O2HTheorem`. The guess reduction's coins include
the oracle table (the unbounded-adversary form, as `tReduction`). The constant
`4q` is that of Ambainis–Hamburg–Unruh, Theorem 2; `q ≠ 0` is required for
the coin type of the reduction to be non-empty.

## References

* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], Theorem 2 (Lemma 7)
* [Hofheinz, Hövelmanns, Kiltz — A Modular Analysis of the Fujisaki–Okamoto
  Transformation, TCC 2017], §4.1, Theorem 4.4
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

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

theorem winProj_eq_diagonal (x : Fin m) :
    winProj m n w x = Matrix.diagonal (fun k => indS m {x} (oPart m n w k)) := by
  unfold winProj
  rw [diagonal_kronecker_one, one_kronecker_diagonal]
  rfl

/-- Conjugating the query projector by the register swap gives the output
    projector. -/
theorem swapU_conj_projS (t : Fin m) :
    (swapU m n w : Matrix (Fin (m * n * (m * w))) (Fin (m * n * (m * w))) ℂ) *
        projS m n (m * w) {t} *
        (swapU m n w : Matrix (Fin (m * n * (m * w))) (Fin (m * n * (m * w))) ℂ)ᴴ =
      winProj m n w t := by
  rw [projS_eq_diagonal, swapU, permUnitary_conj_diagonal, winProj_eq_diagonal]
  congr 1
  funext k
  rw [← oPart_swapPerm m n w ((swapPerm m n w).symm k)]
  simp

/-- `winProj t * swapU = swapU * projS {t}`: the swap carries the query
    projector to the output projector. -/
theorem winProj_mul_swapU (t : Fin m) :
    winProj m n w t * (swapU m n w : Matrix _ _ ℂ) =
      (swapU m n w : Matrix _ _ ℂ) * projS m n (m * w) {t} := by
  rw [← swapU_conj_projS m n w t, Matrix.mul_assoc, Matrix.mul_assoc, swapU,
    star_permUnitary_mul (swapPerm m n w), Matrix.mul_one]

end Swap

/-! ## The guessing reduction -/

section Reduction

variable {m n w q : ℕ} {PK SK M C R : Type} [Fintype PK] [Fintype SK] [Fintype M] [Fintype R]
  [Nonempty M] [Nonempty R] (P : Scheme PK SK M C R) (eM : M ≃ Fin m) (eR : R ≃ Fin n) [NeZero n]

/-- The `0`-query adversary at coins `(j, G)`: the prefix of `A.run pk c t` up
    to query `j` against `G`, then the swap of the query factor into the output
    factor, measured by `winProj t`. -/
def guessRun (A : TAdv m n w q PK C) (j : Fin q) (G : Fin m → Fin n) (pk : PK) (c : C)
    (t : Fin m) : QAdv m n (m * w) 0 where
  U _ := swapU m n w * prefixU (A.run pk c t) G j
  init := (A.run pk c t).init
  final := winProj m n w t
  final_conjTranspose := winProj_conjTranspose m n w t
  final_mul_self := winProj_mul_self m n w t

omit [Fintype PK] in
/-- The guessing adversary at `(j, G)` wins with the probability that the query
    register of the plain run of `A` against `G` lies in `{t}` before query
    `j`, whatever oracle it is run against. -/
theorem prOut_guessRun (A : TAdv m n w q PK C) (j : Fin q) (G H : Fin m → Fin n) (pk : PK)
    (c : C) (t : Fin m) :
    prOut (guessRun A j G pk c t) H = guessProb (A.run pk c t) G {t} j := by
  unfold guessProb prOut prTrue_Q
  rw [run_branch_true, run_branch_true, runOp_zero, runOp_zero]
  simp only [guessRun, prefixAdv, Submonoid.coe_mul]
  have hsw : winProj m n w t * ((swapU m n w : Matrix _ _ ℂ) * (prefixU (A.run pk c t) G j :
      Matrix _ _ ℂ)) = (swapU m n w : Matrix _ _ ℂ) * (projS m n (m * w) {t} *
      (prefixU (A.run pk c t) G j : Matrix _ _ ℂ)) := by
    rw [← Matrix.mul_assoc, winProj_mul_swapU, Matrix.mul_assoc]
  rw [hsw]
  have key : ∀ Y : Matrix (Fin (m * n * (m * w))) (Fin (m * n * (m * w))) ℂ,
      ((swapU m n w : Matrix _ _ ℂ) * Y) * (A.run pk c t).init.val *
        ((swapU m n w : Matrix _ _ ℂ) * Y)ᴴ =
      (swapU m n w : Matrix _ _ ℂ) * (Y * (A.run pk c t).init.val * Yᴴ) *
        (swapU m n w : Matrix _ _ ℂ)ᴴ := by
    intro Y
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [key, trace_mul_mul_conjTranspose_of_mem_unitaryGroup (swapU m n w).prop]

/-- `tFind` is the average over `((pk, sk), m*, r, G)` of the `Find` probability
    of `A.run pk (enc pk m* r) m*` against `G` at `{m*}`: the oracle at `m*`
    is independent of the challenge coins. -/
theorem tFind_eq (A : TAdv m n w q PK C) :
    tFind P eM eR A =
      ∑ i : TInput PK SK M R m n,
        tSample P i * prFind (A.run i.1.1 (P.enc i.1.1 i.2.1 i.2.2.1) (eM i.2.1)) i.2.2.2
          {eM i.2.1} := by
  simp only [tFind, prFindAvg, tGame, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun pk _ => Finset.sum_congr rfl fun sk _ =>
    Finset.sum_congr rfl fun x _ => ?_
  refine (Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun G _ => ?_).trans
    (sum_swapAt eR (eM x) (fun r G => tSample P (((pk, sk), x, r, G) : TInput PK SK M R m n) *
      prFind (A.run pk (P.enc pk x r) (eM x)) G {eM x}))
  obtain ⟨ψ, hψ⟩ := A.pure pk (P.enc pk x (eR.symm (G (eM x)))) (eM x)
  show _ = tSample P (((pk, sk), x, eR.symm (G (eM x)), Function.update G (eM x) (eR r)) :
      TInput PK SK M R m n) * prFind (A.run pk (P.enc pk x (eR.symm (G (eM x)))) (eM x))
      (Function.update G (eM x) (eR r)) {eM x}
  rw [prFind_congr _ G (Function.update G (eM x) (eR r)) {eM x}
    (fun y hy => (Function.update_of_ne (by simpa using hy) _ _).symm) hψ]
  rfl

variable [NeZero q]

omit [Nonempty M] [NeZero n] in
include eM eR in
/-- The uniform weight on `Fin q × (Fin m → Fin n)` sums to one. -/
theorem sum_guess_weight :
    ∑ _p : Fin q × (Fin m → Fin n),
      (q : ℝ≥0∞)⁻¹ * ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹ = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum]
  rw [sum_card_pow_inv (M := M) (R := R) eM eR, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast NeZero.ne q) (ENNReal.natCast_ne_top q)

/-- The reduction from a `TAdv` to a `QOWAdv` that guesses the found query: the
    coins are a uniform query index `j` and a uniform oracle table `G`, and the
    adversary at `(j, G)` is `guessRun A j G`. -/
def guessReduction (A : TAdv m n w q PK C) : QOWAdv m n w PK C where
  Coins := Fin q × (Fin m → Fin n)
  weight _ := (q : ℝ≥0∞)⁻¹ * ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹
  weight_sum := sum_guess_weight eM eR
  run p pk c t := guessRun A p.1 p.2 pk c t
  final_eq _ _ _ _ := rfl
  pure _ pk c t := A.pure pk c t

/-- `q · (q⁻¹ · s) = s` in `ℝ≥0∞` for `q ≠ 0`. -/
theorem natCast_mul_inv_mul (s : ℝ≥0∞) : (q : ℝ≥0∞) * ((q : ℝ≥0∞)⁻¹ * s) = s := by
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast NeZero.ne q)
    (ENNReal.natCast_ne_top q), one_mul]

omit [Nonempty M] in
/-- The quantum OW-CPA game against the guessing reduction, as a sum over the
    key pair, the message, the coins, the query index and the oracle table. -/
theorem qOwcpaAdvantage_guessReduction (A : TAdv m n w q PK C) :
    qOwcpaAdvantage P eM (guessReduction eM eR A) =
      ∑ ks : PK × SK, ∑ x : M, ∑ r : R, ∑ j : Fin q, ∑ G : Fin m → Fin n,
        P.keygen ks * (Fintype.card M : ℝ≥0∞)⁻¹ * (Fintype.card R : ℝ≥0∞)⁻¹ *
          ((q : ℝ≥0∞)⁻¹ * ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹) *
          guessProb (A.run ks.1 (P.enc ks.1 x r) (eM x)) G {eM x} j := by
  unfold qOwcpaAdvantage
  refine Finset.sum_congr rfl fun ks _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun r _ => ?_
  refine (Fintype.sum_equiv (Equiv.refl _) _
    (fun p : Fin q × (Fin m → Fin n) =>
      P.keygen ks * (Fintype.card M : ℝ≥0∞)⁻¹ * (Fintype.card R : ℝ≥0∞)⁻¹ *
        ((q : ℝ≥0∞)⁻¹ * ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹) *
        guessProb (A.run ks.1 (P.enc ks.1 x r) (eM x)) p.2 {eM x} p.1)
    fun p => by simp only [guessReduction, prOut_guessRun, Equiv.refl_apply]).trans
    (Fintype.sum_prod_type' fun j G =>
      P.keygen ks * (Fintype.card M : ℝ≥0∞)⁻¹ * (Fintype.card R : ℝ≥0∞)⁻¹ *
        ((q : ℝ≥0∞)⁻¹ * ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹) *
        guessProb (A.run ks.1 (P.enc ks.1 x r) (eM x)) G {eM x} j)

/-- Theorem 2 of Ambainis–Hamburg–Unruh for the T transform:
    `tFind P A ≤ 4 q · qOwcpaAdvantage P (guessReduction A)`. -/
theorem tFind_le_qOwcpa (A : TAdv m n w q PK C) :
    tFind P eM eR A ≤ 4 * q * qOwcpaAdvantage P eM (guessReduction eM eR A) := by
  rw [tFind_eq, qOwcpaAdvantage_guessReduction]
  simp only [Fintype.sum_prod_type, tSample, Finset.mul_sum]
  refine Finset.sum_le_sum fun pk _ => Finset.sum_le_sum fun sk _ =>
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun r _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun G _ => ?_
  obtain ⟨ψ, hψ⟩ := A.pure pk (P.enc pk x r) (eM x)
  calc P.keygen (pk, sk) * (Fintype.card M : ℝ≥0∞)⁻¹ * (Fintype.card R : ℝ≥0∞)⁻¹ *
        ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹ *
        prFind (A.run pk (P.enc pk x r) (eM x)) G {eM x}
      ≤ P.keygen (pk, sk) * (Fintype.card M : ℝ≥0∞)⁻¹ * (Fintype.card R : ℝ≥0∞)⁻¹ *
        ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹ *
        (4 * ∑ j, guessProb (A.run pk (P.enc pk x r) (eM x)) G {eM x} j) := by
        gcongr
        exact prFind_le_four_sum_guess _ G {eM x} hψ
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show 4 * (q : ℝ≥0∞) * (P.keygen (pk, sk) * (Fintype.card M : ℝ≥0∞)⁻¹ *
            (Fintype.card R : ℝ≥0∞)⁻¹ * ((q : ℝ≥0∞)⁻¹ *
            ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹) *
            guessProb (A.run pk (P.enc pk x r) (eM x)) G {eM x} j) =
          (q : ℝ≥0∞) * ((q : ℝ≥0∞)⁻¹ * (P.keygen (pk, sk) * (Fintype.card M : ℝ≥0∞)⁻¹ *
            (Fintype.card R : ℝ≥0∞)⁻¹ * ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹ *
            (4 * guessProb (A.run pk (P.enc pk x r) (eM x)) G {eM x} j))) by ring,
          natCast_mul_inv_mul]

/-- The T transform in the QROM with both reductions named (Theorem 4.4 of
    Hofheinz–Hövelmanns–Kiltz with the `Find` term bounded by Theorem 2 of
    Ambainis–Hamburg–Unruh):
    `tOwAdvantage ≤ qOwcpaAdvantage (tReduction A) + 4 √(q · 4q · qOwcpaAdvantage (guessReduction A))`. -/
theorem tOw_le_qOwcpa_two (A : TAdv m n w q PK C) :
    tOwAdvantage P eM eR A ≤
      qOwcpaAdvantage P eM (tReduction eM eR A) +
        4 * ((q : ℝ≥0∞) * (4 * q * qOwcpaAdvantage P eM (guessReduction eM eR A))) ^
          (1 / 2 : ℝ) := by
  refine (tOw_le_qOwcpa_add_find P eM eR A).trans ?_
  have := tFind_le_qOwcpa P eM eR A
  gcongr

end Reduction

end CatCrypt.Quantum.QROM
