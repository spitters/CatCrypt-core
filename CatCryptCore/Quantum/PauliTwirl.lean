/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import QuantumFoundations.MatrixMap

/-!
# The Pauli twirl

Averaging the conjugation `X ↦ (1 ⊗ P) X (1 ⊗ P)ᴴ` over the `4ⁿ` Pauli operators `P` of an
`n`-qubit register `Q`, with an arbitrary reference register `R`, gives

`4⁻ⁿ ∑ P, (1 ⊗ P) X (1 ⊗ P)ᴴ = tr_Q X ⊗ 2⁻ⁿ • 1`,

where `tr_Q` is `MatrixMap.traceRight R Q` of QuantumFoundations. This is the security
identity of the quantum one-time pad (Ambainis–Mosca–Tapp–de Wolf, FOCS 2000; Boykin and
Roychowdhury, PRA 67, 2003).

The argument is entrywise. A family `U : K → Matrix Q Q ℂ` is a twirling family of weight `m`
(`IsTwirlFamily U m`) if `∑ c, U c i j * conj (U c i' j') = m` for `i = i'`, `j = j'`, and `0`
otherwise. Every twirling family twirls a reference-extended operator onto its partial trace
(`IsTwirlFamily.twirl_ref`). The four one-qubit Pauli operators form a twirling family of
weight `2` (`isTwirlFamily_pauli`), and entrywise products of twirling families over a finite
index type `ι` form a twirling family on `ι → Q` (`IsTwirlFamily.piOp`), which gives the
`n`-qubit Pauli operators `pauliN` and their twirl.

## Main definitions

* `IsTwirlFamily U m`: the entrywise twirling condition.
* `piOp U k`: the operator `⊗ₗ U (k l)` on `ι → Q`, entry `∏ l, U (k l) (i l) (j l)`.
* `pauli a b`: the one-qubit Pauli operator `X^a Z^b`.
* `pauliN k`: the `n`-qubit Pauli operator `⊗ₗ X^(a l) Z^(b l)` for `k l = (a l, b l)`.

## Main results

* `IsTwirlFamily.twirl`, `IsTwirlFamily.twirl_ref`: the twirl of a family without and with a
  reference register.
* `pauli_twirl`: `∑ a, ∑ b, P_ab M P_abᴴ = 2 tr M • 1`.
* `pauli_twirl_ref`: `4⁻¹ ∑ P, (1 ⊗ P) X (1 ⊗ P)ᴴ = tr_Q X ⊗ 2⁻¹ • 1`.
* `pauliN_twirl_ref`: `4⁻ⁿ ∑ P, (1 ⊗ P) X (1 ⊗ P)ᴴ = tr_Q X ⊗ 2⁻ⁿ • 1` for `n` qubits.
* `pauliN_mul_conjTranspose`, `conjTranspose_mul_pauliN`: each `n`-qubit Pauli operator is
  unitary, so decryption `ρ ↦ Pᴴ ρ P` inverts encryption `ρ ↦ P ρ Pᴴ`
  (`pauliN_decrypt_encrypt`).
-/

@[expose] public section

set_option autoImplicit false

open Matrix Quantum
open scoped Matrix Kronecker

namespace CatCrypt.Quantum.PauliTwirl

/-! ## Twirling families -/

section Family

variable {Q K : Type*} [Fintype Q] [DecidableEq Q] [Fintype K]

omit [Fintype Q] in
/-- `U` is a twirling family of weight `m`: `∑ c, U c i j * conj (U c i' j')` is `m` when
`i = i'` and `j = j'`, and `0` otherwise. -/
def IsTwirlFamily (U : K → Matrix Q Q ℂ) (m : ℂ) : Prop :=
  ∀ i j i' j' : Q, ∑ c, U c i j * star (U c i' j') = if i = i' ∧ j = j' then m else 0

omit [DecidableEq Q] in
/-- The entry of a conjugation sum as a double sum against the family's correlation. -/
theorem sum_conj_apply (U : K → Matrix Q Q ℂ) (M : Matrix Q Q ℂ) (i i' : Q) :
    (∑ c, U c * M * (U c)ᴴ) i i' =
      ∑ j, ∑ j', M j j' * ∑ c, U c i j * star (U c i' j') := by
  simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun j' _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/-- The twirl over a twirling family of weight `m`: `∑ c, U c M (U c)ᴴ = m tr M • 1`. -/
theorem IsTwirlFamily.twirl {U : K → Matrix Q Q ℂ} {m : ℂ} (hU : IsTwirlFamily U m)
    (M : Matrix Q Q ℂ) : ∑ c, U c * M * (U c)ᴴ = (m * M.trace) • (1 : Matrix Q Q ℂ) := by
  ext i i'
  rw [sum_conj_apply]
  unfold IsTwirlFamily at hU
  simp only [hU]
  by_cases h : i = i'
  · subst h
    simp [Matrix.trace, Finset.mul_sum, mul_comm]
  · simp [h]

variable {R : Type*} [Fintype R] [DecidableEq R]

omit [DecidableEq Q] in
/-- The block `(r, r')` of `(1 ⊗ U) X (1 ⊗ U)ᴴ` is `U X_{r r'} Uᴴ`. -/
theorem one_kronecker_conj_apply (U : Matrix Q Q ℂ) (X : Matrix (R × Q) (R × Q) ℂ)
    (r r' : R) (i i' : Q) :
    (((1 : Matrix R R ℂ) ⊗ₖ U) * X * ((1 : Matrix R R ℂ) ⊗ₖ U)ᴴ) (r, i) (r', i') =
      (U * X.submatrix (r, ·) (r', ·) * Uᴴ) i i' := by
  simp only [mul_apply, kroneckerMap_apply, one_apply, ite_mul, one_mul, zero_mul,
    Fintype.sum_prod_type, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, conjTranspose_apply, RCLike.star_def, submatrix_apply,
    apply_ite (starRingEnd ℂ), map_zero, mul_ite, mul_zero]

/-- The twirl with a reference register `R`:
`∑ c, (1 ⊗ U c) X (1 ⊗ U c)ᴴ = m • (tr_Q X ⊗ 1)`. -/
theorem IsTwirlFamily.twirl_ref {U : K → Matrix Q Q ℂ} {m : ℂ} (hU : IsTwirlFamily U m)
    (X : Matrix (R × Q) (R × Q) ℂ) :
    ∑ c, ((1 : Matrix R R ℂ) ⊗ₖ U c) * X * ((1 : Matrix R R ℂ) ⊗ₖ U c)ᴴ =
      m • (MatrixMap.traceRight R Q X ⊗ₖ (1 : Matrix Q Q ℂ)) := by
  ext ⟨r, i⟩ ⟨r', i'⟩
  have h := congrFun (congrFun (hU.twirl (X.submatrix (r, ·) (r', ·))) i) i'
  rw [Matrix.sum_apply]
  simp only [one_kronecker_conj_apply]
  rw [← Matrix.sum_apply, h]
  simp [Matrix.trace, mul_assoc]

end Family

/-! ## Products of twirling families -/

section Pi

variable {Q K ι : Type*} [Fintype ι]

/-- The tensor product `⊗ₗ U (k l)` over a finite index type, as an operator on `ι → Q`:
entry `(i, j)` is `∏ l, U (k l) (i l) (j l)`. -/
def piOp (U : K → Matrix Q Q ℂ) (k : ι → K) : Matrix (ι → Q) (ι → Q) ℂ :=
  Matrix.of fun i j => ∏ l, U (k l) (i l) (j l)

@[simp]
theorem piOp_apply (U : K → Matrix Q Q ℂ) (k : ι → K) (i j : ι → Q) :
    piOp U k i j = ∏ l, U (k l) (i l) (j l) :=
  rfl

variable [Fintype Q] [DecidableEq Q] [DecidableEq ι]

omit [Fintype Q] in
/-- The tensor power of a twirling family of weight `m` is a twirling family of weight
`m ^ card ι`. -/
theorem IsTwirlFamily.piOp [Fintype K] {U : K → Matrix Q Q ℂ} {m : ℂ}
    (hU : IsTwirlFamily U m) :
    IsTwirlFamily (PauliTwirl.piOp (ι := ι) U) (m ^ Fintype.card ι) := by
  intro i j i' j'
  simp only [piOp_apply, star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun l c => U c (i l) (j l) * star (U c (i' l) (j' l)))]
  unfold IsTwirlFamily at hU
  simp only [hU]
  rw [Finset.prod_ite_zero]
  simp [funext_iff, forall_and]

/-- A tensor product of unitaries is unitary. -/
theorem piOp_mul_conjTranspose {U : K → Matrix Q Q ℂ} (hU : ∀ c, U c * (U c)ᴴ = 1)
    (k : ι → K) : PauliTwirl.piOp U k * (PauliTwirl.piOp U k)ᴴ = 1 := by
  ext i i'
  have h (l : ι) : ∑ q, U (k l) (i l) q * star (U (k l) (i' l) q) =
      if i l = i' l then 1 else 0 := by
    simpa [mul_apply, one_apply] using congrFun (congrFun (hU (k l)) (i l)) (i' l)
  simp only [mul_apply, conjTranspose_apply, piOp_apply, star_prod,
    ← Finset.prod_mul_distrib, one_apply]
  rw [← Fintype.prod_sum (fun l q => U (k l) (i l) q * star (U (k l) (i' l) q))]
  simp only [h]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

/-- A tensor product of unitaries is unitary. -/
theorem conjTranspose_mul_piOp {U : K → Matrix Q Q ℂ} (hU : ∀ c, (U c)ᴴ * U c = 1)
    (k : ι → K) : (PauliTwirl.piOp U k)ᴴ * PauliTwirl.piOp U k = 1 := by
  ext i i'
  have h (l : ι) : ∑ q, star (U (k l) q (i l)) * U (k l) q (i' l) =
      if i l = i' l then 1 else 0 := by
    simpa [mul_apply, one_apply] using congrFun (congrFun (hU (k l)) (i l)) (i' l)
  simp only [mul_apply, conjTranspose_apply, piOp_apply, star_prod,
    ← Finset.prod_mul_distrib, one_apply]
  rw [← Fintype.prod_sum (fun l q => star (U (k l) q (i l)) * U (k l) q (i' l))]
  simp only [h]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

end Pi

/-! ## Pauli operators -/

/-- The one-qubit Pauli operator `X^a Z^b`: entry `(i, j)` is `(-1)^(b j)` if `i = j + a` and
`0` otherwise. -/
def pauli (a b : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => if i = j + a then (-1) ^ (b.val * j.val) else 0

/-- The four one-qubit Pauli operators form a twirling family of weight `2`. -/
theorem isTwirlFamily_pauli : IsTwirlFamily (fun c : Fin 2 × Fin 2 => pauli c.1 c.2) 2 := by
  intro i j i' j'
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [pauli, Fintype.sum_prod_type, Fin.sum_univ_two] <;> norm_num

/-- `X^a Z^b` is unitary. -/
theorem pauli_mul_conjTranspose (a b : Fin 2) : pauli a b * (pauli a b)ᴴ = 1 := by
  ext i i'
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases i' <;>
    simp [pauli, mul_apply, one_apply]

/-- `X^a Z^b` is unitary. -/
theorem conjTranspose_mul_pauli (a b : Fin 2) : (pauli a b)ᴴ * pauli a b = 1 := by
  ext i i'
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases i' <;>
    simp [pauli, mul_apply, one_apply]

/-- The one-qubit Pauli twirl: `∑ a, ∑ b, X^a Z^b M (X^a Z^b)ᴴ = 2 tr M • 1`. -/
theorem pauli_twirl (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ a : Fin 2, ∑ b : Fin 2, pauli a b * M * (pauli a b)ᴴ =
      (2 : ℂ) • M.trace • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [← Fintype.sum_prod_type' (f := fun a b => pauli a b * M * (pauli a b)ᴴ),
    isTwirlFamily_pauli.twirl, smul_smul]

/-- The one-qubit Pauli twirl with a reference register `R`:
`4⁻¹ ∑ P, (1 ⊗ P) X (1 ⊗ P)ᴴ = tr_Q X ⊗ 2⁻¹ • 1`. -/
theorem pauli_twirl_ref {R : Type*} [Fintype R] [DecidableEq R]
    (X : Matrix (R × Fin 2) (R × Fin 2) ℂ) :
    (4 : ℂ)⁻¹ • ∑ c : Fin 2 × Fin 2,
        ((1 : Matrix R R ℂ) ⊗ₖ pauli c.1 c.2) * X * ((1 : Matrix R R ℂ) ⊗ₖ pauli c.1 c.2)ᴴ =
      MatrixMap.traceRight R (Fin 2) X ⊗ₖ ((2 : ℂ)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [isTwirlFamily_pauli.twirl_ref, smul_smul, kronecker_smul]
  norm_num

/-! ## `n`-qubit Pauli operators -/

/-- The `n`-qubit Pauli operator `⊗ₗ X^(a l) Z^(b l)` for the key `k l = (a l, b l)`, acting on
the register `Fin n → Fin 2`. -/
def pauliN {n : ℕ} (k : Fin n → Fin 2 × Fin 2) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  piOp (fun c : Fin 2 × Fin 2 => pauli c.1 c.2) k

/-- The `4ⁿ` Pauli operators on `n` qubits form a twirling family of weight `2ⁿ`. -/
theorem isTwirlFamily_pauliN (n : ℕ) : IsTwirlFamily (pauliN (n := n)) (2 ^ n) := by
  have h := isTwirlFamily_pauli.piOp (ι := Fin n)
  rwa [Fintype.card_fin] at h

/-- Each `n`-qubit Pauli operator is unitary. -/
theorem pauliN_mul_conjTranspose {n : ℕ} (k : Fin n → Fin 2 × Fin 2) :
    pauliN k * (pauliN k)ᴴ = 1 := by
  unfold pauliN
  exact piOp_mul_conjTranspose (U := fun c : Fin 2 × Fin 2 => pauli c.1 c.2)
    (fun c => pauli_mul_conjTranspose c.1 c.2) k

/-- Each `n`-qubit Pauli operator is unitary. -/
theorem conjTranspose_mul_pauliN {n : ℕ} (k : Fin n → Fin 2 × Fin 2) :
    (pauliN k)ᴴ * pauliN k = 1 := by
  unfold pauliN
  exact conjTranspose_mul_piOp (U := fun c : Fin 2 × Fin 2 => pauli c.1 c.2)
    (fun c => conjTranspose_mul_pauli c.1 c.2) k

/-- Correctness of the quantum one-time pad: decryption with the key `k` inverts encryption
with `k`. -/
theorem pauliN_decrypt_encrypt {n : ℕ} (k : Fin n → Fin 2 × Fin 2)
    (ρ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    (pauliN k)ᴴ * (pauliN k * ρ * (pauliN k)ᴴ) * pauliN k = ρ := by
  simp only [← mul_assoc, conjTranspose_mul_pauliN, one_mul]
  rw [mul_assoc, conjTranspose_mul_pauliN, mul_one]

/-- The `n`-qubit Pauli twirl: `4⁻ⁿ ∑ P, P M Pᴴ = 2⁻ⁿ tr M • 1`. -/
theorem pauliN_twirl {n : ℕ} (M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    (4 : ℂ)⁻¹ ^ n • ∑ k, pauliN k * M * (pauliN k)ᴴ =
      ((2 : ℂ)⁻¹ ^ n * M.trace) • (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) := by
  rw [(isTwirlFamily_pauliN n).twirl, smul_smul, ← mul_assoc, ← mul_pow]
  norm_num

/-- The `n`-qubit Pauli twirl with a reference register `R`:
`4⁻ⁿ ∑ P, (1 ⊗ P) X (1 ⊗ P)ᴴ = tr_Q X ⊗ 2⁻ⁿ • 1`. -/
theorem pauliN_twirl_ref {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (X : Matrix (R × (Fin n → Fin 2)) (R × (Fin n → Fin 2)) ℂ) :
    (4 : ℂ)⁻¹ ^ n •
        ∑ k, ((1 : Matrix R R ℂ) ⊗ₖ pauliN k) * X * ((1 : Matrix R R ℂ) ⊗ₖ pauliN k)ᴴ =
      MatrixMap.traceRight R (Fin n → Fin 2) X ⊗ₖ
        ((2 : ℂ)⁻¹ ^ n • (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)) := by
  rw [(isTwirlFamily_pauliN n).twirl_ref, smul_smul, kronecker_smul, ← mul_pow]
  norm_num

/-! ## Reindexing along an equivalence of registers -/

/-- Reindexing every operator of a twirling family along an equivalence of registers gives a
twirling family of the same weight. -/
theorem IsTwirlFamily.submatrix {Q Q' K : Type*} [DecidableEq Q] [DecidableEq Q']
    [Fintype K] {U : K → Matrix Q Q ℂ} {m : ℂ} (hU : IsTwirlFamily U m) (e : Q' ≃ Q) :
    IsTwirlFamily (fun c => (U c).submatrix e e) m := by
  intro i j i' j'
  simp only [submatrix_apply, hU (e i) (e j) (e i') (e j'), e.injective.eq_iff]

/-- The `n`-qubit Pauli operator `pauliN k` on the register `Fin (2 ^ n)`, through the
equivalence `Fin (2 ^ n) ≃ (Fin n → Fin 2)` of `finFunctionFinEquiv`. -/
def pauliFin {n : ℕ} (k : Fin n → Fin 2 × Fin 2) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (pauliN k).submatrix finFunctionFinEquiv.symm finFunctionFinEquiv.symm

/-- The Pauli operators on `Fin (2 ^ n)` form a twirling family of weight `2ⁿ`. -/
theorem isTwirlFamily_pauliFin (n : ℕ) : IsTwirlFamily (pauliFin (n := n)) (2 ^ n) :=
  (isTwirlFamily_pauliN n).submatrix finFunctionFinEquiv.symm

/-- Each Pauli operator on `Fin (2 ^ n)` is unitary. -/
theorem pauliFin_mul_conjTranspose {n : ℕ} (k : Fin n → Fin 2 × Fin 2) :
    pauliFin k * (pauliFin k)ᴴ = 1 := by
  rw [pauliFin, conjTranspose_submatrix, submatrix_mul_equiv, pauliN_mul_conjTranspose,
    submatrix_one_equiv]

/-- Each Pauli operator on `Fin (2 ^ n)` is unitary. -/
theorem conjTranspose_mul_pauliFin {n : ℕ} (k : Fin n → Fin 2 × Fin 2) :
    (pauliFin k)ᴴ * pauliFin k = 1 := by
  rw [pauliFin, conjTranspose_submatrix, submatrix_mul_equiv, conjTranspose_mul_pauliN,
    submatrix_one_equiv]

/-- The `n`-qubit Pauli twirl on `Fin (2 ^ n)`: `4⁻ⁿ ∑ P, P M Pᴴ = 2⁻ⁿ tr M • 1`. -/
theorem pauliFin_twirl {n : ℕ} (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    (4 : ℂ)⁻¹ ^ n • ∑ k, pauliFin k * M * (pauliFin k)ᴴ =
      ((2 : ℂ)⁻¹ ^ n * M.trace) • (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) := by
  rw [(isTwirlFamily_pauliFin n).twirl, smul_smul, ← mul_assoc, ← mul_pow]
  norm_num

end CatCrypt.Quantum.PauliTwirl
