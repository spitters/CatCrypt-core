/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.O2HTheorem
public import CatCryptCore.Quantum.KroneckerPSD

/-!
# One-way-to-hiding for adversaries with classical rounds

A multi-round adversary interleaves segments of quantum oracle queries with
classical rounds: a projective measurement of the register, a classical
function of the outcome, and a unitary writing the answer back. Deferred
measurement turns every round into a unitary on the register extended by an
ancilla that records the outcome, so a multi-round adversary is a single-run
`QAdv` on the extended register, and the one-way-to-hiding bound `o2h` of
`O2HTheorem` transfers.

## Main definitions

* `ClassicalRound d c a` — the projectors `P y`, orthogonal and summing to `1`,
  and the answer unitaries `ans z`
* `roundQ R f`, `roundU R f` — the round instrument `ρ ↦ ans (f y) P y ρ P y ans (f y)ᴴ`
  with outcome `y`, and the same with the outcome discarded
* `kr e A B` — the Kronecker product `A ⊗ₖ B` transported along an index
  equivalence `e : Fin (d * c) ≃ Fin d'`
* `ancProj y`, `ancShift y`, `ancUnit y y'` — the ancilla projector `|y⟩⟨y|`, the
  cyclic shift `|j⟩ ↦ |j + y⟩`, and the unit matrix `|y⟩⟨y'|`
* `roundV e R f` — the deferred round: record the outcome on the ancilla,
  then apply the answer controlled on the ancilla
* `mrChainSC O f k head tail R` — the multi-round chain over a `Bool`-valued
  oracle, `head`, then `k` times a round followed by a segment
* `QAdvMR m n w q k c a` — `k + 1` segments of `q` queries, `k` rounds, an
  initial state and a final projector
* `runMR`, `runSCMR`, `prOutMR`, `prFindMR` — the two runs and the two probabilities
* `MRH`, `peel`, `flatten`, `toQAdv` — the deferred-measurement embedding into `QAdv`

## Main results

* `roundV_mul_kr_ancProj_zero` — the deferred round on `σ ⊗ |0⟩⟨0|` is the block
  sum `∑ y y', (ans (f y) P y σ P y' ans (f y')ᴴ) ⊗ |y⟩⟨y'|`
* `trace_kr_one_mul_sum` — `tr ((X ⊗ 1) ∑ y y', B y y' ⊗ |y⟩⟨y'|) = ∑ y, tr (X B y y)`
* `trace_flatten` — the deferred single run and the multi-round run agree on
  every observable `X ⊗ 1` and every branch
* `prOutMR_eq`, `prFindMR_eq`, `prOutNoFindMR_eq` — the probabilities of output,
  Find, and output without Find of a multi-round adversary are those of its `toQAdv`
* `pure_toQAdv` — a rank-one initial state stays rank one
* `o2h_MR`, `o2h_extraction_MR` — the one-way-to-hiding bound for multi-round
  adversaries, with the query count of `toQAdv`

## The model

Rounds are classical in the outcome and in the answer: the outcome is a
projective measurement result `y : Fin c`, the answer is `f y : Fin a` written
by a fixed unitary. The classical function `f` is the same in every round and
depends only on the outcome. The ancilla register `Fin c` per round is a proof device:
`runMR` never allocates it, only `toQAdv` does. The query count of `toQAdv` is
`flatQ q k q`, which is `(k + 1) * q` written as `q + (q + ⋯ + q)`, and its work
register is `ancW c k w`, which is `w * c ^ k` written as `(⋯((w * c) * c)⋯) * c`.

## References

* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], Theorem 1
* [Nielsen, Chuang — Quantum Computation and Quantum Information], §4.4,
  the deferred measurement principle
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix Classical CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
  CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.Measurement

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Classical rounds -/

section Round

variable {d c a : ℕ}

/-- A classical round on a register of dimension `d`: a projective measurement
    with outcomes in `Fin c` and an answer unitary for each answer in `Fin a`. -/
structure ClassicalRound (d c a : ℕ) where
  /-- The measurement projectors. -/
  P : Fin c → Matrix (Fin d) (Fin d) ℂ
  P_conjTranspose : ∀ y, (P y)ᴴ = P y
  P_mul_self : ∀ y, P y * P y = P y
  P_orth : ∀ y y', y ≠ y' → P y * P y' = 0
  P_sum : ∑ y, P y = 1
  /-- The answer unitaries. -/
  ans : Fin a → Matrix.unitaryGroup (Fin d) ℂ

/-- The Kraus operators `ans (f y) P y` of a round with classical function `f`. -/
def ClassicalRound.ops (R : ClassicalRound d c a) (f : Fin c → Fin a) :
    MeasurementOps d (Fin c) where
  op y := (R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y
  completeness := by
    have h : ∀ y, ((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y)ᴴ *
        ((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y) = R.P y := by
      intro y
      rw [conjTranspose_mul, R.P_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (R.P y),
        ← star_eq_conjTranspose, UnitaryGroup.star_mul_self, one_mul, R.P_mul_self]
    simp only [h, R.P_sum]

/-- The round instrument: branch `y` is `ρ ↦ ans (f y) P y ρ P y ans (f y)ᴴ`. -/
def roundQ (R : ClassicalRound d c a) (f : Fin c → Fin a) : QComp d (Fin c) :=
  measureOps (R.ops f)

theorem roundQ_branch (R : ClassicalRound d c a) (f : Fin c → Fin a) (y : Fin c)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (roundQ R f).branch y ρ =
      ((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y) * ρ *
        ((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y)ᴴ := rfl

/-- The round with its outcome discarded. -/
def roundU (R : ClassicalRound d c a) (f : Fin c → Fin a) : QComp d Unit :=
  QComp.qbind (roundQ R f) fun _ => QComp.qpure ()

theorem roundU_branch (R : ClassicalRound d c a) (f : Fin c → Fin a)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (roundU R f).branch () ρ =
      ∑ y, ((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y) * ρ *
        ((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y)ᴴ := by
  unfold roundU
  rw [qbind_branch_apply, tsum_fintype]
  simp only [qpure_branch_apply, ite_true, roundQ_branch]

end Round

/-! ## The Kronecker product along an index equivalence -/

section Kr

variable {d c d' : ℕ}

/-- `A ⊗ₖ B` transported along `e : Fin (d * c) ≃ Fin d'`. -/
def kr (e : Fin (d * c) ≃ Fin d') (A : Matrix (Fin d) (Fin d) ℂ)
    (B : Matrix (Fin c) (Fin c) ℂ) : Matrix (Fin d') (Fin d') ℂ :=
  (A ⊗ₖ B).submatrix e.symm e.symm

theorem kr_mul (e : Fin (d * c) ≃ Fin d') (A C : Matrix (Fin d) (Fin d) ℂ)
    (B D : Matrix (Fin c) (Fin c) ℂ) :
    kr e A B * kr e C D = kr e (A * C) (B * D) := by
  unfold kr
  rw [Matrix.submatrix_mul_equiv, kronecker_mul_kronecker]

theorem kr_conjTranspose (e : Fin (d * c) ≃ Fin d') (A : Matrix (Fin d) (Fin d) ℂ)
    (B : Matrix (Fin c) (Fin c) ℂ) : (kr e A B)ᴴ = kr e Aᴴ Bᴴ := by
  unfold kr
  rw [conjTranspose_submatrix, conjTranspose_kronecker]

theorem kr_one (e : Fin (d * c) ≃ Fin d') : kr e (1 : Matrix (Fin d) (Fin d) ℂ) 1 = 1 := by
  unfold kr
  rw [kronecker_one_one, Matrix.submatrix_one_equiv]

theorem kr_add_left (e : Fin (d * c) ≃ Fin d') (A A' : Matrix (Fin d) (Fin d) ℂ)
    (B : Matrix (Fin c) (Fin c) ℂ) : kr e (A + A') B = kr e A B + kr e A' B := by
  ext i j; simp [kr, kronecker_apply, add_mul]

theorem kr_sub_left (e : Fin (d * c) ≃ Fin d') (A A' : Matrix (Fin d) (Fin d) ℂ)
    (B : Matrix (Fin c) (Fin c) ℂ) : kr e (A - A') B = kr e A B - kr e A' B := by
  ext i j; simp [kr, kronecker_apply, sub_mul]

theorem kr_zero_left (e : Fin (d * c) ≃ Fin d') (B : Matrix (Fin c) (Fin c) ℂ) :
    kr e (0 : Matrix (Fin d) (Fin d) ℂ) B = 0 := by
  ext i j; simp [kr, kronecker_apply]

theorem kr_sum_left {ι : Type} [Fintype ι] (e : Fin (d * c) ≃ Fin d')
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (B : Matrix (Fin c) (Fin c) ℂ) :
    kr e (∑ i, A i) B = ∑ i, kr e (A i) B := by
  ext i j; simp [kr, kronecker_apply, Matrix.sum_apply, Finset.sum_mul]

theorem kr_sum_right {ι : Type} [Fintype ι] (e : Fin (d * c) ≃ Fin d')
    (A : Matrix (Fin d) (Fin d) ℂ) (B : ι → Matrix (Fin c) (Fin c) ℂ) :
    kr e A (∑ i, B i) = ∑ i, kr e A (B i) := by
  ext i j; simp [kr, kronecker_apply, Matrix.sum_apply, Finset.mul_sum]

theorem kr_zero_right (e : Fin (d * c) ≃ Fin d') (A : Matrix (Fin d) (Fin d) ℂ) :
    kr e A (0 : Matrix (Fin c) (Fin c) ℂ) = 0 := by
  ext i j; simp [kr, kronecker_apply]

/-- The trace is invariant under relabelling by an equivalence. -/
theorem trace_submatrix_equiv' {p p' : ℕ} (e : Fin p ≃ Fin p') (N : Matrix (Fin p') (Fin p') ℂ) :
    (N.submatrix e e).trace = N.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact e.sum_comp (fun j => N j j)

theorem trace_kr (e : Fin (d * c) ≃ Fin d') (A : Matrix (Fin d) (Fin d) ℂ)
    (B : Matrix (Fin c) (Fin c) ℂ) : (kr e A B).trace = A.trace * B.trace := by
  unfold kr
  rw [trace_submatrix_equiv', trace_kronecker]

theorem kr_posSemidef (e : Fin (d * c) ≃ Fin d') {A : Matrix (Fin d) (Fin d) ℂ}
    {B : Matrix (Fin c) (Fin c) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (kr e A B).PosSemidef :=
  (QHL.kronecker_posSemidef hA hB).submatrix _

theorem kr_mem_unitaryGroup (e : Fin (d * c) ≃ Fin d') {A : Matrix (Fin d) (Fin d) ℂ}
    {B : Matrix (Fin c) (Fin c) ℂ} (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin c) ℂ) : kr e A B ∈ Matrix.unitaryGroup (Fin d') ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hA hB ⊢
  rw [star_eq_conjTranspose] at hA hB ⊢
  rw [kr_conjTranspose, kr_mul, hA, hB, kr_one]

end Kr

/-! ## The ancilla register -/

section Ancilla

variable {c : ℕ}

/-- The projector `|y⟩⟨y|` on the ancilla. -/
def ancProj (y : Fin c) : Matrix (Fin c) (Fin c) ℂ := Matrix.diagonal (Pi.single y 1)

/-- The cyclic shift `|j⟩ ↦ |j + y⟩` on the ancilla. -/
def ancShift [NeZero c] (y : Fin c) : Matrix (Fin c) (Fin c) ℂ :=
  Matrix.of fun i j => if i = j + y then 1 else 0

/-- The unit matrix `|y⟩⟨y'|` on the ancilla. -/
def ancUnit (y y' : Fin c) : Matrix (Fin c) (Fin c) ℂ :=
  Matrix.of fun i j => if i = y ∧ j = y' then 1 else 0

theorem ancProj_mul_ancProj (y y' : Fin c) :
    ancProj y * ancProj y' = if y = y' then ancProj y else 0 := by
  unfold ancProj
  rw [Matrix.diagonal_mul_diagonal]
  split_ifs with h
  · subst h; congr 1; funext z; simp [Pi.single_apply]
  · rw [← Matrix.diagonal_zero]; congr 1; funext z
    simp only [Pi.single_apply]
    split_ifs with h1 h2 <;> simp_all

theorem ancProj_conjTranspose (y : Fin c) : (ancProj y)ᴴ = ancProj y := by
  unfold ancProj
  rw [Matrix.diagonal_conjTranspose]
  congr 1; funext z; simp [Pi.single_apply]

theorem sum_ancProj : ∑ y, ancProj y = (1 : Matrix (Fin c) (Fin c) ℂ) := by
  unfold ancProj
  rw [← Matrix.diagonal_one]
  have h : (∑ y : Fin c, Matrix.diagonal (Pi.single y (1 : ℂ))) =
      Matrix.diagonal (∑ y : Fin c, Pi.single y (1 : ℂ)) := by
    ext i j; simp [Matrix.diagonal_apply, Matrix.sum_apply, Finset.sum_apply]
  rw [h, Finset.univ_sum_single]

theorem ancShift_mul_conjTranspose_self [NeZero c] (y : Fin c) :
    ancShift y * (ancShift y)ᴴ = 1 := by
  ext i k
  simp only [Matrix.mul_apply, conjTranspose_apply, ancShift, Matrix.of_apply, Matrix.one_apply]
  have : ∀ j : Fin c, (if i = j + y then (1 : ℂ) else 0) * star (if k = j + y then (1 : ℂ) else 0) =
      if j = i - y then (if i = k then 1 else 0) else 0 := by
    intro j
    by_cases hj : j = i - y
    · subst hj
      simp only [sub_add_cancel, ite_true, one_mul]
      by_cases hik : i = k
      · subst hik; simp
      · simp [hik, Ne.symm hik]
    · have : i ≠ j + y := fun h => hj (by rw [h, add_sub_cancel_right])
      simp [this, hj]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem ancShift_mul_ancProj_zero_mul_conjTranspose [NeZero c] (y y' : Fin c) :
    ancShift y * ancProj 0 * (ancShift y')ᴴ = ancUnit y y' := by
  ext i k
  rw [Matrix.mul_apply]
  simp only [ancProj, Matrix.mul_diagonal, conjTranspose_apply, ancShift, Matrix.of_apply,
    ancUnit, Pi.single_apply]
  have : ∀ j : Fin c, (if i = j + y then (1 : ℂ) else 0) * (if j = 0 then (1 : ℂ) else 0) *
      star (if k = j + y' then (1 : ℂ) else 0) =
      if j = 0 then (if i = y ∧ k = y' then 1 else 0) else 0 := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simp only [zero_add, ite_true, mul_one]
      by_cases hi : i = y <;> by_cases hk : k = y' <;> simp [hi, hk]
    · simp [hj]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem ancProj_mul_ancUnit (z y y' : Fin c) :
    ancProj z * ancUnit y y' = if z = y then ancUnit y y' else 0 := by
  ext i k
  simp only [ancProj, Matrix.diagonal_mul, ancUnit, Matrix.of_apply, Pi.single_apply]
  by_cases hz : z = y
  · subst hz
    by_cases hi : i = z <;> simp [hi]
  · by_cases hi : i = z
    · subst hi; simp [hz]
    · simp [hi, hz]

theorem ancUnit_mul_ancProj (y y' z : Fin c) :
    ancUnit y y' * ancProj z = if z = y' then ancUnit y y' else 0 := by
  ext i k
  simp only [ancProj, Matrix.mul_diagonal, ancUnit, Matrix.of_apply, Pi.single_apply]
  by_cases hz : z = y'
  · subst hz
    by_cases hk : k = z <;> simp [hk]
  · by_cases hk : k = z
    · subst hk; simp [hz]
    · simp [hk, hz]

theorem trace_ancUnit (y y' : Fin c) : (ancUnit y y').trace = if y = y' then 1 else 0 := by
  simp only [Matrix.trace, Matrix.diag_apply, ancUnit, Matrix.of_apply]
  by_cases h : y = y'
  · subst h; simp
  · simp [h]

theorem ancProj_posSemidef (y : Fin c) : (ancProj y).PosSemidef := by
  unfold ancProj
  refine Matrix.posSemidef_diagonal_iff.mpr ?_
  intro z; simp only [Pi.single_apply]; split_ifs <;> simp

theorem trace_ancProj (y : Fin c) : (ancProj y).trace = 1 := by
  simp [ancProj, Matrix.trace_diagonal]

end Ancilla

/-! ## The deferred round -/

section Deferred

variable {d c a d' : ℕ} [NeZero c]

/-- The record unitary `∑ y, P y ⊗ shift y`: copies the measurement outcome
    into an ancilla at `|0⟩`. -/
def roundW (e : Fin (d * c) ≃ Fin d') (R : ClassicalRound d c a) : Matrix (Fin d') (Fin d') ℂ :=
  ∑ y, kr e (R.P y) (ancShift y)

/-- The answer unitary `∑ z, ans (f z) ⊗ |z⟩⟨z|`, controlled on the ancilla. -/
def roundC (e : Fin (d * c) ≃ Fin d') (R : ClassicalRound d c a) (f : Fin c → Fin a) :
    Matrix (Fin d') (Fin d') ℂ :=
  ∑ z, kr e (R.ans (f z) : Matrix (Fin d) (Fin d) ℂ) (ancProj z)

theorem roundW_mul_conjTranspose_self (e : Fin (d * c) ≃ Fin d') (R : ClassicalRound d c a) :
    roundW e R * (roundW e R)ᴴ = 1 := by
  unfold roundW
  rw [conjTranspose_sum, Finset.sum_mul_sum]
  simp only [kr_conjTranspose, kr_mul, R.P_conjTranspose]
  have h : ∀ y, ∑ y', kr e (R.P y * R.P y') (ancShift y * (ancShift y')ᴴ) =
      kr e (R.P y) 1 := by
    intro y
    rw [Finset.sum_eq_single y]
    · rw [R.P_mul_self, ancShift_mul_conjTranspose_self]
    · intro y' _ hy'; rw [R.P_orth y y' (Ne.symm hy'), kr_zero_left]
    · intro h; exact absurd (Finset.mem_univ y) h
  simp only [h, ← kr_sum_left, R.P_sum, kr_one]

omit [NeZero c] in
theorem roundC_mul_conjTranspose_self (e : Fin (d * c) ≃ Fin d') (R : ClassicalRound d c a)
    (f : Fin c → Fin a) : roundC e R f * (roundC e R f)ᴴ = 1 := by
  unfold roundC
  rw [conjTranspose_sum, Finset.sum_mul_sum]
  simp only [kr_conjTranspose, kr_mul, ancProj_conjTranspose, ancProj_mul_ancProj]
  have hu : ∀ z, (R.ans (f z) : Matrix (Fin d) (Fin d) ℂ) *
      (R.ans (f z) : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 := fun z => by
    rw [← star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp (R.ans (f z)).prop
  have h : ∀ z, ∑ z', kr e ((R.ans (f z) : Matrix (Fin d) (Fin d) ℂ) *
      (R.ans (f z') : Matrix (Fin d) (Fin d) ℂ)ᴴ) (if z = z' then ancProj z else 0) =
      kr e 1 (ancProj z) := by
    intro z
    rw [Finset.sum_eq_single z]
    · rw [ite_eq_left rfl, hu]
    · intro z' _ hz'; rw [ite_eq_right (Ne.symm hz'), kr_zero_right]
    · intro h; exact absurd (Finset.mem_univ z) h
  simp only [h, ← kr_sum_right, sum_ancProj, kr_one]

/-- The deferred round: record the outcome, then answer controlled on the record. -/
def roundV (e : Fin (d * c) ≃ Fin d') (R : ClassicalRound d c a) (f : Fin c → Fin a) :
    Matrix.unitaryGroup (Fin d') ℂ :=
  ⟨roundC e R f * roundW e R, by
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (roundW e R), roundW_mul_conjTranspose_self, one_mul,
      roundC_mul_conjTranspose_self]⟩

theorem roundW_mul_kr_mul_conjTranspose (e : Fin (d * c) ≃ Fin d') (R : ClassicalRound d c a)
    (σ : Matrix (Fin d) (Fin d) ℂ) :
    roundW e R * kr e σ (ancProj 0) * (roundW e R)ᴴ =
      ∑ y, ∑ y', kr e (R.P y * σ * R.P y') (ancUnit y y') := by
  unfold roundW
  rw [conjTranspose_sum, Finset.sum_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
  rw [kr_mul, kr_conjTranspose, kr_mul, R.P_conjTranspose,
    ancShift_mul_ancProj_zero_mul_conjTranspose]

omit [NeZero c] in
theorem roundC_mul_kr_ancUnit_mul_conjTranspose (e : Fin (d * c) ≃ Fin d')
    (R : ClassicalRound d c a) (f : Fin c → Fin a) (B : Matrix (Fin d) (Fin d) ℂ) (y y' : Fin c) :
    roundC e R f * kr e B (ancUnit y y') * (roundC e R f)ᴴ =
      kr e ((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * B *
        (R.ans (f y') : Matrix (Fin d) (Fin d) ℂ)ᴴ) (ancUnit y y') := by
  unfold roundC
  rw [conjTranspose_sum, Finset.sum_mul, Finset.sum_mul_sum]
  simp only [kr_mul, kr_conjTranspose, ancProj_conjTranspose, ancProj_mul_ancUnit, ite_mul,
    zero_mul, ancUnit_mul_ancProj]
  rw [Finset.sum_eq_single y]
  · rw [Finset.sum_eq_single y']
    · simp
    · intro z' _ hz'; simp [hz', kr_zero_right]
    · intro h; exact absurd (Finset.mem_univ y') h
  · intro z _ hz
    refine Finset.sum_eq_zero fun z' _ => ?_
    simp [hz, kr_zero_right]
  · intro h; exact absurd (Finset.mem_univ y) h

/-- The deferred round on `σ ⊗ |0⟩⟨0|` is the block sum of the round's cross terms. -/
theorem roundV_mul_kr_ancProj_zero (e : Fin (d * c) ≃ Fin d') (R : ClassicalRound d c a)
    (f : Fin c → Fin a) (σ : Matrix (Fin d) (Fin d) ℂ) :
    (roundV e R f : Matrix (Fin d') (Fin d') ℂ) * kr e σ (ancProj 0) *
        (roundV e R f : Matrix (Fin d') (Fin d') ℂ)ᴴ =
      ∑ y, ∑ y', kr e (((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y) * σ *
        ((R.ans (f y') : Matrix (Fin d) (Fin d) ℂ) * R.P y')ᴴ) (ancUnit y y') := by
  show roundC e R f * roundW e R * kr e σ (ancProj 0) * (roundC e R f * roundW e R)ᴴ = _
  have h1 : roundC e R f * roundW e R * kr e σ (ancProj 0) * (roundC e R f * roundW e R)ᴴ =
      roundC e R f * (roundW e R * kr e σ (ancProj 0) * (roundW e R)ᴴ) * (roundC e R f)ᴴ := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [h1, roundW_mul_kr_mul_conjTranspose, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [roundC_mul_kr_ancUnit_mul_conjTranspose, conjTranspose_mul, R.P_conjTranspose]
  simp only [Matrix.mul_assoc]

omit [NeZero c] in
/-- `tr ((X ⊗ 1) ∑ y y', B y y' ⊗ |y⟩⟨y'|) = ∑ y, tr (X B y y)`: the cross terms
    have zero partial trace. -/
theorem trace_kr_one_mul_sum (e : Fin (d * c) ≃ Fin d') (X : Matrix (Fin d) (Fin d) ℂ)
    (B : Fin c → Fin c → Matrix (Fin d) (Fin d) ℂ) :
    (kr e X 1 * ∑ y, ∑ y', kr e (B y y') (ancUnit y y')).trace = ∑ y, (X * B y y).trace := by
  rw [Finset.mul_sum, trace_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum, trace_sum, Finset.sum_eq_single y]
  · rw [kr_mul, one_mul, trace_kr, trace_ancUnit, ite_eq_left rfl, mul_one]
  · intro y' _ hy'
    rw [kr_mul, one_mul, trace_kr, trace_ancUnit, ite_eq_right (Ne.symm hy'), mul_zero]
  · intro h; exact absurd (Finset.mem_univ y) h

end Deferred

/-! ## Merging a unitary between two chains -/

section Merge

variable {d q : ℕ}

/-- `U₀ ; O ; U₁ ; … ; O ; U_q ; V` composed with `W₀ ; O ; … ; O ; W_q'`: the last
    unitary of the first chain, `V`, and the first of the second are one unitary. -/
def mergeChain (V : Matrix.unitaryGroup (Fin d) ℂ)
    (B : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    (q₀ : ℕ) → (Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      Fin (q + q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ
  | 0, A => Fin.cons (B 0 * V * A 0) (Fin.tail B)
  | q₀ + 1, A => Fin.cons (A 0) (mergeChain V B q₀ (Fin.tail A))

theorem unitaryChannel_qbind_unitaryChannel {β : Type} (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (g : Unit → QComp d β) :
    QComp.qbind (unitaryChannel U) (fun _ => QComp.qbind (unitaryChannel V) g) =
      QComp.qbind (unitaryChannel (V * U)) g := by
  rw [← unitaryChannel_compose, QComp.qbind_assoc]

/-- The `Bool` chain of a merged family is the first chain, the unitary, and the
    second chain, with the flags combined by `||`. -/
theorem scChain_mergeChain (O : QComp d Bool) (V : Matrix.unitaryGroup (Fin d) ℂ)
    (B : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (q₀ : ℕ)
    (A : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    scChain O (q + q₀) (mergeChain V B q₀ A) =
      QComp.qbind (scChain O q₀ A) fun b => QComp.qbind (unitaryChannel V) fun _ =>
        QComp.qbind (scChain O q B) fun b' => QComp.qpure (b || b') := by
  induction q₀ with
  | zero =>
    simp only [mergeChain, scChain, QComp.qbind_assoc, QComp.qpure_qbind, Bool.false_or]
    cases q with
    | zero =>
      simp only [scChain, Fin.cons_zero, QComp.qbind_assoc, QComp.qpure_qbind,
        unitaryChannel_qbind_unitaryChannel]
    | succ q =>
      simp only [scChain, Fin.cons_zero, Fin.tail_cons, QComp.qbind_assoc, QComp.qpure_qbind,
        unitaryChannel_qbind_unitaryChannel]
  | succ q₀ ih =>
    show scChain O (q + q₀ + 1) (Fin.cons (A 0) (mergeChain V B q₀ (Fin.tail A))) = _
    simp only [scChain, Fin.cons_zero, Fin.tail_cons, ih, QComp.qbind_assoc, QComp.qpure_qbind,
      Bool.or_assoc]

end Merge

/-! ## The multi-round chain -/

section Chain

variable {d c a q : ℕ}

/-- `head ; (round ; segment)ᵏ` over a `Bool`-valued oracle, returning the
    disjunction of the oracle outcomes; the rounds do not touch the flag. -/
def mrChainSC (O : QComp d Bool) (f : Fin c → Fin a) :
    (k : ℕ) → (q₀ : ℕ) → (Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → ClassicalRound d c a) → QComp d Bool
  | 0, q₀, head, _, _ => scChain O q₀ head
  | k + 1, q₀, head, tail, R =>
    QComp.qbind (scChain O q₀ head) fun b => QComp.qbind (roundU (R 0) f) fun _ =>
      QComp.qbind (mrChainSC O f k q (tail 0) (Fin.tail tail) (Fin.tail R)) fun b' =>
        QComp.qpure (b || b')

/-- `head ; (round ; segment)ᵏ` over a `Unit`-valued oracle. -/
def mrChain (O : QComp d Unit) (f : Fin c → Fin a) :
    (k : ℕ) → (q₀ : ℕ) → (Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → ClassicalRound d c a) → QComp d Unit
  | 0, q₀, head, _, _ => oracleChain O q₀ head
  | k + 1, q₀, head, tail, R =>
    QComp.qbind (oracleChain O q₀ head) fun _ => QComp.qbind (roundU (R 0) f) fun _ =>
      mrChain O f k q (tail 0) (Fin.tail tail) (Fin.tail R)

/-- A `Bool` oracle that always returns `false` gives the `Unit` multi-round chain. -/
theorem mrChainSC_qbind_pure_false (O : QComp d Unit) (f : Fin c → Fin a) (k q₀ : ℕ)
    (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (R : Fin k → ClassicalRound d c a) :
    mrChainSC (QComp.qbind O fun _ => QComp.qpure false) f k q₀ head tail R =
      QComp.qbind (mrChain O f k q₀ head tail R) fun _ => QComp.qpure false := by
  induction k generalizing q₀ head with
  | zero => exact scChain_qbind_pure_false O q₀ head
  | succ k ih =>
    simp only [mrChainSC, mrChain, scChain_qbind_pure_false, ih, QComp.qbind_assoc,
      QComp.qpure_qbind, Bool.false_or]

/-- The multi-round chain over the merged head is the head chain, the unitary
    `V`, and the multi-round chain from the first segment on. -/
theorem mrChainSC_mergeChain (O : QComp d Bool) (f : Fin c → Fin a) (k q₀ : ℕ)
    (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) (V : Matrix.unitaryGroup (Fin d) ℂ)
    (B : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (R : Fin k → ClassicalRound d c a) :
    mrChainSC O f k (q + q₀) (mergeChain V B q₀ head) tail R =
      QComp.qbind (scChain O q₀ head) fun b => QComp.qbind (unitaryChannel V) fun _ =>
        QComp.qbind (mrChainSC O f k q B tail R) fun b' => QComp.qpure (b || b') := by
  cases k with
  | zero => simp only [mrChainSC, scChain_mergeChain]
  | succ k =>
    simp only [mrChainSC, scChain_mergeChain, QComp.qbind_assoc, QComp.qpure_qbind,
      Bool.or_assoc]

end Chain

/-! ## Lifting a chain along an ancilla -/

section Lift

variable {d c a q d' : ℕ}

/-- The unitary `U ⊗ 1` on the extended register. -/
def liftU (e : Fin (d * c) ≃ Fin d') (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.unitaryGroup (Fin d') ℂ :=
  ⟨kr e U 1, kr_mem_unitaryGroup e U.prop (Matrix.mem_unitaryGroup_iff.mpr (by simp))⟩

@[simp]
theorem liftU_val (e : Fin (d * c) ≃ Fin d') (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (liftU e U : Matrix (Fin d') (Fin d') ℂ) = kr e U 1 := rfl

/-- The round with every projector and answer tensored with `1`. -/
def liftR (e : Fin (d * c) ≃ Fin d') (R : ClassicalRound d c a) : ClassicalRound d' c a where
  P y := kr e (R.P y) 1
  P_conjTranspose y := by rw [kr_conjTranspose, R.P_conjTranspose, conjTranspose_one]
  P_mul_self y := by rw [kr_mul, R.P_mul_self, one_mul]
  P_orth y y' h := by rw [kr_mul, R.P_orth y y' h, kr_zero_left]
  P_sum := by rw [← kr_sum_left, R.P_sum, kr_one]
  ans z := liftU e (R.ans z)

/-- A channel on the extended register lifts a channel on the register when it
    acts as `Φ ⊗ id` on every product `B ⊗ E`. -/
def LiftsQ {β : Type} (e : Fin (d * c) ≃ Fin d') (O : QComp d β) (O' : QComp d' β) : Prop :=
  ∀ b (B : Matrix (Fin d) (Fin d) ℂ) (E : Matrix (Fin c) (Fin c) ℂ),
    O'.branch b (kr e B E) = kr e (O.branch b B) E

theorem liftsQ_unitaryChannel (e : Fin (d * c) ≃ Fin d') (U : Matrix.unitaryGroup (Fin d) ℂ) :
    LiftsQ e (unitaryChannel U) (unitaryChannel (liftU e U)) := by
  intro _ B E
  rw [unitaryChannel_branch_apply, unitaryChannel_branch_apply, liftU_val, kr_mul,
    kr_conjTranspose, kr_mul, conjTranspose_one, one_mul, mul_one]

theorem liftsQ_roundU (e : Fin (d * c) ≃ Fin d') (R : ClassicalRound d c a) (f : Fin c → Fin a) :
    LiftsQ e (roundU R f) (roundU (liftR e R) f) := by
  intro _ B E
  rw [roundU_branch, roundU_branch, kr_sum_left]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [liftR, liftU_val]
  rw [kr_mul, kr_conjTranspose, kr_mul, kr_mul]
  simp

theorem liftsQ_qpure {β : Type} (e : Fin (d * c) ≃ Fin d') (x : β) :
    LiftsQ e (QComp.qpure x : QComp d β) (QComp.qpure x) := by
  intro b B E
  rw [qpure_branch_apply, qpure_branch_apply]
  split_ifs
  · rfl
  · rw [kr_zero_left]

theorem liftsQ_qbind {β γ : Type} [Fintype β] (e : Fin (d * c) ≃ Fin d') {I : QComp d β}
    {I' : QComp d' β} {g : β → QComp d γ} {g' : β → QComp d' γ} (hI : LiftsQ e I I')
    (hg : ∀ x, LiftsQ e (g x) (g' x)) : LiftsQ e (QComp.qbind I g) (QComp.qbind I' g') := by
  intro b B E
  rw [qbind_branch_apply, qbind_branch_apply, tsum_fintype, tsum_fintype, kr_sum_left]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hI, hg]

theorem liftsQ_scChain (e : Fin (d * c) ≃ Fin d') (O : QComp d Bool) (O' : QComp d' Bool)
    (hO : LiftsQ e O O') (q₀ : ℕ) (U : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    LiftsQ e (scChain O q₀ U) (scChain O' q₀ (liftU e ∘ U)) := by
  induction q₀ with
  | zero =>
    intro b B E
    simp only [scChain, qbind_unit_branch, qpure_branch_apply, Function.comp]
    split_ifs
    · exact liftsQ_unitaryChannel e (U 0) () B E
    · rw [kr_zero_left]
  | succ q₀ ih =>
    intro b B E
    have hU := liftsQ_unitaryChannel e (U 0) () B E
    have htail : liftU e ∘ Fin.tail U = Fin.tail (liftU e ∘ U) := rfl
    cases b
    · rw [scChain_succ_branch_false, scChain_succ_branch_false]
      show (scChain O' q₀ (Fin.tail (liftU e ∘ U))).branch false
        (O'.branch false ((unitaryChannel (liftU e (U 0))).branch () (kr e B E))) = _
      rw [hU, hO, ← htail, ih (Fin.tail U) false]
      rfl
    · rw [scChain_succ_branch_true, scChain_succ_branch_true]
      show (scChain O' q₀ (Fin.tail (liftU e ∘ U))).branch true
          (O'.branch true ((unitaryChannel (liftU e (U 0))).branch () (kr e B E))) +
        (scChain O' q₀ (Fin.tail (liftU e ∘ U))).branch false
          (O'.branch true ((unitaryChannel (liftU e (U 0))).branch () (kr e B E))) +
        (scChain O' q₀ (Fin.tail (liftU e ∘ U))).branch true
          (O'.branch false ((unitaryChannel (liftU e (U 0))).branch () (kr e B E))) = _
      rw [hU, hO, hO, ← htail, ih (Fin.tail U) true, ih (Fin.tail U) false, ih (Fin.tail U) true,
        ← kr_add_left, ← kr_add_left]
      rfl

theorem liftsQ_mrChainSC (e : Fin (d * c) ≃ Fin d') (O : QComp d Bool) (O' : QComp d' Bool)
    (hO : LiftsQ e O O') (f : Fin c → Fin a) (k q₀ : ℕ)
    (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (R : Fin k → ClassicalRound d c a) :
    LiftsQ e (mrChainSC O f k q₀ head tail R)
      (mrChainSC O' f k q₀ (liftU e ∘ head) (fun j => liftU e ∘ tail j) (liftR e ∘ R)) := by
  induction k generalizing q₀ head with
  | zero => exact liftsQ_scChain e O O' hO q₀ head
  | succ k ih =>
    show LiftsQ e (QComp.qbind (scChain O q₀ head) fun b => QComp.qbind (roundU (R 0) f) fun _ =>
      QComp.qbind (mrChainSC O f k q (tail 0) (Fin.tail tail) (Fin.tail R)) fun b' =>
        QComp.qpure (b || b')) (QComp.qbind (scChain O' q₀ (liftU e ∘ head)) fun b =>
      QComp.qbind (roundU (liftR e (R 0)) f) fun _ =>
        QComp.qbind (mrChainSC O' f k q (liftU e ∘ tail 0) (fun j => liftU e ∘ Fin.tail tail j)
          (liftR e ∘ Fin.tail R)) fun b' => QComp.qpure (b || b'))
    exact liftsQ_qbind e (liftsQ_scChain e O O' hO q₀ head) fun b =>
      liftsQ_qbind e (liftsQ_roundU e (R 0) f) fun _ =>
        liftsQ_qbind e (ih q (tail 0) (Fin.tail tail) (Fin.tail R)) fun b' => liftsQ_qpure e _

end Lift

/-! ## Peeling one round -/

section Peel

variable {d c a q d' : ℕ} [NeZero c]

/-- One round against one deferred round, for any continuation `Rest` lifted
    by `Rest'`: the observable `X ⊗ 1` after the deferred round on `σ ⊗ |0⟩⟨0|`
    sees the round instrument on `σ`. -/
theorem trace_kr_one_mul_roundV {β : Type} (e : Fin (d * c) ≃ Fin d')
    (R : ClassicalRound d c a) (f : Fin c → Fin a) (Rest : QComp d β) (Rest' : QComp d' β)
    (hRest : LiftsQ e Rest Rest') (X σ : Matrix (Fin d) (Fin d) ℂ) (b : β) :
    (kr e X 1 * Rest'.branch b ((roundV e R f : Matrix (Fin d') (Fin d') ℂ) * kr e σ (ancProj 0) *
        (roundV e R f : Matrix (Fin d') (Fin d') ℂ)ᴴ)).trace =
      (X * Rest.branch b ((roundU R f).branch () σ)).trace := by
  have h := hRest b
  rw [roundV_mul_kr_ancProj_zero, map_sum]
  simp only [map_sum, h]
  rw [trace_kr_one_mul_sum, roundU_branch, map_sum, Finset.mul_sum, trace_sum]

omit [NeZero c] in
/-- The multi-round chain over a `Bool` oracle, with the flag of the head and
    the flags of the rest, at the branch level. -/
theorem mrChainSC_succ_branch (O : QComp d Bool) (f : Fin c → Fin a) (k q₀ : ℕ)
    (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (tail : Fin (k + 1) → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (R : Fin (k + 1) → ClassicalRound d c a) (b : Bool) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (mrChainSC O f (k + 1) q₀ head tail R).branch b ρ =
      ∑ b₁, ∑ b₂, if b = (b₁ || b₂) then
        (mrChainSC O f k q (tail 0) (Fin.tail tail) (Fin.tail R)).branch b₂
          ((roundU (R 0) f).branch () ((scChain O q₀ head).branch b₁ ρ)) else 0 := by
  simp only [mrChainSC, qbind_branch_apply, tsum_fintype, Fintype.sum_unique, qpure_branch_apply]
  refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
  congr

/-- The peel identity: the deferred single-round chain on `ρ ⊗ |0⟩⟨0|`, seen
    through `X ⊗ 1`, is the multi-round chain with one more round on `ρ`. -/
theorem trace_peel (e : Fin (d * c) ≃ Fin d') (O : QComp d Bool) (O' : QComp d' Bool)
    (hO : LiftsQ e O O') (f : Fin c → Fin a) (k q₀ : ℕ)
    (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (tail : Fin (k + 1) → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (R : Fin (k + 1) → ClassicalRound d c a) (X ρ : Matrix (Fin d) (Fin d) ℂ) (b : Bool) :
    (kr e X 1 * (mrChainSC O' f k (q + q₀)
        (mergeChain (roundV e (R 0) f) (liftU e ∘ tail 0) q₀ (liftU e ∘ head))
        (fun j => liftU e ∘ Fin.tail tail j) (liftR e ∘ Fin.tail R)).branch b
          (kr e ρ (ancProj 0))).trace =
      (X * (mrChainSC O f (k + 1) q₀ head tail R).branch b ρ).trace := by
  rw [mrChainSC_mergeChain, mrChainSC_succ_branch]
  simp only [qbind_branch_apply, tsum_fintype, Fintype.sum_unique, qpure_branch_apply]
  simp_rw [Finset.mul_sum, trace_sum]
  refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
  split_ifs
  · rw [liftsQ_scChain e O O' hO q₀ head b₁ ρ (ancProj 0)]
    exact trace_kr_one_mul_roundV e (R 0) f _ _
      (liftsQ_mrChainSC e O O' hO f k q (tail 0) (Fin.tail tail) (Fin.tail R)) X _ b₂
  · simp

end Peel

/-! ## The ancilla inside the work register -/

section Register

variable {p w c : ℕ}

/-- The associativity identity of `finProdEquiv`, as a cast. -/
theorem finProdEquiv_assoc (a : Fin p) (b : Fin w) (c' : Fin c) :
    finProdEquiv (p * w) c (finProdEquiv p w (a, b), c') =
      finCongr (Nat.mul_assoc p w c).symm (finProdEquiv p (w * c) (a, finProdEquiv w c (b, c'))) := by
  apply Fin.ext
  simp only [finProdEquiv, finProdFinEquiv_apply_val, finCongr_apply, Fin.val_cast]
  ring

/-- `A ⊗ 1_{w c} = (A ⊗ 1_w) ⊗ 1_c` up to the associativity cast. -/
theorem kronecker_one_assoc (A : Matrix (Fin p) (Fin p) ℂ) :
    A ⊗ₖ (1 : Matrix (Fin (w * c)) (Fin (w * c)) ℂ) =
      kr (finCongr (Nat.mul_assoc p w c)) (A ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℂ)) 1 := by
  ext i j
  obtain ⟨⟨a, bc⟩, rfl⟩ := (finProdEquiv p (w * c)).surjective i
  obtain ⟨⟨b, c'⟩, rfl⟩ := (finProdEquiv w c).surjective bc
  obtain ⟨⟨a', bc'⟩, rfl⟩ := (finProdEquiv p (w * c)).surjective j
  obtain ⟨⟨b', c''⟩, rfl⟩ := (finProdEquiv w c).surjective bc'
  have h1 : (finCongr (Nat.mul_assoc p w c)).symm
      (finProdEquiv p (w * c) (a, finProdEquiv w c (b, c'))) =
      finProdEquiv (p * w) c (finProdEquiv p w (a, b), c') := by
    rw [finProdEquiv_assoc]; rfl
  have h2 : (finCongr (Nat.mul_assoc p w c)).symm
      (finProdEquiv p (w * c) (a', finProdEquiv w c (b', c''))) =
      finProdEquiv (p * w) c (finProdEquiv p w (a', b'), c'') := by
    rw [finProdEquiv_assoc]; rfl
  simp only [kr, Matrix.submatrix_apply, h1, h2, kronecker_apply, Equiv.symm_apply_apply,
    Matrix.one_apply, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hb : b = b' <;> by_cases hc : c' = c'' <;> simp [hb, hc]

end Register

section Oracle

variable {m n w c : ℕ} [NeZero n]

/-- The index equivalence placing the ancilla `Fin c` inside the work register. -/
def ancE (m n w c : ℕ) : Fin (m * n * w * c) ≃ Fin (m * n * (w * c)) :=
  finCongr (Nat.mul_assoc (m * n) w c)

theorem oracleU_lift (H : Fin m → Fin n) :
    (oracleU m n (w * c) H : Matrix (Fin (m * n * (w * c))) (Fin (m * n * (w * c))) ℂ) =
      kr (ancE m n w c) (oracleU m n w H) 1 := by
  rw [oracleU_val, oracleU_val]
  exact kronecker_one_assoc _

omit [NeZero n] in
theorem projS_lift (S : Finset (Fin m)) :
    projS m n (w * c) S = kr (ancE m n w c) (projS m n w S) 1 := by
  unfold projS
  exact kronecker_one_assoc _

theorem kr_one_sub {d d' : ℕ} (e : Fin (d * c) ≃ Fin d') (P : Matrix (Fin d) (Fin d) ℂ) :
    1 - kr e P 1 = kr e (1 - P) 1 := by
  rw [kr_sub_left, kr_one]

/-- The semi-classical oracle on the extended work register lifts the one on
    the work register. -/
theorem liftsQ_scOracleQ (H : Fin m → Fin n) (S : Finset (Fin m)) :
    LiftsQ (ancE m n w c) (scOracleQ m n w H S) (scOracleQ m n (w * c) H S) := by
  intro b B E
  cases b
  · rw [scOracleQ_branch_false, scOracleQ_branch_false, oracleU_lift, projS_lift, kr_one_sub,
      kr_mul, kr_mul, kr_mul, kr_conjTranspose, kr_mul]
    simp
  · rw [scOracleQ_branch_true, scOracleQ_branch_true, oracleU_lift, projS_lift,
      kr_mul, kr_mul, kr_mul, kr_conjTranspose, kr_mul]
    simp

end Oracle

/-! ## The head-tail form of a multi-round adversary and its flattening -/

section Flatten

variable {m n w q q₀ k c a : ℕ}

/-- A multi-round adversary with a head segment of `q₀` queries and `k`
    further segments of `q` queries, each preceded by a round. -/
structure MRH (m n w q q₀ k c a : ℕ) where
  /-- The head segment. -/
  head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin (m * n * w)) ℂ
  /-- The segments after each round. -/
  tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin (m * n * w)) ℂ
  /-- The rounds. -/
  rounds : Fin k → ClassicalRound (m * n * w) c a
  /-- The initial state. -/
  init : DensityMatrix (m * n * w)
  /-- The projector of the final measurement. -/
  final : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ
  final_conjTranspose : finalᴴ = final
  final_mul_self : final * final = final

/-- The state `ρ ⊗ |0⟩⟨0|` with a fresh ancilla inside the work register. -/
def liftInit [NeZero c] (ρ : DensityMatrix (m * n * w)) : DensityMatrix (m * n * (w * c)) where
  val := kr (ancE m n w c) ρ.val (ancProj 0)
  psd := kr_posSemidef _ ρ.psd (ancProj_posSemidef 0)
  tr_one := by rw [trace_kr, ρ.tr_one, trace_ancProj, one_mul]

/-- Absorb the first round into the head by deferred measurement: the head,
    the deferred round and the first segment merge into one segment of
    `q + q₀` queries on the register extended by one ancilla. -/
def peel [NeZero c] (f : Fin c → Fin a) (A : MRH m n w q q₀ (k + 1) c a) :
    MRH m n (w * c) q (q + q₀) k c a where
  head := mergeChain (roundV (ancE m n w c) (A.rounds 0) f) (liftU (ancE m n w c) ∘ A.tail 0) q₀
    (liftU (ancE m n w c) ∘ A.head)
  tail j := liftU (ancE m n w c) ∘ Fin.tail A.tail j
  rounds := liftR (ancE m n w c) ∘ Fin.tail A.rounds
  init := liftInit A.init
  final := kr (ancE m n w c) A.final 1
  final_conjTranspose := by rw [kr_conjTranspose, A.final_conjTranspose, conjTranspose_one]
  final_mul_self := by rw [kr_mul, A.final_mul_self, one_mul]

/-- The work register after `k` ancillas: `(⋯((w * c) * c)⋯) * c`. -/
def ancW (c : ℕ) : ℕ → ℕ → ℕ
  | 0, w => w
  | k + 1, w => ancW c k (w * c)

/-- The query count after flattening `k` rounds: `q + (⋯ + (q + q₀))`. -/
def flatQ (q : ℕ) : ℕ → ℕ → ℕ
  | 0, q₀ => q₀
  | k + 1, q₀ => flatQ q k (q + q₀)

/-- The observable `X ⊗ 1 ⊗ ⋯ ⊗ 1` on the register with `k` ancillas. -/
def liftK (c : ℕ) : (k : ℕ) → {w : ℕ} → Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ →
    Matrix (Fin (m * n * ancW c k w)) (Fin (m * n * ancW c k w)) ℂ
  | 0, _, X => X
  | k + 1, w, X => liftK c k (kr (ancE m n w c) X 1)

theorem liftK_one (c : ℕ) : ∀ (k : ℕ) {w : ℕ},
    liftK c k (1 : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) = 1
  | 0, _ => rfl
  | k + 1, w => by
    show liftK c k (kr (ancE m n w c) 1 1) = 1
    rw [kr_one, liftK_one c k]

/-- The single-run adversary of a multi-round adversary: `k` rounds absorbed
    by `k` deferred measurements. -/
def flatten [NeZero c] (f : Fin c → Fin a) :
    (k : ℕ) → {w q₀ : ℕ} → MRH m n w q q₀ k c a → QAdv m n (ancW c k w) (flatQ q k q₀)
  | 0, _, _, A => ⟨A.head, A.init, A.final, A.final_conjTranspose, A.final_mul_self⟩
  | k + 1, _, _, A => flatten f k (peel f A)

theorem flatten_final [NeZero c] (f : Fin c → Fin a) :
    ∀ (k : ℕ) {w q₀ : ℕ} (A : MRH m n w q q₀ k c a), (flatten f k A).final = liftK c k A.final
  | 0, _, _, _ => rfl
  | k + 1, _, _, A => flatten_final f k (peel f A)

/-- The deferred single run and the multi-round run agree on every observable
    `X ⊗ 1 ⊗ ⋯ ⊗ 1` and every branch of the semi-classical chain. -/
theorem trace_flatten [NeZero n] [NeZero c] (H : Fin m → Fin n) (S : Finset (Fin m))
    (f : Fin c → Fin a) :
    ∀ (k : ℕ) {w q₀ : ℕ} (A : MRH m n w q q₀ k c a)
      (X : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) (b : Bool),
      (liftK c k X * (scChain (scOracleQ m n (ancW c k w) H S) (flatQ q k q₀)
          (flatten f k A).U).branch b (flatten f k A).init.val).trace =
        (X * (mrChainSC (scOracleQ m n w H S) f k q₀ A.head A.tail A.rounds).branch b
          A.init.val).trace
  | 0, _, _, _, _, _ => rfl
  | k + 1, w, q₀, A, X, b =>
    (trace_flatten H S f k (peel f A) (kr (ancE m n w c) X 1) b).trans
      (trace_peel (ancE m n w c) _ _ (liftsQ_scOracleQ H S) f k q₀ A.head A.tail A.rounds X
        A.init.val b)

theorem ancW_eq (c : ℕ) : ∀ (k w : ℕ), ancW c k w = w * c ^ k
  | 0, w => by simp [ancW]
  | k + 1, w => by rw [ancW, ancW_eq c k, pow_succ]; ring

theorem flatQ_eq (q : ℕ) : ∀ (k q₀ : ℕ), flatQ q k q₀ = q₀ + k * q
  | 0, q₀ => by simp [flatQ]
  | k + 1, q₀ => by rw [flatQ, flatQ_eq q k]; ring

/-- The vector `u ⊗ v` along `e`. -/
def kv {d d' : ℕ} (e : Fin (d * c) ≃ Fin d') (u : Fin d → ℂ) (v : Fin c → ℂ) : Fin d' → ℂ :=
  fun i => u ((finProdEquiv d c).symm (e.symm i)).1 * v ((finProdEquiv d c).symm (e.symm i)).2

theorem kr_vecMulVec {d d' : ℕ} (e : Fin (d * c) ≃ Fin d') (u : Fin d → ℂ) (v : Fin c → ℂ) :
    kr e (vecMulVec u (star u)) (vecMulVec v (star v)) =
      vecMulVec (kv e u v) (star (kv e u v)) := by
  ext i j
  simp only [kr, Matrix.submatrix_apply, kronecker_apply, vecMulVec_apply, Pi.star_apply, kv,
    star_mul']
  ring

theorem ancProj_zero_eq_vecMulVec [NeZero c] :
    ancProj (0 : Fin c) = vecMulVec (Pi.single 0 1) (star (Pi.single 0 1)) := by
  ext i j
  simp only [ancProj, Matrix.diagonal_apply, vecMulVec_apply, Pi.star_apply, Pi.single_apply]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj, eq_comm]

/-- A rank-one initial state stays rank one through the flattening, with the
    ancillas at `|0⟩`. -/
theorem flatten_init_pure [NeZero c] (f : Fin c → Fin a) :
    ∀ (k : ℕ) {w q₀ : ℕ} (A : MRH m n w q q₀ k c a),
      (∃ ψ, A.init.val = vecMulVec ψ (star ψ)) →
        ∃ ψ', (flatten f k A).init.val = vecMulVec ψ' (star ψ')
  | 0, _, _, _, h => h
  | k + 1, w, _, A, ⟨ψ, hψ⟩ =>
    flatten_init_pure f k (peel f A) ⟨kv (ancE m n w c) ψ (Pi.single 0 1), by
      show kr (ancE m n w c) A.init.val (ancProj 0) = _
      rw [hψ, ancProj_zero_eq_vecMulVec, kr_vecMulVec]⟩

end Flatten

/-! ## Multi-round adversaries and their runs -/

section MR

variable {m n w q k c a : ℕ}

/-- A multi-round adversary: `k + 1` segments of `q` oracle queries, each
    segment given by its `q + 1` unitaries as in `QAdv`, `k` classical rounds
    between consecutive segments, an initial state and a final projector. -/
structure QAdvMR (m n w q k c a : ℕ) where
  /-- The unitaries of the segments. -/
  seg : Fin (k + 1) → Fin (q + 1) → Matrix.unitaryGroup (Fin (m * n * w)) ℂ
  /-- The rounds, round `j` between segments `j` and `j + 1`. -/
  rounds : Fin k → ClassicalRound (m * n * w) c a
  /-- The initial state. -/
  init : DensityMatrix (m * n * w)
  /-- The projector of the final measurement. -/
  final : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ
  final_conjTranspose : finalᴴ = final
  final_mul_self : final * final = final

/-- The head-tail form: segment `0` is the head. -/
def QAdvMR.toMRH (A : QAdvMR m n w q k c a) : MRH m n w q q k c a where
  head := A.seg 0
  tail := Fin.tail A.seg
  rounds := A.rounds
  init := A.init
  final := A.final
  final_conjTranspose := A.final_conjTranspose
  final_mul_self := A.final_mul_self

/-- The final measurement of `A` as an instrument. -/
def QAdvMR.measure (A : QAdvMR m n w q k c a) : QComp (m * n * w) Bool :=
  measProj A.final A.final_conjTranspose A.final_mul_self

variable [NeZero n]

/-- The standard run: segment `0` with `O_H`, round `0` with `f`, segment `1`,
    …, segment `k`, then the final measurement. -/
def runMR (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) :
    QComp (m * n * w) Bool :=
  QComp.qbind (mrChain (oracleQ m n w H) f k q (A.seg 0) (Fin.tail A.seg) A.rounds) fun _ =>
    A.measure

/-- The semi-classical run with `scOracleQ H S` in the segments and the `Find`
    flag threaded through the rounds, returning `(output, find)`. -/
def runSCMR (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) : QComp (m * n * w) (Bool × Bool) :=
  QComp.qbind (mrChainSC (scOracleQ m n w H S) f k q (A.seg 0) (Fin.tail A.seg) A.rounds)
    fun fl => QComp.qbind A.measure fun out => QComp.qpure (out, fl)

/-- The probability that the standard run outputs `1`. -/
def prOutMR (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) : ℝ≥0∞ :=
  prTrue_Q (runMR A H f) A.init

/-- The probability of `Find` in the semi-classical run. -/
def prFindMR (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) : ℝ≥0∞ :=
  prTrue_Q (QComp.qbind (runSCMR A H f S) fun p => QComp.qpure p.2) A.init

/-- The probability that the semi-classical run outputs `1` and `Find` does not
    occur. -/
def prOutNoFindMR (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) : ℝ≥0∞ :=
  prTrue_Q (QComp.qbind (runSCMR A H f S) fun p => QComp.qpure (p.1 && !p.2)) A.init

/-- The single-run adversary of `A`: `k` deferred measurements on the work
    register `ancW c k w`, with `flatQ q k q` oracle queries. -/
def toQAdv [NeZero c] (A : QAdvMR m n w q k c a) (f : Fin c → Fin a) :
    QAdv m n (ancW c k w) (flatQ q k q) :=
  flatten f k A.toMRH

/-- A projective measurement is trace preserving. -/
theorem measProj_trace_add {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) (hH : Pᴴ = P) (hI : P * P = P)
    (σ : Matrix (Fin d) (Fin d) ℂ) :
    ((measProj P hH hI).branch true σ).trace + ((measProj P hH hI).branch false σ).trace =
      σ.trace := by
  have hP : (1 - P) * (1 - P) = 1 - P := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hI]; abel
  rw [measProj_branch_true, measProj_branch_false, hH, conjTranspose_sub, conjTranspose_one, hH,
    trace_proj_mul_mul_proj hI, trace_proj_mul_mul_proj hP, ← trace_add, ← add_mul,
    add_sub_cancel, one_mul]

/-- At `S = ∅` the `false` branch of the semi-classical chain is the standard chain. -/
theorem scChain_empty_branch_false (H : Fin m → Fin n) (q' : ℕ)
    (U : Fin (q' + 1) → Matrix.unitaryGroup (Fin (m * n * w)) ℂ)
    (ρ : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (scChain (scOracleQ m n w H ∅) q' U).branch false ρ =
      (oracleChain (oracleQ m n w H) q' U).branch () ρ := by
  rw [scOracleQ_empty, scChain_qbind_pure_false, qbind_unit_branch, qpure_branch_apply, ite_eq_left rfl]

/-- At `S = ∅` the `false` branch of the multi-round semi-classical chain is the
    standard multi-round chain. -/
theorem mrChainSC_empty_branch_false (H : Fin m → Fin n) (f : Fin c → Fin a) (q₀ : ℕ)
    (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin (m * n * w)) ℂ)
    (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin (m * n * w)) ℂ)
    (R : Fin k → ClassicalRound (m * n * w) c a) (ρ : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (mrChainSC (scOracleQ m n w H ∅) f k q₀ head tail R).branch false ρ =
      (mrChain (oracleQ m n w H) f k q₀ head tail R).branch () ρ := by
  rw [scOracleQ_empty, mrChainSC_qbind_pure_false, qbind_unit_branch, qpure_branch_apply,
    ite_eq_left rfl]

/-- The acceptance probability of a `QAdv`, through the `false` branch of the
    semi-classical chain at `S = ∅`. -/
theorem prOut_eq_trace_scChain_empty {w' q' : ℕ} (A : QAdv m n w' q') (H : Fin m → Fin n) :
    prOut A H = ENNReal.ofReal (A.final *
      (scChain (scOracleQ m n w' H ∅) q' A.U).branch false A.init.val).trace.re := by
  unfold prOut prTrue_Q run QAdv.measure
  rw [qbind_unit_branch, measProj_branch_true, A.final_conjTranspose,
    trace_proj_mul_mul_proj A.final_mul_self, scChain_empty_branch_false]

theorem prOutMR_eq_trace (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) :
    prOutMR A H f = ENNReal.ofReal (A.final *
      (mrChainSC (scOracleQ m n w H ∅) f k q (A.seg 0) (Fin.tail A.seg) A.rounds).branch false
        A.init.val).trace.re := by
  unfold prOutMR prTrue_Q runMR QAdvMR.measure
  rw [qbind_unit_branch, measProj_branch_true, A.final_conjTranspose,
    trace_proj_mul_mul_proj A.final_mul_self, mrChainSC_empty_branch_false]

theorem runSCMR_branch_apply (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) (out fl : Bool) (ρ : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (runSCMR A H f S).branch (out, fl) ρ =
      A.measure.branch out ((mrChainSC (scOracleQ m n w H S) f k q (A.seg 0) (Fin.tail A.seg)
        A.rounds).branch fl ρ) := by
  unfold runSCMR
  simp only [qbind_branch_apply, tsum_fintype, Fintype.sum_bool, qpure_branch_apply]
  cases out <;> cases fl <;> simp

theorem prFindMR_eq_trace (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) :
    prFindMR A H f S = ENNReal.ofReal ((mrChainSC (scOracleQ m n w H S) f k q (A.seg 0)
      (Fin.tail A.seg) A.rounds).branch true A.init.val).trace.re := by
  unfold prFindMR prTrue_Q
  simp only [qbind_branch_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool,
    qpure_branch_apply, runSCMR_branch_apply]
  simp only [Bool.true_eq_false, ↓reduceIte, add_zero, trace_add]
  unfold QAdvMR.measure
  rw [measProj_trace_add]

variable [NeZero c]

/-- The acceptance probability of a multi-round adversary is that of its
    single-run embedding. -/
theorem prOutMR_eq (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) :
    prOutMR A H f = prOut (toQAdv A f) H := by
  rw [prOutMR_eq_trace, prOut_eq_trace_scChain_empty]
  unfold toQAdv
  rw [flatten_final]
  exact congrArg (fun t : ℂ => ENNReal.ofReal t.re)
    (trace_flatten H ∅ f k A.toMRH A.final false).symm

/-- The `Find` probability of a multi-round adversary is that of its
    single-run embedding. -/
theorem prFindMR_eq (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) : prFindMR A H f S = prFind (toQAdv A f) H S := by
  rw [prFindMR_eq_trace, prFind_eq_trace]
  unfold toQAdv
  have h := trace_flatten H S f k A.toMRH 1 true
  rw [liftK_one, one_mul, one_mul] at h
  exact congrArg (fun t : ℂ => ENNReal.ofReal t.re) h.symm

/-- The probability of `out = 1 ∧ ¬Find` of a multi-round adversary is that of
    its single-run embedding. -/
theorem prOutNoFindMR_eq (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) : prOutNoFindMR A H f S = prOutNoFind (toQAdv A f) H S := by
  rw [prOutNoFind_eq_trace]
  unfold prOutNoFindMR prTrue_Q
  simp only [qbind_branch_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool,
    qpure_branch_apply, runSCMR_branch_apply]
  simp only [Bool.and_self, Bool.not_true, Bool.and_false, Bool.false_and, Bool.not_false,
    Bool.true_eq_false, ↓reduceIte, zero_add, add_zero]
  unfold QAdvMR.measure toQAdv
  rw [measProj_branch_true, A.final_conjTranspose, trace_proj_mul_mul_proj A.final_mul_self,
    trace_proj_mul_mul_proj (flatten f k A.toMRH).final_mul_self, flatten_final]
  exact congrArg (fun t : ℂ => ENNReal.ofReal t.re)
    (trace_flatten H S f k A.toMRH A.final false).symm

omit [NeZero n] in
/-- A rank-one initial state gives a rank-one initial state of `toQAdv`. -/
theorem pure_toQAdv (A : QAdvMR m n w q k c a) (f : Fin c → Fin a)
    {ψ : Fin (m * n * w) → ℂ} (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    ∃ ψ', (toQAdv A f).init.val = vecMulVec ψ' (star ψ') :=
  flatten_init_pure f k A.toMRH ⟨ψ, hpure⟩

/-- The one-way-to-hiding bound for a multi-round adversary with a pure initial
    state and two functions agreeing outside `S`:
    `|Pr[out = 1 : A^H] − Pr[out = 1 : A^{H'}]| ≤ 4 √(q' · Pr[Find])` with
    `q' = flatQ q k q = (k + 1) q` the query count of `toQAdv`. -/
theorem o2h_MR (A : QAdvMR m n w q k c a) (f : Fin c → Fin a) (H H' : Fin m → Fin n)
    (S : Finset (Fin m)) (hHH' : ∀ x, x ∉ S → H x = H' x) {ψ : Fin (m * n * w) → ℂ}
    (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    absDiff (prOutMR A H f) (prOutMR A H' f) ≤
      4 * ((flatQ q k q : ℝ≥0∞) * prFindMR A H f S) ^ (1 / 2 : ℝ) := by
  obtain ⟨ψ', hψ'⟩ := pure_toQAdv A f hpure
  rw [prOutMR_eq, prOutMR_eq, prFindMR_eq]
  exact o2h (toQAdv A f) H H' S hHH' hψ'

/-- The squared form of `o2h_MR`:
    `|Pr[out = 1 : A^H] − Pr[out = 1 : A^{H'}]|² ≤ (4 q')² · Pr[Find]`. -/
theorem o2h_extraction_MR (A : QAdvMR m n w q k c a) (f : Fin c → Fin a) (H H' : Fin m → Fin n)
    (S : Finset (Fin m)) (hHH' : ∀ x, x ∉ S → H x = H' x) {ψ : Fin (m * n * w) → ℂ}
    (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    absDiff (prOutMR A H f) (prOutMR A H' f) ^ 2 ≤
      (4 * (flatQ q k q : ℝ≥0∞)) ^ 2 * prFindMR A H f S := by
  obtain ⟨ψ', hψ'⟩ := pure_toQAdv A f hpure
  rw [prOutMR_eq, prOutMR_eq, prFindMR_eq]
  exact o2h_extraction_of_QAdv (toQAdv A f) H H' S hHH' hψ'

end MR

end CatCrypt.Quantum.QROM
