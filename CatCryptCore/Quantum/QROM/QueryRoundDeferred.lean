/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.QueryRoundAgreement

/-!
# The compiled query round and the deferred round

The deferred round `roundV` of `MultiRound` records the outcome of a
`ClassicalRound` on a fresh ancilla and then answers controlled on that
ancilla. The compiled query round `roundChainU` acts on the register alone,
with the record slot inside the register. This file relates the two on the
clean slice and reads off the record weight that the deferred round leaves on
its ancilla.

## Main results

* `ancShift_mul_ancProj_zero` — the shift applied to `|0⟩⟨0|` is the unit
  matrix `|y⟩⟨0|`
* `recProj_mul_cleanLift` — on a clean state the record projector and the
  clean record projector agree
* `roundV_mul_kr_cleanLift` — on a clean state the deferred round factors as
  the record-copy unitary `roundW` followed by `roundChainU ⊗ 1`
* `trace_kr_one_ancProj_mul_roundV` — the weight of the record ancilla `y`
  after the deferred round is `tr (P y σ)`
* `trace_P_eq_zero_of_roundV_kr_ancProj_zero` — if the deferred round returns
  the ancilla to `|0⟩⟨0|` then `tr (P y σ) = 0` for every `y ≠ 0`
* `trace_recProj_cleanLift_eq_zero_of_deferred_eq` — the same statement for
  the compiled round: the deferred round agrees with `roundChainU ⊗ 1` on a
  clean state only when the record slot carries no weight away from `0`

## Scope

The register of `roundV e R f` is `Fin d'` with `e : Fin (d * c) ≃ Fin d'`,
so its record ancilla is a tensor factor beyond the register `Fin d` carrying
the round's projectors. For the compiled round `d` is the extended register,
whose record slot is one of its own factors, so the two record slots are
different factors of the enlarged register. `roundV_mul_kr_cleanLift` measures
the difference: the deferred round is the compiled unitary composed with
`roundW`, which copies the record slot onto the ancilla.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The record copy on a fresh ancilla -/

/-- The shift applied to `|0⟩⟨0|` is the unit matrix `|y⟩⟨0|`. -/
theorem ancShift_mul_ancProj_zero {c : ℕ} [NeZero c] (y : Fin c) :
    ancShift y * ancProj (0 : Fin c) = ancUnit y 0 := by
  ext i k
  simp only [ancProj, Matrix.mul_diagonal, ancShift, Matrix.of_apply, ancUnit, Pi.single_apply]
  by_cases hk : k = 0
  · subst hk; simp
  · simp [hk]

/-! ## The record weight left on the ancilla -/

section Record

variable {d c a d' : ℕ} [NeZero c]

/-- The weight of the record ancilla at `y` after the deferred round on
    `σ ⊗ |0⟩⟨0|` is the weight the round's projector gives `σ`. -/
theorem trace_kr_one_ancProj_mul_roundV (e : Fin (d * c) ≃ Fin d') (R : ClassicalRound d c a)
    (f : Fin c → Fin a) (σ : Matrix (Fin d) (Fin d) ℂ) (y : Fin c) :
    (kr e 1 (ancProj y) * ((roundV e R f : Matrix (Fin d') (Fin d') ℂ) * kr e σ (ancProj 0) *
      (roundV e R f : Matrix (Fin d') (Fin d') ℂ)ᴴ)).trace = (R.P y * σ).trace := by
  rw [roundV_mul_kr_ancProj_zero, Finset.mul_sum, trace_sum, Finset.sum_eq_single y]
  · rw [Finset.mul_sum, trace_sum, Finset.sum_eq_single y]
    · rw [kr_mul, Matrix.one_mul, trace_kr, ancProj_mul_ancUnit, if_pos rfl, trace_ancUnit,
        if_pos rfl, mul_one]
      have hu : (R.ans (f y) : Matrix (Fin d) (Fin d) ℂ)ᴴ *
          (R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) = 1 := by
        have := (R.ans (f y)).prop
        rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose] at this
        exact this
      rw [Matrix.trace_mul_comm, conjTranspose_mul, R.P_conjTranspose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ)ᴴ), hu, Matrix.one_mul,
        ← Matrix.mul_assoc, R.P_mul_self]
    · intro y' _ hy'
      rw [kr_mul, Matrix.one_mul, trace_kr, ancProj_mul_ancUnit, if_pos rfl, trace_ancUnit,
        if_neg (Ne.symm hy'), mul_zero]
    · intro h; exact absurd (Finset.mem_univ y) h
  · intro y₀ _ hy₀
    rw [Finset.mul_sum, trace_sum]
    refine Finset.sum_eq_zero fun y' _ => ?_
    rw [kr_mul, Matrix.one_mul, trace_kr, ancProj_mul_ancUnit, if_neg (Ne.symm hy₀),
      Matrix.trace_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ y) h

/-- A deferred round that returns its ancilla to `|0⟩⟨0|` leaves no record
    weight away from `0`. -/
theorem trace_P_eq_zero_of_roundV_kr_ancProj_zero (e : Fin (d * c) ≃ Fin d')
    (R : ClassicalRound d c a) (f : Fin c → Fin a) (σ τ : Matrix (Fin d) (Fin d) ℂ) {y : Fin c}
    (hy : y ≠ 0)
    (h : (roundV e R f : Matrix (Fin d') (Fin d') ℂ) * kr e σ (ancProj 0) *
        (roundV e R f : Matrix (Fin d') (Fin d') ℂ)ᴴ = kr e τ (ancProj 0)) :
    (R.P y * σ).trace = 0 := by
  rw [← trace_kr_one_ancProj_mul_roundV e R f σ y, h, kr_mul, Matrix.one_mul, ancProj_mul_ancProj,
    if_neg hy, kr_zero_right, Matrix.trace_zero]

end Record

/-! ## The compiled round against the deferred round -/

variable (m n w c : ℕ) [NeZero m] [NeZero n] [NeZero c]
variable (ν₁ ν₂ : Fin c → Fin m)
variable {a d' : ℕ}

/-- On a clean state the record projector and the clean record projector
    agree. -/
theorem recProj_mul_cleanLift (y : Fin c)
    (ρ : Matrix (CleanReg m n w c) (CleanReg m n w c) ℂ) :
    recProj m n w c y * cleanLift m n w c ρ =
      cleanRecProj m n w c y * cleanLift m n w c ρ := by
  ext i j
  simp only [recProj, cleanRecProj, Matrix.diagonal_mul, cleanLift, Matrix.of_apply]
  by_cases hi : IsClean m n w c i
  · simp [hi]
  · simp [hi]

/-- On a clean state the deferred round of `permRound` is the record-copy
    unitary `roundW` followed by the compiled unitary tensored with `1`. -/
theorem roundV_mul_kr_cleanLift (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (e : Fin (m * n * (w * ancDim m n c) * c) ≃ Fin d')
    (ρ : Matrix (CleanReg m n w c) (CleanReg m n w c) ℂ) :
    (roundV e (permRound m n w c A) (queryFun m n c ν₁ ν₂ φ H) :
        Matrix (Fin d') (Fin d') ℂ) * kr e (cleanLift m n w c ρ) (ancProj 0) =
      kr e (roundChainU m n w c ν₁ ν₂ φ A H : Matrix _ _ ℂ) 1 *
        (roundW e (permRound m n w c A) * kr e (cleanLift m n w c ρ) (ancProj 0)) := by
  have hW : roundW e (permRound m n w c A) * kr e (cleanLift m n w c ρ) (ancProj 0) =
      ∑ y, kr e (recProj m n w c y * cleanLift m n w c ρ) (ancUnit y 0) := by
    unfold roundW
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [kr_mul, ancShift_mul_ancProj_zero, permRound_P]
  have hstep : ∀ y : Fin c,
      ((permRound m n w c A).ans (queryFun m n c ν₁ ν₂ φ H y) : Matrix _ _ ℂ) *
          (recProj m n w c y * cleanLift m n w c ρ) =
        (roundChainU m n w c ν₁ ν₂ φ A H : Matrix _ _ ℂ) *
          (recProj m n w c y * cleanLift m n w c ρ) := by
    intro y
    rw [recProj_mul_cleanLift, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      roundChainU_mul_cleanRecProj]
  show (roundC e (permRound m n w c A) (queryFun m n c ν₁ ν₂ φ H) *
    roundW e (permRound m n w c A)) * kr e (cleanLift m n w c ρ) (ancProj 0) = _
  rw [Matrix.mul_assoc, hW, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [kr_mul, Matrix.one_mul, ← hstep y]
  unfold roundC
  rw [Finset.sum_mul, Finset.sum_eq_single y]
  · rw [kr_mul, ancProj_mul_ancUnit, if_pos rfl]
  · intro z _ hz
    rw [kr_mul, ancProj_mul_ancUnit, if_neg hz, kr_zero_right]
  · intro h; exact absurd (Finset.mem_univ y) h

/-- The deferred round of `permRound` returns its ancilla to `|0⟩⟨0|` on a
    clean state only when the record slot carries no weight away from `0`. -/
theorem trace_recProj_cleanLift_eq_zero_of_deferred_eq
    (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (e : Fin (m * n * (w * ancDim m n c) * c) ≃ Fin d')
    (ρ : Matrix (CleanReg m n w c) (CleanReg m n w c) ℂ) {y : Fin c} (hy : y ≠ 0)
    (h : (roundV e (permRound m n w c A) (queryFun m n c ν₁ ν₂ φ H) :
          Matrix (Fin d') (Fin d') ℂ) * kr e (cleanLift m n w c ρ) (ancProj 0) *
        (roundV e (permRound m n w c A) (queryFun m n c ν₁ ν₂ φ H) :
          Matrix (Fin d') (Fin d') ℂ)ᴴ =
      kr e ((roundChainU m n w c ν₁ ν₂ φ A H : Matrix _ _ ℂ) * cleanLift m n w c ρ *
        (roundChainU m n w c ν₁ ν₂ φ A H : Matrix _ _ ℂ)ᴴ) (ancProj 0)) :
    (recProj m n w c y * cleanLift m n w c ρ).trace = 0 := by
  have hz := trace_P_eq_zero_of_roundV_kr_ancProj_zero e (permRound m n w c A)
    (queryFun m n c ν₁ ν₂ φ H) (cleanLift m n w c ρ) _ hy h
  rwa [permRound_P] at hz

end CatCrypt.Quantum.QROM
