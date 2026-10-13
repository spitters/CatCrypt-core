/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.HopDecapsSharp

/-!
# Rounds that measure a ciphertext label in the computational basis

The measurement of a `ClassicalRound` is an arbitrary orthogonal family of
projectors on the whole register. This module isolates the rounds whose family
is the computational-basis measurement of a ciphertext label carried by the
basis states, which is the shape the guessing probabilities of
`Quantum/QROM/SparseSearch.lean` are stated for.

## Main definitions

* `MeasuresCiphertext R reg` — every projector of `R` is the diagonal indicator
  of a fibre of the label `reg : Fin d → Fin c`
* `ClassicalRound.ofLabel reg ans` — the round with that measurement and the
  answer unitaries `ans`

## Main results

* `roundProjS_eq_diagonal_of_measuresCiphertext` — under `MeasuresCiphertext`
  the projector of a round at a set of outcomes is the diagonal indicator of
  the preimage of that set
* `ofLabel_measuresCiphertext` — `ClassicalRound.ofLabel reg ans` measures the
  label `reg`
* `measuresCiphertext_apply_of_ne` — a round measuring a label annihilates the
  basis states whose label differs from the outcome

## The hypothesis

`MeasuresCiphertext` is a predicate on a round, taken as a hypothesis by
`roundProjS_eq_diagonal_of_measuresCiphertext` and
`measuresCiphertext_apply_of_ne`. The `rounds` field of the `QAdvMR` returned by
`KEMQAdv.run` of `Quantum/QROM/KEMQuantumGame.lean` is an arbitrary family of
classical rounds, so for those adversaries the label and the diagonal form are
supplied at each use.

## References

* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], §4.1
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.Measurement

noncomputable section

namespace CatCrypt.Quantum.QROM

section Label

variable {d c a : ℕ}

/-- Every projector of `R` is the diagonal indicator of a fibre of the label
`reg`: the round measures the computational basis and reports `reg k` on the
basis state `k`. -/
def MeasuresCiphertext (R : ClassicalRound d c a) (reg : Fin d → Fin c) : Prop :=
  ∀ y, R.P y = Matrix.diagonal fun k => indS c {y} (reg k)

theorem indS_singleton_sum (S : Finset (Fin c)) (x : Fin c) :
    ∑ y ∈ S, indS c {y} x = indS c S x := by
  classical
  simp only [indS, Finset.mem_singleton]
  rw [Finset.sum_ite_eq S x fun _ => (1 : ℂ)]

/-- Under `MeasuresCiphertext` the projector of a round at a set of outcomes is
the diagonal indicator of the preimage of that set under the label. -/
theorem roundProjS_eq_diagonal_of_measuresCiphertext {R : ClassicalRound d c a}
    {reg : Fin d → Fin c} (h : MeasuresCiphertext R reg) (S : Finset (Fin c)) :
    roundProjS R S = Matrix.diagonal fun k => indS c S (reg k) := by
  have h' : ∀ y, R.P y = Matrix.diagonal fun k => indS c {y} (reg k) := h
  unfold roundProjS
  simp only [h']
  ext i j
  rw [Matrix.sum_apply]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq]
    exact indS_singleton_sum S (reg i)
  · simp [Matrix.diagonal_apply_ne _ hij]

/-- A round measuring the label `reg` annihilates the basis states whose label
differs from the outcome. -/
theorem measuresCiphertext_apply_of_ne {R : ClassicalRound d c a} {reg : Fin d → Fin c}
    (h : MeasuresCiphertext R reg) (y : Fin c) (k l : Fin d) (hk : reg k ≠ y) :
    R.P y k l = 0 := by
  rw [h y]
  by_cases hkl : k = l
  · subst hkl; simp [Matrix.diagonal_apply_eq, indS, hk]
  · simp [Matrix.diagonal_apply_ne _ hkl]

/-- The round that measures the computational basis, reports the label `reg k`
on the basis state `k`, and answers with `ans`. -/
def ClassicalRound.ofLabel (reg : Fin d → Fin c)
    (ans : Fin a → Matrix.unitaryGroup (Fin d) ℂ) : ClassicalRound d c a where
  P y := Matrix.diagonal fun k => indS c {y} (reg k)
  P_conjTranspose y := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext k
    exact indS_singleton_star c y (reg k)
  P_mul_self y := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    exact indS_singleton_mul_self c y (reg k)
  P_orth y y' hy := by
    rw [Matrix.diagonal_mul_diagonal]
    rw [show (0 : Matrix (Fin d) (Fin d) ℂ) = Matrix.diagonal fun _ : Fin d => (0 : ℂ) by simp]
    congr 1
    funext k
    simp only [indS, Finset.mem_singleton]
    by_cases hk : reg k = y <;> simp [hk, hy]
  P_sum := by
    rw [← Matrix.diagonal_one]
    rw [show (∑ y, Matrix.diagonal fun k => indS c {y} (reg k)) =
        Matrix.diagonal fun k => ∑ y, indS c {y} (reg k) by
      ext i j
      rw [Matrix.sum_apply]
      by_cases hij : i = j
      · subst hij; simp [Matrix.diagonal_apply_eq]
      · simp [Matrix.diagonal_apply_ne _ hij]]
    congr 1
    funext k
    rw [indS_singleton_sum Finset.univ (reg k)]
    simp [indS]
  ans := ans

theorem ofLabel_measuresCiphertext (reg : Fin d → Fin c)
    (ans : Fin a → Matrix.unitaryGroup (Fin d) ℂ) :
    MeasuresCiphertext (ClassicalRound.ofLabel reg ans) reg := fun _ => rfl

end Label

end CatCrypt.Quantum.QROM
