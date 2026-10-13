/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.SparseSearch
public import CatCryptCore.Quantum.QROM.HopDecapsNumeric

/-!
# The round projector as a query-register projector

A classical round that measures the computational basis and reports a label
(`MeasuresCiphertext`) has, at a set of outcomes, the projector
`Matrix.diagonal (indS c S ∘ reg)`. The query-register projector `projS` of
`Quantum/QROM/SemiClassicalOracle.lean` is `Matrix.diagonal (indS m S' ∘ xPart)`.
When the label factors through the query register along a set correspondence
the two projectors coincide, and the round-measurement probability
`roundGuessProb` becomes the weight of the query register at `S'`.

## Main results

* `measProj_congr` — equal projectors give equal projective measurements
* `roundProjS_eq_projS_of_label` — `roundProjS R S = projS m n w S'` for a
  round measuring `reg` whose fibres over `S` are the fibres of `xPart` over `S'`
* `roundGuessProb_eq_query_weight` — `roundGuessProb A H f S j` is the
  probability that the query register of the pre-round chain lies in `S'`

## Scope

The projector-level identification only. It carries no hypothesis on the
adversary beyond `MeasuresCiphertext` at the round in question and the set
correspondence `∀ x, reg x ∈ S ↔ xPart m n w x ∈ S'`, and it asserts nothing
about the query count.

The sparse-search bound of `Quantum/QROM/SparseSearch.lean` is stated for the
plain state of a `QAdv`, which is the initial state conjugated by a single
unitary prefix. The pre-round chain of a `QAdvMR` interleaves the classical
rounds, each a measurement instrument followed by an answer unitary, so it is
not a unitary conjugation and `roundGuessProb` is not a `guessProb` of any
`QAdv` on the same register. Closing that step needs a dilation of the rounds
into unitaries on an enlarged ancilla register together with the equality of
the dilated plain-state weight and the round-measurement weight; no such
dilation is constructed here, and no numeric bound on the decapsulation hop
follows from this module.

## References

* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], §4.1
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.Measurement

noncomputable section

namespace CatCrypt.Quantum.QROM

/-- Equal projectors give the same projective measurement. -/
theorem measProj_congr {d : ℕ} {P Q : Matrix (Fin d) (Fin d) ℂ} (h : P = Q)
    (hPH : Pᴴ = P) (hPI : P * P = P) (hQH : Qᴴ = Q) (hQI : Q * Q = Q) :
    measProj P hPH hPI = measProj Q hQH hQI := by
  subst h
  rfl

variable {m n w q k c a : ℕ}

/-- A round measuring the label `reg` has, at `S`, the query-register projector
at `S'`, whenever the fibres of `reg` over `S` are the fibres of `xPart` over
`S'`. -/
theorem roundProjS_eq_projS_of_label {R : ClassicalRound (m * n * w) c a}
    {reg : Fin (m * n * w) → Fin c} (h : MeasuresCiphertext R reg)
    (S : Finset (Fin c)) (S' : Finset (Fin m))
    (hfac : ∀ x, reg x ∈ S ↔ xPart m n w x ∈ S') :
    roundProjS R S = projS m n w S' := by
  rw [roundProjS_eq_diagonal_of_measuresCiphertext h, projS_eq_diagonal]
  congr 1
  funext x
  simp only [indS]
  by_cases hx : reg x ∈ S
  · rw [if_pos hx, if_pos ((hfac x).1 hx)]
  · rw [if_neg hx, if_neg fun hc => hx ((hfac x).2 hc)]

variable [NeZero n]

/-- The measurement weight of a round at a set of ciphertexts is the weight of
the query register of the pre-round chain at the corresponding set of query
points. -/
theorem roundGuessProb_eq_query_weight (A : QAdvMR m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (j : Fin k) {reg : Fin (m * n * w) → Fin c}
    (h : MeasuresCiphertext (A.rounds j) reg)
    (S : Finset (Fin c)) (S' : Finset (Fin m))
    (hfac : ∀ x, reg x ∈ S ↔ xPart m n w x ∈ S') :
    roundGuessProb A H f S j =
      prTrue_Q (QComp.qbind (preRoundChain A H f j) fun _ =>
        measProj (projS m n w S') (projS_conjTranspose m n w S')
          (projS_mul_self m n w S')) A.init := by
  unfold roundGuessProb
  rw [measProj_congr (roundProjS_eq_projS_of_label h S S' hfac)
    (roundProjS_conjTranspose _ _) (roundProjS_mul_self _ _)
    (projS_conjTranspose m n w S') (projS_mul_self m n w S')]

end CatCrypt.Quantum.QROM

end
