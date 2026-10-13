/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.HopDecapsSparse2

/-!
# The round weight as an acceptance probability of a flattened adversary

The measurement weight of round `j` of a multi-round adversary is the
acceptance probability of a single-run adversary: the segments and rounds of
`A` up to round `j`, flattened by deferred measurement, with the query-register
projector `projS` as its final projector.

## Main definitions

* `truncMR A S' j` — the multi-round adversary that runs the segments and
  rounds of `A` up to segment `j` and measures the query register at `S'`

## Main results

* `liftK_projS` — `liftK c k (projS m n w S) = projS m n (ancW c k w) S`
* `roundGuessProb_eq_prOut_flatten` — `roundGuessProb A H f S j` is
  `prOut (toQAdv (truncMR A S' j) f) H`
* `final_toQAdv_truncMR` — the final projector of that adversary is
  `projS m n (ancW c j w) S'`
* `queries_toQAdv_truncMR` — its query count is `(j + 1) * q`

## Scope

The hypotheses carried are those of `roundGuessProb_eq_query_weight`:
`MeasuresCiphertext (A.rounds j) reg` at the round in question and the set
correspondence `∀ x, reg x ∈ S ↔ xPart m n w x ∈ S'`, together with
`[NeZero n]` and `[NeZero c]`.

The identification is with a truncated adversary, not with a plain state of
`toQAdv A f`. The flattening merges round `j` into the head unitary at index
`(j + 1) * q`: that entry of `mergeChain` is `B 0 * roundV * head ((j+1)*q)`,
so `plainState (toQAdv A f) H ψ ⟨(j+1)*q⟩` is the state after the deferred
round and after the first unitary of segment `j + 1`, while the round weight is
the weight before them. The two differ whenever the answer unitary of the round
moves the query register, so no plain state of `toQAdv A f` carries the
pre-round weight.

`SparseSearch.sparse_search` bounds `∑ H, μ H * prBad bad A H`, and
`prBad bad A H` is `prOut (extend A (badSet bad H)) H`. Turning
`prOut (toQAdv (truncMR A S' j) f) H` into that form needs `toQAdv
(truncMR A S' j) f` exhibited as `extend A' (badSet bad H)` for some `A'`:
a last unitary of the flattened head of the form `swapU * U`, an identity
unitary after one further query, and a work register of the shape `m * w'`
for the swap to typecheck. None of those is available from the data of a
`QAdvMR`, so no numeric bound on the decapsulation hop follows here.

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

variable {m n w q k c a : ℕ}

/-- The query-register projector lifted along `k` ancillas is the
query-register projector of the extended work register. -/
theorem liftK_projS (S : Finset (Fin m)) : ∀ (k : ℕ) {w : ℕ},
    liftK (m := m) (n := n) c k (projS m n w S) = projS m n (ancW c k w) S
  | 0, _ => rfl
  | k + 1, w => by
    show liftK c k (kr (ancE m n w c) (projS m n w S) 1) = _
    rw [← projS_lift, liftK_projS S k]
    rfl

/-- The adversary that runs the segments and rounds of `A` up to segment `j`
and measures the query register at `S'`. -/
def truncMR (A : QAdvMR m n w q k c a) (S' : Finset (Fin m)) (j : Fin k) :
    QAdvMR m n w q (j : ℕ) c a where
  seg := Fin.cons (A.seg 0) fun i : Fin (j : ℕ) => Fin.tail A.seg (Fin.castLE j.isLt.le i)
  rounds := fun i : Fin (j : ℕ) => A.rounds (Fin.castLE j.isLt.le i)
  init := A.init
  final := projS m n w S'
  final_conjTranspose := projS_conjTranspose m n w S'
  final_mul_self := projS_mul_self m n w S'

variable [NeZero n]

/-- The run of `truncMR A S' j` is the pre-round chain of round `j` followed by
the query-register measurement. -/
theorem runMR_truncMR (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S' : Finset (Fin m)) (j : Fin k) :
    runMR (truncMR A S' j) H f =
      QComp.qbind (preRoundChain A H f j) fun _ =>
        measProj (projS m n w S') (projS_conjTranspose m n w S')
          (projS_mul_self m n w S') := by
  unfold runMR preRoundChain QAdvMR.measure truncMR
  simp only [Fin.cons_zero, Fin.tail_cons]

variable [NeZero c]

/-- The measurement weight of round `j` at a set of ciphertexts is the
acceptance probability of the flattened truncated adversary. -/
theorem roundGuessProb_eq_prOut_flatten (A : QAdvMR m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (j : Fin k) {reg : Fin (m * n * w) → Fin c}
    (h : MeasuresCiphertext (A.rounds j) reg)
    (S : Finset (Fin c)) (S' : Finset (Fin m))
    (hfac : ∀ x, reg x ∈ S ↔ xPart m n w x ∈ S') :
    roundGuessProb A H f S j = prOut (toQAdv (truncMR A S' j) f) H := by
  rw [roundGuessProb_eq_query_weight A H f j h S S' hfac, ← prOutMR_eq]
  unfold prOutMR prTrue_Q
  rw [runMR_truncMR]
  rfl

omit [NeZero n] in
/-- The final projector of the flattened truncated adversary. -/
theorem final_toQAdv_truncMR (A : QAdvMR m n w q k c a) (f : Fin c → Fin a)
    (S' : Finset (Fin m)) (j : Fin k) :
    (toQAdv (truncMR A S' j) f).final = projS m n (ancW c (j : ℕ) w) S' := by
  unfold toQAdv
  rw [flatten_final]
  exact liftK_projS S' (j : ℕ)

/-- The query count of the flattened truncated adversary. -/
theorem queries_toQAdv_truncMR (j : Fin k) : flatQ q (j : ℕ) q = ((j : ℕ) + 1) * q := by
  rw [flatQ_eq]
  ring

end CatCrypt.Quantum.QROM

end
