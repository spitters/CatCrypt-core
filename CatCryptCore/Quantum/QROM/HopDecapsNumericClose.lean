/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.MeasuredQueryRun
public import CatCryptCore.Quantum.QROM.O2HTheorem

/-!
# The compiled decapsulation run as a fixed oracle program

The measured decapsulation round of the KEM game is, on the clean slice, the
record-slot measurement followed by the unitary of the compiled query round,
and that unitary is five table-independent step unitaries interleaved with
four copies of the oracle unitary. Absorbing the four queries into the head of
the following segment turns the run into a multi-round chain whose segments
carry `q + 4` queries, whose rounds are the record copy, and whose unitaries do
not mention the oracle table.

## Main definitions

* `roundSteps φ A` — the five step unitaries of the compiled query round
* `prependSteps S V` — the segment `V` with the four-query program `S` in
  front, the last step unitary merged into the first unitary of `V`
* `compiledMRH A φ Ans` — the multi-round adversary with a head segment of `q`
  oracle calls, `k` segments of `q + 4`, and the record copy as every round

## Main results

* `chainOp_roundSteps` — the chain operator of `roundSteps` at four queries is
  the unitary of the compiled query round
* `compiledRound_branch_eq_oracleChain` — the compiled round is the record copy
  followed by the four-query chain of `roundSteps`
* `chainOp_prependSteps` — the chain operator of `prependSteps S V` is the
  chain operator of `V` after the chain operator of `S`
* `mrChainR_qbind_unitary_eq_mrChain` — a multi-round chain whose rounds are a
  classical round followed by a four-query unitary is the multi-round chain
  with those four queries in the segments
* `mrChain_recordCopy_branch_indep` — a chain whose rounds are the record copy
  has the same branch for every classical function
* `prOutMR_eq_fixed_program`, `prOutMR_eq_compiledMRH` — the output probability
  of a multi-round adversary whose rounds are `permRound` is the acceptance
  probability of a chain whose unitaries and rounds do not mention the oracle
  table

## Scope

The identification of the run is at the level of `mrChain`: the rounds are
still measurement instruments, not unitaries on an enlarged register. The
hypotheses of `prOutMR_eq_fixed_program` are those of
`MeasuredQueryRun.prOutMR_eq_compiled`: every segment unitary commutes with
`cleanProjM`, every round of the adversary is `permRound m n w c Ans`, and the
initial state is supported by `cleanProjM`.

`GenericSearchUniform.generic_search_uniform` averages `prBad` of a single
`QAdv`, so applying it needs the chain of `prOutMR_eq_fixed_program` flattened
by `MultiRound.flatten` into a `QAdv` whose unitaries are the ones exhibited
here. `flatten` takes the classical function of the rounds as a parameter and
carries it into the merged head unitaries through `roundV`; the record copy has
`ans = 1`, so that parameter drops out, but no lemma stating
`flatten f k A = flatten f' k A` for rounds with `ans = 1` is available. The
remaining steps are recorded in the module documentation of
`Quantum/QROM/TruncExtend.lean` and `Quantum/QROM/RoundWeightDeferred.lean`;
no numeric bound on the decapsulation hop follows from this module.

## References

* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], §4.1
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.UnitaryChannel

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The four-query program of the compiled round -/

section Steps

variable (m n w c : ℕ) [NeZero m] [NeZero n] [NeZero c]
variable (ν₁ ν₂ : Fin c → Fin m)
variable {a : ℕ}

/-- The five step unitaries of the compiled query round, in the order in which
    the chain applies them. -/
def roundSteps (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) :
    Fin 5 → Matrix.unitaryGroup (Fin (m * n * (w * ancDim m n c))) ℂ :=
  ![permUnitary (stepZero m n w c ν₁), permUnitary (stepOne m n w c ν₂),
    permUnitary (stepTwo m n w c φ A), permUnitary (stepThree m n w c ν₂),
    permUnitary (stepFour m n w c ν₁)]

/-- The chain operator of the five step unitaries with four oracle calls is the
    unitary of the compiled query round. -/
theorem chainOp_roundSteps (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n) :
    chainOp (oracleU m n (w * ancDim m n c) H :
        Matrix (Fin (m * n * (w * ancDim m n c))) (Fin (m * n * (w * ancDim m n c))) ℂ) 4
        (roundSteps m n w c ν₁ ν₂ φ A) =
      (roundChainU m n w c ν₁ ν₂ φ A H : Matrix _ _ ℂ) := by
  rw [roundChainU_eq_chain]
  simp [chainOp, roundSteps, Fin.tail]

/-- The compiled round is the record copy followed by the four-query chain of
    the step unitaries. -/
theorem compiledRound_branch_eq_oracleChain (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (f : Fin c → Fin a)
    (ρ : Matrix (Fin (m * n * (w * ancDim m n c))) (Fin (m * n * (w * ancDim m n c))) ℂ) :
    (compiledRound m n w c ν₁ ν₂ φ A H f).branch () ρ =
      (oracleChain (oracleQ m n (w * ancDim m n c) H) 4
        (roundSteps m n w c ν₁ ν₂ φ A)).branch ()
          ((roundU (recordCopy m n w c a) f).branch () ρ) := by
  rw [compiledRound_branch, oracleQ, oracleChain_unitaryChannel_branch, chainOp_roundSteps,
    unitaryChannel_branch_apply]

end Steps

/-! ## A four-query program in front of a segment -/

section Prepend

variable {d q : ℕ}

/-- The segment `V` with the four-query program `S` in front: the last step
    unitary of `S` is merged into the first unitary of `V`. -/
def prependSteps (S : Fin 5 → Matrix.unitaryGroup (Fin d) ℂ)
    (V : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    Fin (q + 4 + 1) → Matrix.unitaryGroup (Fin d) ℂ :=
  Fin.cons (S 0) (Fin.cons (S 1) (Fin.cons (S 2)
    (Fin.cons (S 3) (Fin.cons (V 0 * S 4) (Fin.tail V)))))

/-- Merging a unitary into the first unitary of a segment multiplies the chain
    operator on the right. -/
theorem chainOp_cons_mul (O : Matrix (Fin d) (Fin d) ℂ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ∀ (q : ℕ) (V : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ),
      chainOp O q (Fin.cons (V 0 * U) (Fin.tail V)) =
        chainOp O q V * (U : Matrix (Fin d) (Fin d) ℂ)
  | 0, V => by simp [chainOp]
  | q + 1, V => by
    show chainOp O q (Fin.tail (Fin.cons ((V 0 * U : Matrix.unitaryGroup (Fin d) ℂ))
        (Fin.tail V))) * O * ((V 0 * U : Matrix.unitaryGroup (Fin d) ℂ) :
          Matrix (Fin d) (Fin d) ℂ) = _
    rw [Fin.tail_cons]
    show _ = chainOp O q (Fin.tail V) * O * (V 0 : Matrix (Fin d) (Fin d) ℂ) *
      (U : Matrix (Fin d) (Fin d) ℂ)
    simp only [Submonoid.coe_mul, Matrix.mul_assoc]

/-- The step equation of `chainOp`. -/
theorem chainOp_succ (O : Matrix (Fin d) (Fin d) ℂ) {q' : ℕ}
    (U : Fin (q' + 1 + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    chainOp O (q' + 1) U =
      chainOp O q' (Fin.tail U) * O * (U 0 : Matrix (Fin d) (Fin d) ℂ) := rfl

/-- The chain operator of a segment with four unitaries in front. -/
theorem chainOp_cons4 (O : Matrix (Fin d) (Fin d) ℂ)
    (u₀ u₁ u₂ u₃ : Matrix.unitaryGroup (Fin d) ℂ)
    (W : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    chainOp O (q + 4) (Fin.cons u₀ (Fin.cons u₁ (Fin.cons u₂ (Fin.cons u₃ W)))) =
      chainOp O q W * O * (u₃ : Matrix (Fin d) (Fin d) ℂ) * O *
        (u₂ : Matrix (Fin d) (Fin d) ℂ) * O * (u₁ : Matrix (Fin d) (Fin d) ℂ) * O *
        (u₀ : Matrix (Fin d) (Fin d) ℂ) := by
  simp only [chainOp_succ, Fin.tail_cons, Fin.cons_zero]

/-- The chain operator of five unitaries with four oracle calls. -/
theorem chainOp_four (O : Matrix (Fin d) (Fin d) ℂ)
    (S : Fin 5 → Matrix.unitaryGroup (Fin d) ℂ) :
    chainOp O 4 S = (S 4 : Matrix (Fin d) (Fin d) ℂ) * O * (S 3 : Matrix (Fin d) (Fin d) ℂ) *
      O * (S 2 : Matrix (Fin d) (Fin d) ℂ) * O * (S 1 : Matrix (Fin d) (Fin d) ℂ) * O *
      (S 0 : Matrix (Fin d) (Fin d) ℂ) := by
  simp [chainOp, Fin.tail]

/-- The chain operator of `prependSteps S V` is the chain operator of `V` after
    the chain operator of `S`. -/
theorem chainOp_prependSteps (O : Matrix (Fin d) (Fin d) ℂ)
    (S : Fin 5 → Matrix.unitaryGroup (Fin d) ℂ)
    (V : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    chainOp O (q + 4) (prependSteps S V) = chainOp O q V * chainOp O 4 S := by
  rw [prependSteps, chainOp_cons4, chainOp_cons_mul, chainOp_four]
  simp only [Matrix.mul_assoc]

/-- The chain of `prependSteps S V` is the chain of `V` after the four-query
    chain of `S`. -/
theorem oracleChain_prependSteps_branch (O : Matrix.unitaryGroup (Fin d) ℂ)
    (S : Fin 5 → Matrix.unitaryGroup (Fin d) ℂ)
    (V : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (oracleChain (unitaryChannel O) (q + 4) (prependSteps S V)).branch () ρ =
      (oracleChain (unitaryChannel O) q V).branch ()
        ((oracleChain (unitaryChannel O) 4 S).branch () ρ) := by
  rw [oracleChain_unitaryChannel_branch, oracleChain_unitaryChannel_branch,
    oracleChain_unitaryChannel_branch, chainOp_prependSteps, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end Prepend

/-! ## The round absorbed into the following segment -/

section Absorb

variable {d q c a : ℕ}

/-- A multi-round chain whose head segment carries a four-query program in
    front is the chain with the plain head segment, run after that program. -/
theorem mrChain_prependSteps_head (O : Matrix.unitaryGroup (Fin d) ℂ)
    (S : Fin 5 → Matrix.unitaryGroup (Fin d) ℂ) (f : Fin c → Fin a) {q' : ℕ} :
    ∀ (k : ℕ) (V : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q' + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a) (ρ : Matrix (Fin d) (Fin d) ℂ),
      (mrChain (unitaryChannel O) f k (q + 4) (prependSteps S V) tail R).branch () ρ =
        (mrChain (unitaryChannel O) f k q V tail R).branch ()
          ((oracleChain (unitaryChannel O) 4 S).branch () ρ)
  | 0, V, _, _, ρ => oracleChain_prependSteps_branch O S V ρ
  | k + 1, V, tail, R, ρ => by
    show ((QComp.qbind (oracleChain (unitaryChannel O) (q + 4) (prependSteps S V)) fun _ =>
        QComp.qbind (roundU (R 0) f) fun _ =>
          mrChain (unitaryChannel O) f k q' (tail 0) (Fin.tail tail)
            (Fin.tail R)).branch () ρ) = _
    show _ = ((QComp.qbind (oracleChain (unitaryChannel O) q V) fun _ =>
      QComp.qbind (roundU (R 0) f) fun _ =>
        mrChain (unitaryChannel O) f k q' (tail 0) (Fin.tail tail) (Fin.tail R)).branch ()
          ((oracleChain (unitaryChannel O) 4 S).branch () ρ))
    rw [qbind_unit_branch, qbind_unit_branch, qbind_unit_branch, qbind_unit_branch,
      oracleChain_prependSteps_branch]

/-- A multi-round chain whose rounds are a classical round followed by a
    unitary with four oracle calls is the multi-round chain whose segments
    carry those four calls. -/
theorem mrChainR_qbind_unitary_eq_mrChain (O : Matrix.unitaryGroup (Fin d) ℂ)
    (S : Fin 5 → Matrix.unitaryGroup (Fin d) ℂ) (W : Matrix.unitaryGroup (Fin d) ℂ)
    (hW : (W : Matrix (Fin d) (Fin d) ℂ) = chainOp (O : Matrix (Fin d) (Fin d) ℂ) 4 S)
    (f : Fin c → Fin a) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a) (ρ : Matrix (Fin d) (Fin d) ℂ),
      (mrChainR (unitaryChannel O) k q₀ head tail
          (fun j => QComp.qbind (roundU (R j) f) fun _ => unitaryChannel W)).branch () ρ =
        (mrChain (unitaryChannel O) f k q₀ head
          (fun j => prependSteps S (tail j)) R).branch () ρ
  | 0, _, _, _, _, _ => rfl
  | k + 1, q₀, head, tail, R, ρ => by
    have hWb : ∀ σ : Matrix (Fin d) (Fin d) ℂ, (unitaryChannel W).branch () σ =
        (oracleChain (unitaryChannel O) 4 S).branch () σ := by
      intro σ
      rw [oracleChain_unitaryChannel_branch, unitaryChannel_branch_apply, hW]
    show ((QComp.qbind (oracleChain (unitaryChannel O) q₀ head) fun _ =>
        QComp.qbind (QComp.qbind (roundU (R 0) f) fun _ => unitaryChannel W) fun _ =>
          mrChainR (unitaryChannel O) k q (tail 0) (Fin.tail tail)
            (fun j => QComp.qbind (roundU (Fin.tail R j) f) fun _ =>
              unitaryChannel W)).branch () ρ) = _
    show _ = ((QComp.qbind (oracleChain (unitaryChannel O) q₀ head) fun _ =>
      QComp.qbind (roundU (R 0) f) fun _ =>
        mrChain (unitaryChannel O) f k (q + 4) (prependSteps S (tail 0))
          (fun j => prependSteps S (Fin.tail tail j)) (Fin.tail R)).branch () ρ)
    rw [qbind_unit_branch, qbind_unit_branch, qbind_unit_branch, qbind_unit_branch,
      qbind_unit_branch,
      mrChainR_qbind_unitary_eq_mrChain O S W hW f k q (tail 0) (Fin.tail tail) (Fin.tail R),
      mrChain_prependSteps_head O S f k (tail 0)
        (fun j => prependSteps S (Fin.tail tail j)) (Fin.tail R), hWb]

end Absorb

/-! ## The record copy does not read the classical function -/

section RecordCopy

variable (m n w c : ℕ) [NeZero m] [NeZero n] [NeZero c]
variable {q a : ℕ}

/-- A multi-round chain whose rounds are the record copy has the same branch
    for every classical function. -/
theorem mrChain_recordCopy_branch_indep
    (O : QComp (m * n * (w * ancDim m n c)) Unit) (f f' : Fin c → Fin a) :
    ∀ (k q₀ : ℕ)
      (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin (m * n * (w * ancDim m n c))) ℂ)
      (tail : Fin k → Fin (q + 1) →
        Matrix.unitaryGroup (Fin (m * n * (w * ancDim m n c))) ℂ)
      (ρ : Matrix (Fin (m * n * (w * ancDim m n c))) (Fin (m * n * (w * ancDim m n c))) ℂ),
      (mrChain O f k q₀ head tail fun _ => recordCopy m n w c a).branch () ρ =
        (mrChain O f' k q₀ head tail fun _ => recordCopy m n w c a).branch () ρ
  | 0, _, _, _, _ => rfl
  | k + 1, q₀, head, tail, ρ => by
    show ((QComp.qbind (oracleChain O q₀ head) fun _ =>
        QComp.qbind (roundU (recordCopy m n w c a) f) fun _ =>
          mrChain O f k q (tail 0) (Fin.tail tail)
            fun _ => recordCopy m n w c a).branch () ρ) = _
    show _ = ((QComp.qbind (oracleChain O q₀ head) fun _ =>
      QComp.qbind (roundU (recordCopy m n w c a) f') fun _ =>
        mrChain O f' k q (tail 0) (Fin.tail tail)
          fun _ => recordCopy m n w c a).branch () ρ)
    rw [qbind_unit_branch, qbind_unit_branch, qbind_unit_branch, qbind_unit_branch,
      roundU_recordCopy_branch, roundU_recordCopy_branch,
      mrChain_recordCopy_branch_indep O f f' k q (tail 0) (Fin.tail tail)]

end RecordCopy

/-! ## The run as a fixed program applied to the oracle -/

section Fixed

variable (m n w c : ℕ) [NeZero m] [NeZero n] [NeZero c]
variable (ν₁ ν₂ : Fin c → Fin m)
variable {q k a : ℕ}

/-- The multi-round adversary of the compiled run: the head segment of `A`,
    the segments of `A` with the four-query program of the compiled round in
    front, and the record copy as every round. -/
def compiledMRH (A : QAdvMR m n (w * ancDim m n c) q k c a)
    (φ : Fin c → Fin n → Fin n → Fin a)
    (Ans : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) :
    MRH m n (w * ancDim m n c) (q + 4) q k c a where
  head := A.seg 0
  tail := fun j => prependSteps (roundSteps m n w c ν₁ ν₂ φ Ans) (Fin.tail A.seg j)
  rounds := fun _ => recordCopy m n w c a
  init := A.init
  final := A.final
  final_conjTranspose := A.final_conjTranspose
  final_mul_self := A.final_mul_self

/-- The output probability of a multi-round adversary whose rounds are
    `permRound` is the acceptance probability of a chain whose segment
    unitaries and whose rounds do not mention the oracle table: the segments
    carry `q + 4` oracle calls and the rounds are the record copy. -/
theorem prOutMR_eq_fixed_program (A : QAdvMR m n (w * ancDim m n c) q k c a)
    (φ : Fin c → Fin n → Fin n → Fin a)
    (Ans : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (f : Fin c → Fin a)
    (hseg : ∀ j i, (A.seg j i : Matrix _ _ ℂ) * cleanProjM m n w c =
      cleanProjM m n w c * (A.seg j i : Matrix _ _ ℂ))
    (hrounds : ∀ j, A.rounds j = permRound m n w c Ans)
    (hinit : SupportedOn (cleanProjM m n w c) A.init.val) :
    prOutMR A H (queryFun m n c ν₁ ν₂ φ H) =
      prTrue_Q (QComp.qbind (mrChain (oracleQ m n (w * ancDim m n c) H) f k q (A.seg 0)
        (fun j => prependSteps (roundSteps m n w c ν₁ ν₂ φ Ans) (Fin.tail A.seg j))
        fun _ => recordCopy m n w c a) fun _ => A.measure) A.init := by
  rw [prOutMR_eq_compiled m n w c ν₁ ν₂ A φ Ans H hseg hrounds hinit]
  unfold runMRCompiled prTrue_Q
  simp only [compiledRound, oracleQ]
  rw [qbind_unit_branch, qbind_unit_branch,
    mrChainR_qbind_unitary_eq_mrChain (oracleU m n (w * ancDim m n c) H)
      (roundSteps m n w c ν₁ ν₂ φ Ans) (roundChainU m n w c ν₁ ν₂ φ Ans H)
      (chainOp_roundSteps m n w c ν₁ ν₂ φ Ans H).symm
      (queryFun m n c ν₁ ν₂ φ H) k q (A.seg 0) (Fin.tail A.seg)
      (fun _ => recordCopy m n w c a),
    mrChain_recordCopy_branch_indep m n w c _ (queryFun m n c ν₁ ν₂ φ H) f k q (A.seg 0)]

/-- The chain of `prOutMR_eq_fixed_program` is the chain of `compiledMRH`, so
    the compiled run is the run of a multi-round adversary with a head segment
    of `q` oracle calls and `k` segments of `q + 4`. -/
theorem prOutMR_eq_compiledMRH (A : QAdvMR m n (w * ancDim m n c) q k c a)
    (φ : Fin c → Fin n → Fin n → Fin a)
    (Ans : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (f : Fin c → Fin a)
    (hseg : ∀ j i, (A.seg j i : Matrix _ _ ℂ) * cleanProjM m n w c =
      cleanProjM m n w c * (A.seg j i : Matrix _ _ ℂ))
    (hrounds : ∀ j, A.rounds j = permRound m n w c Ans)
    (hinit : SupportedOn (cleanProjM m n w c) A.init.val) :
    prOutMR A H (queryFun m n c ν₁ ν₂ φ H) =
      prTrue_Q (QComp.qbind (mrChain (oracleQ m n (w * ancDim m n c) H) f k q
        (compiledMRH m n w c ν₁ ν₂ A φ Ans).head (compiledMRH m n w c ν₁ ν₂ A φ Ans).tail
        (compiledMRH m n w c ν₁ ν₂ A φ Ans).rounds) fun _ => A.measure) A.init :=
  prOutMR_eq_fixed_program m n w c ν₁ ν₂ A φ Ans H f hseg hrounds hinit

end Fixed

end CatCrypt.Quantum.QROM

end
