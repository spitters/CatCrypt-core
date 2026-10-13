/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.QueryRoundDeferred
public import CatCryptCore.Quantum.QROM.CoherentCleanRun

/-!
# The measured multi-round run through the compiled query round

A decapsulation round of the KEM game is a measurement of the record slot, so
the run of a multi-round adversary keeps the measuring round `roundU` of
`MultiRound`. On the clean slice the answer unitary of `permRound` agrees with
the unitary `roundChainU` of the compiled query round, and that unitary does
not depend on the measurement outcome. The measuring round therefore splits
into the record-slot measurement, which reads no oracle, followed by
`roundChainU`, which reads the oracle four times.

## Main definitions

* `mrChainR` — the chain `head ; (round ; segment)ᵏ` with the rounds given as
  arbitrary `Unit`-valued channels
* `recordCopy` — the classical round measuring the record slot with identity
  answers
* `compiledRound` — the record-slot measurement followed by `roundChainU`
* `runMRCompiled` — the run of a multi-round adversary with `compiledRound` in
  place of its rounds

## Main results

* `roundV_eq_compiled_copy` — on a clean state the deferred round of
  `permRound` and the unitary `(roundChainU ⊗ 1) * roundW` act alike
* `roundU_permRound_branch_eq` — at a state supported by `cleanProjM` the
  measuring round of `permRound` and `compiledRound` have the same branch
* `runMR_measured_eq_compiled` — at a supported initial state the measured
  multi-round run and `runMRCompiled` have the same branches, and the two
  acceptance probabilities agree
* `roundU_recordCopy_indep_oracle` — the record copy has the same branch for
  every oracle
* `roundChainU_four_queries` — the compiled round is five oracle-independent
  unitaries interleaved with four copies of the oracle unitary
* `compiledQueryCount` — the query count of a run with `k` rounds and segments
  of `q` queries

## Scope

The agreement of the two runs is an equality of their branches at a state
supported by `cleanProjM`, not an equality of the two `QComp` values: off the
clean slice the answer unitary of `permRound` and `roundChainU` differ. The
hypotheses are that every segment unitary commutes with `cleanProjM`, that
every round of the adversary is `permRound`, and that the initial state is
supported by `cleanProjM`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder ENNReal
open Matrix Classical CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
  CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.Measurement

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The deferred round against the compiled unitary and the record copy -/

section Deferred

variable (m n w c : ℕ) [NeZero m] [NeZero n] [NeZero c]
variable (ν₁ ν₂ : Fin c → Fin m)
variable {a d' : ℕ}

/-- The conjugate transpose of a clean state is the clean state of the
    conjugate transpose of its block. -/
theorem cleanLift_conjTranspose (ρ : Matrix (CleanReg m n w c) (CleanReg m n w c) ℂ) :
    (cleanLift m n w c ρ)ᴴ = cleanLift m n w c ρᴴ := by
  ext i j
  simp only [cleanLift, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases hi : IsClean m n w c i <;> by_cases hj : IsClean m n w c j <;>
    simp [hi, hj, and_comm]

/-- The compiled unitary on the register, tensored with the identity on the
    record ancilla, after the record-copy unitary of the deferred round. -/
def deferredCompiled (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (e : Fin (m * n * (w * ancDim m n c) * c) ≃ Fin d') : Matrix (Fin d') (Fin d') ℂ :=
  kr e (roundChainU m n w c ν₁ ν₂ φ A H : Matrix _ _ ℂ) 1 *
    roundW e (permRound m n w c A)

/-- `deferredCompiled` is unitary. -/
theorem deferredCompiled_mem_unitaryGroup (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (e : Fin (m * n * (w * ancDim m n c) * c) ≃ Fin d') :
    deferredCompiled m n w c ν₁ ν₂ φ A H e ∈ Matrix.unitaryGroup (Fin d') ℂ := by
  have hW : roundW e (permRound m n w c A) ∈ Matrix.unitaryGroup (Fin d') ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]
    exact roundW_mul_conjTranspose_self e (permRound m n w c A)
  have hU : kr e (roundChainU m n w c ν₁ ν₂ φ A H : Matrix _ _ ℂ) 1 ∈
      Matrix.unitaryGroup (Fin d') ℂ :=
    kr_mem_unitaryGroup e (roundChainU m n w c ν₁ ν₂ φ A H).prop (Submonoid.one_mem _)
  exact Submonoid.mul_mem _ hU hW

/-- On a clean state the deferred round of `permRound` and `deferredCompiled`
    conjugate alike: the deferred round is the compiled unitary after the
    record copy. -/
theorem roundV_eq_compiled_copy (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (e : Fin (m * n * (w * ancDim m n c) * c) ≃ Fin d')
    (ρ : Matrix (CleanReg m n w c) (CleanReg m n w c) ℂ) :
    (roundV e (permRound m n w c A) (queryFun m n c ν₁ ν₂ φ H) :
          Matrix (Fin d') (Fin d') ℂ) * kr e (cleanLift m n w c ρ) (ancProj 0) *
        (roundV e (permRound m n w c A) (queryFun m n c ν₁ ν₂ φ H) :
          Matrix (Fin d') (Fin d') ℂ)ᴴ =
      deferredCompiled m n w c ν₁ ν₂ φ A H e * kr e (cleanLift m n w c ρ) (ancProj 0) *
        (deferredCompiled m n w c ν₁ ν₂ φ A H e)ᴴ := by
  have key : ∀ σ : Matrix (CleanReg m n w c) (CleanReg m n w c) ℂ,
      (roundV e (permRound m n w c A) (queryFun m n c ν₁ ν₂ φ H) :
          Matrix (Fin d') (Fin d') ℂ) * kr e (cleanLift m n w c σ) (ancProj 0) =
        deferredCompiled m n w c ν₁ ν₂ φ A H e * kr e (cleanLift m n w c σ) (ancProj 0) :=
    fun σ => by
      rw [roundV_mul_kr_cleanLift, deferredCompiled, Matrix.mul_assoc]
  have hY : (kr e (cleanLift m n w c ρᴴ) (ancProj 0))ᴴ =
      kr e (cleanLift m n w c ρ) (ancProj 0) := by
    rw [kr_conjTranspose, cleanLift_conjTranspose, Matrix.conjTranspose_conjTranspose,
      ancProj_conjTranspose]
  have hright : kr e (cleanLift m n w c ρ) (ancProj 0) *
      (roundV e (permRound m n w c A) (queryFun m n c ν₁ ν₂ φ H) :
        Matrix (Fin d') (Fin d') ℂ)ᴴ =
      kr e (cleanLift m n w c ρ) (ancProj 0) *
        (deferredCompiled m n w c ν₁ ν₂ φ A H e)ᴴ := by
    have h := congrArg Matrix.conjTranspose (key ρᴴ)
    rwa [conjTranspose_mul, conjTranspose_mul, hY] at h
  rw [key ρ, Matrix.mul_assoc, hright, ← Matrix.mul_assoc]

end Deferred

/-! ## The chain with arbitrary round channels -/

section ChainR

variable {d q : ℕ}

/-- `head ; (round ; segment)ᵏ` with the rounds given as `Unit`-valued
    channels. -/
def mrChainR (O : QComp d Unit) :
    (k : ℕ) → (q₀ : ℕ) → (Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → QComp d Unit) → QComp d Unit
  | 0, q₀, head, _, _ => oracleChain O q₀ head
  | k + 1, q₀, head, tail, W =>
    QComp.qbind (oracleChain O q₀ head) fun _ =>
      QComp.qbind (W 0) fun _ => mrChainR O k q (tail 0) (Fin.tail tail) (Fin.tail W)

variable {c a : ℕ}

/-- The chain of an adversary with classical rounds is the chain with those
    rounds as channels. -/
theorem mrChain_eq_mrChainR (O : QComp d Unit) (f : Fin c → Fin a) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a),
      mrChain O f k q₀ head tail R = mrChainR O k q₀ head tail fun j => roundU (R j) f
  | 0, _, _, _, _ => rfl
  | k + 1, q₀, head, tail, R => by
    show QComp.qbind (oracleChain O q₀ head) _ = QComp.qbind (oracleChain O q₀ head) _
    rw [mrChain_eq_mrChainR O f k q (tail 0) (Fin.tail tail) (Fin.tail R)]
    rfl

/-- The chain with unitary rounds is the chain with those unitaries as
    channels. -/
theorem mrChainW_eq_mrChainR (O : QComp d Unit) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (W : Fin k → Matrix.unitaryGroup (Fin d) ℂ),
      mrChainW O k q₀ head tail W = mrChainR O k q₀ head tail fun j => unitaryChannel (W j)
  | 0, _, _, _, _ => rfl
  | k + 1, q₀, head, tail, W => by
    show QComp.qbind (oracleChain O q₀ head) _ = QComp.qbind (oracleChain O q₀ head) _
    rw [mrChainW_eq_mrChainR O k q (tail 0) (Fin.tail tail) (Fin.tail W)]
    rfl

/-- Two chains differing only in their round channels have the same branch at a
    state supported by `P`, provided the round channels preserve the support of
    `P` and agree on states supported by `P`, and the segments commute with
    `P`. -/
theorem mrChainR_branch_congr {P : Matrix (Fin d) (Fin d) ℂ} (hP : Pᴴ = P)
    (O : QComp d Unit) (hO : PreservesSupport P O) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (W W' : Fin k → QComp d Unit),
      (∀ i, (head i : Matrix (Fin d) (Fin d) ℂ) * P = P * (head i : Matrix (Fin d) (Fin d) ℂ)) →
      (∀ j i, (tail j i : Matrix (Fin d) (Fin d) ℂ) * P =
        P * (tail j i : Matrix (Fin d) (Fin d) ℂ)) →
      (∀ j, PreservesSupport P (W j)) →
      (∀ j ρ, SupportedOn P ρ → (W j).branch () ρ = (W' j).branch () ρ) →
      ∀ ρ, SupportedOn P ρ →
        (mrChainR O k q₀ head tail W).branch () ρ = (mrChainR O k q₀ head tail W').branch () ρ
  | 0, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | k + 1, q₀, head, tail, W, W', hhead, htail, hWc, hW, ρ, hρ => by
    have hσ : SupportedOn P ((oracleChain O q₀ head).branch () ρ) :=
      oracleChain_preservesSupport hP O hO q₀ head hhead ρ hρ
    show ((QComp.qbind (oracleChain O q₀ head) fun _ =>
        QComp.qbind (W 0) fun _ =>
          mrChainR O k q (tail 0) (Fin.tail tail) (Fin.tail W)).branch () ρ) =
      ((QComp.qbind (oracleChain O q₀ head) fun _ =>
        QComp.qbind (W' 0) fun _ =>
          mrChainR O k q (tail 0) (Fin.tail tail) (Fin.tail W')).branch () ρ)
    rw [qbind_unit_branch, qbind_unit_branch, qbind_unit_branch, qbind_unit_branch,
      ← hW 0 _ hσ]
    exact mrChainR_branch_congr hP O hO k q (tail 0) (Fin.tail tail) (Fin.tail W) (Fin.tail W')
      (htail 0) (fun j i => htail j.succ i) (fun j => hWc j.succ) (fun j => hW j.succ) _
      (hWc 0 _ hσ)

end ChainR

/-! ## The record copy and the compiled round -/

section Round

variable (m n w c : ℕ) [NeZero m] [NeZero n] [NeZero c]
variable (ν₁ ν₂ : Fin c → Fin m)
variable (a : ℕ)

/-- The classical round measuring the record slot with identity answers. -/
def recordCopy : ClassicalRound (m * n * (w * ancDim m n c)) c a :=
  { permRound m n w c (fun _ : Fin a => (1 : Equiv.Perm ((Fin m × Fin n) × Fin w))) with
    ans := fun _ => 1 }

theorem recordCopy_P (y : Fin c) : (recordCopy m n w c a).P y = recProj m n w c y := rfl

theorem recordCopy_ans (k : Fin a) :
    (recordCopy m n w c a).ans k = 1 := rfl

variable {m n w c a}

/-- The record copy dephases the record slot. -/
theorem roundU_recordCopy_branch (f : Fin c → Fin a)
    (ρ : Matrix (Fin (m * n * (w * ancDim m n c))) (Fin (m * n * (w * ancDim m n c))) ℂ) :
    (roundU (recordCopy m n w c a) f).branch () ρ =
      ∑ y, recProj m n w c y * ρ * recProj m n w c y := by
  rw [roundU_branch]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [recordCopy_ans, recordCopy_P]
  have hP : (recProj m n w c y)ᴴ = recProj m n w c y :=
    (recordCopy m n w c a).P_conjTranspose y
  simp only [Submonoid.coe_one, Matrix.one_mul, hP]

/-- The record copy has the same branch for every oracle. -/
theorem roundU_recordCopy_indep_oracle (φ : Fin c → Fin n → Fin n → Fin a)
    (H H' : Fin m → Fin n)
    (ρ : Matrix (Fin (m * n * (w * ancDim m n c))) (Fin (m * n * (w * ancDim m n c))) ℂ) :
    (roundU (recordCopy m n w c a) (queryFun m n c ν₁ ν₂ φ H)).branch () ρ =
      (roundU (recordCopy m n w c a) (queryFun m n c ν₁ ν₂ φ H')).branch () ρ := by
  rw [roundU_recordCopy_branch, roundU_recordCopy_branch]

/-- The record copy preserves the support of the clean slice. -/
theorem roundU_recordCopy_preservesSupport (f : Fin c → Fin a) :
    PreservesSupport (cleanProjM m n w c) (roundU (recordCopy m n w c a) f) := by
  intro ρ hρ
  rw [roundU_recordCopy_branch]
  unfold SupportedOn at hρ ⊢
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  calc cleanProjM m n w c * (recProj m n w c y * ρ * recProj m n w c y) * cleanProjM m n w c
      = (cleanProjM m n w c * recProj m n w c y) * ρ *
          (recProj m n w c y * cleanProjM m n w c) := by simp only [Matrix.mul_assoc]
    _ = (recProj m n w c y * cleanProjM m n w c) * ρ *
          (cleanProjM m n w c * recProj m n w c y) := by
        rw [← recProj_comm_cleanProjM]
    _ = recProj m n w c y * (cleanProjM m n w c * ρ * cleanProjM m n w c) *
          recProj m n w c y := by simp only [Matrix.mul_assoc]
    _ = recProj m n w c y * ρ * recProj m n w c y := by rw [hρ]

/-- The projector onto the record-`y` slice compressed to the clean slice. -/
theorem recProj_mul_cleanProjM (y : Fin c) :
    recProj m n w c y * cleanProjM m n w c = cleanRecProj m n w c y := by
  rw [recProj, cleanProjM, cleanRecProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hc : IsClean m n w c i <;> by_cases hy : cleanRec m n w c i = y <;>
    simp [hc, hy]

variable (m n w c)

/-- The record-slot measurement followed by the unitary of the compiled query
    round. -/
def compiledRound (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (f : Fin c → Fin a) : QComp (m * n * (w * ancDim m n c)) Unit :=
  QComp.qbind (roundU (recordCopy m n w c a) f) fun _ =>
    unitaryChannel (roundChainU m n w c ν₁ ν₂ φ A H)

/-- The branch of the compiled round: the record copy, then conjugation by the
    unitary of the compiled query round. -/
theorem compiledRound_branch (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (f : Fin c → Fin a)
    (ρ : Matrix (Fin (m * n * (w * ancDim m n c))) (Fin (m * n * (w * ancDim m n c))) ℂ) :
    (compiledRound m n w c ν₁ ν₂ φ A H f).branch () ρ =
      (unitaryChannel (roundChainU m n w c ν₁ ν₂ φ A H)).branch ()
        ((roundU (recordCopy m n w c a) f).branch () ρ) := by
  unfold compiledRound
  rw [qbind_unit_branch]

/-- At a state supported by the clean slice the measuring round of `permRound`
    and `compiledRound` have the same branch: the measured round is the
    oracle-free record copy followed by the compiled unitary. -/
theorem roundU_permRound_branch_eq (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (ρ : Matrix (Fin (m * n * (w * ancDim m n c))) (Fin (m * n * (w * ancDim m n c))) ℂ)
    (hρ : SupportedOn (cleanProjM m n w c) ρ) :
    (roundU (permRound m n w c A) (queryFun m n c ν₁ ν₂ φ H)).branch () ρ =
      (compiledRound m n w c ν₁ ν₂ φ A H (queryFun m n c ν₁ ν₂ φ H)).branch () ρ := by
  have hkey : ∀ y : Fin c,
      (((permRound m n w c A).ans (queryFun m n c ν₁ ν₂ φ H y) : Matrix _ _ ℂ) *
          recProj m n w c y) * cleanProjM m n w c =
        ((roundChainU m n w c ν₁ ν₂ φ A H : Matrix _ _ ℂ) * recProj m n w c y) *
          cleanProjM m n w c := by
    intro y
    rw [Matrix.mul_assoc, Matrix.mul_assoc, recProj_mul_cleanProjM,
      roundChainU_mul_cleanRecProj]
  rw [roundU_branch, compiledRound, qbind_unit_branch, unitaryChannel_branch_apply,
    roundU_recordCopy_branch, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hP : (recProj m n w c y)ᴴ = recProj m n w c y := (permRound m n w c A).P_conjTranspose y
  have hconj := conj_eq_of_mul_eq (cleanProjM_conjTranspose m n w c) (hkey y) hρ
  rw [permRound_P]
  rw [hconj, conjTranspose_mul, hP]
  simp only [Matrix.mul_assoc]

end Round

/-! ## The measured run through the compiled round -/

section Run

variable (m n w c : ℕ) [NeZero m] [NeZero n] [NeZero c]
variable (ν₁ ν₂ : Fin c → Fin m)
variable {q k a : ℕ}

/-- The run of a multi-round adversary whose rounds are the record copy
    followed by the unitary of the compiled query round. -/
def runMRCompiled (A : QAdvMR m n (w * ancDim m n c) q k c a)
    (φ : Fin c → Fin n → Fin n → Fin a)
    (Ans : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (f : Fin c → Fin a) : QComp (m * n * (w * ancDim m n c)) Bool :=
  QComp.qbind (mrChainR (oracleQ m n (w * ancDim m n c) H) k q (A.seg 0) (Fin.tail A.seg)
    fun _ => compiledRound m n w c ν₁ ν₂ φ Ans H f) fun _ => A.measure

/-- At an initial state supported by the clean slice the measured multi-round
    run and the run with the compiled round have the same branches. -/
theorem runMR_measured_eq_compiled (A : QAdvMR m n (w * ancDim m n c) q k c a)
    (φ : Fin c → Fin n → Fin n → Fin a)
    (Ans : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (hseg : ∀ j i, (A.seg j i : Matrix _ _ ℂ) * cleanProjM m n w c =
      cleanProjM m n w c * (A.seg j i : Matrix _ _ ℂ))
    (hrounds : ∀ j, A.rounds j = permRound m n w c Ans)
    (b : Bool) (ρ : Matrix (Fin (m * n * (w * ancDim m n c))) (Fin (m * n * (w * ancDim m n c))) ℂ)
    (hρ : SupportedOn (cleanProjM m n w c) ρ) :
    (runMR A H (queryFun m n c ν₁ ν₂ φ H)).branch b ρ =
      (runMRCompiled m n w c ν₁ ν₂ A φ Ans H (queryFun m n c ν₁ ν₂ φ H)).branch b ρ := by
  unfold runMR runMRCompiled
  rw [qbind_unit_branch, qbind_unit_branch,
    mrChain_eq_mrChainR (oracleQ m n (w * ancDim m n c) H) (queryFun m n c ν₁ ν₂ φ H)
      k q (A.seg 0) (Fin.tail A.seg) A.rounds]
  refine congrArg _ ?_
  refine mrChainR_branch_congr (cleanProjM_conjTranspose m n w c) _
    (oracleQ_preservesSupport m n w c H) k q (A.seg 0) (Fin.tail A.seg) _ _
    (fun i => hseg 0 i) (fun j i => hseg j.succ i) (fun j => ?_) (fun j σ hσ => ?_) ρ hρ
  · rw [hrounds j]
    intro σ hσ
    rw [roundU_permRound_branch_eq m n w c ν₁ ν₂ φ Ans H σ hσ, compiledRound_branch]
    exact preservesSupport_unitaryChannel (cleanProjM_conjTranspose m n w c)
      (roundChainU_comm_cleanProjM m n w c ν₁ ν₂ φ Ans H) _
      (roundU_recordCopy_preservesSupport (queryFun m n c ν₁ ν₂ φ H) σ hσ)
  · rw [hrounds j]
    exact roundU_permRound_branch_eq m n w c ν₁ ν₂ φ Ans H σ hσ

/-- At an initial state supported by the clean slice the measured multi-round
    run and the run with the compiled round accept with the same
    probability. -/
theorem prOutMR_eq_compiled (A : QAdvMR m n (w * ancDim m n c) q k c a)
    (φ : Fin c → Fin n → Fin n → Fin a)
    (Ans : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (hseg : ∀ j i, (A.seg j i : Matrix _ _ ℂ) * cleanProjM m n w c =
      cleanProjM m n w c * (A.seg j i : Matrix _ _ ℂ))
    (hrounds : ∀ j, A.rounds j = permRound m n w c Ans)
    (hinit : SupportedOn (cleanProjM m n w c) A.init.val) :
    prOutMR A H (queryFun m n c ν₁ ν₂ φ H) =
      prTrue_Q (runMRCompiled m n w c ν₁ ν₂ A φ Ans H (queryFun m n c ν₁ ν₂ φ H)) A.init := by
  rw [prOutMR, prTrue_Q, prTrue_Q,
    runMR_measured_eq_compiled m n w c ν₁ ν₂ A φ Ans H hseg hrounds true A.init.val hinit]

end Run

/-! ## The oracle queries of the compiled round -/

section Count

variable (m n w c : ℕ) [NeZero m] [NeZero n] [NeZero c]
variable (ν₁ ν₂ : Fin c → Fin m)
variable {a : ℕ}

/-- The compiled round is five oracle-independent unitaries interleaved with
    four copies of the oracle unitary. -/
theorem roundChainU_four_queries (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) :
    ∃ S₀ S₁ S₂ S₃ S₄ : Matrix (Fin (m * n * (w * ancDim m n c)))
        (Fin (m * n * (w * ancDim m n c))) ℂ,
      ∀ H : Fin m → Fin n,
        (roundChainU m n w c ν₁ ν₂ φ A H : Matrix _ _ ℂ) =
          S₄ * (oracleU m n (w * ancDim m n c) H : Matrix _ _ ℂ) *
            S₃ * (oracleU m n (w * ancDim m n c) H : Matrix _ _ ℂ) *
            S₂ * (oracleU m n (w * ancDim m n c) H : Matrix _ _ ℂ) *
            S₁ * (oracleU m n (w * ancDim m n c) H : Matrix _ _ ℂ) * S₀ := by
  refine ⟨(permUnitary (stepZero m n w c ν₁) : Matrix _ _ ℂ),
    (permUnitary (stepOne m n w c ν₂) : Matrix _ _ ℂ),
    (permUnitary (stepTwo m n w c φ A) : Matrix _ _ ℂ),
    (permUnitary (stepThree m n w c ν₂) : Matrix _ _ ℂ),
    (permUnitary (stepFour m n w c ν₁) : Matrix _ _ ℂ), fun H => ?_⟩
  exact roundChainU_eq_chain m n w c ν₁ ν₂ φ A H

/-- The oracle queries of a run with a head segment of `q₀` queries and `k`
    further segments of `q` queries, each preceded by a compiled round of four
    queries. -/
theorem compiledQueryCount (q q₀ k : ℕ) : q₀ + k * (q + 4) = flatQ (q + 4) k q₀ :=
  (flatQ_eq (q + 4) k q₀).symm

end Count

end CatCrypt.Quantum.QROM
