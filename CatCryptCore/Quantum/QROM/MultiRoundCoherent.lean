/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.QueryRoundAgreement

/-!
# Adversaries with coherent rounds

A coherent round is a controlled unitary whose control is a projective
decomposition of the register itself: the answer unitary selected by the control
value is applied without measuring and without copying the control to an
ancilla. When every answer unitary commutes with the control projectors the
round is a single unitary of the register, so an adversary with `k` coherent
rounds is a `QAdv` on the same register, obtained by merging each round unitary
into the surrounding segments.

## Main definitions

* `CoherentRound d c a` — the control projectors `P y`, the answer unitaries
  `ans z`, and the commutation of the two
* `CoherentRound.op`, `roundCoh` — the round `∑ y, ans (f y) * P y` as a matrix
  and as a unitary
* `mrChainCoh`, `mrChainCohSC` — the chain `head ; (round ; segment)ᵏ` over a
  `Unit`-valued and a `Bool`-valued oracle
* `MRHCoh`, `peelCoh`, `flattenCoh` — the head-tail form of an adversary with
  coherent rounds and the merging of one round and of all rounds
* `QAdvMRCoh m n w q k c a` — `k + 1` segments of `q` queries, `k` coherent
  rounds, an initial state and a final projector
* `runMRCoh`, `runSCMRCoh`, `prOutMRCoh`, `prFindMRCoh` — the two runs and the
  two probabilities
* `toQAdvCoh` — the single-run adversary of an adversary with coherent rounds
* `permRoundCoh` — the coherent round on the extended register of a query round,
  with the record slot as control and `parkLift` as answer

## Main results

* `roundCoh_mul_conjTranspose_self` — the round is unitary
* `mrChainCoh_flatten`, `mrChainCohSC_flatten` — the chain of an adversary with
  coherent rounds is the chain of its `flattenCoh`
* `runMRCoh_eq`, `runSCMRCoh_eq`, `prOutMRCoh_eq`, `prFindMRCoh_eq` — the runs
  and the probabilities of an adversary with coherent rounds are those of its
  `toQAdvCoh`
* `roundCoh_permRoundCoh_mul_cleanRecProj` — on the clean record-`y` slice the
  round `roundCoh (permRoundCoh …)` agrees with the unitary `roundChainU` of the
  compiled query round

## Registers and query count

The register of `toQAdvCoh` is the register of the adversary: merging a coherent
round allocates no ancilla and changes no dimension, so the work register `w` is
unchanged and the query count becomes `flatQ q k q`. The commutation field of
`CoherentRound` is the hypothesis under which `roundCoh_mul_conjTranspose_self`
proves `∑ y, ans (f y) * P y` unitary. The agreement of `permRoundCoh` with
`roundChainU` in `roundCoh_permRoundCoh_mul_cleanRecProj` is the agreement of the
two matrices on the clean record-`y` slice, as in `roundChainU_mul_cleanRecProj`.

## References

* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], Theorem 1
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix Classical CatCrypt.Quantum CatCrypt.Quantum.UnitaryChannel
  CatCrypt.Quantum.Measurement

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Coherent rounds -/

section Round

variable {d c a : ℕ}

/-- A coherent round on a register of dimension `d`: a decomposition of the
    register into `c` control subspaces and an answer unitary for each answer in
    `Fin a`, each answer unitary commuting with the control projectors. -/
structure CoherentRound (d c a : ℕ) where
  /-- The control projectors. -/
  P : Fin c → Matrix (Fin d) (Fin d) ℂ
  P_conjTranspose : ∀ y, (P y)ᴴ = P y
  P_mul_self : ∀ y, P y * P y = P y
  P_orth : ∀ y y', y ≠ y' → P y * P y' = 0
  P_sum : ∑ y, P y = 1
  /-- The answer unitaries. -/
  ans : Fin a → Matrix.unitaryGroup (Fin d) ℂ
  /-- Each answer unitary preserves the control decomposition. -/
  ans_comm : ∀ z y, (ans z : Matrix (Fin d) (Fin d) ℂ) * P y =
    P y * (ans z : Matrix (Fin d) (Fin d) ℂ)

/-- The answer unitaries of a coherent round commute with the control
    projectors after conjugate transposition. -/
theorem CoherentRound.ans_conjTranspose_comm (R : CoherentRound d c a) (z : Fin a) (y : Fin c) :
    (R.ans z : Matrix (Fin d) (Fin d) ℂ)ᴴ * R.P y = R.P y * (R.ans z : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
  have h := congrArg Matrix.conjTranspose (R.ans_comm z y)
  rw [conjTranspose_mul, conjTranspose_mul, R.P_conjTranspose] at h
  exact h.symm

/-- The round `∑ y, ans (f y) * P y` with classical function `f`. -/
def CoherentRound.op (R : CoherentRound d c a) (f : Fin c → Fin a) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ y, (R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y

theorem CoherentRound.op_mul_conjTranspose_self (R : CoherentRound d c a) (f : Fin c → Fin a) :
    R.op f * (R.op f)ᴴ = 1 := by
  unfold CoherentRound.op
  rw [conjTranspose_sum, Finset.sum_mul_sum]
  have h : ∀ y, ∑ y', ((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y) *
      ((R.ans (f y') : Matrix (Fin d) (Fin d) ℂ) * R.P y')ᴴ = R.P y := by
    intro y
    rw [Finset.sum_eq_single y]
    · rw [conjTranspose_mul, R.P_conjTranspose, Matrix.mul_assoc,
        ← Matrix.mul_assoc (R.P y) (R.P y), R.P_mul_self,
        ← R.ans_conjTranspose_comm, ← Matrix.mul_assoc,
        ← star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.mp (R.ans (f y)).prop, one_mul]
    · intro y' _ hy'
      rw [conjTranspose_mul, R.P_conjTranspose, Matrix.mul_assoc,
        ← Matrix.mul_assoc (R.P y) (R.P y'), R.P_orth y y' (Ne.symm hy'),
        Matrix.zero_mul, Matrix.mul_zero]
    · intro h; exact absurd (Finset.mem_univ y) h
  rw [Finset.sum_congr rfl fun y _ => h y, R.P_sum]

/-- The coherent round as one unitary of the register. -/
def roundCoh (R : CoherentRound d c a) (f : Fin c → Fin a) : Matrix.unitaryGroup (Fin d) ℂ :=
  ⟨R.op f, by
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]
    exact R.op_mul_conjTranspose_self f⟩

theorem roundCoh_val (R : CoherentRound d c a) (f : Fin c → Fin a) :
    (roundCoh R f : Matrix (Fin d) (Fin d) ℂ) =
      ∑ y, (R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y := rfl

theorem roundCoh_mul_conjTranspose_self (R : CoherentRound d c a) (f : Fin c → Fin a) :
    (roundCoh R f : Matrix (Fin d) (Fin d) ℂ) * (roundCoh R f : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 :=
  R.op_mul_conjTranspose_self f

end Round

/-! ## The chain of an adversary with coherent rounds -/

section Chain

variable {d c a q : ℕ}

/-- `head ; (round ; segment)ᵏ` over a `Unit`-valued oracle. -/
def mrChainCoh (O : QComp d Unit) (f : Fin c → Fin a) :
    (k : ℕ) → (q₀ : ℕ) → (Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → CoherentRound d c a) → QComp d Unit
  | 0, q₀, head, _, _ => oracleChain O q₀ head
  | k + 1, q₀, head, tail, R =>
    QComp.qbind (oracleChain O q₀ head) fun _ =>
      QComp.qbind (unitaryChannel (roundCoh (R 0) f)) fun _ =>
        mrChainCoh O f k q (tail 0) (Fin.tail tail) (Fin.tail R)

/-- `head ; (round ; segment)ᵏ` over a `Bool`-valued oracle, returning the
    disjunction of the oracle outcomes. -/
def mrChainCohSC (O : QComp d Bool) (f : Fin c → Fin a) :
    (k : ℕ) → (q₀ : ℕ) → (Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → CoherentRound d c a) → QComp d Bool
  | 0, q₀, head, _, _ => scChain O q₀ head
  | k + 1, q₀, head, tail, R =>
    QComp.qbind (scChain O q₀ head) fun b =>
      QComp.qbind (unitaryChannel (roundCoh (R 0) f)) fun _ =>
        QComp.qbind (mrChainCohSC O f k q (tail 0) (Fin.tail tail) (Fin.tail R)) fun b' =>
          QComp.qpure (b || b')

/-- The `Unit` chain of a merged family is the first chain, the unitary, and the
    second chain. -/
theorem oracleChain_mergeChain (O : QComp d Unit) (V : Matrix.unitaryGroup (Fin d) ℂ)
    (B : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (q₀ : ℕ)
    (A : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    oracleChain O (q + q₀) (mergeChain V B q₀ A) =
      QComp.qbind (oracleChain O q₀ A) fun _ => QComp.qbind (unitaryChannel V) fun _ =>
        oracleChain O q B := by
  induction q₀ with
  | zero =>
    cases q with
    | zero =>
      simp only [mergeChain, oracleChain, Fin.cons_zero, unitaryChannel_compose]
    | succ q =>
      simp only [mergeChain, oracleChain, Fin.cons_zero, Fin.tail_cons,
        unitaryChannel_qbind_unitaryChannel]
  | succ q₀ ih =>
    show oracleChain O (q + q₀ + 1) (Fin.cons (A 0) (mergeChain V B q₀ (Fin.tail A))) = _
    simp only [oracleChain, Fin.cons_zero, Fin.tail_cons, ih, QComp.qbind_assoc]

/-- The coherent chain over a merged head is the head chain, the round unitary,
    and the coherent chain from the first segment on. -/
theorem mrChainCoh_mergeChain (O : QComp d Unit) (f : Fin c → Fin a) (k q₀ : ℕ)
    (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) (V : Matrix.unitaryGroup (Fin d) ℂ)
    (B : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (R : Fin k → CoherentRound d c a) :
    mrChainCoh O f k (q + q₀) (mergeChain V B q₀ head) tail R =
      QComp.qbind (oracleChain O q₀ head) fun _ => QComp.qbind (unitaryChannel V) fun _ =>
        mrChainCoh O f k q B tail R := by
  cases k with
  | zero => simp only [mrChainCoh, oracleChain_mergeChain]
  | succ k =>
    simp only [mrChainCoh, oracleChain_mergeChain, QComp.qbind_assoc]

/-- The semi-classical coherent chain over a merged head. -/
theorem mrChainCohSC_mergeChain (O : QComp d Bool) (f : Fin c → Fin a) (k q₀ : ℕ)
    (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) (V : Matrix.unitaryGroup (Fin d) ℂ)
    (B : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (R : Fin k → CoherentRound d c a) :
    mrChainCohSC O f k (q + q₀) (mergeChain V B q₀ head) tail R =
      QComp.qbind (scChain O q₀ head) fun b => QComp.qbind (unitaryChannel V) fun _ =>
        QComp.qbind (mrChainCohSC O f k q B tail R) fun b' => QComp.qpure (b || b') := by
  cases k with
  | zero => simp only [mrChainCohSC, scChain_mergeChain]
  | succ k =>
    simp only [mrChainCohSC, scChain_mergeChain, QComp.qbind_assoc, QComp.qpure_qbind,
      Bool.or_assoc]

end Chain

/-! ## The head-tail form and its flattening -/

section Flatten

variable {m n w q q₀ k c a : ℕ}

/-- An adversary with coherent rounds in head-tail form: a head segment of `q₀`
    queries and `k` further segments of `q` queries, each preceded by a round. -/
structure MRHCoh (m n w q q₀ k c a : ℕ) where
  /-- The head segment. -/
  head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin (m * n * w)) ℂ
  /-- The segments after each round. -/
  tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin (m * n * w)) ℂ
  /-- The rounds. -/
  rounds : Fin k → CoherentRound (m * n * w) c a
  /-- The initial state. -/
  init : DensityMatrix (m * n * w)
  /-- The projector of the final measurement. -/
  final : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ
  final_conjTranspose : finalᴴ = final
  final_mul_self : final * final = final

/-- Absorb the first round into the head: the head, the round unitary and the
    first segment merge into one segment of `q + q₀` queries on the same
    register. -/
def peelCoh (f : Fin c → Fin a) (A : MRHCoh m n w q q₀ (k + 1) c a) :
    MRHCoh m n w q (q + q₀) k c a where
  head := mergeChain (roundCoh (A.rounds 0) f) (A.tail 0) q₀ A.head
  tail := Fin.tail A.tail
  rounds := Fin.tail A.rounds
  init := A.init
  final := A.final
  final_conjTranspose := A.final_conjTranspose
  final_mul_self := A.final_mul_self

/-- The single-run adversary of an adversary with coherent rounds: `k` rounds
    merged into the segments around them. -/
def flattenCoh (f : Fin c → Fin a) :
    (k : ℕ) → {q₀ : ℕ} → MRHCoh m n w q q₀ k c a → QAdv m n w (flatQ q k q₀)
  | 0, _, A => ⟨A.head, A.init, A.final, A.final_conjTranspose, A.final_mul_self⟩
  | k + 1, _, A => flattenCoh f k (peelCoh f A)

theorem flattenCoh_init (f : Fin c → Fin a) :
    ∀ (k : ℕ) {q₀ : ℕ} (A : MRHCoh m n w q q₀ k c a), (flattenCoh f k A).init = A.init
  | 0, _, _ => rfl
  | k + 1, _, A => flattenCoh_init f k (peelCoh f A)

theorem flattenCoh_final (f : Fin c → Fin a) :
    ∀ (k : ℕ) {q₀ : ℕ} (A : MRHCoh m n w q q₀ k c a), (flattenCoh f k A).final = A.final
  | 0, _, _ => rfl
  | k + 1, _, A => flattenCoh_final f k (peelCoh f A)

/-- The chain of an adversary with coherent rounds over a `Unit`-valued oracle
    is the chain of its flattening. -/
theorem mrChainCoh_flatten (O : QComp (m * n * w) Unit) (f : Fin c → Fin a) :
    ∀ (k : ℕ) {q₀ : ℕ} (A : MRHCoh m n w q q₀ k c a),
      oracleChain O (flatQ q k q₀) (flattenCoh f k A).U =
        mrChainCoh O f k q₀ A.head A.tail A.rounds
  | 0, _, _ => rfl
  | k + 1, q₀, A =>
    (mrChainCoh_flatten O f k (peelCoh f A)).trans
      (mrChainCoh_mergeChain O f k q₀ A.head (roundCoh (A.rounds 0) f) (A.tail 0)
        (Fin.tail A.tail) (Fin.tail A.rounds))

/-- The chain of an adversary with coherent rounds over a `Bool`-valued oracle
    is the chain of its flattening. -/
theorem mrChainCohSC_flatten (O : QComp (m * n * w) Bool) (f : Fin c → Fin a) :
    ∀ (k : ℕ) {q₀ : ℕ} (A : MRHCoh m n w q q₀ k c a),
      scChain O (flatQ q k q₀) (flattenCoh f k A).U =
        mrChainCohSC O f k q₀ A.head A.tail A.rounds
  | 0, _, _ => rfl
  | k + 1, q₀, A =>
    (mrChainCohSC_flatten O f k (peelCoh f A)).trans
      (mrChainCohSC_mergeChain O f k q₀ A.head (roundCoh (A.rounds 0) f) (A.tail 0)
        (Fin.tail A.tail) (Fin.tail A.rounds))

end Flatten

/-! ## Adversaries with coherent rounds and their runs -/

section MR

variable {m n w q k c a : ℕ}

/-- An adversary with coherent rounds: `k + 1` segments of `q` oracle queries,
    each segment given by its `q + 1` unitaries as in `QAdv`, `k` coherent
    rounds between consecutive segments, an initial state and a final
    projector. -/
structure QAdvMRCoh (m n w q k c a : ℕ) where
  /-- The unitaries of the segments. -/
  seg : Fin (k + 1) → Fin (q + 1) → Matrix.unitaryGroup (Fin (m * n * w)) ℂ
  /-- The rounds, round `j` between segments `j` and `j + 1`. -/
  rounds : Fin k → CoherentRound (m * n * w) c a
  /-- The initial state. -/
  init : DensityMatrix (m * n * w)
  /-- The projector of the final measurement. -/
  final : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ
  final_conjTranspose : finalᴴ = final
  final_mul_self : final * final = final

/-- The head-tail form: segment `0` is the head. -/
def QAdvMRCoh.toMRHCoh (A : QAdvMRCoh m n w q k c a) : MRHCoh m n w q q k c a where
  head := A.seg 0
  tail := Fin.tail A.seg
  rounds := A.rounds
  init := A.init
  final := A.final
  final_conjTranspose := A.final_conjTranspose
  final_mul_self := A.final_mul_self

/-- The final measurement of `A` as an instrument. -/
def QAdvMRCoh.measure (A : QAdvMRCoh m n w q k c a) : QComp (m * n * w) Bool :=
  measProj A.final A.final_conjTranspose A.final_mul_self

/-- Two projective measurements with the same projector are the same
    instrument. -/
theorem measProj_eq_of_proj_eq {d : ℕ} {P Q : Matrix (Fin d) (Fin d) ℂ} (h : P = Q)
    (hH : Pᴴ = P) (hI : P * P = P) (hH' : Qᴴ = Q) (hI' : Q * Q = Q) :
    measProj P hH hI = measProj Q hH' hI' := by
  subst h; rfl

variable [NeZero n]

/-- The standard run: segment `0` with `O_H`, round `0` with `f`, segment `1`,
    …, segment `k`, then the final measurement. -/
def runMRCoh (A : QAdvMRCoh m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) :
    QComp (m * n * w) Bool :=
  QComp.qbind (mrChainCoh (oracleQ m n w H) f k q (A.seg 0) (Fin.tail A.seg) A.rounds) fun _ =>
    A.measure

/-- The semi-classical run with `scOracleQ H S` in the segments, returning
    `(output, find)`. -/
def runSCMRCoh (A : QAdvMRCoh m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) : QComp (m * n * w) (Bool × Bool) :=
  QComp.qbind (mrChainCohSC (scOracleQ m n w H S) f k q (A.seg 0) (Fin.tail A.seg) A.rounds)
    fun fl => QComp.qbind A.measure fun out => QComp.qpure (out, fl)

/-- The probability that the standard run outputs `1`. -/
def prOutMRCoh (A : QAdvMRCoh m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) : ℝ≥0∞ :=
  prTrue_Q (runMRCoh A H f) A.init

/-- The probability of `Find` in the semi-classical run. -/
def prFindMRCoh (A : QAdvMRCoh m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) : ℝ≥0∞ :=
  prTrue_Q (QComp.qbind (runSCMRCoh A H f S) fun p => QComp.qpure p.2) A.init

/-- The single-run adversary of `A`: the same work register `w`, with
    `flatQ q k q` oracle queries. -/
def toQAdvCoh (A : QAdvMRCoh m n w q k c a) (f : Fin c → Fin a) :
    QAdv m n w (flatQ q k q) :=
  flattenCoh f k A.toMRHCoh

omit [NeZero n] in
theorem toQAdvCoh_init (A : QAdvMRCoh m n w q k c a) (f : Fin c → Fin a) :
    (toQAdvCoh A f).init = A.init :=
  flattenCoh_init f k A.toMRHCoh

omit [NeZero n] in
theorem toQAdvCoh_measure (A : QAdvMRCoh m n w q k c a) (f : Fin c → Fin a) :
    (toQAdvCoh A f).measure = A.measure :=
  measProj_eq_of_proj_eq (flattenCoh_final f k A.toMRHCoh) _ _ _ _

/-- The standard run of an adversary with coherent rounds is the run of its
    single-run embedding. -/
theorem runMRCoh_eq (A : QAdvMRCoh m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) :
    runMRCoh A H f = run (toQAdvCoh A f) H := by
  unfold runMRCoh run
  rw [toQAdvCoh_measure]
  unfold toQAdvCoh
  rw [mrChainCoh_flatten (oracleQ m n w H) f k A.toMRHCoh]
  rfl

/-- The semi-classical run of an adversary with coherent rounds is the
    semi-classical run of its single-run embedding. -/
theorem runSCMRCoh_eq (A : QAdvMRCoh m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) : runSCMRCoh A H f S = runSC (toQAdvCoh A f) H S := by
  unfold runSCMRCoh runSC
  rw [toQAdvCoh_measure]
  unfold toQAdvCoh
  rw [mrChainCohSC_flatten (scOracleQ m n w H S) f k A.toMRHCoh]
  rfl

/-- The acceptance probability of an adversary with coherent rounds is that of
    its single-run embedding. -/
theorem prOutMRCoh_eq (A : QAdvMRCoh m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) :
    prOutMRCoh A H f = prOut (toQAdvCoh A f) H := by
  unfold prOutMRCoh prOut
  rw [runMRCoh_eq, toQAdvCoh_init]

/-- The `Find` probability of an adversary with coherent rounds is that of its
    single-run embedding. -/
theorem prFindMRCoh_eq (A : QAdvMRCoh m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) : prFindMRCoh A H f S = prFind (toQAdvCoh A f) H S := by
  unfold prFindMRCoh prFind
  rw [runSCMRCoh_eq, toQAdvCoh_init]

end MR

/-! ## The compiled query round as a coherent round -/

section Query

variable (m n w c : ℕ) [NeZero m] [NeZero n] [NeZero c]
variable (ν₁ ν₂ : Fin c → Fin m)
variable {a : ℕ}

theorem diagonal_mul_permUnitary {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι)
    (g : ι → ℂ) :
    Matrix.diagonal g * (permUnitary σ : Matrix ι ι ℂ) =
      Matrix.of fun i j => if i = σ j then g i else 0 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · simp only [Matrix.diagonal_apply_eq, permUnitary_apply, Matrix.of_apply]
    by_cases h : i = σ j <;> simp [h]
  · intro b _ hb
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

omit [NeZero m] [NeZero n] [NeZero c] in
/-- An answer permutation of the query and work registers leaves the record slot
    of an index fixed. -/
theorem cleanRec_parkLift (B : Equiv.Perm ((Fin m × Fin n) × Fin w))
    (i : Fin (m * n * (w * ancDim m n c))) :
    cleanRec m n w c (parkLift m n w c B i) = cleanRec m n w c i := by
  simp [cleanRec, parkLift, parkLiftReg, Equiv.permCongr_apply]

omit [NeZero m] [NeZero n] [NeZero c] in
/-- The answer unitary of an answer permutation commutes with the projector onto
    the indices with record slot `y`. -/
theorem permUnitary_parkLift_mul_recProj (B : Equiv.Perm ((Fin m × Fin n) × Fin w))
    (y : Fin c) :
    (permUnitary (parkLift m n w c B) : Matrix _ _ ℂ) * recProj m n w c y =
      recProj m n w c y * (permUnitary (parkLift m n w c B) : Matrix _ _ ℂ) := by
  rw [recProj, permUnitary_mul_diagonal, diagonal_mul_permUnitary]
  ext i j
  simp only [Matrix.of_apply]
  by_cases h : i = parkLift m n w c B j
  · rw [if_pos h, if_pos h, h, cleanRec_parkLift]
  · rw [if_neg h, if_neg h]

omit [NeZero c] in
/-- The projector onto the record-`y'` indices restricted to the clean
    record-`y` slice. -/
theorem recProj_mul_cleanRecProj (y y' : Fin c) :
    recProj m n w c y' * cleanRecProj m n w c y =
      if y' = y then cleanRecProj m n w c y else 0 := by
  rw [recProj, cleanRecProj, Matrix.diagonal_mul_diagonal]
  split_ifs with h
  · subst h
    congr 1
    funext i
    split_ifs <;> simp_all
  · rw [← Matrix.diagonal_zero]
    congr 1
    funext i
    split_ifs <;> simp_all

/-- The coherent round on the extended register of a query round: the control is
    the record slot, the answer is an answer permutation of the query and work
    registers. -/
def permRoundCoh (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) :
    CoherentRound (m * n * (w * ancDim m n c)) c a where
  P := recProj m n w c
  P_conjTranspose := (permRound m n w c A).P_conjTranspose
  P_mul_self := (permRound m n w c A).P_mul_self
  P_orth := (permRound m n w c A).P_orth
  P_sum := (permRound m n w c A).P_sum
  ans := fun z => permUnitary (parkLift m n w c (A z))
  ans_comm := fun z y => permUnitary_parkLift_mul_recProj m n w c (A z) y

omit [NeZero m] [NeZero n] [NeZero c] in
theorem permRoundCoh_P (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (y : Fin c) :
    (permRoundCoh m n w c A).P y = recProj m n w c y := rfl

omit [NeZero m] [NeZero n] [NeZero c] in
theorem permRoundCoh_ans (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (z : Fin a) :
    (permRoundCoh m n w c A).ans z = permUnitary (parkLift m n w c (A z)) := rfl

/-- On the clean slice with record slot `y`, the coherent round of the record
    slot and the unitary of the compiled query round agree. -/
theorem roundCoh_permRoundCoh_mul_cleanRecProj (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n) (y : Fin c) :
    (roundCoh (permRoundCoh m n w c A) (queryFun m n c ν₁ ν₂ φ H) : Matrix _ _ ℂ) *
        cleanRecProj m n w c y =
      (roundChainU m n w c ν₁ ν₂ φ A H : Matrix _ _ ℂ) * cleanRecProj m n w c y := by
  rw [roundChainU_mul_cleanRecProj, permRound_ans, roundCoh_val]
  simp only [permRoundCoh_P, permRoundCoh_ans]
  rw [Finset.sum_mul, Finset.sum_eq_single y]
  · rw [Matrix.mul_assoc, recProj_mul_cleanRecProj, if_pos rfl]
  · intro y' _ hy'
    rw [Matrix.mul_assoc, recProj_mul_cleanRecProj, if_neg hy', Matrix.mul_zero]
  · intro h; exact absurd (Finset.mem_univ y) h

end Query

end CatCrypt.Quantum.QROM
