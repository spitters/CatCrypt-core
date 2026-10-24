/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.QOwcpaAux
public import CatCryptCore.Quantum.QROM.RoundWeightDeferred

/-!
# The one-wayness game with measured decapsulation rounds

`qOwcpaAux` defines the output of its adversary as a query-register measurement
of a prefix of the single-run adversary `toQAdv A f`, in which each round is a
deferred measurement recorded on an ancilla. This module states the same
probability for the multi-round run in which each round is measured, cut at the
same query, and proves the two equal.

## Main definitions

* `mrPrefix O f k q₀ head tail R j` — the multi-round chain over a `Bool`-valued
  oracle, cut after the unitary at flat index `j`
* `mrPrefixU O f k q₀ head tail R j` — the same chain over a `Unit`-valued
  oracle
* `prOutPrefixMR A H f S j` — the probability that the multi-round run of `A`
  with measured rounds, cut after flat index `j`, has its query register in `S`
* `qOwcpaAuxRunMR`, `qOwcpaAuxMR` — the winning probabilities of the one-wayness
  game with the adversary's output given by `prOutPrefixMR`

## Main results

* `trace_flatten_prefix` — a prefix of the flattened adversary and the cut
  multi-round chain agree on every observable `X ⊗ 1 ⊗ ⋯ ⊗ 1`
* `prOut_queryPrefix_toQAdv` —
  `prOut (queryPrefix (toQAdv A f) S j) H = prOutPrefixMR A H f S j`
* `qOwcpaAuxRun_eq_measured`, `qOwcpaAux_eq_measured` — the game of
  `QOwcpaAux` is the game with measured decapsulation rounds

## The cut

The cut at flat index `j` keeps the unitaries `U₀, …, U_j` of the flattened
adversary. When `j` is the first index of a segment after round `r`, that
unitary is the merge of the last unitary of the previous segment, the deferred
round and the first unitary of the segment, so the cut run contains round `r`
and the first unitary of the segment after it. `mrPrefix` follows the same
convention.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.Measurement
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The cut multi-round chain -/

section Cut

variable {d c a q : ℕ}

theorem flatQ_succ_sub_lt {k q₀ j : ℕ} (hj : j < flatQ q (k + 1) q₀) (h : ¬ j < q₀) :
    j - q₀ < flatQ q k q := by
  rw [flatQ, flatQ_eq] at hj
  rw [flatQ_eq]
  omega

/-- The multi-round chain over a `Bool`-valued oracle cut after the unitary at
flat index `j`. -/
def mrPrefix (O : QComp d Bool) (f : Fin c → Fin a) :
    (k : ℕ) → (q₀ : ℕ) → (Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → ClassicalRound d c a) → Fin (flatQ q k q₀) → QComp d Bool
  | 0, _, head, _, _, j => scChain O j fun i => head (Fin.castLE (Nat.succ_le_succ j.isLt.le) i)
  | k + 1, q₀, head, tail, R, j =>
    if h : (j : ℕ) < q₀ then scChain O j fun i => head (Fin.castLE (by omega) i)
    else QComp.qbind (scChain O q₀ head) fun b => QComp.qbind (roundU (R 0) f) fun _ =>
      QComp.qbind (mrPrefix O f k q (tail 0) (Fin.tail tail) (Fin.tail R)
        ⟨j - q₀, flatQ_succ_sub_lt j.isLt h⟩) fun b' => QComp.qpure (b || b')

/-- The multi-round chain over a `Unit`-valued oracle cut after the unitary at
flat index `j`. -/
def mrPrefixU (O : QComp d Unit) (f : Fin c → Fin a) :
    (k : ℕ) → (q₀ : ℕ) → (Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → ClassicalRound d c a) → Fin (flatQ q k q₀) → QComp d Unit
  | 0, _, head, _, _, j =>
    oracleChain O j fun i => head (Fin.castLE (Nat.succ_le_succ j.isLt.le) i)
  | k + 1, q₀, head, tail, R, j =>
    if h : (j : ℕ) < q₀ then oracleChain O j fun i => head (Fin.castLE (by omega) i)
    else QComp.qbind (oracleChain O q₀ head) fun _ => QComp.qbind (roundU (R 0) f) fun _ =>
      mrPrefixU O f k q (tail 0) (Fin.tail tail) (Fin.tail R)
        ⟨j - q₀, flatQ_succ_sub_lt j.isLt h⟩

theorem mrPrefix_mk_congr (O : QComp d Bool) (f : Fin c → Fin a) (k q₀ : ℕ)
    (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (R : Fin k → ClassicalRound d c a) {j j' : ℕ} (hj : j < flatQ q k q₀)
    (hj' : j' < flatQ q k q₀) (h : j = j') :
    mrPrefix O f k q₀ head tail R ⟨j, hj⟩ = mrPrefix O f k q₀ head tail R ⟨j', hj'⟩ := by
  subst h; rfl

/-- Before the end of the head, the cut chain is a prefix of the head chain. -/
theorem mrPrefix_of_lt (O : QComp d Bool) (f : Fin c → Fin a) (k q₀ : ℕ)
    (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (R : Fin k → ClassicalRound d c a) (j : ℕ) (hj : j < flatQ q k q₀) (h : j < q₀) :
    mrPrefix O f k q₀ head tail R ⟨j, hj⟩ =
      scChain O j fun i => head (Fin.castLE (by omega) i) := by
  cases k with
  | zero => rfl
  | succ k => simp only [mrPrefix, dite_eq_left h]

end Cut

/-! ## Prefixes of a merged chain -/

section MergePrefix

variable {d q : ℕ}

/-- A prefix of a merged family that ends inside the first family is a prefix
of the first family. -/
theorem mergeChain_castLE_lt (V : Matrix.unitaryGroup (Fin d) ℂ)
    (B : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    ∀ (q₀ : ℕ) (A : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) (j : ℕ) (hj : j < q₀),
      (fun i : Fin (j + 1) => mergeChain V B q₀ A (Fin.castLE (by omega) i)) =
        fun i => A (Fin.castLE (by omega) i)
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | q₀ + 1, A, 0, _ => by
    funext i
    refine Fin.cases ?_ (fun i => i.elim0) i
    rfl
  | q₀ + 1, A, j + 1, hj => by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · have ih := congrFun (mergeChain_castLE_lt V B q₀ (Fin.tail A) j (by omega)) i
      exact ih

/-- A prefix of a merged family that ends inside the second family merges the
first family with a prefix of the second. -/
theorem mergeChain_castLE (V : Matrix.unitaryGroup (Fin d) ℂ)
    (B : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (j : ℕ) (hj : j ≤ q) :
    ∀ (q₀ : ℕ) (A : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ),
      (fun i : Fin (j + q₀ + 1) => mergeChain V B q₀ A (Fin.castLE (by omega) i)) =
        mergeChain V (fun i : Fin (j + 1) => B (Fin.castLE (by omega) i)) q₀ A
  | 0, A => by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · rfl
  | q₀ + 1, A => by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · exact congrFun (mergeChain_castLE V B j hj q₀ (Fin.tail A)) i

end MergePrefix

section CutMerge

variable {d c a q : ℕ}

/-- The cut chain over a merged head, cut inside or after the second family, is
the first family, the unitary `V`, and the cut chain from the second family on. -/
theorem mrPrefix_mergeChain (O : QComp d Bool) (f : Fin c → Fin a) (q₀ : ℕ)
    (A : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) (V : Matrix.unitaryGroup (Fin d) ℂ)
    (B : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (k : ℕ)
    (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (R : Fin k → ClassicalRound d c a) (j : ℕ) (h1 : j + q₀ < flatQ q k (q + q₀))
    (h2 : j < flatQ q k q) :
    mrPrefix O f k (q + q₀) (mergeChain V B q₀ A) tail R ⟨j + q₀, h1⟩ =
      QComp.qbind (scChain O q₀ A) fun b => QComp.qbind (unitaryChannel V) fun _ =>
        QComp.qbind (mrPrefix O f k q B tail R ⟨j, h2⟩) fun b' => QComp.qpure (b || b') := by
  cases k with
  | zero =>
    have hq : j ≤ q := by rw [flatQ] at h2; omega
    show scChain O (j + q₀) (fun i => mergeChain V B q₀ A (Fin.castLE _ i)) = _
    rw [mergeChain_castLE V B j hq q₀ A, scChain_mergeChain]
    rfl
  | succ k =>
    by_cases h : j < q
    · rw [mrPrefix_of_lt _ _ _ _ _ _ _ _ _ (by omega), mrPrefix_of_lt _ _ _ _ _ _ _ _ _ h,
        mergeChain_castLE V B j h.le q₀ A, scChain_mergeChain]
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + q := ⟨j - q, by omega⟩
      have hl : ¬ j' + q + q₀ < q + q₀ := by omega
      simp only [mrPrefix, dite_eq_right hl, dite_eq_right h, scChain_mergeChain, QComp.qbind_assoc,
        QComp.qpure_qbind, Bool.or_assoc, show j' + q + q₀ - (q + q₀) = j' by omega,
        Nat.add_sub_cancel]

end CutMerge

/-! ## Peeling one round from a cut chain -/

section CutPeel

variable {d c a q d' : ℕ}

theorem liftsQ_mrPrefix (e : Fin (d * c) ≃ Fin d') (O : QComp d Bool) (O' : QComp d' Bool)
    (hO : LiftsQ e O O') (f : Fin c → Fin a) : ∀ (k q₀ : ℕ)
    (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (R : Fin k → ClassicalRound d c a) (j : Fin (flatQ q k q₀)),
    LiftsQ e (mrPrefix O f k q₀ head tail R j)
      (mrPrefix O' f k q₀ (liftU e ∘ head) (fun j => liftU e ∘ tail j) (liftR e ∘ R) j)
  | 0, q₀, head, _, _, j => liftsQ_scChain e O O' hO j _
  | k + 1, q₀, head, tail, R, j => by
    by_cases h : (j : ℕ) < q₀
    · simp only [mrPrefix, dite_eq_left h]
      exact liftsQ_scChain e O O' hO j _
    · simp only [mrPrefix, dite_eq_right h]
      exact liftsQ_qbind e (liftsQ_scChain e O O' hO q₀ head) fun b =>
        liftsQ_qbind e (liftsQ_roundU e (R 0) f) fun _ =>
          liftsQ_qbind e (liftsQ_mrPrefix e O O' hO f k q (tail 0) (Fin.tail tail) (Fin.tail R) _)
            fun b' => liftsQ_qpure e _

variable [NeZero c]

/-- The deferred round between a lifted head chain and a lifted continuation,
on `ρ ⊗ |0⟩⟨0|` and seen through `X ⊗ 1`, is the measured round between the
head chain and the continuation on `ρ`. -/
theorem trace_kr_one_mul_head_roundV (e : Fin (d * c) ≃ Fin d') (O : QComp d Bool)
    (O' : QComp d' Bool) (hO : LiftsQ e O O') (f : Fin c → Fin a) (q₀ : ℕ)
    (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) (R : ClassicalRound d c a)
    (Rest : QComp d Bool) (Rest' : QComp d' Bool) (hRest : LiftsQ e Rest Rest')
    (X ρ : Matrix (Fin d) (Fin d) ℂ) (b : Bool) :
    (kr e X 1 * (QComp.qbind (scChain O' q₀ (liftU e ∘ head)) fun b₁ =>
        QComp.qbind (unitaryChannel (roundV e R f)) fun _ =>
          QComp.qbind Rest' fun b₂ => QComp.qpure (b₁ || b₂)).branch b
        (kr e ρ (ancProj 0))).trace =
      (X * (QComp.qbind (scChain O q₀ head) fun b₁ => QComp.qbind (roundU R f) fun _ =>
        QComp.qbind Rest fun b₂ => QComp.qpure (b₁ || b₂)).branch b ρ).trace := by
  simp only [qbind_branch_apply, tsum_fintype, Fintype.sum_unique, qpure_branch_apply]
  simp_rw [Finset.mul_sum, trace_sum]
  refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
  split_ifs
  · rw [liftsQ_scChain e O O' hO q₀ head b₁ ρ (ancProj 0)]
    exact trace_kr_one_mul_roundV e R f _ _ hRest X _ b₂
  · simp

/-- The peel identity for cut chains: the cut chain of the head with one round
deferred, on `ρ ⊗ |0⟩⟨0|` and seen through `X ⊗ 1`, is the cut chain with that
round measured on `ρ`. -/
theorem trace_peel_prefix (e : Fin (d * c) ≃ Fin d') (O : QComp d Bool) (O' : QComp d' Bool)
    (hO : LiftsQ e O O') (f : Fin c → Fin a) (k q₀ : ℕ)
    (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (tail : Fin (k + 1) → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (R : Fin (k + 1) → ClassicalRound d c a) (X ρ : Matrix (Fin d) (Fin d) ℂ) (b : Bool)
    (j : Fin (flatQ q (k + 1) q₀)) :
    (kr e X 1 * (mrPrefix O' f k (q + q₀)
        (mergeChain (roundV e (R 0) f) (liftU e ∘ tail 0) q₀ (liftU e ∘ head))
        (fun j => liftU e ∘ Fin.tail tail j) (liftR e ∘ Fin.tail R) j).branch b
          (kr e ρ (ancProj 0))).trace =
      (X * (mrPrefix O f (k + 1) q₀ head tail R j).branch b ρ).trace := by
  obtain ⟨jv, hjv⟩ := j
  have hjv' : jv < flatQ q k (q + q₀) := hjv
  change (kr e X 1 * (mrPrefix O' f k (q + q₀) _ _ _ ⟨jv, hjv'⟩).branch b
    (kr e ρ (ancProj 0))).trace = _
  by_cases h : jv < q₀
  · rw [mrPrefix_of_lt _ _ _ _ _ _ _ _ _ (by omega : jv < q + q₀),
      mergeChain_castLE_lt _ _ q₀ _ jv h]
    simp only [mrPrefix, dite_eq_left h]
    have hl := liftsQ_scChain e O O' hO jv (fun i => head (Fin.castLE (by omega) i)) b ρ
      (ancProj 0)
    erw [hl]
    rw [kr_mul, one_mul, trace_kr, trace_ancProj, mul_one]
  · obtain ⟨j', rfl⟩ : ∃ j', jv = j' + q₀ := ⟨jv - q₀, by omega⟩
    have h2 : j' < flatQ q k q := by
      have := flatQ_succ_sub_lt hjv h
      rwa [Nat.add_sub_cancel] at this
    rw [mrPrefix_mergeChain O' f q₀ _ _ _ k _ _ j' hjv' h2]
    simp only [mrPrefix, dite_eq_right h]
    rw [mrPrefix_mk_congr O f k q (tail 0) (Fin.tail tail) (Fin.tail R) _ h2
      (Nat.add_sub_cancel j' q₀)]
    exact trace_kr_one_mul_head_roundV e O O' hO f q₀ head (R 0) _ _
      (liftsQ_mrPrefix e O O' hO f k q (tail 0) (Fin.tail tail) (Fin.tail R) ⟨j', h2⟩) X ρ b

end CutPeel

/-! ## Prefixes of the flattened adversary -/

section FlattenPrefix

variable {m n w q k c a : ℕ}

/-- The prefix of the flattened adversary cut after flat index `j` and the cut
multi-round chain agree on every observable `X ⊗ 1 ⊗ ⋯ ⊗ 1` and every branch
of the semi-classical chain. -/
theorem trace_flatten_prefix [NeZero n] [NeZero c] (H : Fin m → Fin n) (S : Finset (Fin m))
    (f : Fin c → Fin a) :
    ∀ (k : ℕ) {w q₀ : ℕ} (A : MRH m n w q q₀ k c a)
      (X : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) (b : Bool) (j : Fin (flatQ q k q₀)),
      (liftK c k X * (scChain (scOracleQ m n (ancW c k w) H S) j fun i =>
          (flatten f k A).U (Fin.castLE (Nat.succ_le_succ j.isLt.le) i)).branch b
          (flatten f k A).init.val).trace =
        (X * (mrPrefix (scOracleQ m n w H S) f k q₀ A.head A.tail A.rounds j).branch b
          A.init.val).trace
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, w, q₀, A, X, b, j =>
    (trace_flatten_prefix H S f k (peel f A) (kr (ancE m n w c) X 1) b j).trans
      (trace_peel_prefix (ancE m n w c) _ _ (liftsQ_scOracleQ H S) f k q₀ A.head A.tail
        A.rounds X A.init.val b j)

variable {d : ℕ}

/-- A `Bool`-valued oracle that always returns `false` gives the `Unit` cut
chain. -/
theorem mrPrefix_qbind_pure_false (O : QComp d Unit) (f : Fin c → Fin a) : ∀ (k q₀ : ℕ)
    (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (R : Fin k → ClassicalRound d c a) (j : Fin (flatQ q k q₀)),
    mrPrefix (QComp.qbind O fun _ => QComp.qpure false) f k q₀ head tail R j =
      QComp.qbind (mrPrefixU O f k q₀ head tail R j) fun _ => QComp.qpure false
  | 0, _, _, _, _, _ => scChain_qbind_pure_false O _ _
  | k + 1, q₀, head, tail, R, j => by
    by_cases h : (j : ℕ) < q₀
    · simp only [mrPrefix, mrPrefixU, dite_eq_left h, scChain_qbind_pure_false]
    · simp only [mrPrefix, mrPrefixU, dite_eq_right h, scChain_qbind_pure_false,
        mrPrefix_qbind_pure_false O f k q (tail 0) (Fin.tail tail) (Fin.tail R),
        QComp.qbind_assoc, QComp.qpure_qbind, Bool.false_or]

end FlattenPrefix

/-! ## The measured-rounds output -/

section Measured

variable {m n w q k c a : ℕ} [NeZero n]

/-- The probability that the multi-round run of `A` against `H` with measured
rounds answered by `f`, cut after the unitary at flat index `j`, has its query
register in `S`. -/
def prOutPrefixMR (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) (j : Fin (flatQ q k q)) : ℝ≥0∞ :=
  prTrue_Q (QComp.qbind (mrPrefixU (oracleQ m n w H) f k q (A.seg 0) (Fin.tail A.seg) A.rounds j)
    fun _ => measProj (projS m n w S) (projS_conjTranspose m n w S) (projS_mul_self m n w S))
    A.init

/-- `prOutPrefixMR` through the `false` branch of the semi-classical cut chain
at `S = ∅`. -/
theorem prOutPrefixMR_eq_trace (A : QAdvMR m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (S : Finset (Fin m)) (j : Fin (flatQ q k q)) :
    prOutPrefixMR A H f S j = ENNReal.ofReal (projS m n w S *
      (mrPrefix (scOracleQ m n w H ∅) f k q (A.seg 0) (Fin.tail A.seg) A.rounds j).branch false
        A.init.val).trace.re := by
  unfold prOutPrefixMR prTrue_Q
  rw [qbind_unit_branch, measProj_branch_true, projS_conjTranspose,
    trace_proj_mul_mul_proj (projS_mul_self m n w S), scOracleQ_empty,
    mrPrefix_qbind_pure_false, qbind_unit_branch, qpure_branch_apply, ite_eq_left rfl]

variable [NeZero c]

/-- The query-register measurement of a prefix of the single-run embedding is
the query-register measurement of the multi-round run with measured rounds, cut
at the same query. -/
theorem prOut_queryPrefix_toQAdv (A : QAdvMR m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (S : Finset (Fin m)) (j : Fin (flatQ q k q)) :
    prOut (queryPrefix (toQAdv A f) S j) H = prOutPrefixMR A H f S j := by
  rw [prOut_eq_trace_scChain_empty, prOutPrefixMR_eq_trace]
  show ENNReal.ofReal (projS m n (ancW c k w) S * _).trace.re = _
  rw [← liftK_projS S k]
  exact congrArg (fun t : ℂ => ENNReal.ofReal t.re)
    (trace_flatten_prefix H ∅ f k A.toMRH (projS m n w S) false j)

end Measured

/-! ## The game with measured decapsulation rounds -/

section Game

variable {m₁ m₂ n W q k c a : ℕ} {PK SK M C R K Hash Z ι : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [DecidableEq Z] [Fintype K] [Nonempty K]
  [Fintype R] [Fintype C] [DecidableEq C] [DecidableEq Hash] [Fintype ι]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n]

/-- The winning probability of `B` at a key pair, a challenge ciphertext and the
challenger's tables, in the run whose decapsulation rounds are measured: `B`
draws its coins, receives `pk`, `cst` and `Hq cst`, runs its multi-round
adversary against `auxOracle` with each round measured and answered by
`decapsHq Hq cst`, stops after its stop index, and wins when the measured query
register lies in `owWinSet`. -/
def qOwcpaAuxRunMR (B : QOwAuxAdv ι (m₁ + m₂) n W q k c a PK C K) (pk : PK) (sk : SK)
    (cst : C) (Hq : C → K) (G : Fin m₁ → Fin n) (J : Fin m₂ → Fin n) (T : C → Fin n) (z : Z) :
    ℝ≥0∞ :=
  ∑ x : ι, (Fintype.card ι : ℝ≥0∞)⁻¹ *
    prOutPrefixMR (B.prog pk cst (Hq cst) x) (auxOracle P hpk eG eJ eKR pk Hq G J T z)
      (decapsHq eC eKa Hq cst) (owWinSet P eG sk cst) (B.stop pk cst (Hq cst) x)

/-- The one-wayness game with oracle access and measured decapsulation rounds:
the sampling of `qOwcpaAux` with the winning probability `qOwcpaAuxRunMR`. -/
def qOwcpaAuxMR (B : QOwAuxAdv ι (m₁ + m₂) n W q k c a PK C K) : ℝ≥0∞ :=
  ∑ ks : PK × SK, P.keygen ks * ∑ m : M, (Fintype.card M : ℝ≥0∞)⁻¹ *
    ∑ r : R, (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ z : Z, (Fintype.card Z : ℝ≥0∞)⁻¹ *
      ∑ G : Fin m₁ → Fin n, (Fintype.card (Fin m₁ → Fin n) : ℝ≥0∞)⁻¹ *
        ∑ J : Fin m₂ → Fin n, (Fintype.card (Fin m₂ → Fin n) : ℝ≥0∞)⁻¹ *
          ∑ Hq : C → K, (Fintype.card (C → K) : ℝ≥0∞)⁻¹ *
            ∑ T : C → Fin n, (Fintype.card (C → Fin n) : ℝ≥0∞)⁻¹ *
              qOwcpaAuxRunMR P hpk eG eJ eKR eC eKa B ks.1 ks.2 (P.enc ks.1 m r) Hq G J T z

variable [NeZero c]

omit [Fintype PK] [Fintype SK] [Fintype M] [Fintype Z] [Fintype K] [Fintype R] [Fintype C] in
/-- The winning probability of `qOwcpaAux` at every key pair, challenge and
table is the one of the run with measured decapsulation rounds. -/
theorem qOwcpaAuxRun_eq_measured (B : QOwAuxAdv ι (m₁ + m₂) n W q k c a PK C K) (pk : PK)
    (sk : SK) (cst : C) (Hq : C → K) (G : Fin m₁ → Fin n) (J : Fin m₂ → Fin n)
    (T : C → Fin n) (z : Z) :
    qOwcpaAuxRun P hpk eG eJ eKR eC eKa B pk sk cst Hq G J T z =
      qOwcpaAuxRunMR P hpk eG eJ eKR eC eKa B pk sk cst Hq G J T z := by
  unfold qOwcpaAuxRun qOwcpaAuxRunMR
  simp only [prOut_queryPrefix_toQAdv]

/-- `qOwcpaAux` is the one-wayness game with measured decapsulation rounds. -/
theorem qOwcpaAux_eq_measured (B : QOwAuxAdv ι (m₁ + m₂) n W q k c a PK C K) :
    qOwcpaAux P hpk eG eJ eKR eC eKa B = qOwcpaAuxMR P hpk eG eJ eKR eC eKa B := by
  unfold qOwcpaAux qOwcpaAuxMR
  simp only [qOwcpaAuxRun_eq_measured]

end Game

end CatCrypt.Quantum.QROM
