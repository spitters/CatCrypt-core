/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.KEMAdvNormalForm
public import CatCryptCore.Quantum.Stinespring
public import CatCryptCore.Quantum.CPCompMonad

/-!
# Multi-round adversaries with general local operations

A general multi-round adversary `QAdvMRGen` has the shape of `QAdvMR`, with two
differences: every local operation between two oracle calls is a
trace-preserving completely positive map on the whole register (a `CPComp`
with outcome `Unit`), and the initial state is any density matrix. The
classical rounds and the final projector are those of `QAdvMR`.

This module proves the embedding of `QAdvMR` into `QAdvMRGen` and the two
single steps of the reduction of `QAdvMRGen` to the unitary, pure-state normal
form: the Stinespring step for one local operation and the purification of the
initial state.

## Main definitions

* `blk e M i j` — block `(i, j)` of `M` on a register `Fin D ≃ Fin (d * c)`
* `DilatesQ e O O'` — `O'` reproduces `O` under the ancilla partial trace on
  inputs `ρ ⊗ |0⟩⟨0|`
* `stineU Φ hTP e` — a Stinespring unitary of a trace-preserving `Φ`
* `chainG`, `mrChainG` — the oracle chain and the multi-round chain with
  arbitrary `Unit` instruments as local operations
* `QAdvMRGen`, `runMRGen`, `prOutMRGen`, `KEMQAdvGen`
* `QAdvMR.toGen`, `KEMQAdv.toGen` — the embedding of unitary adversaries
* `liftCh e Φ hTP` — the channel `Φ ⊗ id` on the register extended by an ancilla
* `liftGen e A σ` — `A` with every operation tensored with `1` and initial state `σ`
* `purifyGen A` — `liftGen` at a purification of the initial state of `A`

## Main results

* `LiftsQ.trAnc_branch` — an instrument that lifts `O` along `e` commutes with
  the ancilla partial trace on every input, product or not
* `trace_kr_one_mul` — `tr ((X ⊗ 1) M) = tr (X · trAnc e M)`
* `dilatesQ_stineU` — the Stinespring unitary dilates `Φ`
* `dilatesQ_qbind_liftsQ`, `liftsQ_qbind_dilatesQ` — the dilation relation
  composes with lifted instruments before and after it
* `trace_stineU_step`, `trace_kr_one_mul_stineU_step` — the single Stinespring
  step: `U` on `σ ⊗ |0⟩⟨0|` followed by a lifted continuation has the trace, and
  the value of every observable `X ⊗ 1`, of `Φ` on `σ` followed by the
  continuation
* `prOutMRGen_toGen` — the embedding preserves the acceptance probability
* `prOutMRGen_liftGen` — lifting preserves the acceptance probability whenever
  the new initial state has the old one as its ancilla partial trace
* `prOutMRGen_purifyGen`, `purifyGen_init_pure` — the purified adversary has a
  pure initial state and the acceptance probability of `A`

## Register design

All registers have the shape `m * n * w`: the query register `m * n` and a
work register `w`. An ancilla `Fin c` is appended inside the work register
along `padE m n rfl : Fin (m * n * w * c) ≃ Fin (m * n * (w * c))` (equal to
`ancE m n w c`), so the oracle, the rounds (`liftRA`) and the final projector
(`kr e P 1`) of the extended register are the lifts of those of the original
register (`oracleU_lift`, `liftsQ_roundU_liftRA`, `liftsQ_measProj`).

* Purification appends one ancilla of dimension `m * n * w`: `purifyGen A` has
  work register `w * (m * n * w)`.
* Stinespring appends one ancilla of dimension `d * d` per local operation,
  `d = m * n * w` the current register: `stineU Φ hTP (padE m n rfl)` is a
  unitary on `m * n * (w * (d * d))`. The dilation of the whole chain
  replaces one local operation at a time, front to back, extending the work
  register by a fresh ancilla at each step. At a step, the operations already
  processed and the ones still to come are lifted along the new ancilla
  (`liftCh` for the general ones, `liftU` for the unitary ones, whose lifts
  agree by `LiftsQ.branch_eq`), the prefix is related by `LiftsQ`, the replaced
  operation by `DilatesQ`, and the suffix by `LiftsQ`;
  `liftsQ_qbind_dilatesQ` and `dilatesQ_qbind_liftsQ` compose the three, and
  `DilatesQ.trace_branch` reads off the acceptance probability. After the
  `(k + 1) * (q + 1)` steps the work register is the nested product
  `(⋯(w * r₀) * ⋯) * r_N` with `r_s = d_s * d_s`, `d_s` the register before
  step `s`.

The initial state of a step is `ρ ⊗ |0⟩⟨0|` for the current initial state `ρ`,
so a pure initial state stays pure (`kr_vecMulVec`).
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct CatCrypt.Quantum.UnitaryChannel
  CatCrypt.Quantum.Stinespring

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Blocks and the ancilla partial trace -/

section Blocks

variable {d c D : ℕ}

/-- Block `(i, j)` of a matrix on the register `Fin D ≃ Fin (d * c)`:
`blk e M i j x x' = M (x, i) (x', j)`. -/
def blk (e : Fin (d * c) ≃ Fin D) (M : Matrix (Fin D) (Fin D) ℂ) (i j : Fin c) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun x x' => M (e (finProdEquiv d c (x, i))) (e (finProdEquiv d c (x', j)))

theorem kr_apply_pair (e : Fin (d * c) ≃ Fin D) (A : Matrix (Fin d) (Fin d) ℂ)
    (B : Matrix (Fin c) (Fin c) ℂ) (x x' : Fin d) (i j : Fin c) :
    kr e A B (e (finProdEquiv d c (x, i))) (e (finProdEquiv d c (x', j))) = A x x' * B i j := by
  simp [kr, kronecker_apply]

/-- A matrix on the register is the sum of its blocks tensored with the matrix
units of the ancilla. -/
theorem sum_kr_blk (e : Fin (d * c) ≃ Fin D) (M : Matrix (Fin D) (Fin D) ℂ) :
    ∑ i, ∑ j, kr e (blk e M i j) (ancUnit i j) = M := by
  ext a b
  obtain ⟨⟨x, i⟩, rfl⟩ := ((finProdEquiv d c).trans e).surjective a
  obtain ⟨⟨x', j⟩, rfl⟩ := ((finProdEquiv d c).trans e).surjective b
  simp [Matrix.sum_apply, kr_apply_pair, ancUnit, blk, ite_and, Finset.sum_ite_eq]

theorem trAnc_sum {ι : Type} [Fintype ι] (e : Fin (d * c) ≃ Fin D)
    (M : ι → Matrix (Fin D) (Fin D) ℂ) : trAnc e (∑ i, M i) = ∑ i, trAnc e (M i) := by
  ext x x'
  simp only [trAnc_apply, Matrix.sum_apply]
  exact Finset.sum_comm

/-- `trAnc e (A ⊗ B) = tr B • A`. -/
theorem trAnc_kr (e : Fin (d * c) ≃ Fin D) (A : Matrix (Fin d) (Fin d) ℂ)
    (B : Matrix (Fin c) (Fin c) ℂ) : trAnc e (kr e A B) = B.trace • A := by
  ext x x'
  simp [trAnc_apply, kr_apply_pair, Matrix.trace, Finset.mul_sum, mul_comm]

theorem trAnc_eq_sum_blk (e : Fin (d * c) ≃ Fin D) (M : Matrix (Fin D) (Fin D) ℂ) :
    trAnc e M = ∑ i, blk e M i i := by
  ext x x'
  simp [trAnc_apply, blk, Matrix.sum_apply]

/-- `tr ((X ⊗ 1) M) = tr (X · trAnc e M)`. -/
theorem trace_kr_one_mul (e : Fin (d * c) ≃ Fin D) (X : Matrix (Fin d) (Fin d) ℂ)
    (M : Matrix (Fin D) (Fin D) ℂ) : (kr e X 1 * M).trace = (X * trAnc e M).trace := by
  conv_lhs => rw [← sum_kr_blk e M]
  rw [trace_kr_one_mul_sum, trAnc_eq_sum_blk, Finset.mul_sum, trace_sum]

/-- An instrument that lifts `O` acts blockwise on every input. -/
theorem LiftsQ.branch_eq_sum {β : Type} {e : Fin (d * c) ≃ Fin D} {O : QComp d β}
    {O' : QComp D β} (hO : LiftsQ e O O') (b : β) (M : Matrix (Fin D) (Fin D) ℂ) :
    O'.branch b M = ∑ i, ∑ j, kr e (O.branch b (blk e M i j)) (ancUnit i j) := by
  conv_lhs => rw [← sum_kr_blk e M]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hO b _ _

/-- Two lifts of the same instrument have the same branches. -/
theorem LiftsQ.branch_eq {β : Type} {e : Fin (d * c) ≃ Fin D} {O : QComp d β}
    {O₁ O₂ : QComp D β} (h₁ : LiftsQ e O O₁) (h₂ : LiftsQ e O O₂) (b : β) :
    O₁.branch b = O₂.branch b :=
  LinearMap.ext fun M => by rw [h₁.branch_eq_sum, h₂.branch_eq_sum]

/-- A lift of `O` commutes with the ancilla partial trace on every input. -/
theorem LiftsQ.trAnc_branch {β : Type} {e : Fin (d * c) ≃ Fin D} {O : QComp d β}
    {O' : QComp D β} (hO : LiftsQ e O O') (b : β) (M : Matrix (Fin D) (Fin D) ℂ) :
    trAnc e (O'.branch b M) = O.branch b (trAnc e M) := by
  rw [hO.branch_eq_sum, trAnc_sum, trAnc_eq_sum_blk, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [trAnc_sum, Finset.sum_eq_single i]
  · rw [trAnc_kr, trace_ancUnit, ite_eq_left rfl, one_smul]
  · intro j _ hj
    rw [trAnc_kr, trace_ancUnit, ite_eq_right (Ne.symm hj), zero_smul]
  · intro h; exact absurd (Finset.mem_univ i) h

end Blocks

/-! ## The dilation relation -/

section Dilation

variable {d c D : ℕ}

/-- `O'` dilates `O` along `e`: on `ρ ⊗ |0⟩⟨0|`, every branch of `O'` has the
branch of `O` on `ρ` as its ancilla partial trace. -/
def DilatesQ [NeZero c] {β : Type} (e : Fin (d * c) ≃ Fin D) (O : QComp d β)
    (O' : QComp D β) : Prop :=
  ∀ b (ρ : Matrix (Fin d) (Fin d) ℂ), trAnc e (O'.branch b (kr e ρ (ancProj 0))) = O.branch b ρ

variable [NeZero c]

theorem trAnc_kr_ancProj_zero (e : Fin (d * c) ≃ Fin D) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    trAnc e (kr e ρ (ancProj 0)) = ρ := by
  rw [trAnc_kr, trace_ancProj, one_smul]

theorem LiftsQ.dilatesQ {β : Type} {e : Fin (d * c) ≃ Fin D} {O : QComp d β} {O' : QComp D β}
    (hO : LiftsQ e O O') : DilatesQ e O O' := fun b ρ => by
  rw [hO, trAnc_kr_ancProj_zero]

/-- A dilation followed by lifts is a dilation. -/
theorem dilatesQ_qbind_liftsQ {α β : Type} [Fintype α] {e : Fin (d * c) ≃ Fin D}
    {I : QComp d α} {I' : QComp D α} {g : α → QComp d β} {g' : α → QComp D β}
    (hI : DilatesQ e I I') (hg : ∀ x, LiftsQ e (g x) (g' x)) :
    DilatesQ e (QComp.qbind I g) (QComp.qbind I' g') := fun b ρ => by
  rw [qbind_branch_apply, qbind_branch_apply, tsum_fintype, tsum_fintype, trAnc_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [(hg x).trAnc_branch, hI]

/-- A lift followed by dilations is a dilation. -/
theorem liftsQ_qbind_dilatesQ {α β : Type} [Fintype α] {e : Fin (d * c) ≃ Fin D}
    {I : QComp d α} {I' : QComp D α} {g : α → QComp d β} {g' : α → QComp D β}
    (hI : LiftsQ e I I') (hg : ∀ x, DilatesQ e (g x) (g' x)) :
    DilatesQ e (QComp.qbind I g) (QComp.qbind I' g') := fun b ρ => by
  rw [qbind_branch_apply, qbind_branch_apply, tsum_fintype, tsum_fintype, trAnc_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hI, hg]

/-- The trace of a dilated branch on `ρ ⊗ |0⟩⟨0|` is that of the original branch. -/
theorem DilatesQ.trace_branch {β : Type} {e : Fin (d * c) ≃ Fin D} {O : QComp d β}
    {O' : QComp D β} (hO : DilatesQ e O O') (b : β) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (O'.branch b (kr e ρ (ancProj 0))).trace = (O.branch b ρ).trace := by
  rw [← trace_trAnc e, hO]

/-- The observable `X ⊗ 1` on a dilated branch is `X` on the original branch. -/
theorem DilatesQ.trace_kr_one_mul_branch {β : Type} {e : Fin (d * c) ≃ Fin D} {O : QComp d β}
    {O' : QComp D β} (hO : DilatesQ e O O') (X : Matrix (Fin d) (Fin d) ℂ) (b : β)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (kr e X 1 * O'.branch b (kr e ρ (ancProj 0))).trace = (X * O.branch b ρ).trace := by
  rw [trace_kr_one_mul, hO]

end Dilation

/-! ## The Stinespring step -/

section Stinespring

variable {d D : ℕ} [NeZero d]

/-- A Stinespring unitary of a trace-preserving completely positive `Φ`, on the
register `Fin D ≃ Fin (d * (d * d))`. -/
def stineU (Φ : CPComp d Unit) (hTP : IsTP (Φ.toQComp.branch ()))
    (e : Fin (d * (d * d)) ≃ Fin D) : Matrix.unitaryGroup (Fin D) ℂ :=
  ⟨(stinespring (Φ.branch_cp ()) hTP e).choose, (stinespring (Φ.branch_cp ()) hTP e).choose_spec.1⟩

/-- The Stinespring unitary dilates `Φ`. -/
theorem dilatesQ_stineU (Φ : CPComp d Unit) (hTP : IsTP (Φ.toQComp.branch ()))
    (e : Fin (d * (d * d)) ≃ Fin D) :
    DilatesQ e Φ.toQComp (unitaryChannel (stineU Φ hTP e)) := fun _ ρ =>
  ((stinespring (Φ.branch_cp ()) hTP e).choose_spec.2 ρ).symm

/-- The single Stinespring step: `U` on `σ ⊗ |0⟩⟨0|` followed by a lift `Rest'`
of `Rest` has, under the ancilla partial trace, the branch of `Φ` followed by
`Rest` on `σ`. -/
theorem trAnc_stineU_step {β : Type} (Φ : CPComp d Unit) (hTP : IsTP (Φ.toQComp.branch ()))
    (e : Fin (d * (d * d)) ≃ Fin D) (Rest : QComp d β) (Rest' : QComp D β)
    (hRest : LiftsQ e Rest Rest') (b : β) (σ : Matrix (Fin d) (Fin d) ℂ) :
    trAnc e ((QComp.qbind (unitaryChannel (stineU Φ hTP e)) fun _ => Rest').branch b
        (kr e σ (ancProj 0))) =
      (QComp.qbind Φ.toQComp fun _ => Rest).branch b σ :=
  dilatesQ_qbind_liftsQ (dilatesQ_stineU Φ hTP e) (fun _ => hRest) b σ

/-- The single Stinespring step at the level of traces. -/
theorem trace_stineU_step {β : Type} (Φ : CPComp d Unit) (hTP : IsTP (Φ.toQComp.branch ()))
    (e : Fin (d * (d * d)) ≃ Fin D) (Rest : QComp d β) (Rest' : QComp D β)
    (hRest : LiftsQ e Rest Rest') (b : β) (σ : Matrix (Fin d) (Fin d) ℂ) :
    ((QComp.qbind (unitaryChannel (stineU Φ hTP e)) fun _ => Rest').branch b
        (kr e σ (ancProj 0))).trace =
      ((QComp.qbind Φ.toQComp fun _ => Rest).branch b σ).trace :=
  (dilatesQ_qbind_liftsQ (dilatesQ_stineU Φ hTP e) (fun _ => hRest)).trace_branch b σ

/-- The single Stinespring step on an observable `X ⊗ 1`. -/
theorem trace_kr_one_mul_stineU_step {β : Type} (Φ : CPComp d Unit)
    (hTP : IsTP (Φ.toQComp.branch ())) (e : Fin (d * (d * d)) ≃ Fin D) (Rest : QComp d β)
    (Rest' : QComp D β) (hRest : LiftsQ e Rest Rest') (X : Matrix (Fin d) (Fin d) ℂ) (b : β)
    (σ : Matrix (Fin d) (Fin d) ℂ) :
    (kr e X 1 * (QComp.qbind (unitaryChannel (stineU Φ hTP e)) fun _ => Rest').branch b
        (kr e σ (ancProj 0))).trace =
      (X * (QComp.qbind Φ.toQComp fun _ => Rest).branch b σ).trace :=
  (dilatesQ_qbind_liftsQ (dilatesQ_stineU Φ hTP e) (fun _ => hRest)).trace_kr_one_mul_branch
    X b σ

end Stinespring

/-! ## Chains with general local operations -/

section Chain

variable {d c a q : ℕ}

/-- `U₀ ; O ; U₁ ; … ; O ; U_q` for `Unit` instruments `U i` and a `Unit` oracle `O`. -/
def chainG (O : QComp d Unit) :
    (q : ℕ) → (Fin (q + 1) → QComp d Unit) → QComp d Unit
  | 0, U => U 0
  | q + 1, U => QComp.qbind (U 0) fun _ => QComp.qbind O fun _ => chainG O q (Fin.tail U)

/-- `head ; (round ; segment)ᵏ` with general local operations. -/
def mrChainG (O : QComp d Unit) (f : Fin c → Fin a) :
    (k : ℕ) → (q₀ : ℕ) → (Fin (q₀ + 1) → QComp d Unit) →
      (Fin k → Fin (q + 1) → QComp d Unit) → (Fin k → ClassicalRound d c a) → QComp d Unit
  | 0, q₀, head, _, _ => chainG O q₀ head
  | k + 1, q₀, head, tail, R =>
    QComp.qbind (chainG O q₀ head) fun _ => QComp.qbind (roundU (R 0) f) fun _ =>
      mrChainG O f k q (tail 0) (Fin.tail tail) (Fin.tail R)

theorem oracleChain_eq_chainG (O : QComp d Unit) :
    ∀ (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ),
      oracleChain O q U = chainG O q (unitaryChannel ∘ U)
  | 0, _ => rfl
  | q + 1, U => by
    rw [oracleChain, chainG, oracleChain_eq_chainG O q (Fin.tail U)]
    rfl

theorem mrChain_eq_mrChainG (O : QComp d Unit) (f : Fin c → Fin a) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a),
      mrChain O f k q₀ head tail R =
        mrChainG O f k q₀ (unitaryChannel ∘ head) (fun j => unitaryChannel ∘ tail j) R
  | 0, q₀, head, _, _ => oracleChain_eq_chainG O q₀ head
  | k + 1, q₀, head, tail, R => by
    rw [mrChain, mrChainG, oracleChain_eq_chainG O q₀ head,
      mrChain_eq_mrChainG O f k q (tail 0) (Fin.tail tail) (Fin.tail R)]
    rfl

variable {r D : ℕ}

theorem liftsQ_chainG (e : Fin (d * r) ≃ Fin D) {O : QComp d Unit} {O' : QComp D Unit}
    (hO : LiftsQ e O O') :
    ∀ (q : ℕ) (U : Fin (q + 1) → QComp d Unit) (U' : Fin (q + 1) → QComp D Unit),
      (∀ i, LiftsQ e (U i) (U' i)) → LiftsQ e (chainG O q U) (chainG O' q U')
  | 0, _, _, hU => hU 0
  | q + 1, U, U', hU =>
    liftsQ_qbind e (hU 0) fun _ => liftsQ_qbind e hO fun _ =>
      liftsQ_chainG e hO q (Fin.tail U) (Fin.tail U') fun i => hU i.succ

theorem liftsQ_mrChainG (e : Fin (d * r) ≃ Fin D) {O : QComp d Unit} {O' : QComp D Unit}
    (hO : LiftsQ e O O') (f : Fin c → Fin a) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → QComp d Unit) (head' : Fin (q₀ + 1) → QComp D Unit)
      (tail : Fin k → Fin (q + 1) → QComp d Unit) (tail' : Fin k → Fin (q + 1) → QComp D Unit)
      (R : Fin k → ClassicalRound d c a) (R' : Fin k → ClassicalRound D c a),
      (∀ i, LiftsQ e (head i) (head' i)) → (∀ j i, LiftsQ e (tail j i) (tail' j i)) →
      (∀ j, LiftsQ e (roundU (R j) f) (roundU (R' j) f)) →
      LiftsQ e (mrChainG O f k q₀ head tail R) (mrChainG O' f k q₀ head' tail' R')
  | 0, q₀, head, head', _, _, _, _, hh, _, _ => liftsQ_chainG e hO q₀ head head' hh
  | k + 1, q₀, head, head', tail, tail', R, R', hh, ht, hR =>
    liftsQ_qbind e (liftsQ_chainG e hO q₀ head head' hh) fun _ =>
      liftsQ_qbind e (hR 0) fun _ =>
        liftsQ_mrChainG e hO f k q (tail 0) (tail' 0) (Fin.tail tail) (Fin.tail tail')
          (Fin.tail R) (Fin.tail R') (ht 0) (fun j => ht j.succ) fun j => hR j.succ

end Chain

/-! ## General multi-round adversaries -/

section Adv

variable {m n w q k c a : ℕ}

/-- A multi-round adversary with general local operations: `k + 1` segments of
`q` oracle queries, each segment given by its `q + 1` trace-preserving
completely positive maps on the whole register, `k` classical rounds, an
initial density matrix and a final projector. -/
structure QAdvMRGen (m n w q k c a : ℕ) where
  /-- The local operations of the segments. -/
  seg : Fin (k + 1) → Fin (q + 1) → CPComp (m * n * w) Unit
  /-- Every local operation is trace preserving. -/
  seg_tp : ∀ j i, IsTP ((seg j i).toQComp.branch ())
  /-- The rounds, round `j` between segments `j` and `j + 1`. -/
  rounds : Fin k → ClassicalRound (m * n * w) c a
  /-- The initial state. -/
  init : DensityMatrix (m * n * w)
  /-- The projector of the final measurement. -/
  final : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ
  final_conjTranspose : finalᴴ = final
  final_mul_self : final * final = final

/-- The final measurement of `A` as an instrument. -/
def QAdvMRGen.measure (A : QAdvMRGen m n w q k c a) : QComp (m * n * w) Bool :=
  measProj A.final A.final_conjTranspose A.final_mul_self

variable [NeZero n]

/-- The run: segment `0` with `O_H`, round `0` with `f`, segment `1`, …,
segment `k`, then the final measurement. -/
def runMRGen (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) :
    QComp (m * n * w) Bool :=
  QComp.qbind (mrChainG (oracleQ m n w H) f k q (fun i => (A.seg 0 i).toQComp)
    (fun j i => (Fin.tail A.seg j i).toQComp) A.rounds) fun _ => A.measure

/-- The probability that the run outputs `1`. -/
def prOutMRGen (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) : ℝ≥0∞ :=
  prTrue_Q (runMRGen A H f) A.init

/-- A general quantum IND-CCA adversary against the FIPS 203 KEM: `KEMQAdv`
with general local operations and any initial state. -/
structure KEMQAdvGen (m₁ m₂ n w q k c a : ℕ) (PK C K : Type) where
  /-- The adversary at a public key, a challenge ciphertext and a challenge key. -/
  run : PK → C → K → QAdvMRGen (m₁ + m₂) n (2 * w) q k c a
  /-- The final projector is the projector onto output bit `1`. -/
  final_eq : ∀ pk c K, (run pk c K).final = winBitProj (m₁ + m₂) n w

end Adv

/-! ## Unitary adversaries are general adversaries -/

section Embed

variable {m n w q k c a : ℕ}

/-- A unitary channel is trace preserving. -/
theorem isTP_unitaryChannel {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) :
    IsTP ((unitaryChannel U).branch ()) := fun ρ => by
  rw [unitaryChannel_branch_apply, trace_mul_cycle, ← star_eq_conjTranspose,
    UnitaryGroup.star_mul_self, one_mul]

/-- `A` with each unitary `U` read as the channel `ρ ↦ U ρ Uᴴ`. -/
def QAdvMR.toGen (A : QAdvMR m n w q k c a) : QAdvMRGen m n w q k c a where
  seg j i := CPComp.unitary (A.seg j i)
  seg_tp j i := isTP_unitaryChannel (A.seg j i)
  rounds := A.rounds
  init := A.init
  final := A.final
  final_conjTranspose := A.final_conjTranspose
  final_mul_self := A.final_mul_self

variable [NeZero n]

theorem runMRGen_toGen (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) :
    runMRGen A.toGen H f = runMR A H f := by
  unfold runMRGen runMR
  rw [mrChain_eq_mrChainG]
  rfl

/-- The embedding preserves the acceptance probability. -/
theorem prOutMRGen_toGen (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) :
    prOutMRGen A.toGen H f = prOutMR A H f := by
  unfold prOutMRGen prOutMR
  rw [runMRGen_toGen]
  rfl

/-- A KEM adversary with unitary local operations and a pure initial state is a
general KEM adversary. -/
def KEMQAdv.toGen {m₁ m₂ : ℕ} {PK C K : Type} (A : KEMQAdv m₁ m₂ n w q k c a PK C K) :
    KEMQAdvGen m₁ m₂ n w q k c a PK C K where
  run pk cs κ := (A.run pk cs κ).toGen
  final_eq pk cs κ := A.final_eq pk cs κ

theorem KEMQAdv.toGen_run {m₁ m₂ : ℕ} {PK C K : Type} (A : KEMQAdv m₁ m₂ n w q k c a PK C K)
    (pk : PK) (cs : C) (κ : K) (H : Fin (m₁ + m₂) → Fin n) (f : Fin c → Fin a) :
    prOutMRGen (A.toGen.run pk cs κ) H f = prOutMR (A.run pk cs κ) H f :=
  prOutMRGen_toGen _ H f

end Embed

/-! ## Lifting a general adversary along an ancilla -/

section LiftGen

variable {d c D : ℕ}

/-- The Kraus operators of a completely positive `Φ`. -/
def krausOf (Φ : CPComp d Unit) : Fin (d * d) → Matrix (Fin d) (Fin d) ℂ :=
  (exists_kraus_fin (Φ.branch_cp ())).choose

theorem krausOf_spec (Φ : CPComp d Unit) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Φ.toQComp.branch () ρ = ∑ i, krausOf Φ i * ρ * (krausOf Φ i)ᴴ :=
  (exists_kraus_fin (Φ.branch_cp ())).choose_spec ρ

theorem krausOf_complete (Φ : CPComp d Unit) (hTP : IsTP (Φ.toQComp.branch ())) :
    ∑ i, (krausOf Φ i)ᴴ * krausOf Φ i = 1 :=
  kraus_sum_conjTranspose_mul_self_eq_one (krausOf_spec Φ) hTP

theorem kr_krausOf_complete (e : Fin (d * c) ≃ Fin D) (Φ : CPComp d Unit)
    (hTP : IsTP (Φ.toQComp.branch ())) :
    ∑ i, (kr e (krausOf Φ i) 1)ᴴ * kr e (krausOf Φ i) 1 = 1 := by
  simp only [kr_conjTranspose, kr_mul, conjTranspose_one, one_mul]
  rw [← kr_sum_left, krausOf_complete Φ hTP, kr_one]

/-- The Kraus instrument of `{K i ⊗ 1}` with its outcome discarded. -/
def liftChQ (e : Fin (d * c) ≃ Fin D) (Φ : CPComp d Unit) (hTP : IsTP (Φ.toQComp.branch ())) :
    QComp D Unit :=
  QComp.qbind (QComp.ofKraus (fun i => kr e (krausOf Φ i) 1) (kr_krausOf_complete e Φ hTP))
    fun _ => QComp.qpure ()

theorem liftChQ_branch (e : Fin (d * c) ≃ Fin D) (Φ : CPComp d Unit)
    (hTP : IsTP (Φ.toQComp.branch ())) (u : Unit) (M : Matrix (Fin D) (Fin D) ℂ) :
    (liftChQ e Φ hTP).branch u M =
      ∑ i, kr e (krausOf Φ i) 1 * M * (kr e (krausOf Φ i) 1)ᴴ := by
  unfold liftChQ
  rw [qbind_branch_apply, tsum_fintype]
  simp only [qpure_branch_apply, QComp.ofKraus_branch]
  simp

/-- The channel `Φ ⊗ id` on the register extended by the ancilla `Fin c`. -/
def liftCh (e : Fin (d * c) ≃ Fin D) (Φ : CPComp d Unit) (hTP : IsTP (Φ.toQComp.branch ())) :
    CPComp D Unit where
  toQComp := liftChQ e Φ hTP
  branch_cp u := isCPMap_krausSum _ _ (liftChQ_branch e Φ hTP u)

theorem isTP_liftCh (e : Fin (d * c) ≃ Fin D) (Φ : CPComp d Unit)
    (hTP : IsTP (Φ.toQComp.branch ())) : IsTP ((liftCh e Φ hTP).toQComp.branch ()) := fun M => by
  show ((liftChQ e Φ hTP).branch () M).trace = M.trace
  rw [liftChQ_branch, trace_sum]
  simp_rw [trace_mul_cycle _ M]
  rw [← trace_sum, ← Finset.sum_mul, kr_krausOf_complete e Φ hTP, one_mul]

theorem liftsQ_liftCh (e : Fin (d * c) ≃ Fin D) (Φ : CPComp d Unit)
    (hTP : IsTP (Φ.toQComp.branch ())) : LiftsQ e Φ.toQComp (liftCh e Φ hTP).toQComp := by
  intro u B E
  show (liftChQ e Φ hTP).branch u (kr e B E) = _
  rw [liftChQ_branch, krausOf_spec, kr_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kr_conjTranspose, kr_mul, kr_mul, conjTranspose_one, one_mul, mul_one]

/-- The measurement of `P ⊗ 1` lifts the measurement of `P`. -/
theorem liftsQ_measProj (e : Fin (d * c) ≃ Fin D) (P : Matrix (Fin d) (Fin d) ℂ) (hH : Pᴴ = P)
    (hI : P * P = P) (hH' : (kr e P 1)ᴴ = kr e P 1) (hI' : kr e P 1 * kr e P 1 = kr e P 1) :
    LiftsQ e (measProj P hH hI) (measProj (kr e P 1) hH' hI') := by
  intro b B E
  cases b
  · rw [measProj_branch_false, measProj_branch_false, kr_one_sub, kr_conjTranspose, kr_mul, kr_mul,
      conjTranspose_one, one_mul, mul_one]
  · rw [measProj_branch_true, measProj_branch_true, kr_conjTranspose, kr_mul, kr_mul,
      conjTranspose_one, one_mul, mul_one]

variable {m n W W' q k a : ℕ}

/-- `A` with every local operation, round and the final projector tensored with
`1` on the ancilla `Fin D`, and the initial state `σ`. -/
def liftGen (e : Fin (m * n * W * D) ≃ Fin (m * n * W')) (A : QAdvMRGen m n W q k c a)
    (σ : DensityMatrix (m * n * W')) : QAdvMRGen m n W' q k c a where
  seg j i := liftCh e (A.seg j i) (A.seg_tp j i)
  seg_tp j i := isTP_liftCh e (A.seg j i) (A.seg_tp j i)
  rounds j := liftRA e (A.rounds j)
  init := σ
  final := kr e A.final 1
  final_conjTranspose := by rw [kr_conjTranspose, A.final_conjTranspose, conjTranspose_one]
  final_mul_self := by rw [kr_mul, A.final_mul_self, one_mul]

/-- The run of the lifted adversary lifts the run of `A`. -/
theorem liftsQ_runMRGen [NeZero n] (A : QAdvMRGen m n W q k c a)
    (σ : DensityMatrix (m * n * (W * D))) (H : Fin m → Fin n) (f : Fin c → Fin a) :
    LiftsQ (padE m n rfl) (runMRGen A H f) (runMRGen (liftGen (padE m n rfl) A σ) H f) := by
  have hOU : oracleU m n (W * D) H = liftU (ancE m n W D) (oracleU m n W H) :=
    Subtype.ext (oracleU_lift H)
  have hO : LiftsQ (ancE m n W D) (oracleQ m n W H) (oracleQ m n (W * D) H) := by
    rw [oracleQ, oracleQ, hOU]
    exact liftsQ_unitaryChannel _ _
  exact liftsQ_qbind _
    (liftsQ_mrChainG _ hO f k q _ _ _ _ _ _ (fun i => liftsQ_liftCh _ _ _)
      (fun j i => liftsQ_liftCh _ _ _) fun j => liftsQ_roundU_liftRA _ _ f)
    fun _ => liftsQ_measProj _ _ _ _ _ _

/-- Lifting preserves the acceptance probability when the ancilla partial trace
of the new initial state is the old one. -/
theorem prOutMRGen_liftGen [NeZero n] (hW : W * D = W') (A : QAdvMRGen m n W q k c a)
    (σ : DensityMatrix (m * n * W')) (hσ : trAnc (padE m n hW) σ.val = A.init.val)
    (H : Fin m → Fin n) (f : Fin c → Fin a) :
    prOutMRGen (liftGen (padE m n hW) A σ) H f = prOutMRGen A H f := by
  subst hW
  unfold prOutMRGen prTrue_Q
  rw [← trace_trAnc (padE m n rfl), (liftsQ_runMRGen A σ H f).trAnc_branch]
  exact congrArg (fun M => ENNReal.ofReal (((runMRGen A H f).branch true) M).trace.re) hσ

/-- `A` with the initial state `ρ ⊗ |0⟩⟨0|`. -/
theorem prOutMRGen_liftGen_ancProj [NeZero n] [NeZero D] (hW : W * D = W')
    (A : QAdvMRGen m n W q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) :
    prOutMRGen (liftGen (padE m n hW) A
      { val := kr (padE m n hW) A.init.val (ancProj 0)
        psd := kr_posSemidef _ A.init.psd (ancProj_posSemidef 0)
        tr_one := by rw [trace_kr, A.init.tr_one, trace_ancProj, one_mul] }) H f =
      prOutMRGen A H f :=
  prOutMRGen_liftGen hW A _ (trAnc_kr_ancProj_zero _ _) H f

end LiftGen

/-! ## Purification of the initial state -/

section Purify

variable {m n w q k c a : ℕ}

/-- A purification of the initial state of `A` on the work register
`w * (m * n * w)`. -/
def purVec (A : QAdvMRGen m n w q k c a) : Fin (m * n * (w * (m * n * w))) → ℂ :=
  (exists_purification (padE m n rfl) A.init.psd A.init.tr_one).choose

theorem purVec_spec (A : QAdvMRGen m n w q k c a) :
    star (purVec A) ⬝ᵥ purVec A = 1 ∧
      A.init.val = trAnc (padE m n rfl) (vecMulVec (purVec A) (star (purVec A))) :=
  (exists_purification (padE m n rfl) A.init.psd A.init.tr_one).choose_spec

/-- The pure state `|ψ⟩⟨ψ|` of the purification. -/
def purDensity (A : QAdvMRGen m n w q k c a) : DensityMatrix (m * n * (w * (m * n * w))) where
  val := vecMulVec (purVec A) (star (purVec A))
  psd := posSemidef_vecMulVec_self_star _
  tr_one := by rw [trace_vecMulVec, dotProduct_comm, (purVec_spec A).1]

/-- `A` with every operation tensored with `1` on an ancilla of dimension
`m * n * w`, started in a purification of its initial state. -/
def purifyGen (A : QAdvMRGen m n w q k c a) : QAdvMRGen m n (w * (m * n * w)) q k c a :=
  liftGen (padE m n rfl) A (purDensity A)

theorem purifyGen_init_pure (A : QAdvMRGen m n w q k c a) :
    ∃ ψ, (purifyGen A).init.val = vecMulVec ψ (star ψ) :=
  ⟨purVec A, rfl⟩

/-- The purified adversary accepts with the probability of `A`. -/
theorem prOutMRGen_purifyGen [NeZero n] (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) : prOutMRGen (purifyGen A) H f = prOutMRGen A H f :=
  prOutMRGen_liftGen rfl A _ (purVec_spec A).2.symm H f

end Purify

end CatCrypt.Quantum.QROM
