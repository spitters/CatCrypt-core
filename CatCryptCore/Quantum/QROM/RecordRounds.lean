/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.SigGame
public import CatCryptCore.Quantum.QROM.KEMAdvGeneral

/-!
# Recording the round outcomes in the ancillas of the flattened register

`toQAdv A f` runs the `k` rounds of a multi-round adversary `A` as deferred measurements: round
`j` copies its outcome into ancilla `j` of the work register `ancW c k w` and answers controlled
on that ancilla, and nothing is measured. The adversary `recordGen A G` of the general model
`QAdvMRGen` has the same work register with every ancilla prepared at `|0⟩`; its round `j`
copies the outcome into ancilla `j`, measures ancilla `j` and answers by `f` of the measured
outcome, and its final projector is `diagB G`. The two have the same acceptance probability
for every final test `G` on the flattened register (`prOut_withFinalB_toQAdv_eq`), so a test
that reads the round outcomes from the ancilla digits (`roundOutcomes`) is a final projector of
an adversary whose rounds are classical rounds of `f`.

## Main definitions

* `maskR r M` — the pinching of `M` along a labelling `r` of the basis: the entries between
  basis states of different labels set to `0`
* `BlockDiag r U` — `U` has no entry between basis states of different labels
* `CovQ r O` — every branch of `O` commutes with `maskR r`
* `recordRound e R` — copy the outcome of `R` into a fresh ancilla, measure the ancilla, answer
* `recAt s X`, `recordFrom j s X` — lift a head-tail adversary along one, resp. `j`, fresh
  ancillas, recording round `s`, resp. rounds `s, …, s + j - 1`
* `recordMR A G`, `recordGen A G` — all `k` rounds of `A` recorded, with final projector `diagB G`

## Main results

* `trace_mul_maskR` — an observable block diagonal along `r` does not see the pinching
* `roundU_recordRound` — the recorded round is the deferred round `roundV` followed by the
  pinching of its ancilla
* `trace_flatten_blockDiag` — the deferred single run and the recorded run agree on every
  observable block diagonal in the round-outcome ancillas, on every input and every branch
* `prOut_withFinalB_toQAdv_eq` — `prOut ((toQAdv A f).withFinalB G) H =
  prOutMRGen (recordGen A G) H f`

## The argument

The recorded round is `roundV` followed by the pinching of its ancilla (`roundU_recordRound`).
Every later operation is block diagonal along the digit of that ancilla, so the pinching
commutes with the rest of the run (`CovQ`), and an observable block diagonal along the digit
does not see it (`trace_mul_maskR`). The induction over the rounds follows `flatten`: the round
peeled first is round `0`, whose ancilla is the innermost one.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct CatCrypt.Quantum.UnitaryChannel

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The pinching along a labelling -/

section Mask

variable {D : ℕ} {α : Type} [DecidableEq α]

/-- The pinching of `M` along `r`: the entries between basis states of different labels are
    set to `0`. -/
def maskR (r : Fin D → α) (M : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun i j => if r i = r j then M i j else 0

/-- `U` is block diagonal along `r`: it has no entry between basis states of different
    labels. -/
def BlockDiag (r : Fin D → α) (U : Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ i j, r i ≠ r j → U i j = 0

theorem maskR_add (r : Fin D → α) (M N : Matrix (Fin D) (Fin D) ℂ) :
    maskR r (M + N) = maskR r M + maskR r N := by
  ext i j; by_cases h : r i = r j <;> simp [maskR, h]

theorem maskR_zero (r : Fin D → α) : maskR r (0 : Matrix (Fin D) (Fin D) ℂ) = 0 := by
  ext i j; simp [maskR]

theorem maskR_sum {ι : Type} (s : Finset ι) (r : Fin D → α) (M : ι → Matrix (Fin D) (Fin D) ℂ) :
    maskR r (∑ x ∈ s, M x) = ∑ x ∈ s, maskR r (M x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [maskR_zero]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, maskR_add, ih]

theorem maskR_ite (r : Fin D → α) (p : Prop) [Decidable p] (M : Matrix (Fin D) (Fin D) ℂ) :
    maskR r (if p then M else 0) = if p then maskR r M else 0 := by
  split_ifs <;> simp [maskR_zero]

theorem BlockDiag.mul_maskR {r : Fin D → α} {U : Matrix (Fin D) (Fin D) ℂ} (hU : BlockDiag r U)
    (M : Matrix (Fin D) (Fin D) ℂ) : U * maskR r M = maskR r (U * M) := by
  ext i j
  simp only [maskR, Matrix.mul_apply, of_apply]
  split_ifs with h <;> [refine Finset.sum_congr rfl fun l _ => ?_;
    refine Finset.sum_eq_zero fun l _ => ?_] <;> grind [BlockDiag]

theorem BlockDiag.maskR_mul {r : Fin D → α} {U : Matrix (Fin D) (Fin D) ℂ} (hU : BlockDiag r U)
    (M : Matrix (Fin D) (Fin D) ℂ) : maskR r M * U = maskR r (M * U) := by
  ext i j
  simp only [maskR, Matrix.mul_apply, of_apply]
  split_ifs with h <;> [refine Finset.sum_congr rfl fun l _ => ?_;
    refine Finset.sum_eq_zero fun l _ => ?_] <;> grind [BlockDiag]

theorem BlockDiag.conj_maskR {r : Fin D → α} {U V : Matrix (Fin D) (Fin D) ℂ}
    (hU : BlockDiag r U) (hV : BlockDiag r V) (M : Matrix (Fin D) (Fin D) ℂ) :
    U * maskR r M * V = maskR r (U * M * V) := by
  rw [hU.mul_maskR, hV.maskR_mul]

end Mask

section BlockDiagLemmas

variable {D : ℕ} {α γ : Type}

theorem BlockDiag.mul {r : Fin D → α} {U V : Matrix (Fin D) (Fin D) ℂ} (hU : BlockDiag r U)
    (hV : BlockDiag r V) : BlockDiag r (U * V) := by
  intro i j hij
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun l _ => by by_cases hl : r i = r l <;> grind [BlockDiag]

theorem BlockDiag.add {r : Fin D → α} {U V : Matrix (Fin D) (Fin D) ℂ} (hU : BlockDiag r U)
    (hV : BlockDiag r V) : BlockDiag r (U + V) :=
  fun i j hij => by simp [hU i j hij, hV i j hij]

theorem BlockDiag.sum {ι : Type} {r : Fin D → α} (s : Finset ι)
    {U : ι → Matrix (Fin D) (Fin D) ℂ} (hU : ∀ x, BlockDiag r (U x)) :
    BlockDiag r (∑ x ∈ s, U x) :=
  fun i j hij => by simp [Matrix.sum_apply, hU _ i j hij]

theorem BlockDiag.conjTranspose {r : Fin D → α} {U : Matrix (Fin D) (Fin D) ℂ}
    (hU : BlockDiag r U) : BlockDiag r Uᴴ :=
  fun i j hij => by simp [hU j i (Ne.symm hij)]

theorem BlockDiag.of_isDiag {r : Fin D → α} {U : Matrix (Fin D) (Fin D) ℂ}
    (hU : ∀ i j, i ≠ j → U i j = 0) : BlockDiag r U :=
  fun i j hij => hU i j fun h => hij (h ▸ rfl)

theorem BlockDiag.one (r : Fin D → α) : BlockDiag r (1 : Matrix (Fin D) (Fin D) ℂ) :=
  BlockDiag.of_isDiag fun _ _ h => Matrix.one_apply_ne h

theorem BlockDiag.comp {r : Fin D → α} {U : Matrix (Fin D) (Fin D) ℂ} (hU : BlockDiag r U)
    (g : α → γ) : BlockDiag (g ∘ r) U :=
  fun i j hij => hU i j fun h => hij (by simp [h])

theorem BlockDiag.diagB (r : Fin D → α) (G : Fin D → Bool) : BlockDiag r (diagB G) :=
  BlockDiag.of_isDiag fun _ _ h => diagonal_apply_ne _ h

end BlockDiagLemmas

section MaskTrace

variable {D : ℕ} {α : Type} [DecidableEq α]

/-- An observable block diagonal along `r` does not see the pinching along `r`. -/
theorem trace_mul_maskR {r : Fin D → α} {Y : Matrix (Fin D) (Fin D) ℂ} (hY : BlockDiag r Y)
    (M : Matrix (Fin D) (Fin D) ℂ) : (Y * maskR r M).trace = (Y * M).trace := by
  simp only [Matrix.trace, diag_apply, Matrix.mul_apply, maskR, of_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by grind [BlockDiag]

end MaskTrace

/-! ## Instruments that commute with the pinching -/

section Cov

variable {D : ℕ} {α : Type} [DecidableEq α]

/-- Every branch of `O` commutes with the pinching along `r`. -/
def CovQ {β : Type} (r : Fin D → α) (O : QComp D β) : Prop :=
  ∀ b M, O.branch b (maskR r M) = maskR r (O.branch b M)

theorem covQ_qpure {β : Type} (r : Fin D → α) (x : β) : CovQ r (QComp.qpure x : QComp D β) := by
  intro b M
  rw [qpure_branch_apply, qpure_branch_apply, maskR_ite]

theorem covQ_qbind {β γ : Type} [Finite β] {r : Fin D → α} {I : QComp D β}
    {g : β → QComp D γ} (hI : CovQ r I) (hg : ∀ x, CovQ r (g x)) :
    CovQ r (QComp.qbind I g) := by
  have := Fintype.ofFinite β
  intro b M
  rw [qbind_branch_apply, qbind_branch_apply, tsum_fintype, tsum_fintype, maskR_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [hI, hg]

theorem covQ_unitaryChannel {r : Fin D → α} {U : Matrix.unitaryGroup (Fin D) ℂ}
    (hU : BlockDiag r (U : Matrix (Fin D) (Fin D) ℂ)) : CovQ r (unitaryChannel U) := by
  intro _ M
  rw [unitaryChannel_branch_apply, unitaryChannel_branch_apply,
    hU.conj_maskR hU.conjTranspose]

theorem covQ_roundU {c a : ℕ} {r : Fin D → α} (R : ClassicalRound D c a) (f : Fin c → Fin a)
    (hP : ∀ y, BlockDiag r (R.P y)) (hA : ∀ z, BlockDiag r (R.ans z : Matrix (Fin D) (Fin D) ℂ)) :
    CovQ r (roundU R f) := by
  intro _ M
  rw [roundU_branch, roundU_branch, maskR_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h := (hA (f y)).mul (hP y)
  rw [h.conj_maskR h.conjTranspose]

theorem covQ_scChain {r : Fin D → α} {O : QComp D Bool} (hO : CovQ r O) :
    ∀ (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin D) ℂ),
      (∀ i, BlockDiag r (U i : Matrix (Fin D) (Fin D) ℂ)) → CovQ r (scChain O q U)
  | 0, _, hU => covQ_qbind (covQ_unitaryChannel (hU 0)) fun _ => covQ_qpure r _
  | q + 1, U, hU =>
    covQ_qbind (covQ_unitaryChannel (hU 0)) fun _ => covQ_qbind hO fun _ =>
      covQ_qbind (covQ_scChain hO q (Fin.tail U) fun i => hU i.succ) fun _ => covQ_qpure r _

theorem covQ_mrChainSC {c a q : ℕ} {r : Fin D → α} {O : QComp D Bool} (hO : CovQ r O)
    (f : Fin c → Fin a) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin D) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin D) ℂ)
      (R : Fin k → ClassicalRound D c a),
      (∀ i, BlockDiag r (head i : Matrix (Fin D) (Fin D) ℂ)) →
      (∀ j i, BlockDiag r (tail j i : Matrix (Fin D) (Fin D) ℂ)) →
      (∀ j y, BlockDiag r ((R j).P y)) →
      (∀ j z, BlockDiag r ((R j).ans z : Matrix (Fin D) (Fin D) ℂ)) →
      CovQ r (mrChainSC O f k q₀ head tail R)
  | 0, q₀, head, _, _, hh, _, _, _ => covQ_scChain hO q₀ head hh
  | k + 1, q₀, head, tail, R, hh, ht, hP, hA =>
    covQ_qbind (covQ_scChain hO q₀ head hh) fun _ =>
      covQ_qbind (covQ_roundU (R 0) f (hP 0) (hA 0)) fun _ =>
        covQ_qbind (covQ_mrChainSC hO f k q (tail 0) (Fin.tail tail) (Fin.tail R) (ht 0)
          (fun j => ht j.succ) (fun j => hP j.succ) fun j => hA j.succ) fun _ => covQ_qpure r _

end Cov

/-! ## Labellings of a register with one more ancilla -/

section KrLab

variable {d c D : ℕ} {α : Type}

theorem BlockDiag.kr {r : Fin d → α} {A : Matrix (Fin d) (Fin d) ℂ} (hA : BlockDiag r A)
    (e : Fin (d * c) ≃ Fin D) (B : Matrix (Fin c) (Fin c) ℂ) :
    BlockDiag (fun i => r ((finProdEquiv d c).symm (e.symm i)).1) (kr e A B) := by
  intro i j hij
  obtain ⟨⟨x, y⟩, rfl⟩ := ((finProdEquiv d c).trans e).surjective i
  obtain ⟨⟨x', y'⟩, rfl⟩ := ((finProdEquiv d c).trans e).surjective j
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at hij ⊢
  rw [kr_apply_pair, hA x x' hij, zero_mul]

theorem blockDiag_kr_anc (e : Fin (d * c) ≃ Fin D) (A : Matrix (Fin d) (Fin d) ℂ)
    {B : Matrix (Fin c) (Fin c) ℂ} (hB : ∀ y y', y ≠ y' → B y y' = 0) :
    BlockDiag (fun i => ((finProdEquiv d c).symm (e.symm i)).2) (kr e A B) := by
  intro i j hij
  obtain ⟨⟨x, y⟩, rfl⟩ := ((finProdEquiv d c).trans e).surjective i
  obtain ⟨⟨x', y'⟩, rfl⟩ := ((finProdEquiv d c).trans e).surjective j
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at hij ⊢
  rw [kr_apply_pair, hB y y' hij, mul_zero]

theorem ancProj_apply_ne (y : Fin c) : ∀ z z' : Fin c, z ≠ z' → ancProj y z z' = 0 :=
  fun _ _ h => diagonal_apply_ne _ h

theorem maskR_kr [DecidableEq α] {r : Fin d → α} (e : Fin (d * c) ≃ Fin D)
    (B : Matrix (Fin d) (Fin d) ℂ) (E : Matrix (Fin c) (Fin c) ℂ) :
    maskR (fun i => r ((finProdEquiv d c).symm (e.symm i)).1) (kr e B E) = kr e (maskR r B) E := by
  ext i j
  obtain ⟨⟨x, y⟩, rfl⟩ := ((finProdEquiv d c).trans e).surjective i
  obtain ⟨⟨x', y'⟩, rfl⟩ := ((finProdEquiv d c).trans e).surjective j
  simp only [maskR, of_apply, Equiv.trans_apply, Equiv.symm_apply_apply, kr_apply_pair]
  split_ifs <;> simp

theorem kr_one_ancProj_eq (e : Fin (d * c) ≃ Fin D) (y : Fin c) :
    kr e 1 (ancProj y) =
      Matrix.diagonal fun i => if ((finProdEquiv d c).symm (e.symm i)).2 = y then 1 else 0 := by
  ext i j
  obtain ⟨⟨x, z⟩, rfl⟩ := ((finProdEquiv d c).trans e).surjective i
  obtain ⟨⟨x', z'⟩, rfl⟩ := ((finProdEquiv d c).trans e).surjective j
  simp only [Equiv.trans_apply, kr_apply_pair, ancProj, diagonal_apply, Matrix.one_apply,
    Pi.single_apply, Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hx : x = x' <;> by_cases hz : z = z' <;> by_cases hy : z = y <;> simp_all

/-- The pinching along the ancilla digit is the sum of the conjugations by the ancilla
    projectors. -/
theorem maskR_anc_eq_sum (e : Fin (d * c) ≃ Fin D) (N : Matrix (Fin D) (Fin D) ℂ) :
    maskR (fun i => ((finProdEquiv d c).symm (e.symm i)).2) N =
      ∑ y, kr e 1 (ancProj y) * N * kr e 1 (ancProj y) := by
  ext i j
  simp [kr_one_ancProj_eq, diagonal_mul, mul_diagonal, Matrix.sum_apply, maskR, ite_mul, mul_ite]

end KrLab

/-! ## The recorded round -/

section Record

variable {d c a D : ℕ} [NeZero c]

/-- The record unitary `roundW e R` as an element of the unitary group. -/
def roundWU (e : Fin (d * c) ≃ Fin D) (R : ClassicalRound d c a) :
    Matrix.unitaryGroup (Fin D) ℂ :=
  ⟨roundW e R, by
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]
    exact roundW_mul_conjTranspose_self e R⟩

theorem roundW_conjTranspose_mul_self (e : Fin (d * c) ≃ Fin D) (R : ClassicalRound d c a) :
    (roundW e R)ᴴ * roundW e R = 1 :=
  UnitaryGroup.star_mul_self (roundWU e R)

/-- The recorded round: copy the outcome of `R` into the ancilla by `roundW`, measure the
    ancilla in the computational basis, and answer by the answers of `R`. Its projectors are
    the ancilla projectors conjugated by `roundW`, its answers the lifted answers after
    `roundW`. -/
def recordRound (e : Fin (d * c) ≃ Fin D) (R : ClassicalRound d c a) : ClassicalRound D c a where
  P y := (roundW e R)ᴴ * kr e 1 (ancProj y) * roundW e R
  P_conjTranspose y := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, kr_conjTranspose,
      conjTranspose_one, ancProj_conjTranspose, Matrix.mul_assoc]
  P_mul_self y := by
    calc _ = (roundW e R)ᴴ * (kr e 1 (ancProj y) * (roundW e R * (roundW e R)ᴴ) *
          kr e 1 (ancProj y)) * roundW e R := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [roundW_mul_conjTranspose_self, Matrix.mul_one, kr_mul, Matrix.one_mul,
          ancProj_mul_ancProj, ite_eq_left rfl]
  P_orth y y' h := by
    calc _ = (roundW e R)ᴴ * (kr e 1 (ancProj y) * (roundW e R * (roundW e R)ᴴ) *
          kr e 1 (ancProj y')) * roundW e R := by simp only [Matrix.mul_assoc]
      _ = 0 := by
        rw [roundW_mul_conjTranspose_self, Matrix.mul_one, kr_mul, ancProj_mul_ancProj,
          ite_eq_right h, kr_zero_right, Matrix.mul_zero, Matrix.zero_mul]
  P_sum := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← kr_sum_right, sum_ancProj, kr_one, Matrix.mul_one,
      roundW_conjTranspose_mul_self]
  ans z := liftU e (R.ans z) * roundWU e R

/-- The unfolding lemma of the answers of `recordRound`. -/
theorem recordRound_ans_val (e : Fin (d * c) ≃ Fin D) (R : ClassicalRound d c a) (z : Fin a) :
    ((recordRound e R).ans z : Matrix (Fin D) (Fin D) ℂ) =
      kr e (R.ans z : Matrix (Fin d) (Fin d) ℂ) 1 * roundW e R := rfl

omit [NeZero c] in
theorem roundC_mul_kr_one_ancProj (e : Fin (d * c) ≃ Fin D) (R : ClassicalRound d c a)
    (f : Fin c → Fin a) (y : Fin c) :
    roundC e R f * kr e 1 (ancProj y) =
      kr e (R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) (ancProj y) := by
  unfold roundC
  rw [Finset.sum_mul, Finset.sum_eq_single y] <;>
    simp +contextual [kr_mul, ancProj_mul_ancProj, kr_zero_right]

omit [NeZero c] in
theorem kr_one_ancProj_mul_roundC (e : Fin (d * c) ≃ Fin D) (R : ClassicalRound d c a)
    (f : Fin c → Fin a) (y : Fin c) :
    kr e 1 (ancProj y) * roundC e R f =
      kr e (R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) (ancProj y) := by
  unfold roundC
  rw [Finset.mul_sum, Finset.sum_eq_single y] <;>
    simp +contextual [kr_mul, ancProj_mul_ancProj, kr_zero_right, eq_comm]

/-- The recorded round is the deferred round `roundV` followed by the pinching of its
    ancilla. -/
theorem roundU_recordRound (e : Fin (d * c) ≃ Fin D) (R : ClassicalRound d c a)
    (f : Fin c → Fin a) (ρ : Matrix (Fin D) (Fin D) ℂ) :
    (roundU (recordRound e R) f).branch () ρ =
      maskR (fun i => ((finProdEquiv d c).symm (e.symm i)).2)
        ((roundV e R f : Matrix (Fin D) (Fin D) ℂ) * ρ *
          (roundV e R f : Matrix (Fin D) (Fin D) ℂ)ᴴ) := by
  have hK : ∀ y, ((recordRound e R).ans (f y) : Matrix (Fin D) (Fin D) ℂ) *
      (recordRound e R).P y =
      roundC e R f * kr e 1 (ancProj y) * roundW e R := by
    intro y
    rw [recordRound_ans_val, roundC_mul_kr_one_ancProj]
    change kr e (R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) 1 * roundW e R *
      ((roundW e R)ᴴ * kr e 1 (ancProj y) * roundW e R) = _
    calc _ = kr e (R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) 1 * (roundW e R * (roundW e R)ᴴ) *
          kr e 1 (ancProj y) * roundW e R := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [roundW_mul_conjTranspose_self, Matrix.mul_one, kr_mul, Matrix.mul_one,
          Matrix.one_mul]
  have h2 : ∀ y (X : Matrix (Fin D) (Fin D) ℂ), kr e 1 (ancProj y) * (roundC e R f * X) =
      roundC e R f * (kr e 1 (ancProj y) * X) := fun y X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, roundC_mul_kr_one_ancProj,
      kr_one_ancProj_mul_roundC]
  have h3 : ∀ y, (roundC e R f)ᴴ * kr e 1 (ancProj y) = kr e 1 (ancProj y) * (roundC e R f)ᴴ :=
    fun y => by
      simpa [conjTranspose_mul, kr_conjTranspose, ancProj_conjTranspose,
        ← roundC_mul_kr_one_ancProj] using
        congrArg conjTranspose (kr_one_ancProj_mul_roundC e R f y)
  rw [roundU_branch, maskR_anc_eq_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hK]
  change _ = kr e 1 (ancProj y) * (roundC e R f * roundW e R * ρ *
    (roundC e R f * roundW e R)ᴴ) * kr e 1 (ancProj y)
  simp only [conjTranspose_mul, kr_conjTranspose, conjTranspose_one, ancProj_conjTranspose,
    Matrix.mul_assoc, h2, h3]

end Record

/-! ## Lifting along the later ancillas -/

section LiftK

variable {m n a : ℕ}

/-- The unitary `U ⊗ 1 ⊗ ⋯ ⊗ 1` on the register with `k` more ancillas. -/
def liftKU (c : ℕ) : (k : ℕ) → {W : ℕ} → Matrix.unitaryGroup (Fin (m * n * W)) ℂ →
    Matrix.unitaryGroup (Fin (m * n * ancW c k W)) ℂ
  | 0, _, U => U
  | k + 1, W, U => liftKU c k (liftU (ancE m n W c) U)

/-- The round `R` with every projector and answer tensored with `1` on `k` more ancillas. -/
def liftKR (c : ℕ) : (k : ℕ) → {W : ℕ} → ClassicalRound (m * n * W) c a →
    ClassicalRound (m * n * ancW c k W) c a
  | 0, _, R => R
  | k + 1, W, R => liftKR c k (liftR (ancE m n W c) R)

/-- The labelling `r` read off the register part of the register with `k` more ancillas. -/
def liftKLab {α : Type} (c : ℕ) : (k : ℕ) → {W : ℕ} → (Fin (m * n * W) → α) →
    Fin (m * n * ancW c k W) → α
  | 0, _, r => r
  | k + 1, W, r => liftKLab c k fun i => r (ancSplit m n W c i).1

/-- The state `ρ ⊗ |0⟩⟨0| ⊗ ⋯ ⊗ |0⟩⟨0|` with `k` fresh ancillas. -/
def liftInitK (c : ℕ) [NeZero c] : (k : ℕ) → {W : ℕ} → DensityMatrix (m * n * W) →
    DensityMatrix (m * n * ancW c k W)
  | 0, _, ρ => ρ
  | k + 1, _, ρ => liftInitK c k (liftInit (c := c) ρ)

theorem liftKLab_apply {α : Type} (c : ℕ) :
    ∀ (k : ℕ) {W : ℕ} (r : Fin (m * n * W) → α) (i : Fin (m * n * ancW c k W)),
      liftKLab c k r i = r (ancDigits m n c k i).1
  | 0, _, _, _ => rfl
  | k + 1, W, _, i => liftKLab_apply c k (W := W * c) _ i

theorem liftU_comp_mergeChain {c d d' q : ℕ} (e : Fin (d * c) ≃ Fin d')
    (V : Matrix.unitaryGroup (Fin d) ℂ) (B : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    ∀ (q₀ : ℕ) (A' : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ),
      liftU e ∘ mergeChain V B q₀ A' = mergeChain (liftU e V) (liftU e ∘ B) q₀ (liftU e ∘ A')
  | 0, A' => by
    have hm : ∀ U U' : Matrix.unitaryGroup (Fin d) ℂ, liftU e (U * U') = liftU e U * liftU e U' :=
      fun U U' => Subtype.ext (by simp [kr_mul])
    rw [mergeChain, mergeChain, Fin.comp_cons, hm, hm]
    rfl
  | q₀ + 1, A' => by
    rw [mergeChain, mergeChain, Fin.comp_cons, liftU_comp_mergeChain e V B q₀ (Fin.tail A')]
    rfl

theorem liftKU_comp_mergeChain (c : ℕ) {q : ℕ} :
    ∀ (k : ℕ) {W : ℕ} (V : Matrix.unitaryGroup (Fin (m * n * W)) ℂ)
      (B : Fin (q + 1) → Matrix.unitaryGroup (Fin (m * n * W)) ℂ) (q₀ : ℕ)
      (A' : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin (m * n * W)) ℂ),
      liftKU c k ∘ mergeChain V B q₀ A' =
        mergeChain (liftKU c k V) (liftKU c k ∘ B) q₀ (liftKU c k ∘ A')
  | 0, _, _, _, _, _ => rfl
  | k + 1, W, V, B, q₀, A' => by
    change liftKU c k ∘ (liftU (ancE m n W c) ∘ mergeChain V B q₀ A') = _
    rw [liftU_comp_mergeChain, liftKU_comp_mergeChain c k]
    rfl

/-- One lift of the pinching identity of a round. -/
theorem roundU_liftR_pinch {c d D : ℕ} {α : Type} [DecidableEq α] (e : Fin (d * c) ≃ Fin D)
    {r : Fin d → α} (R : ClassicalRound d c a) (f : Fin c → Fin a)
    (V : Matrix.unitaryGroup (Fin d) ℂ)
    (h : ∀ ρ, (roundU R f).branch () ρ =
      maskR r ((V : Matrix (Fin d) (Fin d) ℂ) * ρ * (V : Matrix (Fin d) (Fin d) ℂ)ᴴ))
    (ρ : Matrix (Fin D) (Fin D) ℂ) :
    (roundU (liftR e R) f).branch () ρ =
      maskR (fun i => r ((finProdEquiv d c).symm (e.symm i)).1)
        ((liftU e V : Matrix (Fin D) (Fin D) ℂ) * ρ * (liftU e V : Matrix (Fin D) (Fin D) ℂ)ᴴ) := by
  rw [(liftsQ_roundU e R f).branch_eq_sum]
  conv_rhs => rw [← sum_kr_blk e ρ]
  simp only [Finset.mul_sum, Finset.sum_mul, maskR_sum, h, liftU_val, kr_conjTranspose, kr_mul,
    conjTranspose_one, Matrix.one_mul, Matrix.mul_one, maskR_kr]

/-- The pinching identity of a round, lifted along `k` more ancillas. -/
theorem roundU_liftKR_pinch (c : ℕ) {α : Type} [DecidableEq α] (f : Fin c → Fin a) :
    ∀ (k : ℕ) {W : ℕ} (R : ClassicalRound (m * n * W) c a) (r : Fin (m * n * W) → α)
      (V : Matrix.unitaryGroup (Fin (m * n * W)) ℂ),
      (∀ ρ, (roundU R f).branch () ρ = maskR r ((V : Matrix _ _ ℂ) * ρ * (V : Matrix _ _ ℂ)ᴴ)) →
      ∀ ρ, (roundU (liftKR c k R) f).branch () ρ =
        maskR (liftKLab c k r)
          ((liftKU c k V : Matrix _ _ ℂ) * ρ * (liftKU c k V : Matrix _ _ ℂ)ᴴ)
  | 0, _, _, _, _, h => h
  | k + 1, W, R, _, V, h =>
    roundU_liftKR_pinch c f k (liftR (ancE m n W c) R) _ (liftU (ancE m n W c) V)
      (roundU_liftR_pinch (ancE m n W c) R f V h)

end LiftK

/-! ## Recording the rounds of a head-tail adversary -/

section RecordH

variable {m n q K c a : ℕ} [NeZero c]

/-- `X` lifted along one fresh ancilla, with round `s` replaced by its recorded round on that
    ancilla and every other round lifted. -/
def recAt (s : ℕ) {W q₀ : ℕ} (X : MRH m n W q q₀ K c a) : MRH m n (W * c) q q₀ K c a where
  head := liftU (ancE m n W c) ∘ X.head
  tail j := liftU (ancE m n W c) ∘ X.tail j
  rounds i := if (i : ℕ) = s then recordRound (ancE m n W c) (X.rounds i)
    else liftR (ancE m n W c) (X.rounds i)
  init := liftInit X.init
  final := kr (ancE m n W c) X.final 1
  final_conjTranspose := by rw [kr_conjTranspose, X.final_conjTranspose, conjTranspose_one]
  final_mul_self := by rw [kr_mul, X.final_mul_self, Matrix.one_mul]

/-- `X` lifted along `j` fresh ancillas, recording round `s + i` into ancilla `i`. -/
def recordFrom : (j : ℕ) → (s : ℕ) → {W q₀ : ℕ} → MRH m n W q q₀ K c a →
    MRH m n (ancW c j W) q q₀ K c a
  | 0, _, _, _, X => X
  | j + 1, s, _, _, X => recordFrom j (s + 1) (recAt s X)

/-- The adversary after the head and the first round: segment `1` is its head. -/
def restH {W q₀ K' : ℕ} (X : MRH m n W q q₀ (K' + 1) c a) : MRH m n W q q K' c a where
  head := X.tail 0
  tail := Fin.tail X.tail
  rounds := Fin.tail X.rounds
  init := X.init
  final := X.final
  final_conjTranspose := X.final_conjTranspose
  final_mul_self := X.final_mul_self

omit [NeZero c] in
theorem MRH.ext_fields {W q₀ K' : ℕ} {X Y : MRH m n W q q₀ K' c a} (h1 : X.head = Y.head)
    (h2 : X.tail = Y.tail) (h3 : X.rounds = Y.rounds) (h4 : X.init = Y.init)
    (h5 : X.final = Y.final) : X = Y := by
  cases X; cases Y; congr

theorem head_recordFrom : ∀ (j s : ℕ) {W q₀ : ℕ} (X : MRH m n W q q₀ K c a),
    (recordFrom j s X).head = liftKU c j ∘ X.head
  | 0, _, _, _, _ => rfl
  | j + 1, s, _, _, X => head_recordFrom j (s + 1) (recAt s X)

theorem init_recordFrom : ∀ (j s : ℕ) {W q₀ : ℕ} (X : MRH m n W q q₀ K c a),
    (recordFrom j s X).init = liftInitK c j X.init
  | 0, _, _, _, _ => rfl
  | j + 1, s, _, _, X => init_recordFrom j (s + 1) (recAt s X)

theorem init_flatten (f : Fin c → Fin a) : ∀ (k : ℕ) {W q₀ : ℕ} (X : MRH m n W q q₀ k c a),
    (flatten f k X).init = liftInitK c k X.init
  | 0, _, _, _ => rfl
  | k + 1, _, _, X => init_flatten f k (peel f X)

theorem recordFrom_tail_rounds : ∀ (j s : ℕ) {W q₀ q₀' : ℕ} (X : MRH m n W q q₀ K c a)
    (X' : MRH m n W q q₀' K c a), X.tail = X'.tail → X.rounds = X'.rounds →
    (recordFrom j s X).tail = (recordFrom j s X').tail ∧
      (recordFrom j s X).rounds = (recordFrom j s X').rounds
  | 0, _, _, _, _, _, _, ht, hr => ⟨ht, hr⟩
  | j + 1, s, W, _, _, X, X', ht, hr =>
    recordFrom_tail_rounds j (s + 1) (recAt s X) (recAt s X')
      (congrArg (fun t => fun j => liftU (ancE m n W c) ∘ t j) ht)
      (congrArg (fun (t : Fin K → ClassicalRound (m * n * W) c a) (i : Fin K) =>
        if (i : ℕ) = s then recordRound (ancE m n W c) (t i) else liftR (ancE m n W c) (t i)) hr)

theorem restH_recAt (s : ℕ) {W q₀ : ℕ} (X : MRH m n W q q₀ (K + 1) c a) :
    restH (recAt (s + 1) X) = recAt s (restH X) :=
  MRH.ext_fields rfl rfl (funext fun i => by simp [restH, recAt, Fin.tail]) rfl rfl

theorem restH_recordFrom : ∀ (j s : ℕ) {W q₀ : ℕ} (X : MRH m n W q q₀ (K + 1) c a),
    restH (recordFrom j (s + 1) X) = recordFrom j s (restH X)
  | 0, _, _, _, _ => rfl
  | j + 1, s, _, _, X =>
    (restH_recordFrom j (s + 1) (recAt (s + 1) X)).trans (congrArg _ (restH_recAt s X))

theorem rounds_zero_recordFrom : ∀ (j s : ℕ) {W q₀ : ℕ} (X : MRH m n W q q₀ (K + 1) c a),
    (recordFrom j (s + 1) X).rounds 0 = liftKR c j (X.rounds 0)
  | 0, _, _, _, _ => rfl
  | j + 1, s, _, _, X => rounds_zero_recordFrom j (s + 1) (recAt (s + 1) X)

end RecordH

/-! ## Block diagonality of the recorded adversary -/

section BD

variable {m n q K c a : ℕ} {α : Type}

/-- Every unitary, projector and answer of `X` is block diagonal along `r`. -/
def MRH.BD {W q₀ : ℕ} (r : Fin (m * n * W) → α) (X : MRH m n W q q₀ K c a) : Prop :=
  (∀ i, BlockDiag r (X.head i : Matrix _ _ ℂ)) ∧ (∀ j i, BlockDiag r (X.tail j i : Matrix _ _ ℂ)) ∧
    (∀ j y, BlockDiag r ((X.rounds j).P y)) ∧
    (∀ j z, BlockDiag r ((X.rounds j).ans z : Matrix _ _ ℂ))

/-- The oracle and the projector `projS S` are block diagonal along `r`. -/
def OracleBD [NeZero n] {W : ℕ} (r : Fin (m * n * W) → α) (H : Fin m → Fin n)
    (S : Finset (Fin m)) : Prop :=
  BlockDiag r (oracleU m n W H : Matrix _ _ ℂ) ∧ BlockDiag r (projS m n W S)

theorem BlockDiag.one_sub {D : ℕ} {r : Fin D → α} {P : Matrix (Fin D) (Fin D) ℂ}
    (hP : BlockDiag r P) : BlockDiag r (1 - P) :=
  fun i j hij => by simp [hP i j hij, BlockDiag.one r i j hij]

variable [NeZero c]

theorem roundW_blockDiag {d D : ℕ} {r : Fin d → α} (e : Fin (d * c) ≃ Fin D)
    (R : ClassicalRound d c a) (hP : ∀ y, BlockDiag r (R.P y)) :
    BlockDiag (fun i => r ((finProdEquiv d c).symm (e.symm i)).1) (roundW e R) :=
  BlockDiag.sum _ fun y => (hP y).kr e _

theorem MRH.BD.lift_recAt {W q₀ : ℕ} {r : Fin (m * n * W) → α} {X : MRH m n W q q₀ K c a}
    (h : X.BD r) (s : ℕ) : (recAt s X).BD fun i => r (ancSplit m n W c i).1 := by
  obtain ⟨hh, ht, hP, hA⟩ := h
  have hW : ∀ j, BlockDiag (fun i => r (ancSplit m n W c i).1)
      (roundW (ancE m n W c) (X.rounds j)) := fun j => roundW_blockDiag _ _ (hP j)
  refine ⟨fun i => (hh i).kr _ 1, fun j i => (ht j i).kr _ 1, fun j y => ?_, fun j z => ?_⟩
  all_goals by_cases hj : (j : ℕ) = s <;> simp only [recAt, hj, ↓reduceIte]
  exacts [((hW j).conjTranspose.mul ((BlockDiag.one r).kr _ _)).mul (hW j), (hP j y).kr _ 1,
    ((hA j z).kr _ 1).mul (hW j), (hA j z).kr _ 1]

omit [NeZero c] in
theorem OracleBD.lift [NeZero n] {W : ℕ} {r : Fin (m * n * W) → α} {H : Fin m → Fin n}
    {S : Finset (Fin m)} (h : OracleBD r H S) :
    OracleBD (fun i => r (ancSplit m n W c i).1) H S := by
  rw [OracleBD, oracleU_lift, projS_lift]; exact ⟨h.1.kr _ 1, h.2.kr _ 1⟩

theorem MRH.BD.recordFrom [NeZero n] {H : Fin m → Fin n} {S : Finset (Fin m)} :
    ∀ (j s : ℕ) {W q₀ : ℕ} (X : MRH m n W q q₀ K c a) (r : Fin (m * n * W) → α),
      X.BD r → OracleBD r H S →
        (QROM.recordFrom j s X).BD (liftKLab c j r) ∧ OracleBD (liftKLab c j r) H S
  | 0, _, _, _, _, _, h, ho => ⟨h, ho⟩
  | j + 1, s, _, _, X, _, h, ho =>
    MRH.BD.recordFrom j (s + 1) (QROM.recAt s X) _ (h.lift_recAt s) ho.lift

theorem covQ_scOracleQ [NeZero n] [DecidableEq α] {W : ℕ} {r : Fin (m * n * W) → α}
    {H : Fin m → Fin n} {S : Finset (Fin m)} (h : OracleBD r H S) :
    CovQ r (scOracleQ m n W H S) := by
  intro b M
  cases b <;> simp only [scOracleQ_branch_false, scOracleQ_branch_true,
    h.2.one_sub.conj_maskR h.2.one_sub, h.2.conj_maskR h.2, h.1.conj_maskR h.1.conjTranspose]

theorem covQ_mrChainSC_recordFrom [NeZero n] [DecidableEq α] {H : Fin m → Fin n}
    {S : Finset (Fin m)} (f : Fin c → Fin a) (j s : ℕ) {W q₀ : ℕ} (X : MRH m n W q q₀ K c a)
    (r : Fin (m * n * W) → α) (h : X.BD r) (ho : OracleBD r H S) :
    CovQ (liftKLab c j r) (mrChainSC (scOracleQ m n (ancW c j W) H S) f K q₀
      (QROM.recordFrom j s X).head (QROM.recordFrom j s X).tail
      (QROM.recordFrom j s X).rounds) := by
  obtain ⟨⟨hh, ht, hP, hA⟩, ho'⟩ := MRH.BD.recordFrom j s X r h ho
  exact covQ_mrChainSC (covQ_scOracleQ ho') f K q₀ _ _ _ hh ht hP hA

end BD

/-! ## The deferred run and the recorded run -/

section Main

variable {m n q c a : ℕ} [NeZero c]

/-- Replacing the deferred round `V` by a round that is `V` followed by the pinching along `r`
    leaves the value of every observable block diagonal along `r`, when the rest of the run
    commutes with the pinching. -/
theorem trace_pinch_step {D : ℕ} {α : Type} [DecidableEq α] {r : Fin D → α}
    {Y : Matrix (Fin D) (Fin D) ℂ} (hY : BlockDiag r Y) (Hd : QComp D Bool)
    (V : Matrix.unitaryGroup (Fin D) ℂ) (Rd : QComp D Unit)
    (hR : ∀ ρ, Rd.branch () ρ =
      maskR r ((V : Matrix (Fin D) (Fin D) ℂ) * ρ * (V : Matrix (Fin D) (Fin D) ℂ)ᴴ))
    (Rest : QComp D Bool) (hRest : CovQ r Rest) (b : Bool) (ρ : Matrix (Fin D) (Fin D) ℂ) :
    (Y * (QComp.qbind Hd fun b₁ => QComp.qbind (unitaryChannel V) fun _ =>
        QComp.qbind Rest fun b₂ => QComp.qpure (b₁ || b₂)).branch b ρ).trace =
      (Y * (QComp.qbind Hd fun b₁ => QComp.qbind Rd fun _ =>
        QComp.qbind Rest fun b₂ => QComp.qpure (b₁ || b₂)).branch b ρ).trace := by
  rw [qbind_branch_apply, qbind_branch_apply, tsum_fintype, tsum_fintype, Matrix.mul_sum,
    Matrix.mul_sum, trace_sum, trace_sum]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [qbind_unit_branch, qbind_unit_branch, unitaryChannel_branch_apply, hR, qbind_branch_apply,
    qbind_branch_apply, tsum_fintype, tsum_fintype, Matrix.mul_sum, Matrix.mul_sum, trace_sum,
    trace_sum]
  refine Finset.sum_congr rfl fun b₂ _ => ?_
  rw [hRest, qpure_branch_apply, qpure_branch_apply]
  split_ifs <;> [exact (trace_mul_maskR hY _).symm; rfl]

/-- The head-tail adversary after the first round, with that round recorded, is block
    diagonal along the digit of its ancilla. -/
theorem restH_recAt_zero_BD [NeZero n] {k w q₀ : ℕ} (A : MRH m n w q q₀ (k + 1) c a)
    (H : Fin m → Fin n) (S : Finset (Fin m)) :
    (restH (recAt 0 A)).BD (fun i => (ancSplit m n w c i).2) ∧
      OracleBD (fun i => (ancSplit m n w c i).2) H S := by
  have h1 : ∀ y y' : Fin c, y ≠ y' → (1 : Matrix (Fin c) (Fin c) ℂ) y y' = 0 :=
    fun _ _ h => Matrix.one_apply_ne h
  have hr : ∀ i : Fin k, (restH (recAt 0 A)).rounds i = liftR (ancE m n w c) (A.rounds i.succ) :=
    fun i => by simp [restH, recAt, Fin.tail]
  refine ⟨⟨fun i => blockDiag_kr_anc _ _ h1, fun j i => blockDiag_kr_anc _ _ h1,
    fun j y => ?_, fun j z => ?_⟩, ?_, ?_⟩
  all_goals (simp only [hr, oracleU_lift, projS_lift]; exact blockDiag_kr_anc _ _ h1)

/-- One round of the induction: the run of `peel f A` with its rounds recorded and the run of
    `A` with all its rounds recorded agree on every observable block diagonal along the
    ancilla of round `0`. -/
theorem trace_record_step [NeZero n] (H : Fin m → Fin n) (S : Finset (Fin m))
    (f : Fin c → Fin a) {k w q₀ : ℕ} (A : MRH m n w q q₀ (k + 1) c a)
    (Y : Matrix (Fin (m * n * ancW c k (w * c))) (Fin (m * n * ancW c k (w * c))) ℂ)
    (hY : BlockDiag (liftKLab c k fun i => (ancSplit m n w c i).2) Y) (b : Bool)
    (ρ : Matrix (Fin (m * n * ancW c k (w * c))) (Fin (m * n * ancW c k (w * c))) ℂ) :
    (Y * (mrChainSC (scOracleQ m n (ancW c k (w * c)) H S) f k (q + q₀)
        (recordFrom k 0 (peel f A)).head (recordFrom k 0 (peel f A)).tail
        (recordFrom k 0 (peel f A)).rounds).branch b ρ).trace =
      (Y * (mrChainSC (scOracleQ m n (ancW c k (w * c)) H S) f (k + 1) q₀
        (recordFrom (k + 1) 0 A).head (recordFrom (k + 1) 0 A).tail
        (recordFrom (k + 1) 0 A).rounds).branch b ρ).trace := by
  have hrounds : (peel f A).rounds = (restH (recAt 0 A)).rounds :=
    funext fun i => by simp [peel, restH, recAt, Fin.tail]
  obtain ⟨ht, hr⟩ := recordFrom_tail_rounds k 0 (peel f A) (restH (recAt 0 A)) rfl hrounds
  have hh : (recordFrom k 0 (peel f A)).head =
      mergeChain (liftKU c k (roundV (ancE m n w c) (A.rounds 0) f))
        (recordFrom k 0 (restH (recAt 0 A))).head q₀
        (liftKU c k ∘ (liftU (ancE m n w c) ∘ A.head)) := by
    rw [head_recordFrom, head_recordFrom]
    exact liftKU_comp_mergeChain c k _ _ q₀ _
  rw [hh, ht, hr, mrChainSC_mergeChain]
  have hZ := restH_recordFrom k 0 (recAt 0 A)
  have hZh : (recordFrom (k + 1) 0 A).head = liftKU c k ∘ (liftU (ancE m n w c) ∘ A.head) :=
    head_recordFrom k 1 (recAt 0 A)
  have hZr : (recordFrom (k + 1) 0 A).rounds 0 =
      liftKR c k (recordRound (ancE m n w c) (A.rounds 0)) :=
    rounds_zero_recordFrom k 0 (recAt 0 A)
  change _ = (Y * (QComp.qbind (scChain (scOracleQ m n (ancW c k (w * c)) H S) q₀
    (recordFrom (k + 1) 0 A).head) fun b₁ =>
      QComp.qbind (roundU ((recordFrom (k + 1) 0 A).rounds 0) f) fun _ =>
        QComp.qbind (mrChainSC (scOracleQ m n (ancW c k (w * c)) H S) f k q
          (restH (recordFrom k (0 + 1) (recAt 0 A))).head
          (restH (recordFrom k (0 + 1) (recAt 0 A))).tail
          (restH (recordFrom k (0 + 1) (recAt 0 A))).rounds) fun b₂ =>
            QComp.qpure (b₁ || b₂)).branch b ρ).trace
  rw [hZh, hZr, hZ]
  obtain ⟨hBD, hO⟩ := restH_recAt_zero_BD A H S
  exact trace_pinch_step hY _ _ _
    (roundU_liftKR_pinch c f k _ _ _ (roundU_recordRound (ancE m n w c) (A.rounds 0) f)) _
    (covQ_mrChainSC_recordFrom f k 0 _ _ hBD hO) b ρ

/-- The deferred single run and the run with every round recorded agree on every observable
    block diagonal in the round-outcome ancillas, on every input and every branch of the
    semi-classical chain. -/
theorem trace_flatten_blockDiag [NeZero n] (H : Fin m → Fin n) (S : Finset (Fin m))
    (f : Fin c → Fin a) :
    ∀ (k : ℕ) {w q₀ : ℕ} (A : MRH m n w q q₀ k c a)
      (Y : Matrix (Fin (m * n * ancW c k w)) (Fin (m * n * ancW c k w)) ℂ),
      BlockDiag (roundOutcomes m n c (k := k) (w := w)) Y →
      ∀ (b : Bool) (ρ : Matrix (Fin (m * n * ancW c k w)) (Fin (m * n * ancW c k w)) ℂ),
        (Y * (scChain (scOracleQ m n (ancW c k w) H S) (flatQ q k q₀)
            (flatten f k A).U).branch b ρ).trace =
          (Y * (mrChainSC (scOracleQ m n (ancW c k w) H S) f k q₀ (recordFrom k 0 A).head
            (recordFrom k 0 A).tail (recordFrom k 0 A).rounds).branch b ρ).trace
  | 0, _, _, _, _, _, _, _ => rfl
  | k + 1, w, q₀, A, Y, hY, b, ρ => by
    have h1 : BlockDiag (roundOutcomes m n c (k := k) (w := w * c)) Y :=
      fun i j hij => hY i j fun h => hij (congrArg Fin.tail h)
    have h2 : BlockDiag (liftKLab c k fun i => (ancSplit m n w c i).2) Y :=
      fun i j hij => hY i j fun h => hij <| by
        rw [liftKLab_apply, liftKLab_apply]; exact congrFun h 0
    exact (trace_flatten_blockDiag H S f k (peel f A) Y h1 b ρ).trans
      (trace_record_step H S f A Y h2 b ρ)

variable {w k : ℕ}

/-- `A` with every round recorded into its ancilla of the flattened register and the final
    projector `diagB G`. -/
def recordMR (A : QAdvMR m n w q k c a) (G : Fin (m * n * ancW c k w) → Bool) :
    QAdvMR m n (ancW c k w) q k c a where
  seg := Fin.cons (recordFrom k 0 A.toMRH).head (recordFrom k 0 A.toMRH).tail
  rounds := (recordFrom k 0 A.toMRH).rounds
  init := (recordFrom k 0 A.toMRH).init
  final := diagB G
  final_conjTranspose := diagB_conjTranspose G
  final_mul_self := diagB_mul_self G

/-- The general multi-round adversary on the flattened register whose round `j` writes the
    outcome into ancilla `j` before it is measured, with the final projector `diagB G`. -/
def recordGen (A : QAdvMR m n w q k c a) (G : Fin (m * n * ancW c k w) → Bool) :
    QAdvMRGen m n (ancW c k w) q k c a :=
  (recordMR A G).toGen

/-- A diagonal final test of the flattened adversary is the final projector of the adversary
    that records its round outcomes in the ancillas and measures its rounds. -/
theorem prOut_withFinalB_toQAdv_eq [NeZero n] (A : QAdvMR m n w q k c a) (f : Fin c → Fin a)
    (G : Fin (m * n * ancW c k w) → Bool) (H : Fin m → Fin n) :
    prOut ((toQAdv A f).withFinalB G) H = prOutMRGen (recordGen A G) H f := by
  rw [recordGen, prOutMRGen_toGen, prOutMR_eq_trace, prOut_eq_trace_scChain_empty]
  have hi : (toQAdv A f).init = (recordFrom k 0 A.toMRH).init := by
    rw [toQAdv, init_flatten, init_recordFrom]
  have h := trace_flatten_blockDiag H ∅ f k A.toMRH (diagB G) (BlockDiag.diagB _ G) false
    (toQAdv A f).init.val
  exact congrArg (fun t : ℂ => ENNReal.ofReal t.re) (h.trans (by rw [hi]; rfl))

end Main

end CatCrypt.Quantum.QROM
