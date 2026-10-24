/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.QOwcpaAuxMeasured
public import CatCryptCore.Quantum.QROM.KEMQuantumGame

/-!
# Multi-round adversaries transported along an isometry

An isometry `V` from a register of dimension `d` into a register of dimension
`d'` (`Vᴴ V = 1`) carries a multi-round adversary on the first register to one
on the second: every unitary `U` becomes `V U Vᴴ + (1 - V Vᴴ)`, every round
projector `P y` becomes `V (P y) Vᴴ`, with the complement `1 - V Vᴴ` added to one
outcome, and every unitary that precedes an oracle call is composed with a fixed
unitary `C`. When the oracle channel `O'` of the second register satisfies
`O' (C V ρ Vᴴ Cᴴ) = V (O ρ) Vᴴ`, the transported chain on `V ρ Vᴴ` is `V` of the
original chain, and every measurement whose projector pulls back along `V` has
the same outcome probability.

## Main definitions

* `Carries X Y O O'` — `O' (X ρ Xᴴ) = Y (O ρ) Yᴴ` for every `ρ`
* `isoU V hV U` — the unitary `V U Vᴴ + (1 - V Vᴴ)`
* `isoR V hV y₀ R` — the round with projectors `V (P y) Vᴴ`, the complement of
  the image added at `y₀`, and answers `isoU`
* `isoChain C V hV U` — the segment `U` transported, with `C` composed after
  every unitary that precedes an oracle call
* `isoMR C V hV y₀ A P' …` — the multi-round adversary `A` transported, with
  final projector `P'`

## Main results

* `carries_oracleChain`, `carries_mrChain`, `carries_mrPrefixU` — the
  transported chains are carried along `V`
* `prOutMR_isoMR`, `prOutPrefixMR_isoMR` — the transported adversary has the
  output probability and the cut query-register probability of `A`, when its
  oracle carries the oracle of `A` and the measured projectors pull back
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct CatCrypt.Quantum.UnitaryChannel
  CatCrypt.Quantum.Measurement

noncomputable section

namespace CatCrypt.Quantum.QROM.PRFAdvEmbed

/-! ## Channels carried along a map -/

section Carry

variable {d d' : ℕ}

/-- `O'` applied to `X ρ Xᴴ` is `Y (O ρ) Yᴴ`, for every `ρ`. -/
def Carries (X Y : Matrix (Fin d') (Fin d) ℂ) (O : QComp d Unit) (O' : QComp d' Unit) : Prop :=
  ∀ ρ : Matrix (Fin d) (Fin d) ℂ, O'.branch () (X * ρ * Xᴴ) = Y * O.branch () ρ * Yᴴ

theorem carries_qbind {X Y Z : Matrix (Fin d') (Fin d) ℂ} {O P : QComp d Unit}
    {O' P' : QComp d' Unit} (hO : Carries X Y O O') (hP : Carries Y Z P P') :
    Carries X Z (QComp.qbind O fun _ => P) (QComp.qbind O' fun _ => P') := by
  intro ρ
  rw [qbind_unit_branch, qbind_unit_branch, hO, hP]

theorem carries_unitaryChannel {X Y : Matrix (Fin d') (Fin d) ℂ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) (U' : Matrix.unitaryGroup (Fin d') ℂ)
    (h : (U' : Matrix (Fin d') (Fin d') ℂ) * X = Y * (U : Matrix (Fin d) (Fin d) ℂ)) :
    Carries X Y (unitaryChannel U) (unitaryChannel U') := by
  intro ρ
  rw [unitaryChannel_branch_apply, unitaryChannel_branch_apply]
  calc (U' : Matrix (Fin d') (Fin d') ℂ) * (X * ρ * Xᴴ) * (U' : Matrix (Fin d') (Fin d') ℂ)ᴴ
      = ((U' : Matrix (Fin d') (Fin d') ℂ) * X) * ρ *
          ((U' : Matrix (Fin d') (Fin d') ℂ) * X)ᴴ := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [h, conjTranspose_mul]; simp only [Matrix.mul_assoc]

theorem carries_roundU {c a : ℕ} {X : Matrix (Fin d') (Fin d) ℂ} (R : ClassicalRound d c a)
    (R' : ClassicalRound d' c a) (f : Fin c → Fin a)
    (hP : ∀ y, R'.P y * X = X * R.P y)
    (hA : ∀ z, (R'.ans z : Matrix (Fin d') (Fin d') ℂ) * X = X * (R.ans z : Matrix (Fin d) (Fin d) ℂ)) :
    Carries X X (roundU R f) (roundU R' f) := by
  intro ρ
  rw [roundU_branch, roundU_branch, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hk : (R'.ans (f y) : Matrix (Fin d') (Fin d') ℂ) * R'.P y * X =
      X * ((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y) := by
    rw [Matrix.mul_assoc, hP, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]
  calc (R'.ans (f y) : Matrix (Fin d') (Fin d') ℂ) * R'.P y * (X * ρ * Xᴴ) *
        ((R'.ans (f y) : Matrix (Fin d') (Fin d') ℂ) * R'.P y)ᴴ
      = ((R'.ans (f y) : Matrix (Fin d') (Fin d') ℂ) * R'.P y * X) * ρ *
          ((R'.ans (f y) : Matrix (Fin d') (Fin d') ℂ) * R'.P y * X)ᴴ := by
        rw [conjTranspose_mul (_ * _) X]; simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hk, conjTranspose_mul]; simp only [Matrix.mul_assoc]

end Carry

/-! ## Unitaries and rounds transported along an isometry -/

section Iso

variable {d d' : ℕ} (V : Matrix (Fin d') (Fin d) ℂ) (hV : Vᴴ * V = 1)

include hV in
theorem iso_compl_mul : (1 - V * Vᴴ) * V = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV, Matrix.mul_one, sub_self]

include hV in
theorem iso_mul_compl : Vᴴ * (1 - V * Vᴴ) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hV, Matrix.one_mul, sub_self]

include hV in
theorem iso_compl_mul_self : (1 - V * Vᴴ) * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, iso_compl_mul V hV, Matrix.zero_mul,
    sub_zero]

theorem iso_compl_conjTranspose : (1 - V * Vᴴ)ᴴ = 1 - V * Vᴴ := by
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose]

/-- The matrix `V U Vᴴ + (1 - V Vᴴ)`. -/
def isoMat (U : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d') (Fin d') ℂ :=
  V * U * Vᴴ + (1 - V * Vᴴ)

include hV in
theorem isoMat_mul_iso (U : Matrix (Fin d) (Fin d) ℂ) : isoMat V U * V = V * U := by
  rw [isoMat, Matrix.add_mul, iso_compl_mul V hV, add_zero, Matrix.mul_assoc, hV,
    Matrix.mul_one]

include hV in
theorem isoMat_mul (U U' : Matrix (Fin d) (Fin d) ℂ) :
    isoMat V U * isoMat V U' = isoMat V (U * U') := by
  have h1 : V * U * Vᴴ * (V * U' * Vᴴ) = V * (U * U') * Vᴴ := by
    rw [show V * U * Vᴴ * (V * U' * Vᴴ) = V * U * (Vᴴ * V) * U' * Vᴴ by
      simp only [Matrix.mul_assoc], hV]
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  have h2 : V * U * Vᴴ * (1 - V * Vᴴ) = 0 := by
    rw [Matrix.mul_assoc, iso_mul_compl V hV, Matrix.mul_zero]
  have h3 : (1 - V * Vᴴ) * (V * U' * Vᴴ) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, iso_compl_mul V hV, Matrix.zero_mul,
      Matrix.zero_mul]
  rw [isoMat, isoMat, isoMat, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h1, h2, h3,
    iso_compl_mul_self V hV, add_zero, zero_add]

theorem isoMat_conjTranspose (U : Matrix (Fin d) (Fin d) ℂ) :
    (isoMat V U)ᴴ = isoMat V Uᴴ := by
  rw [isoMat, isoMat, conjTranspose_add, iso_compl_conjTranspose, conjTranspose_mul,
    conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem isoMat_one : isoMat V (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  rw [isoMat, Matrix.mul_one, add_sub_cancel]

/-- The unitary `V U Vᴴ + (1 - V Vᴴ)`. -/
def isoU (U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix.unitaryGroup (Fin d') ℂ :=
  ⟨isoMat V U, Matrix.mem_unitaryGroup_iff'.mpr (by
    rw [star_eq_conjTranspose, isoMat_conjTranspose, isoMat_mul V hV, ← star_eq_conjTranspose,
      UnitaryGroup.star_mul_self, isoMat_one V])⟩

theorem isoU_val (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (isoU V hV U : Matrix (Fin d') (Fin d') ℂ) = isoMat V U := rfl

theorem isoU_mul_iso (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (isoU V hV U : Matrix (Fin d') (Fin d') ℂ) * V = V * (U : Matrix (Fin d) (Fin d) ℂ) :=
  isoMat_mul_iso V hV U

variable {c a : ℕ}

/-- The projector `V P Vᴴ`, with the complement `1 - V Vᴴ` added when `y = y₀`. -/
def isoP (y₀ y : Fin c) (P : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d') (Fin d') ℂ :=
  V * P * Vᴴ + if y = y₀ then 1 - V * Vᴴ else 0

include hV in
theorem isoP_mul_iso (y₀ y : Fin c) (P : Matrix (Fin d) (Fin d) ℂ) :
    isoP V y₀ y P * V = V * P := by
  rw [isoP, Matrix.add_mul, Matrix.mul_assoc, hV, Matrix.mul_one]
  split_ifs
  · rw [iso_compl_mul V hV, add_zero]
  · rw [Matrix.zero_mul, add_zero]

include hV in
theorem isoP_mul (y₀ y y' : Fin c) (P P' : Matrix (Fin d) (Fin d) ℂ) :
    isoP V y₀ y P * isoP V y₀ y' P' =
      V * (P * P') * Vᴴ + if y = y₀ ∧ y' = y₀ then 1 - V * Vᴴ else 0 := by
  have h1 : V * P * Vᴴ * (V * P' * Vᴴ) = V * (P * P') * Vᴴ := by
    rw [show V * P * Vᴴ * (V * P' * Vᴴ) = V * P * (Vᴴ * V) * P' * Vᴴ by
      simp only [Matrix.mul_assoc], hV]
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  have h2 : V * P * Vᴴ * (1 - V * Vᴴ) = 0 := by
    rw [Matrix.mul_assoc, iso_mul_compl V hV, Matrix.mul_zero]
  have h3 : (1 - V * Vᴴ) * (V * P' * Vᴴ) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, iso_compl_mul V hV, Matrix.zero_mul,
      Matrix.zero_mul]
  rw [isoP, isoP, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h1]
  by_cases hy : y = y₀ <;> by_cases hy' : y' = y₀ <;>
    simp [hy, hy', h2, h3, iso_compl_mul_self V hV]

/-- The round `R` transported along `V`: projectors `isoP`, answers `isoU`. -/
def isoR (y₀ : Fin c) (R : ClassicalRound d c a) : ClassicalRound d' c a where
  P y := isoP V y₀ y (R.P y)
  P_conjTranspose y := by
    rw [isoP, conjTranspose_add, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, R.P_conjTranspose, Matrix.mul_assoc]
    split_ifs
    · rw [iso_compl_conjTranspose]
    · rw [conjTranspose_zero]
  P_mul_self y := by
    rw [isoP_mul V hV, R.P_mul_self, isoP]
    simp only [and_self]
  P_orth y y' h := by
    rw [isoP_mul V hV, R.P_orth y y' h, Matrix.mul_zero, Matrix.zero_mul, zero_add, ite_eq_right]
    rintro ⟨h1, h2⟩
    exact h (h1.trans h2.symm)
  P_sum := by
    simp only [isoP, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, R.P_sum, Matrix.mul_one, add_sub_cancel]
  ans z := isoU V hV (R.ans z)

theorem carries_isoR (y₀ : Fin c) (R : ClassicalRound d c a) (f : Fin c → Fin a) :
    Carries V V (roundU R f) (roundU (isoR V hV y₀ R) f) :=
  carries_roundU R _ f (fun y => isoP_mul_iso V hV y₀ y (R.P y))
    (fun z => isoU_mul_iso V hV (R.ans z))

end Iso

/-! ## Chains transported along an isometry -/

section Chain

variable {d d' : ℕ} (C : Matrix.unitaryGroup (Fin d') ℂ) (V : Matrix (Fin d') (Fin d) ℂ)
  (hV : Vᴴ * V = 1)

/-- The segment `U` transported along `V`, with `C` composed after every unitary
that precedes an oracle call. -/
def isoChain {q : ℕ} (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    Fin (q + 1) → Matrix.unitaryGroup (Fin d') ℂ :=
  fun i => if (i : ℕ) < q then C * isoU V hV (U i) else isoU V hV (U i)

theorem isoChain_tail {q : ℕ} (U : Fin (q + 1 + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    Fin.tail (isoChain C V hV U) = isoChain C V hV (Fin.tail U) := by
  funext i
  simp only [Fin.tail, isoChain, Fin.val_succ, Nat.add_lt_add_iff_right]

variable {O : QComp d Unit} {O' : QComp d' Unit}

/-- A chain whose every unitary is `C` after the transported unitary is carried
from `V` to `C V`. -/
theorem carries_oracleChain_pre
    (hO : Carries ((C : Matrix (Fin d') (Fin d') ℂ) * V) V O O') :
    ∀ (j : ℕ) (U : Fin (j + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (U' : Fin (j + 1) → Matrix.unitaryGroup (Fin d') ℂ), (∀ i, U' i = C * isoU V hV (U i)) →
      Carries V ((C : Matrix (Fin d') (Fin d') ℂ) * V) (oracleChain O j U) (oracleChain O' j U')
  | 0, U, U', hU => by
    refine carries_unitaryChannel _ _ ?_
    rw [hU, MulMemClass.coe_mul, Matrix.mul_assoc, isoU_mul_iso, Matrix.mul_assoc]
  | j + 1, U, U', hU => by
    refine carries_qbind (carries_unitaryChannel (U 0) (U' 0) ?_)
      (carries_qbind hO (carries_oracleChain_pre hO j (Fin.tail U) (Fin.tail U')
        fun i => hU i.succ))
    rw [hU, MulMemClass.coe_mul, Matrix.mul_assoc, isoU_mul_iso, Matrix.mul_assoc]

/-- The transported segment is carried from `V` to `V`. -/
theorem carries_oracleChain
    (hO : Carries ((C : Matrix (Fin d') (Fin d') ℂ) * V) V O O') :
    ∀ (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ),
      Carries V V (oracleChain O q U) (oracleChain O' q (isoChain C V hV U))
  | 0, U => carries_unitaryChannel _ _ (isoU_mul_iso V hV (U 0))
  | q + 1, U => by
    refine carries_qbind (carries_unitaryChannel (U 0) _ ?_)
      (carries_qbind hO ?_)
    · simp only [isoChain, Fin.val_zero, Nat.zero_lt_succ, ite_true]
      rw [MulMemClass.coe_mul, Matrix.mul_assoc, isoU_mul_iso, Matrix.mul_assoc]
    · show Carries V V (oracleChain O q (Fin.tail U))
        (oracleChain O' q (Fin.tail (isoChain C V hV U)))
      rw [isoChain_tail]
      exact carries_oracleChain hO q (Fin.tail U)

variable {c a q : ℕ} (y₀ : Fin c) (f : Fin c → Fin a)

/-- The transported multi-round chain is carried from `V` to `V`. -/
theorem carries_mrChain
    (hO : Carries ((C : Matrix (Fin d') (Fin d') ℂ) * V) V O O') :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a),
      Carries V V (mrChain O f k q₀ head tail R)
        (mrChain O' f k q₀ (isoChain C V hV head) (fun j => isoChain C V hV (tail j))
          (fun j => isoR V hV y₀ (R j)))
  | 0, q₀, head, _, _ => carries_oracleChain C V hV hO q₀ head
  | k + 1, q₀, head, tail, R =>
    carries_qbind (carries_oracleChain C V hV hO q₀ head)
      (carries_qbind (carries_isoR V hV y₀ (R 0) f)
        (carries_mrChain hO k q (tail 0) (Fin.tail tail) (Fin.tail R)))

/-- The transported cut multi-round chain is carried from `V` to `C V`. -/
theorem carries_mrPrefixU
    (hO : Carries ((C : Matrix (Fin d') (Fin d') ℂ) * V) V O O') :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a) (j : Fin (flatQ q k q₀)),
      Carries V ((C : Matrix (Fin d') (Fin d') ℂ) * V) (mrPrefixU O f k q₀ head tail R j)
        (mrPrefixU O' f k q₀ (isoChain C V hV head) (fun j => isoChain C V hV (tail j))
          (fun j => isoR V hV y₀ (R j)) j)
  | 0, q₀, head, _, _, j =>
    carries_oracleChain_pre C V hV hO j _ _ fun i => by
      have hi : ((Fin.castLE (Nat.succ_le_succ j.isLt.le) i : Fin (q₀ + 1)) : ℕ) < q₀ := by
        have := i.isLt; have := j.isLt; simp only [flatQ] at this; simp; omega
      simp only [isoChain, ite_eq_left hi]
  | k + 1, q₀, head, tail, R, j => by
    by_cases h : (j : ℕ) < q₀
    · simp only [mrPrefixU, dite_eq_left h]
      exact carries_oracleChain_pre C V hV hO j _ _ fun i => by
        have hi : ((Fin.castLE (by omega) i : Fin (q₀ + 1)) : ℕ) < q₀ := by
          have := i.isLt; simp; omega
        simp only [isoChain, ite_eq_left hi]
    · simp only [mrPrefixU, dite_eq_right h]
      exact carries_qbind (carries_oracleChain C V hV hO q₀ head)
        (carries_qbind (carries_isoR V hV y₀ (R 0) f)
          (carries_mrPrefixU hO k q (tail 0) (Fin.tail tail) (Fin.tail R) _))

end Chain

/-! ## Multi-round adversaries transported along an isometry -/

section MR

variable {d d' : ℕ}

/-- A projector that pulls back along `Y` to a projector `P` measures `Y σ Yᴴ`
with the probability that `P` measures `σ`. -/
theorem trace_pullback (Y : Matrix (Fin d') (Fin d) ℂ) (P : Matrix (Fin d) (Fin d) ℂ)
    (P' : Matrix (Fin d') (Fin d') ℂ) (hP'H : P'ᴴ = P') (hP'I : P' * P' = P')
    (hPH : Pᴴ = P) (hPI : P * P = P) (h : Yᴴ * P' * Y = P) (σ : Matrix (Fin d) (Fin d) ℂ) :
    (P' * (Y * σ * Yᴴ) * P'ᴴ).trace = (P * σ * Pᴴ).trace := by
  rw [hP'H, hPH, trace_mul_cycle, hP'I, trace_mul_cycle, hPI,
    show P' * (Y * σ * Yᴴ) = (P' * Y * σ) * Yᴴ by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm, ← h]
  simp only [Matrix.mul_assoc]

variable {m m' n w w' q k c a : ℕ}

/-- The isometric image `V ρ Vᴴ` of a density matrix. -/
def isoDM (V : Matrix (Fin d') (Fin d) ℂ) (hV : Vᴴ * V = 1) (ρ : DensityMatrix d) :
    DensityMatrix d' where
  val := V * ρ.val * Vᴴ
  psd := ρ.psd.mul_mul_conjTranspose_same V
  tr_one := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, ρ.tr_one]

/-- The multi-round adversary `A` transported along `V`: segments `isoChain`,
rounds `isoR`, the initial state `V ρ Vᴴ` and the final projector `P'`. -/
def isoMR (C : Matrix.unitaryGroup (Fin (m' * n * w')) ℂ)
    (V : Matrix (Fin (m' * n * w')) (Fin (m * n * w)) ℂ) (hV : Vᴴ * V = 1) (y₀ : Fin c)
    (A : QAdvMR m n w q k c a) (P' : Matrix (Fin (m' * n * w')) (Fin (m' * n * w')) ℂ)
    (hP'H : P'ᴴ = P') (hP'I : P' * P' = P') : QAdvMR m' n w' q k c a where
  seg j := isoChain C V hV (A.seg j)
  rounds j := isoR V hV y₀ (A.rounds j)
  init := isoDM V hV A.init
  final := P'
  final_conjTranspose := hP'H
  final_mul_self := hP'I

variable [NeZero n] (C : Matrix.unitaryGroup (Fin (m' * n * w')) ℂ)
  (V : Matrix (Fin (m' * n * w')) (Fin (m * n * w)) ℂ) (hV : Vᴴ * V = 1) (y₀ : Fin c)
  (A : QAdvMR m n w q k c a) (P' : Matrix (Fin (m' * n * w')) (Fin (m' * n * w')) ℂ)
  (hP'H : P'ᴴ = P') (hP'I : P' * P' = P')

/-- **The transported adversary outputs `1` with the probability of `A`**, when
the oracle `H'` carries the oracle `H` from `C V` to `V` and the final projector
pulls back to the final projector of `A`. -/
theorem prOutMR_isoMR (H : Fin m → Fin n) (H' : Fin m' → Fin n) (f : Fin c → Fin a)
    (hO : Carries ((C : Matrix _ _ ℂ) * V) V (oracleQ m n w H) (oracleQ m' n w' H'))
    (hP : Vᴴ * P' * V = A.final) :
    prOutMR (isoMR C V hV y₀ A P' hP'H hP'I) H' f = prOutMR A H f := by
  unfold prOutMR prTrue_Q runMR QAdvMR.measure
  rw [qbind_unit_branch, qbind_unit_branch, measProj_branch_true, measProj_branch_true]
  have h := carries_mrChain C V hV y₀ f hO k q (A.seg 0) (Fin.tail A.seg) A.rounds A.init.val
  change (mrChain (oracleQ m' n w' H') f k q (isoChain C V hV (A.seg 0))
      (fun j => isoChain C V hV (Fin.tail A.seg j)) (fun j => isoR V hV y₀ (A.rounds j))).branch ()
      (V * A.init.val * Vᴴ) = _ at h
  change ENNReal.ofReal (P' * (mrChain (oracleQ m' n w' H') f k q (isoChain C V hV (A.seg 0))
      (fun j => isoChain C V hV (Fin.tail A.seg j)) (fun j => isoR V hV y₀ (A.rounds j))).branch ()
      (V * A.init.val * Vᴴ) * P'ᴴ).trace.re = _
  rw [h, trace_pullback V A.final P' hP'H hP'I A.final_conjTranspose A.final_mul_self hP]

/-- **The transported adversary, cut at a query, has its query register in `S'`
with the probability that `A`, cut at the same query, has its query register in
`S`**, when `projS S'` pulls back along `C V` to `projS S`. -/
theorem prOutPrefixMR_isoMR (H : Fin m → Fin n) (H' : Fin m' → Fin n) (f : Fin c → Fin a)
    (hO : Carries ((C : Matrix _ _ ℂ) * V) V (oracleQ m n w H) (oracleQ m' n w' H'))
    (S : Finset (Fin m)) (S' : Finset (Fin m'))
    (hS : ((C : Matrix (Fin (m' * n * w')) (Fin (m' * n * w')) ℂ) * V)ᴴ * projS m' n w' S' *
      ((C : Matrix (Fin (m' * n * w')) (Fin (m' * n * w')) ℂ) * V) = projS m n w S)
    (j : Fin (flatQ q k q)) :
    prOutPrefixMR (isoMR C V hV y₀ A P' hP'H hP'I) H' f S' j = prOutPrefixMR A H f S j := by
  unfold prOutPrefixMR prTrue_Q
  rw [qbind_unit_branch, qbind_unit_branch, measProj_branch_true, measProj_branch_true]
  have h := carries_mrPrefixU C V hV y₀ f hO k q (A.seg 0) (Fin.tail A.seg) A.rounds j
    A.init.val
  change ENNReal.ofReal (projS m' n w' S' * (mrPrefixU (oracleQ m' n w' H') f k q
      (isoChain C V hV (A.seg 0)) (fun j => isoChain C V hV (Fin.tail A.seg j))
      (fun j => isoR V hV y₀ (A.rounds j)) j).branch ()
      (V * A.init.val * Vᴴ) * (projS m' n w' S')ᴴ).trace.re = _
  rw [h, trace_pullback _ _ _ (projS_conjTranspose m' n w' S') (projS_mul_self m' n w' S')
    (projS_conjTranspose m n w S) (projS_mul_self m n w S) hS]

end MR

/-! ## The embedding of a merged-oracle register -/

section Embed

variable (m mF n w : ℕ)

/-- The tag register: empty, or a query point of the second summand with its
value register. -/
abbrev Tag : Type := Option (Fin mF × Fin n)

/-- The number of tag states. -/
def tagN : ℕ := mF * n + 1

/-- An enumeration of the tag register. -/
def tagE : Tag mF n ≃ Fin (tagN mF n) :=
  (Fintype.equivFin _).trans (finCongr (by simp [tagN, Fintype.card_option]))

/-- The index set of the embedding register: query point, value, work register
and tag. -/
abbrev NewIdx : Type := ((Fin m × Fin n) × Fin (2 * w)) × Tag mF n

/-- The work register and the tag as the work register `Fin (2 * (w * tagN))`,
keeping the first factor of `Fin (2 * w)` first. -/
def wtE : Fin (2 * w) × Tag mF n ≃ Fin (2 * (w * tagN mF n)) :=
  ((finProdEquiv 2 w).symm.prodCongr (tagE mF n)).trans ((Equiv.prodAssoc _ _ _).trans
    (((Equiv.refl (Fin 2)).prodCongr (finProdEquiv w (tagN mF n))).trans
      (finProdEquiv 2 (w * tagN mF n))))

/-- The row-major index of the embedding register. -/
def newE : NewIdx m mF n w ≃ Fin (m * n * (2 * (w * tagN mF n))) :=
  (Equiv.prodAssoc _ _ _).trans (((Equiv.refl _).prodCongr (wtE mF n w)).trans
    (oracleIndex m n (2 * (w * tagN mF n))))

variable {m mF n} (u₀ : Fin m)

/-- The amplitude of the embedding: a point `castAdd u₁` of the merged domain
goes to the query point `u₁` with its value and the empty tag; a point
`natAdd v` goes to the query point `u₀` with the uniform superposition of
values and the tag `(v, y)`. -/
def coreV (u : Fin m) (y' : Fin n) (t : Tag mF n) (x : Fin (m + mF)) (y : Fin n) : ℂ :=
  Fin.addCases (motive := fun _ => ℂ) (fun u₁ => if u = u₁ ∧ y' = y ∧ t = none then 1 else 0)
    (fun v => if u = u₀ ∧ t = some (v, y) then ((Real.sqrt n : ℝ) : ℂ)⁻¹ else 0) x

theorem natCast_mul_inv_sqrt [NeZero n] :
    (n : ℂ) * ((((Real.sqrt n : ℝ) : ℂ))⁻¹ * ((Real.sqrt n : ℝ) : ℂ)⁻¹) = 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hn.le, Complex.ofReal_natCast]
  exact mul_inv_cancel₀ (by exact_mod_cast hn.ne')

theorem sum_coreV [NeZero n] (x x₂ : Fin (m + mF)) (y y₂ : Fin n) :
    ∑ u : Fin m, ∑ y' : Fin n, ∑ t : Tag mF n,
        star (coreV u₀ u y' t x y) * coreV u₀ u y' t x₂ y₂ =
      if x = x₂ ∧ y = y₂ then 1 else 0 := by
  induction x using Fin.addCases with
  | left u₁ =>
    induction x₂ using Fin.addCases with
    | left u₂ =>
      simp only [coreV, Fin.addCases_left, Fintype.sum_option, ite_and]
      simp [Finset.sum_ite_eq', Fin.castAdd_inj]
      by_cases h₁ : u₁ = u₂ <;> by_cases h₂ : y = y₂ <;> simp_all [eq_comm]
    | right v₂ =>
      simp only [coreV, Fin.addCases_left, Fin.addCases_right, Fintype.sum_option]
      simp
      intro h
      exact absurd (congrArg Fin.val h) (by simp; omega)
  | right v =>
    induction x₂ using Fin.addCases with
    | left u₂ =>
      simp only [coreV, Fin.addCases_left, Fin.addCases_right, Fintype.sum_option]
      simp
      intro h
      exact absurd (congrArg Fin.val h) (by simp; omega)
    | right v₂ =>
      simp only [coreV, Fin.addCases_right, Fintype.sum_option]
      simp only [reduceCtorEq, and_false, ite_false, star_zero, zero_mul, zero_add, ite_and,
        Option.some.injEq]
      simp [Finset.sum_ite_eq', Fin.natAdd_inj]
      have hn : n ≠ 0 := NeZero.ne n
      by_cases h₁ : v = v₂ <;> by_cases h₂ : y = y₂
      · subst h₁ h₂
        simpa using natCast_mul_inv_sqrt (n := n)
      · simp [h₁, h₂, hn]; exact fun h => h₂ h.symm
      · simp [h₁, h₂, hn]; exact fun h => h₁ h.symm
      · simp [h₁, hn]; exact fun h => absurd h.symm h₁

/-- The index set of the merged-oracle register. -/
abbrev OldIdx : Type := (Fin (m + mF) × Fin n) × Fin (2 * w)

/-- The embedding on index sets: the work register is kept, the query point and
value are mapped by `coreV`. -/
def embT : Matrix (NewIdx m mF n w) (OldIdx (m := m) (mF := mF) (n := n) w) ℂ :=
  fun i j => if i.1.2 = j.2 then coreV u₀ i.1.1.1 i.1.1.2 i.2 j.1.1 j.1.2 else 0

theorem embT_iso [NeZero n] :
    (embT (mF := mF) (n := n) w u₀)ᴴ * embT (mF := mF) (n := n) w u₀ = 1 := by
  ext ⟨⟨x, y⟩, r⟩ ⟨⟨x₂, y₂⟩, r₂⟩
  simp only [Matrix.mul_apply, conjTranspose_apply, embT, Fintype.sum_prod_type]
  have h : ∀ (u : Fin m) (y' : Fin n), (∑ r' : Fin (2 * w), ∑ t : Tag mF n,
      star (if r' = r then coreV u₀ u y' t x y else 0) *
        if r' = r₂ then coreV u₀ u y' t x₂ y₂ else 0) =
      if r = r₂ then ∑ t : Tag mF n, star (coreV u₀ u y' t x y) * coreV u₀ u y' t x₂ y₂
      else 0 := by
    intro u y'
    simp only [apply_ite star, star_zero, ite_mul, zero_mul, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    by_cases hr : r = r₂
    · subst hr; simp
    · simp only [ite_eq_right hr]
      exact Finset.sum_eq_zero fun t _ => by rw [ite_eq_right (Ne.symm hr)]
  simp only [h]
  rw [Matrix.one_apply]
  by_cases hr : r = r₂
  · simp only [ite_eq_left hr]
    rw [sum_coreV]
    subst hr
    simp [Prod.ext_iff]
  · simp [hr, Prod.ext_iff]

/-- The embedding on the total registers. -/
def embV : Matrix (Fin (m * n * (2 * (w * tagN mF n)))) (Fin ((m + mF) * n * (2 * w))) ℂ :=
  (embT w u₀).submatrix (newE m mF n w).symm (oracleIndex (m + mF) n (2 * w)).symm

theorem embV_iso [NeZero n] :
    (embV (mF := mF) (n := n) w u₀)ᴴ * embV (mF := mF) (n := n) w u₀ = 1 := by
  rw [embV, conjTranspose_submatrix, Matrix.submatrix_mul_equiv, embT_iso,
    Matrix.submatrix_one_equiv]

variable [NeZero n]

/-- The shift of the tag value by the table `F`: `(v, y) ↦ (v, y + F v)`. -/
def tagShift (F : Fin mF → Fin n) : Equiv.Perm (Tag mF n) :=
  Equiv.optionCongr (Equiv.prodShear (Equiv.refl _) fun v => Equiv.addRight (F v))

/-- The permutation of the embedding register that shifts the tag by `F`. -/
def shiftT (F : Fin mF → Fin n) : Equiv.Perm (NewIdx m mF n w) :=
  (Equiv.refl _).prodCongr (tagShift F)

/-- The standard oracle for `H` on the query point and value of the embedding
register. -/
def oracleT (H : Fin m → Fin n) : Equiv.Perm (NewIdx m mF n w) :=
  ((stdOraclePerm H).prodCongr (Equiv.refl _)).prodCongr (Equiv.refl _)

/-- The unitary that shifts the tag by `F`. -/
def shiftU (F : Fin mF → Fin n) : Matrix.unitaryGroup (Fin (m * n * (2 * (w * tagN mF n)))) ℂ :=
  permUnitary ((newE m mF n w).permCongr (shiftT w F))

end Embed

/-! ## Permutation unitaries on index sets -/

section Perm

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {N : ℕ}

theorem permUnitary_permCongr (e : α ≃ Fin N) (π : Equiv.Perm α) :
    (permUnitary (e.permCongr π) : Matrix (Fin N) (Fin N) ℂ) =
      (permUnitary π : Matrix α α ℂ).submatrix e.symm e.symm := by
  ext i j
  simp only [submatrix_apply, permUnitary_apply, Equiv.permCongr_apply]
  congr 1
  exact propext ⟨fun h => by rw [h]; simp, fun h => by rw [← h]; simp⟩

omit [Fintype β] [DecidableEq β] in
theorem permUnitary_mul_apply (σ : Equiv.Perm α) (M : Matrix α β ℂ) (i : α) (j : β) :
    ((permUnitary σ : Matrix α α ℂ) * M) i j = M (σ.symm i) j := by
  simp [Matrix.mul_apply]

omit [Fintype α] [DecidableEq α] in
theorem mul_permUnitary_apply (σ : Equiv.Perm β) (M : Matrix α β ℂ) (i : α) (j : β) :
    (M * (permUnitary σ : Matrix β β ℂ)) i j = M i (σ j) := by
  simp [Matrix.mul_apply, Equiv.symm_apply_eq]

end Perm

/-! ## The oracle of the embedding register -/

section EmbedOracle

variable {m mF n : ℕ} (w : ℕ) (u₀ : Fin m) [NeZero n]

/-- On index sets, the oracle `O` after the tag shift by `F`, applied to the
embedding, is the embedding of the merged oracle `mergeOracle O F`. -/
theorem oracleT_shiftT_embT (O : Fin m → Fin n) (F : Fin mF → Fin n) :
    (permUnitary (oracleT (mF := mF) w O) : Matrix (NewIdx m mF n w) (NewIdx m mF n w) ℂ) *
        (permUnitary (shiftT (m := m) w F) : Matrix (NewIdx m mF n w) (NewIdx m mF n w) ℂ) *
        embT w u₀ =
      embT w u₀ * (permUnitary ((stdOraclePerm (mergeOracle O F)).prodCongr
        (Equiv.refl (Fin (2 * w)))) : Matrix (OldIdx (m := m) (mF := mF) (n := n) w) _ ℂ) := by
  ext ⟨⟨⟨u, y'⟩, r'⟩, t⟩ ⟨⟨x, y⟩, r⟩
  rw [Matrix.mul_assoc, permUnitary_mul_apply, permUnitary_mul_apply, mul_permUnitary_apply]
  simp only [oracleT, shiftT, embT, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map,
    Equiv.refl_symm, Equiv.refl_apply, stdOraclePerm, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk]
  congr 1
  induction x using Fin.addCases with
  | left u₁ =>
    simp only [coreV, Fin.addCases_left, mergeOracle_castAdd, Equiv.symm_apply_eq]
    simp only [tagShift, sub_eq_iff_eq_add, Equiv.optionCongr_apply]
    by_cases hu : u = u₁
    · subst hu; rfl
    · simp [hu]
  | right v =>
    simp only [coreV, Fin.addCases_right, mergeOracle_natAdd, Equiv.symm_apply_eq]
    simp [tagShift]

theorem oraclePerm_newE (O : Fin m → Fin n) :
    oraclePerm m n (2 * (w * tagN mF n)) O = (newE m mF n w).permCongr (oracleT w O) := by
  ext i
  obtain ⟨⟨⟨⟨u, y'⟩, r⟩, t⟩, rfl⟩ := (newE m mF n w).surjective i
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  simp [newE, oracleT, stdOraclePerm]

/-- **The oracle of the embedding register carries the merged oracle.** The
oracle `O` applied after the tag shift by `F` to `V ρ Vᴴ` is `V` of the merged
oracle `mergeOracle O F` applied to `ρ`. -/
theorem carries_oracle (O : Fin m → Fin n) (F : Fin mF → Fin n) :
    Carries ((shiftU (m := m) w F : Matrix _ _ ℂ) * embV w u₀) (embV w u₀)
      (oracleQ (m + mF) n (2 * w) (mergeOracle O F)) (oracleQ m n (2 * (w * tagN mF n)) O) := by
  refine carries_unitaryChannel _ _ ?_
  rw [oracleU_eq_permUnitary, oracleU_eq_permUnitary, oraclePerm_newE, shiftU, embV,
    permUnitary_permCongr, permUnitary_permCongr, oraclePerm, permUnitary_permCongr,
    ← Matrix.mul_assoc, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, oracleT_shiftT_embT]

end EmbedOracle

/-! ## Diagonal projectors pulled back along the embedding -/

section Diag

variable {d d' : ℕ}

/-- A diagonal on the left equals a diagonal on the right when the two diagonals
agree wherever the matrix is nonzero. -/
theorem diagonal_mul_eq_mul_diagonal (V : Matrix (Fin d') (Fin d) ℂ) (g : Fin d' → ℂ)
    (h : Fin d → ℂ) (hgh : ∀ i j, V i j ≠ 0 → g i = h j) :
    Matrix.diagonal g * V = V * Matrix.diagonal h := by
  ext i j
  rw [diagonal_mul, mul_diagonal]
  by_cases hij : V i j = 0
  · rw [hij, mul_zero, zero_mul]
  · rw [hgh i j hij, mul_comm]

/-- A projector that commutes with `V` on the left pulls back along `V`. -/
theorem pullback_of_mul_eq (V : Matrix (Fin d') (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (P' : Matrix (Fin d') (Fin d') ℂ) (P : Matrix (Fin d) (Fin d) ℂ) (h : P' * V = V * P) :
    Vᴴ * P' * V = P := by
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, hV, Matrix.one_mul]

theorem one_kronecker_diagonal {d₁ d₂ : ℕ} (f : Fin d₂ → ℂ) :
    (1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ Matrix.diagonal f =
      Matrix.diagonal (fun k => f ((finProdEquiv d₁ d₂).symm k).2) := by
  ext i j
  rw [kronecker_apply, diagonal_apply, one_apply, diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : (finProdEquiv d₁ d₂).symm i ≠ (finProdEquiv d₁ d₂).symm j :=
      fun e => h ((finProdEquiv d₁ d₂).symm.injective e)
    rw [ite_eq_right h]
    by_cases h1 : ((finProdEquiv d₁ d₂).symm i).1 = ((finProdEquiv d₁ d₂).symm j).1
    · rw [ite_eq_left h1, ite_eq_right (fun h2 => h' (Prod.ext h1 h2)), mul_zero]
    · rw [ite_eq_right h1, zero_mul]

/-- `winBitProj` is the diagonal of the indicator that the first factor of the
work register is `1`. -/
theorem winBitProj_eq_diagonal (M n w : ℕ) :
    winBitProj M n w = Matrix.diagonal (fun k => indS 2 {1}
      ((finProdEquiv 2 w).symm ((finProdEquiv (M * n) (2 * w)).symm k).2).1) := by
  unfold winBitProj
  rw [diagonal_kronecker_one, one_kronecker_diagonal]

end Diag

section EmbedDiag

variable {m mF n : ℕ} (w : ℕ) (u₀ : Fin m) [NeZero n]

omit [NeZero n] in
theorem embV_apply (z : NewIdx m mF n w) (o : OldIdx (m := m) (mF := mF) (n := n) w) :
    embV w u₀ (newE m mF n w z) (oracleIndex (m + mF) n (2 * w) o) = embT w u₀ z o := by
  simp [embV]

omit [NeZero n] in
theorem winBitProj_mul_embV :
    winBitProj m n (w * tagN mF n) * embV w u₀ = embV w u₀ * winBitProj (m + mF) n w := by
  rw [winBitProj_eq_diagonal, winBitProj_eq_diagonal]
  refine diagonal_mul_eq_mul_diagonal _ _ _ fun i j hij => ?_
  obtain ⟨⟨⟨⟨u, y'⟩, r'⟩, t⟩, rfl⟩ := (newE m mF n w).surjective i
  obtain ⟨⟨⟨x, y⟩, r⟩, rfl⟩ := (oracleIndex (m + mF) n (2 * w)).surjective j
  rw [embV_apply] at hij
  have hr : r' = r := by
    by_contra hr
    exact hij (by simp [embT, hr])
  subst hr
  simp [newE, wtE, oracleIndex]

/-- The embedding pulls `winBitProj` back to `winBitProj`. -/
theorem winBitProj_pullback :
    (embV w u₀)ᴴ * winBitProj m n (w * tagN mF n) * embV w u₀ = winBitProj (m + mF) n w :=
  pullback_of_mul_eq _ (embV_iso w u₀) _ _ (winBitProj_mul_embV w u₀)

/-- The query point of the embedding register at a point of the merged domain:
`u₁` at `castAdd u₁` and `u₀` on the second summand. -/
def embQ (x : Fin (m + mF)) : Fin m :=
  Fin.addCases (motive := fun _ => Fin m) id (fun _ => u₀) x

/-- The points of the merged domain whose query point lies in `S`. -/
def pullS (S : Finset (Fin m)) : Finset (Fin (m + mF)) :=
  Finset.univ.filter fun x => embQ u₀ x ∈ S

omit [NeZero n] in
theorem projS_mul_embV (S : Finset (Fin m)) :
    projS m n (2 * (w * tagN mF n)) S * embV w u₀ =
      embV w u₀ * projS (m + mF) n (2 * w) (pullS u₀ S) := by
  rw [projS_eq_diagonal, projS_eq_diagonal]
  refine diagonal_mul_eq_mul_diagonal _ _ _ fun i j hij => ?_
  obtain ⟨⟨⟨⟨u, y'⟩, r'⟩, t⟩, rfl⟩ := (newE m mF n w).surjective i
  obtain ⟨⟨⟨x, y⟩, r⟩, rfl⟩ := (oracleIndex (m + mF) n (2 * w)).surjective j
  rw [embV_apply] at hij
  have hu : u = embQ u₀ x := by
    by_contra hu
    apply hij
    induction x using Fin.addCases with
    | left u₁ =>
      have : u ≠ u₁ := by simpa [embQ] using hu
      simp [embT, coreV, this]
    | right v =>
      have : u ≠ u₀ := by simpa [embQ] using hu
      simp [embT, coreV, this]
  simp [xPart, newE, oracleIndex, indS, pullS, hu]

theorem shiftU_mul_projS (F : Fin mF → Fin n) (S : Finset (Fin m)) :
    (shiftU (m := m) w F : Matrix _ _ ℂ) * projS m n (2 * (w * tagN mF n)) S =
      projS m n (2 * (w * tagN mF n)) S * (shiftU (m := m) w F : Matrix _ _ ℂ) := by
  ext i j
  rw [shiftU, permUnitary_mul_apply, mul_permUnitary_apply, projS_eq_diagonal, diagonal_apply,
    diagonal_apply]
  obtain ⟨z, rfl⟩ := (newE m mF n w).surjective j
  obtain ⟨z₁, rfl⟩ := (newE m mF n w).surjective i
  have hx : ∀ z' : NewIdx m mF n w,
      xPart m n (2 * (w * tagN mF n)) (newE m mF n w z') = z'.1.1.1 := fun z' => by
    simp [xPart, newE, oracleIndex]
  have hs : ∀ z' : NewIdx m mF n w, ((newE m mF n w).permCongr (shiftT w F)).symm
      (newE m mF n w z') = newE m mF n w ((shiftT w F).symm z') := fun z' => by
    rw [Equiv.symm_apply_eq, Equiv.permCongr_apply]; simp
  simp only [hs, Equiv.permCongr_apply, Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq,
    hx, Equiv.symm_apply_eq]
  by_cases h : z₁ = shiftT w F z
  · subst h; simp [shiftT]
  · rw [ite_eq_right h, ite_eq_right h]

/-- The embedding after the tag shift pulls `projS S` back to `projS (pullS u₀ S)`. -/
theorem projS_pullback (F : Fin mF → Fin n) (S : Finset (Fin m)) :
    ((shiftU (m := m) w F).val * embV (mF := mF) (n := n) w u₀)ᴴ *
        projS m n (2 * (w * tagN mF n)) S *
        ((shiftU (m := m) w F).val * embV (mF := mF) (n := n) w u₀) =
      projS (m + mF) n (2 * w) (pullS u₀ S) := by
  set Cm : Matrix (Fin (m * n * (2 * (w * tagN mF n)))) (Fin (m * n * (2 * (w * tagN mF n)))) ℂ :=
    (shiftU (m := m) w F).val with hCm
  have hC : Cmᴴ * Cm = 1 := by
    rw [hCm, ← star_eq_conjTranspose, UnitaryGroup.star_mul_self]
  have hPC : Cm * projS m n (2 * (w * tagN mF n)) S = projS m n (2 * (w * tagN mF n)) S * Cm :=
    shiftU_mul_projS w F S
  set V := embV (mF := mF) (n := n) w u₀ with hVd
  calc (Cm * V)ᴴ * projS m n (2 * (w * tagN mF n)) S * (Cm * V)
      = Vᴴ * (Cmᴴ * (projS m n (2 * (w * tagN mF n)) S * Cm)) * V := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Vᴴ * projS m n (2 * (w * tagN mF n)) S * V := by
        rw [← hPC, ← Matrix.mul_assoc Cmᴴ, hC, Matrix.one_mul]
    _ = _ := pullback_of_mul_eq _ (embV_iso w u₀) _ _ (projS_mul_embV w u₀ S)

end EmbedDiag

/-! ## A KEM adversary whose oracle also answers a table -/

section KEM

variable {m₁ m₂ m₃ n w q k c a : ℕ} {PK C K : Type} [NeZero (m₁ + m₂)] [NeZero n] [NeZero c]

/-- The rank-one state `ψ ψᴴ` conjugated by `X` is the rank-one state of `X ψ`. -/
theorem mul_vecMulVec_mul_conjTranspose {d d' : ℕ} (X : Matrix (Fin d') (Fin d) ℂ)
    (ψ : Fin d → ℂ) : X * vecMulVec ψ (star ψ) * Xᴴ = vecMulVec (X *ᵥ ψ) (star (X *ᵥ ψ)) := by
  rw [mul_vecMulVec, vecMulVec_mul, star_mulVec]

/-- The KEM adversary with the table `F` built in: every run of `A`, whose oracle
domain is the merged domain `(m₁ + m₂) + m₃`, transported along `embV` with the
tag shift by `F` after every unitary that precedes an oracle call. The table
enters only through the fixed unitary `shiftU F`. -/
def hardwire (F : Fin m₃ → Fin n) (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) :
    KEMQAdv m₁ m₂ n (w * tagN m₃ n) q k c a PK C K where
  run pk cs κ := isoMR (shiftU (m := m₁ + m₂) w F) (embV w 0) (embV_iso w 0) 0 (A.run pk cs κ)
    (winBitProj (m₁ + m₂) n (w * tagN m₃ n)) (winBitProj_conjTranspose _ _ _)
    (winBitProj_mul_self _ _ _)
  final_eq _ _ _ := rfl
  pure pk cs κ := by
    obtain ⟨ψ, hψ⟩ := A.pure pk cs κ
    exact ⟨embV w 0 *ᵥ ψ, show embV w 0 * (A.run pk cs κ).init.val * (embV w 0)ᴴ = _ by
      rw [hψ, mul_vecMulVec_mul_conjTranspose]⟩

/-- **The hard-wired adversary accepts with the probability of `A` against the
merged oracle.** -/
theorem prOutMR_hardwire (F : Fin m₃ → Fin n) (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K)
    (pk : PK) (cs : C) (κ : K) (O : Fin (m₁ + m₂) → Fin n) (f : Fin c → Fin a) :
    prOutMR ((hardwire F A).run pk cs κ) O f = prOutMR (A.run pk cs κ) (mergeOracle O F) f := by
  refine prOutMR_isoMR _ _ _ _ _ _ _ _ _ _ f (carries_oracle w 0 O F) ?_
  rw [(A.final_eq pk cs κ), winBitProj_pullback]

/-- **The hard-wired adversary, cut at a query, has its query register in `S` with
the probability that `A`, cut at the same query against the merged oracle, has
its query register in `pullS 0 S`.** -/
theorem prOutPrefixMR_hardwire (F : Fin m₃ → Fin n)
    (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (pk : PK) (cs : C) (κ : K)
    (O : Fin (m₁ + m₂) → Fin n) (f : Fin c → Fin a) (S : Finset (Fin (m₁ + m₂)))
    (j : Fin (flatQ q k q)) :
    prOutPrefixMR ((hardwire F A).run pk cs κ) O f S j =
      prOutPrefixMR (A.run pk cs κ) (mergeOracle O F) f (pullS 0 S) j :=
  prOutPrefixMR_isoMR _ _ _ _ _ _ _ _ _ _ f (carries_oracle w 0 O F) _ _ (projS_pullback w 0 F S) j

end KEM

/-! ## Padding an adversary with queries after its last unitary -/

section Pad

variable {d : ℕ}

/-- A chain whose unitaries after the first are `1` is `O` applied `Q` times after
the first unitary. -/
theorem oracleChain_ones (O : QComp d Unit) :
    ∀ (Q : ℕ) (U : Fin (Q + 1) → Matrix.unitaryGroup (Fin d) ℂ), (∀ i : Fin (Q + 1), 0 < (i : ℕ) → U i = 1) →
      ∀ ρ, (oracleChain O Q U).branch () ρ =
        (fun σ => O.branch () σ)^[Q] ((U 0 : Matrix (Fin d) (Fin d) ℂ) * ρ * (U 0 : Matrix (Fin d) (Fin d) ℂ)ᴴ)
  | 0, U, _, ρ => by rw [oracleChain, unitaryChannel_branch_apply]; rfl
  | Q + 1, U, hU, ρ => by
    rw [oracleChain, qbind_unit_branch, qbind_unit_branch, unitaryChannel_branch_apply,
      oracleChain_ones O Q (Fin.tail U) (fun i hi => hU i.succ (by simp)) _,
      Function.iterate_succ_apply]
    have h1 : Fin.tail U 0 = 1 := hU 1 (by simp)
    rw [h1]
    simp

/-- A chain that continues the chain of `V` with unitaries `1` is `O` applied
`Q - j` more times after the chain of `V`. -/
theorem oracleChain_pad (O : QComp d Unit) :
    ∀ (j Q : ℕ) (_ : j ≤ Q) (V : Fin (j + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (U : Fin (Q + 1) → Matrix.unitaryGroup (Fin d) ℂ),
      (∀ (i : Fin (Q + 1)) (hi : (i : ℕ) ≤ j), U i = V ⟨i, by omega⟩) →
      (∀ i : Fin (Q + 1), j < (i : ℕ) → U i = 1) →
      ∀ ρ, (oracleChain O Q U).branch () ρ =
        (fun σ => O.branch () σ)^[Q - j] ((oracleChain O j V).branch () ρ)
  | 0, Q, _, V, U, hV, h1, ρ => by
    rw [oracleChain_ones O Q U (fun i hi => h1 i hi), hV 0 (by simp), oracleChain,
      unitaryChannel_branch_apply, Nat.sub_zero]
    rfl
  | j + 1, 0, hj, _, _, _, _, _ => absurd hj (by omega)
  | j + 1, Q + 1, hj, V, U, hV, h1, ρ => by
    rw [oracleChain, oracleChain, qbind_unit_branch, qbind_unit_branch, qbind_unit_branch,
      qbind_unit_branch, unitaryChannel_branch_apply, unitaryChannel_branch_apply,
      hV 0 (by simp), Nat.add_sub_add_right]
    exact oracleChain_pad O j Q (by omega) (Fin.tail V) (Fin.tail U)
      (fun i hi => by rw [Fin.tail, hV i.succ (by simp; omega)]; rfl)
      (fun i hi => h1 i.succ (by simp; omega)) _

/-- A projector commuting with `U` measures `U σ Uᴴ` with the probability that it
measures `σ`. -/
theorem trace_proj_conj_comm (P : Matrix (Fin d) (Fin d) ℂ) (hH : Pᴴ = P)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (hPU : P * (U : Matrix (Fin d) (Fin d) ℂ) = U * P)
    (σ : Matrix (Fin d) (Fin d) ℂ) :
    (P * ((U : Matrix (Fin d) (Fin d) ℂ) * σ * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) * Pᴴ).trace =
      (P * σ * Pᴴ).trace := by
  have hUP : (U : Matrix (Fin d) (Fin d) ℂ)ᴴ * P = P * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
    have := congrArg conjTranspose hPU
    rw [conjTranspose_mul, conjTranspose_mul, hH] at this
    exact this
  have hU : (U : Matrix (Fin d) (Fin d) ℂ)ᴴ * (U : Matrix (Fin d) (Fin d) ℂ) = 1 := by
    rw [← star_eq_conjTranspose, UnitaryGroup.star_mul_self]
  have hc : P * ((U : Matrix (Fin d) (Fin d) ℂ) * σ * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) * P =
      (U : Matrix (Fin d) (Fin d) ℂ) * (P * σ * P) * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ :=
    calc P * ((U : Matrix (Fin d) (Fin d) ℂ) * σ * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) * P
        = (P * (U : Matrix (Fin d) (Fin d) ℂ)) * σ * ((U : Matrix (Fin d) (Fin d) ℂ)ᴴ * P) := by
          simp only [Matrix.mul_assoc]
      _ = ((U : Matrix (Fin d) (Fin d) ℂ) * P) * σ * (P * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) := by
          rw [hPU, hUP]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hH, hc, trace_mul_cycle, ← Matrix.mul_assoc, hU, Matrix.one_mul]

variable {m n w j : ℕ}

/-- The adversary `Y` with `Q - j` further queries after its last unitary, each
followed by the unitary `1`. -/
def padQ (Q : ℕ) (_hj : j ≤ Q) (Y : QAdv m n w j) : QAdv m n w Q where
  U i := if h : (i : ℕ) ≤ j then Y.U ⟨i, by omega⟩ else 1
  init := Y.init
  final := Y.final
  final_conjTranspose := Y.final_conjTranspose
  final_mul_self := Y.final_mul_self

variable [NeZero n]

/-- **Padding does not change the output probability** when the final projector
commutes with the oracle unitary. -/
theorem prOut_padQ (Q : ℕ) (hj : j ≤ Q) (Y : QAdv m n w j) (H : Fin m → Fin n)
    (hcomm : Y.final * (oracleU m n w H : Matrix _ _ ℂ) = (oracleU m n w H : Matrix _ _ ℂ) * Y.final) :
    prOut (padQ Q hj Y) H = prOut Y H := by
  unfold prOut prTrue_Q run QAdv.measure
  rw [qbind_unit_branch, qbind_unit_branch, measProj_branch_true, measProj_branch_true]
  change ENNReal.ofReal (Y.final * (oracleChain (oracleQ m n w H) Q (padQ Q hj Y).U).branch ()
      Y.init.val * Y.finalᴴ).trace.re = _
  rw [oracleChain_pad (oracleQ m n w H) j Q hj Y.U (padQ Q hj Y).U
    (fun i hi => by simp [padQ, hi]) (fun i hi => by simp [padQ, show ¬ (i : ℕ) ≤ j by omega])]
  congr 2
  generalize (oracleChain (oracleQ m n w H) j Y.U).branch () Y.init.val = σ
  induction Q - j generalizing σ with
  | zero => rfl
  | succ p ih =>
    rw [Function.iterate_succ_apply, ih]
    exact trace_proj_conj_comm _ Y.final_conjTranspose _ hcomm σ

/-- The query-register projector commutes with the oracle unitary. -/
theorem projS_mul_oracleU (S : Finset (Fin m)) (H : Fin m → Fin n) :
    projS m n w S * (oracleU m n w H : Matrix _ _ ℂ) =
      (oracleU m n w H : Matrix _ _ ℂ) * projS m n w S := by
  rw [oracleU_eq_permUnitary, projS_eq_diagonal]
  ext i j
  rw [diagonal_mul, mul_diagonal, permUnitary_apply]
  split_ifs with h
  · subst h
    obtain ⟨⟨⟨x, y⟩, z⟩, rfl⟩ := (oracleIndex m n w).surjective j
    rw [oraclePerm_apply]
    simp [xPart, oracleIndex]
  · simp

end Pad

end CatCrypt.Quantum.QROM.PRFAdvEmbed

end

end
