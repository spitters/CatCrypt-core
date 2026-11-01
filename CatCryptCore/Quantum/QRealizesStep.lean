/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QRealizesMem
public import CatCryptCore.Crypto.UCMonad.LocalOpFunctorial

/-!
# Realization from a bound on the steps

Two quantum reactive systems with the same state space and private register whose steps are
close realize each other behind the identity simulator, against environments with a private
quantum memory.

The distance between steps is the diamond distance `sidist p q` of two subinstruments
`p q : SubInstrument A B α` over arbitrary finite registers: the supremum, over reference
registers `Fin r`, inputs `ρ` on `A × Fin r` (positive semidefinite, trace at most `1`) and
families `ψ` of tests on the output (`QTest`), of the gap between the acceptances of `ψ` after
`p ⊗ id` and after `q ⊗ id`. A test is a functional on positive semidefinite matrices, countably
additive on summable families, positively homogeneous and bounded by the trace; the true branch
of any `QComp` distinguisher is one, so `sidist` bounds `qdistDiamond`
(`qdistDiamond_toQComp_le`).

The distance does not increase under sequencing on the right (`sidist_bind_right`), under
sequencing on the left (`sidist_bind_left`, the supremum of the distances of the
continuations), under framing (`sidist_frame`), relabelling (`sidist_relabel`) and placement of
an environment operation (`sidist_envPlace`). A hybrid over activations bounds the distance of
the joint runs: if `V t` bounds the distance of the steps at `t` plus `V` at every state the
ideal step reaches with a nonzero branch, then the runs from `t` are within `V t`
(`sidist_qloopQ_le`). `V` bounds the sum of the per-step distances along every run of the ideal
system.

## Main definitions

* `ReactiveUC.QTest` — a test on a finite register
* `ReactiveUC.accept p ψ ρ` — the acceptance of the tests `ψ` after `p` on `ρ`
* `ReactiveUC.sidist p q` — the diamond distance of two subinstruments

## Main results

* `ReactiveUC.qdistDiamond_toQComp_le` — `qdistDiamond` of the underlying instruments is at
  most the supremum of `sidist`
* `ReactiveUC.sidist_bind_left`, `ReactiveUC.sidist_bind_right`, `ReactiveUC.sidist_frame`,
  `ReactiveUC.sidist_relabel`, `ReactiveUC.sidist_envPlace`
* `ReactiveUC.sidist_qloopQ_le` — the hybrid over activations
* `ReactiveUC.QRealizesSimQ.of_potential` — realization at distance `V R.init`
* `ReactiveUC.QRealizesSimQ.of_oneShot` — systems whose steps differ only at states of a set
  `S` that the ideal system never enters, with steps within `ε` there, realize each other at
  distance `ε`
* `ReactiveUC.QRealizesSim.of_potential`, `ReactiveUC.QRealizesSim.of_oneShot` — the same
  bounds against memoryless environments
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum
open Matrix
open CatCrypt.Crypto.UCMonad.DiamondNorm
open CatCrypt.Quantum.TensorProduct
open UCMonad.QuantumUC
open scoped ENNReal NNReal ComplexOrder

/-! ## Linear maps and sums of matrices -/

section Linear

variable {X : Type} [Finite X]

/-- A linear map out of a space of matrices commutes with sums of summable families. -/
theorem linearMap_map_tsum {V : Type} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V] {ι : Type}
    (f : Matrix X X ℂ →ₗ[ℂ] V) {M : ι → Matrix X X ℂ} (hM : Summable M) :
    f (∑' i, M i) = ∑' i, f (M i) :=
  (LinearMap.toContinuousLinearMap f).map_tsum hM

/-- A linear map out of a space of matrices sends summable families to summable families. -/
theorem linearMap_summable {V : Type} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V] {ι : Type}
    (f : Matrix X X ℂ →ₗ[ℂ] V) {M : ι → Matrix X X ℂ} (hM : Summable M) :
    Summable fun i => f (M i) :=
  (LinearMap.toContinuousLinearMap f).summable hM

/-- The gap between two sums is at most the sum of the gaps. -/
theorem absDiff_tsum_le {ι : Type} (x y : ι → ℝ≥0∞) :
    absDiff (∑' i, x i) (∑' i, y i) ≤ ∑' i, absDiff (x i) (y i) := by
  have key : ∀ u v : ι → ℝ≥0∞, ∑' i, u i - ∑' i, v i ≤ ∑' i, absDiff (u i) (v i) := by
    intro u v
    rw [tsub_le_iff_right, ← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum fun i =>
      le_tsub_add.trans (add_le_add (le_sup_left : u i - v i ≤ absDiff (u i) (v i)) le_rfl)
  refine max_le (key x y) ((key y x).trans_eq (tsum_congr fun i => ?_))
  exact absDiff_comm _ _

/-- The gap scales with a finite factor. -/
theorem absDiff_mul_le (c a b : ℝ≥0∞) (hc : c ≠ ∞) :
    absDiff (c * a) (c * b) ≤ c * absDiff a b := by
  refine max_le ?_ ?_
  · rw [← ENNReal.mul_sub fun _ _ => hc]
    gcongr
    exact le_sup_left
  · rw [← ENNReal.mul_sub fun _ _ => hc]
    gcongr
    exact le_sup_right

end Linear

/-! ## Tests -/

/-- A **test** on the register `B`: a functional on positive semidefinite matrices with values
in `[0, ∞]`, countably additive on summable families, positively homogeneous and bounded by the
trace. -/
structure QTest (B : Type) [Fintype B] where
  /-- The value of the test on a matrix. -/
  toFun : Matrix B B ℂ → ℝ≥0∞
  /-- Countable additivity on summable families of positive semidefinite matrices. -/
  map_tsum : ∀ {ι : Type} (M : ι → Matrix B B ℂ), (∀ i, (M i).PosSemidef) → Summable M →
    toFun (∑' i, M i) = ∑' i, toFun (M i)
  /-- Positive homogeneity. -/
  map_smul : ∀ (t : ℝ≥0) (M : Matrix B B ℂ), M.PosSemidef →
    toFun (((t : ℝ) : ℂ) • M) = t * toFun M
  /-- The value on a positive semidefinite matrix is at most its trace. -/
  le_trace : ∀ M : Matrix B B ℂ, M.PosSemidef → toFun M ≤ ENNReal.ofReal M.trace.re

section Tests

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C] {α β : Type}

/-- A test vanishes on the zero matrix. -/
theorem QTest.map_zero (ψ : QTest B) : ψ.toFun 0 = 0 := by
  have h := ψ.map_smul 0 0 PosSemidef.zero
  simpa using h

/-- The **acceptance** of the tests `ψ` after the subinstrument `p` on the input `ρ`: the sum,
over the outcomes `a`, of the test `ψ a` on the branch of `p` at `a`. -/
def accept (p : SubInstrument A B α) (ψ : α → QTest B) (ρ : Matrix A A ℂ) : ℝ≥0∞ :=
  ∑' a, (ψ a).toFun (p.branch a ρ)

/-- On a positive semidefinite input, the traces of the branches of a subinstrument sum to at
most the trace of the input. -/
theorem tsum_ofReal_trace_le (p : SubInstrument A B α) {ρ : Matrix A A ℂ}
    (hρ : ρ.PosSemidef) :
    ∑' a, ENNReal.ofReal (p.branch a ρ).trace.re ≤ ENNReal.ofReal ρ.trace.re := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun a => p.trace_re_branch_apply_nonneg a hρ)
    (p.isCPTNIFamily.summable_trace_re_apply hρ)]
  exact ENNReal.ofReal_le_ofReal (p.tsum_trace_re_le hρ)

/-- The tests `ψ` after the subinstrument `p`, as a test on the input register. -/
def QTest.comp (p : SubInstrument A B α) (ψ : α → QTest B) : QTest A where
  toFun := accept p ψ
  map_tsum M hM hs := by
    simp only [accept]
    calc ∑' a, (ψ a).toFun (p.branch a (∑' i, M i))
        = ∑' a, ∑' i, (ψ a).toFun (p.branch a (M i)) := tsum_congr fun a => by
          rw [linearMap_map_tsum (p.branch a) hs]
          exact (ψ a).map_tsum _ (fun i => p.posSemidef_branch_apply a (hM i))
            (linearMap_summable (p.branch a) hs)
      _ = _ := ENNReal.tsum_comm
  map_smul t M hM := by
    simp only [accept]
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun a => by
      rw [LinearMap.map_smul, (ψ a).map_smul _ _ (p.posSemidef_branch_apply a hM)]
  le_trace M hM :=
    (ENNReal.tsum_le_tsum fun a => (ψ a).le_trace _ (p.posSemidef_branch_apply a hM)).trans
      (tsum_ofReal_trace_le p hM)

/-- The acceptance after a sequence is the acceptance after the first subinstrument of the
continuations followed by the tests. -/
theorem accept_bind (p : SubInstrument A B α) (k : α → SubInstrument B C β) (ψ : β → QTest C)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    accept (p.bind k) ψ ρ = accept p (fun a => QTest.comp (k a) ψ) ρ := by
  simp only [accept]
  calc ∑' c, (ψ c).toFun ((p.bind k).branch c ρ)
      = ∑' c, ∑' a, (ψ c).toFun ((k a).branch c (p.branch a ρ)) := tsum_congr fun c => by
        rw [SubInstrument.bind, DSubInstrument.branch_bind_apply]
        exact (ψ c).map_tsum _
          (fun a => (k a).posSemidef_branch_apply c (p.posSemidef_branch_apply a hρ))
          ((p.isCPTNIFamily.comp_eval (fun a => (k a).isCPTNIFamily) c).summable_apply _)
    _ = _ := ENNReal.tsum_comm

/-- The test `ψ` read through the relabelling `e` of basis states. -/
def QTest.reindex {X Y : Type} [Fintype X] [Fintype Y] (ψ : QTest Y) (e : X ≃ Y) : QTest X where
  toFun M := ψ.toFun (M.submatrix e.symm e.symm)
  map_tsum M hM hs := by
    have h := linearMap_map_tsum (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap hs
    simp only [LinearEquiv.coe_coe, Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply] at h
    rw [h]
    refine ψ.map_tsum _ (fun i => (hM i).submatrix _) ?_
    have hs' := linearMap_summable (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap hs
    simpa only [LinearEquiv.coe_coe, Matrix.coe_reindexLinearEquiv,
      Matrix.reindex_apply] using hs'
  map_smul t M hM := by
    rw [Matrix.submatrix_smul]
    exact ψ.map_smul _ _ (hM.submatrix _)
  le_trace M hM :=
    (ψ.le_trace _ (hM.submatrix _)).trans_eq (by rw [trace_submatrix_equiv])

end Tests

/-! ## The diamond distance of two subinstruments -/

section Dist

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C] {α β : Type}

/-- The **diamond distance** of two subinstruments over finite registers: the supremum, over
reference registers `Fin r`, positive semidefinite inputs `ρ` on `A × Fin r` of trace at most
`1` and tests `ψ` on `B × Fin r`, of the gap between the acceptances after `p ⊗ id` and after
`q ⊗ id`. -/
def sidist (p q : SubInstrument A B α) : ℝ≥0∞ :=
  ⨆ (r : ℕ) (ρ : Matrix (A × Fin r) (A × Fin r) ℂ) (_ : ρ.PosSemidef) (_ : ρ.trace.re ≤ 1)
    (ψ : α → QTest (B × Fin r)),
    absDiff (accept (p.frame (Fin r)) ψ ρ) (accept (q.frame (Fin r)) ψ ρ)

/-- Each gap is at most the diamond distance. -/
theorem le_sidist (p q : SubInstrument A B α) (r : ℕ) {ρ : Matrix (A × Fin r) (A × Fin r) ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1) (ψ : α → QTest (B × Fin r)) :
    absDiff (accept (p.frame (Fin r)) ψ ρ) (accept (q.frame (Fin r)) ψ ρ) ≤ sidist p q :=
  le_iSup_of_le r <| le_iSup_of_le ρ <| le_iSup_of_le hρ <| le_iSup_of_le htr <|
    le_iSup_of_le ψ le_rfl

/-- The distance of a subinstrument to itself is `0`. -/
theorem sidist_self (p : SubInstrument A B α) : sidist p p = 0 := by
  simp [sidist, absDiff_self]

/-- Triangle inequality. -/
theorem sidist_triangle (p q s : SubInstrument A B α) :
    sidist p s ≤ sidist p q + sidist q s := by
  refine iSup_le fun r => iSup_le fun ρ => iSup_le fun hρ => iSup_le fun htr =>
    iSup_le fun ψ => ?_
  exact (absDiff_triangle _ _ _).trans
    (add_le_add (le_sidist p q r hρ htr ψ) (le_sidist q s r hρ htr ψ))

/-- On a positive semidefinite input of any trace, the gap is at most the trace times the
diamond distance. -/
theorem absDiff_accept_le_trace_mul (p q : SubInstrument A B α) (r : ℕ)
    {σ : Matrix (A × Fin r) (A × Fin r) ℂ} (hσ : σ.PosSemidef) (ψ : α → QTest (B × Fin r)) :
    absDiff (accept (p.frame (Fin r)) ψ σ) (accept (q.frame (Fin r)) ψ σ) ≤
      ENNReal.ofReal σ.trace.re * sidist p q := by
  have ht : 0 ≤ σ.trace.re := hσ.trace_re_nonneg
  rcases ht.eq_or_lt with h0 | hpos
  · have hσ0 : σ = 0 := hσ.trace_eq_zero_iff.mp
      (Complex.ext (by simpa using h0.symm) (trace_im_zero_of_psd hσ))
    subst hσ0
    simp only [accept, map_zero, QTest.map_zero, tsum_zero, absDiff_self]
    exact bot_le
  · set t := σ.trace.re
    set σ' : Matrix (A × Fin r) (A × Fin r) ℂ := ((t⁻¹ : ℝ) : ℂ) • σ
    have hσ' : σ'.PosSemidef :=
      hσ.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr ht))
    have htr' : σ'.trace.re ≤ 1 := by
      simp only [σ', Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      rw [inv_mul_cancel₀ hpos.ne']
    have hσeq : σ = (((t.toNNReal : ℝ≥0) : ℝ) : ℂ) • σ' := by
      simp only [σ', smul_smul, Real.coe_toNNReal _ ht, ← Complex.ofReal_mul,
        mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, one_smul]
    have hacc : ∀ P : SubInstrument A B α, accept (P.frame (Fin r)) ψ σ =
        (t.toNNReal : ℝ≥0∞) * accept (P.frame (Fin r)) ψ σ' := fun P => by
      rw [hσeq]
      exact (QTest.comp (P.frame (Fin r)) ψ).map_smul _ _ hσ'
    rw [hacc p, hacc q]
    exact (absDiff_mul_le _ _ _ ENNReal.coe_ne_top).trans
      (by gcongr <;> first | exact le_rfl | exact le_sidist p q r hσ' htr' ψ)

/-- **Sequencing on the right.** A common continuation does not increase the distance. -/
theorem sidist_bind_right (p q : SubInstrument A B α) (k : α → SubInstrument B C β) :
    sidist (p.bind k) (q.bind k) ≤ sidist p q := by
  refine iSup_le fun r => iSup_le fun ρ => iSup_le fun hρ => iSup_le fun htr =>
    iSup_le fun ψ => ?_
  rw [SubInstrument.frame_bind, SubInstrument.frame_bind, accept_bind _ _ _ hρ,
    accept_bind _ _ _ hρ]
  exact le_sidist p q r hρ htr _

/-- **Sequencing on the left.** After a common first subinstrument, the distance is at most the
supremum of the distances of the continuations. -/
theorem sidist_bind_left (s : SubInstrument A B β) (k₁ k₂ : β → SubInstrument B C α) :
    sidist (s.bind k₁) (s.bind k₂) ≤ ⨆ b, sidist (k₁ b) (k₂ b) := by
  refine iSup_le fun r => iSup_le fun ρ => iSup_le fun hρ => iSup_le fun htr =>
    iSup_le fun ψ => ?_
  rw [SubInstrument.frame_bind, SubInstrument.frame_bind, accept_bind _ _ _ hρ,
    accept_bind _ _ _ hρ]
  refine (absDiff_tsum_le _ _).trans ?_
  calc ∑' b, absDiff (accept ((k₁ b).frame (Fin r)) ψ ((s.frame (Fin r)).branch b ρ))
          (accept ((k₂ b).frame (Fin r)) ψ ((s.frame (Fin r)).branch b ρ))
      ≤ ∑' b, ENNReal.ofReal ((s.frame (Fin r)).branch b ρ).trace.re *
          ⨆ b, sidist (k₁ b) (k₂ b) :=
        ENNReal.tsum_le_tsum fun b =>
          (absDiff_accept_le_trace_mul (k₁ b) (k₂ b) r
            ((s.frame (Fin r)).posSemidef_branch_apply b hρ) ψ).trans
            (by gcongr; exact le_iSup (fun b => sidist (k₁ b) (k₂ b)) b)
    _ = (∑' b, ENNReal.ofReal ((s.frame (Fin r)).branch b ρ).trace.re) *
          ⨆ b, sidist (k₁ b) (k₂ b) := ENNReal.tsum_mul_right
    _ ≤ 1 * ⨆ b, sidist (k₁ b) (k₂ b) := by
        gcongr
        exact (tsum_ofReal_trace_le _ hρ).trans (ENNReal.ofReal_le_one.mpr htr)
    _ = _ := one_mul _

/-- Sequences that agree on the outcomes where the first subinstrument has a nonzero branch are
equal. -/
theorem bind_congr_of_branch {p : SubInstrument A B α} {k₁ k₂ : α → SubInstrument B C β}
    (h : ∀ a, p.branch a ≠ 0 → k₁ a = k₂ a) : p.bind k₁ = p.bind k₂ := by
  refine DSubInstrument.ext <| funext fun c => LinearMap.ext fun ρ => ?_
  rw [SubInstrument.bind, SubInstrument.bind, DSubInstrument.branch_bind_apply,
    DSubInstrument.branch_bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : p.branch a = 0
  · simp [ha]
  · rw [h a ha]

/-- **Sequencing on the left, on the support.** After a common first subinstrument, the distance
is at most the supremum of the distances of the continuations at the outcomes with a nonzero
branch. -/
theorem sidist_bind_left_of_support (s : SubInstrument A B β)
    (k₁ k₂ : β → SubInstrument B C α) :
    sidist (s.bind k₁) (s.bind k₂) ≤ ⨆ (b : β) (_ : s.branch b ≠ 0), sidist (k₁ b) (k₂ b) := by
  classical
  have h : s.bind k₂ = s.bind fun b => if s.branch b ≠ 0 then k₂ b else k₁ b :=
    bind_congr_of_branch fun b hb => by simp only [ne_eq, hb, not_false_eq_true, ite_true]
  rw [h]
  refine (sidist_bind_left s k₁ _).trans (iSup_le fun b => ?_)
  by_cases hb : s.branch b ≠ 0
  · simp only [ne_eq, hb, not_false_eq_true, ite_true]
    exact le_iSup₂_of_le b hb le_rfl
  · simp only [hb, ite_false, sidist_self]
    exact bot_le

/-- The equivalence `(X × K) × R ≃ X × S` given by `e : K × R ≃ S`. -/
def assocEquiv (X : Type) {K R S : Type} (e : K × R ≃ S) : (X × K) × R ≃ X × S :=
  (Equiv.prodAssoc X K R).trans ((Equiv.refl X).prodCongr e)

/-- Framing by `K` and then by `R` is framing by `S`, read through `e : K × R ≃ S`. -/
theorem frame_frame_branch {K R S : Type} [Fintype K] [Fintype R] [Fintype S]
    (p : SubInstrument A B α) (e : K × R ≃ S) (a : α) (ρ : Matrix ((A × K) × R) ((A × K) × R) ℂ) :
    ((p.frame K).frame R).branch a ρ =
      ((p.frame S).branch a (ρ.submatrix (assocEquiv A e).symm (assocEquiv A e).symm)).submatrix
        (assocEquiv B e) (assocEquiv B e) := by
  ext x y
  have hM : (ρ.submatrix (assocEquiv A e).symm (assocEquiv A e).symm).submatrix
      (·, e (x.1.2, x.2)) (·, e (y.1.2, y.2)) =
      (ρ.submatrix (·, x.2) (·, y.2)).submatrix (·, x.1.2) (·, y.1.2) := by
    ext u v
    simp [assocEquiv]
  simp only [DSubInstrument.branch_frame_apply, MatrixMap.amplify_apply, Matrix.submatrix_apply,
    assocEquiv, Equiv.trans_apply, Equiv.prodAssoc_apply, Equiv.prodCongr_apply, Prod.map,
    Equiv.refl_apply]
  exact congrArg (fun M => p.branch a M x.1.1 y.1.1) hM.symm

/-- **Framing.** Framing both subinstruments by a register does not increase the distance. -/
theorem sidist_frame (p q : SubInstrument A B α) (K : Type) [Fintype K] :
    sidist (p.frame K) (q.frame K) ≤ sidist p q := by
  refine iSup_le fun r => iSup_le fun ρ => iSup_le fun hρ => iSup_le fun htr =>
    iSup_le fun ψ => ?_
  let e : K × Fin r ≃ Fin (Fintype.card K * r) :=
    ((Fintype.equivFin K).prodCongr (Equiv.refl _)).trans finProdFinEquiv
  have h : ∀ P : SubInstrument A B α, accept ((P.frame K).frame (Fin r)) ψ ρ =
      accept (P.frame (Fin (Fintype.card K * r))) (fun a => (ψ a).reindex (assocEquiv B e).symm)
        (ρ.submatrix (assocEquiv A e).symm (assocEquiv A e).symm) := fun P =>
    tsum_congr fun a => by rw [frame_frame_branch P e]; rfl
  rw [h p, h q]
  refine le_sidist p q _ (hρ.submatrix _) ?_ _
  rwa [trace_submatrix_equiv]

/-- **Relabelling.** Relabelling the basis states of both subinstruments does not increase the
distance. -/
theorem sidist_relabel {X Y : Type} [Fintype X] [Fintype Y] (e : X ≃ Y)
    (p q : SubInstrument X X α) : sidist (relabel e p) (relabel e q) ≤ sidist p q := by
  refine iSup_le fun r => iSup_le fun ρ => iSup_le fun hρ => iSup_le fun htr =>
    iSup_le fun ψ => ?_
  rw [frame_relabel, frame_relabel]
  have h : ∀ P : SubInstrument X X α,
      accept (relabel (e.prodCongr (Equiv.refl (Fin r))) (P.frame (Fin r))) ψ ρ =
        accept (P.frame (Fin r)) (fun a => (ψ a).reindex (e.prodCongr (Equiv.refl (Fin r))))
          (ρ.submatrix (e.prodCongr (Equiv.refl (Fin r))) (e.prodCongr (Equiv.refl (Fin r)))) :=
    fun P => rfl
  rw [h p, h q]
  refine le_sidist p q r (hρ.submatrix _) ?_ _
  have := trace_submatrix_equiv (e.prodCongr (Equiv.refl (Fin r))).symm ρ
  rw [Equiv.symm_symm] at this
  rwa [this]

/-- **Environment operations.** Placing two environment operations on the joint register does
not increase their distance. -/
theorem sidist_envPlace {K : Type} [Fintype K] {d : ℕ} (H : Type) [Fintype H]
    (w₁ w₂ : SubInstrument (Fin d × K) (Fin d × K) α) :
    sidist (envPlace H w₁) (envPlace H w₂) ≤ sidist w₁ w₂ :=
  (sidist_relabel _ _ _).trans (sidist_frame _ _ H)

end Dist

/-! ## Comparison with the diamond distance of `QComp` -/

section Bridge

variable {d : ℕ} {β : Type}

/-- The true branch of the distinguisher `D`, read through `e : X ≃ Fin n`, as a test. -/
def QTest.ofQComp {n : ℕ} {X : Type} [Fintype X] (D : QComp n Bool) (e : X ≃ Fin n) :
    QTest X where
  toFun M := ENNReal.ofReal (D.branch true (M.submatrix e.symm e.symm)).trace.re
  map_tsum M hM hs := by
    let f : Matrix X X ℂ →ₗ[ℂ] ℂ := (Matrix.traceLinearMap (Fin n) ℂ ℂ).comp
      ((D.branch true).comp (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap)
    have hf : ∀ M, f M = (D.branch true (M.submatrix e.symm e.symm)).trace := fun M => rfl
    have hsum := linearMap_summable f hs
    have hre := Complex.reCLM.map_tsum hsum
    simp only [Complex.reCLM_apply] at hre
    simp only [← hf]
    rw [linearMap_map_tsum f hs, hre]
    refine ENNReal.ofReal_tsum_of_nonneg (fun i => ?_) (Complex.reCLM.summable hsum)
    rw [hf]
    exact (D.branch_psd true _ ((hM i).submatrix _)).trace_re_nonneg
  map_smul t M hM := by
    have hs : ((((t : ℝ) : ℂ)) • M).submatrix e.symm e.symm =
        ((t : ℝ) : ℂ) • M.submatrix e.symm e.symm := by
      ext u v
      simp
    rw [hs, LinearMap.map_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
      ENNReal.ofReal_mul (NNReal.coe_nonneg t), ENNReal.ofReal_coe_nnreal]
  le_trace M hM := by
    refine ENNReal.ofReal_le_ofReal ?_
    have hM' := hM.submatrix e.symm
    have h := D.branch_stp _ hM'
    rw [tsum_fintype, Fintype.sum_bool, Complex.add_re] at h
    have hf := (D.branch_psd false _ hM').trace_re_nonneg
    rw [← trace_submatrix_equiv e M]
    linarith

/-- The reference extension of `C.toQComp` applies the framed branch of `C`, read through
`finProdEquiv`. -/
theorem localOp₁_toQComp_branch {r : ℕ} (C : CPComp d β) (c : β)
    (M : Matrix (Fin (d * r)) (Fin (d * r)) ℂ) :
    (localOp₁ (d₂ := r) C.toQComp C.branch_cp).branch c M =
      ((C.frame (Fin r)).branch c (M.submatrix (finProdEquiv d r) (finProdEquiv d r))).submatrix
        (finProdEquiv d r).symm (finProdEquiv d r).symm := by
  ext i j
  rw [localOp₁_branch_entry]
  simp only [Matrix.submatrix_apply, DSubInstrument.branch_frame_apply, MatrixMap.amplify_apply,
    CPComp.toQComp_branch]
  rfl

/-- The acceptance probability of `D` after the reference extension of `C.toQComp` is the
acceptance of the tests `QTest.ofQComp (D c)` after `C ⊗ id`. -/
theorem prTrue_Q_localOp₁_eq_accept {r : ℕ} (C : CPComp d β) (D : β → QComp (d * r) Bool)
    (ρ : DensityMatrix (d * r)) :
    prTrue_Q (QComp.qbind (localOp₁ (d₂ := r) C.toQComp C.branch_cp) D) ρ =
      accept (C.frame (Fin r)) (fun c => QTest.ofQComp (D c) (finProdEquiv d r))
        (ρ.val.submatrix (finProdEquiv d r) (finProdEquiv d r)) := by
  set L := localOp₁ (d₂ := r) C.toQComp C.branch_cp
  have hsum : Summable fun c => (D c).branch true (L.branch c ρ.val) :=
    QComp.bind_summable L D true ρ.val
  have heq : prTrue_Q (QComp.qbind L D) ρ =
      ENNReal.ofReal (∑' c, ((D c).branch true (L.branch c ρ.val)).trace.re) := by
    rw [prTrue_Q, qbind_branch_apply, trace_tsum hsum, Complex.re_tsum (trace_summable hsum)]
  rw [heq, ENNReal.ofReal_tsum_of_nonneg (fun c => ?_) (trace_re_summable hsum)]
  · refine tsum_congr fun c => ?_
    simp only [QTest.ofQComp, L, localOp₁_toQComp_branch]
  · exact ((D c).branch_psd true _ (L.branch_psd c _ ρ.psd)).trace_re_nonneg

/-- **Comparison.** The diamond distance of the underlying instruments of two families of
completely positive instruments is at most the supremum of their `sidist`. -/
theorem qdistDiamond_toQComp_le {ι : Type} (p q : ι → CPComp d β) :
    qdistDiamond (fun i => (p i).toQComp) (fun i => (q i).toQComp)
        (fun i => CPComp.branch_cp (p i)) (fun i => CPComp.branch_cp (q i)) ≤
      ⨆ i, sidist (p i) (q i) := by
  refine iSup_le fun r => iSup_le fun D => iSup_le fun i => iSup_le fun ρ => ?_
  refine le_iSup_of_le i ?_
  change absDiff (prTrue_Q (QComp.qbind (localOp₁ (d₂ := r) (p i).toQComp
      (CPComp.branch_cp (p i))) D) ρ) (prTrue_Q (QComp.qbind (localOp₁ (d₂ := r)
      (q i).toQComp (CPComp.branch_cp (q i))) D) ρ) ≤ _
  rw [prTrue_Q_localOp₁_eq_accept, prTrue_Q_localOp₁_eq_accept]
  refine le_sidist _ _ r (ρ.psd.submatrix _) ?_ _
  have := trace_submatrix_equiv (finProdEquiv d r).symm ρ.val
  rw [Equiv.symm_symm] at this
  rw [this, ρ.tr_one, Complex.one_re]

end Bridge

/-! ## The hybrid over activations -/

section Hybrid

variable {H K : Type} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
variable {τ ζ E O : Type} {d : ℕ}

omit [DecidableEq H] [DecidableEq K] in
/-- **Hybrid over activations.** Let `V t` bound the distance of the steps of `R` and `I` at the
state `t` plus `V` at every state that a step of `I` at `t` reaches with a nonzero branch. Then
the joint runs of an environment with `R` and with `I` from the state `t` are within `V t`. -/
theorem sidist_qloopQ_le (R I : QSys H τ E O d) (Z : QStratQ K ζ E O d) (V : τ → ℝ≥0∞)
    (hV : ∀ t e, sidist (R.step t e) (I.step t e) +
      ⨆ (p : τ × O) (_ : (I.step t e).branch p ≠ 0), V p.1 ≤ V t) :
    ∀ (n : ℕ) (c : ζ × τ), sidist (qloopQ R Z n c) (qloopQ I Z n c) ≤ V c.2 := by
  intro n
  induction n with
  | zero =>
    intro c
    simp only [qloopQ, sidist_self]
    exact bot_le
  | succ n ih =>
    intro c
    simp only [qloopQ]
    refine (sidist_bind_left _ _ _).trans (iSup_le fun a => ?_)
    refine (sidist_triangle _ (((I.step c.2 a.2).frame K).bind fun p =>
      (envPlace H (Z.obs a.1 p.2)).bind fun z => qloopQ R Z n (z, p.1)) _).trans ?_
    refine le_trans (add_le_add ((sidist_bind_right _ _ _).trans (sidist_frame _ _ K)) ?_)
      (hV c.2 a.2)
    refine (sidist_bind_left_of_support _ _ _).trans (iSup₂_le fun p hp => ?_)
    have hp' : (I.step c.2 a.2).branch p ≠ 0 := fun h0 =>
      hp (by rw [DSubInstrument.branch_frame_apply, h0, MatrixMap.amplify_zero])
    refine le_iSup₂_of_le p hp' ?_
    exact (sidist_bind_left _ _ _).trans (iSup_le fun z => ih (z, p.1))

/-- The views of an environment against `R` and against `I` are within `V R.init`, under the
hypothesis of `sidist_qloopQ_le`, when the two systems start in the same state and the same
basis state of the private register. -/
theorem sidist_qviewQ_le (R I : QSys H τ E O d) (Z : QStratQ K ζ E O d) (V : τ → ℝ≥0∞)
    (hinit : R.init = I.init) (hreg : R.initReg = I.initReg)
    (hV : ∀ t e, sidist (R.step t e) (I.step t e) +
      ⨆ (p : τ × O) (_ : (I.step t e).branch p ≠ 0), V p.1 ≤ V t) :
    sidist (qviewQ R Z) (qviewQ I Z) ≤ V R.init := by
  simp only [qviewQ, ← hinit, ← hreg]
  refine (sidist_bind_left _ _ _).trans (iSup_le fun _ => ?_)
  refine (sidist_bind_left _ _ _).trans (iSup_le fun _ => ?_)
  exact (sidist_bind_right _ _ _).trans (sidist_qloopQ_le R I Z V hV _ _)

/-- **Realization from a potential.** Under the hypothesis of `sidist_qloopQ_le`, `R` realizes
`I` behind the identity simulator at distance `V R.init`, against environments with a private
quantum memory. -/
theorem QRealizesSimQ.of_potential (R I : QSys H τ E O d) (V : τ → ℝ≥0∞)
    (hinit : R.init = I.init) (hreg : R.initReg = I.initReg)
    (hV : ∀ t e, sidist (R.step t e) (I.step t e) +
      ⨆ (p : τ × O) (_ : (I.step t e).branch p ≠ 0), V p.1 ≤ V t) :
    QRealizesSimQ R I QSimQ.id (V R.init) := by
  intro K' _ _ ζ'
  exact quc_congr _ _ ((qdistDiamond_toQComp_le _ _).trans
    (iSup_le fun Z => sidist_qviewQ_le R I Z V hinit hreg hV)) rfl
    (funext fun Z => by rw [simViewQ_id])

/-- **One-shot realization.** Let the steps of `R` and `I` agree outside a set `S` of states,
let no step of `I` reach a state of `S` with a nonzero branch, and let the steps at states of
`S` be within `ε`. Then `R` realizes `I` behind the identity simulator at distance `ε`, against
environments with a private quantum memory. -/
theorem QRealizesSimQ.of_oneShot (R I : QSys H τ E O d) (S : Set τ) (ε : ℝ≥0∞)
    (hinit : R.init = I.init) (hreg : R.initReg = I.initReg)
    (hagree : ∀ t, t ∉ S → ∀ e, R.step t e = I.step t e)
    (hout : ∀ t e (p : τ × O), p.1 ∈ S → (I.step t e).branch p = 0)
    (hε : ∀ t, t ∈ S → ∀ e, sidist (R.step t e) (I.step t e) ≤ ε) :
    QRealizesSimQ R I QSimQ.id ε := by
  classical
  have hV : ∀ t e, sidist (R.step t e) (I.step t e) +
      ⨆ (p : τ × O) (_ : (I.step t e).branch p ≠ 0), S.indicator (fun _ => ε) p.1 ≤
        S.indicator (fun _ => ε) t := by
    intro t e
    have hsup : (⨆ (p : τ × O) (_ : (I.step t e).branch p ≠ 0),
        S.indicator (fun _ => ε) p.1) = 0 :=
      le_antisymm (iSup₂_le fun p hp => by
        rw [Set.indicator_of_notMem fun hS => hp (hout t e p hS)]) bot_le
    rw [hsup, add_zero]
    by_cases ht : t ∈ S
    · rw [Set.indicator_of_mem ht]
      exact hε t ht e
    · rw [hagree t ht e, sidist_self]
      exact bot_le
  have hle : S.indicator (fun _ => ε) R.init ≤ ε := by
    by_cases ht : R.init ∈ S
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht]
      exact bot_le
  exact fun K' _ _ ζ' =>
    (QRealizesSimQ.of_potential R I _ hinit hreg hV K' ζ').mono hle

/-- Realization behind the identity simulator against environments with memory gives
realization behind the identity simulator against memoryless environments. -/
theorem QRealizesSim.of_QRealizesSimQ_id {R I : QSys H τ E O d} {ε : ℝ≥0∞}
    (h : QRealizesSimQ R I QSimQ.id ε) : QRealizesSim R I QSim.id ε := fun ζ' =>
  quc_congr _ _ (quc_precomp (h Unit ζ') QStrat.toQ) (funext fun Z => by rw [qviewQ_toQ])
    (funext fun Z => by rw [simViewQ_id, qviewQ_toQ, simView_id])

/-- **Realization from a potential**, against memoryless environments. -/
theorem QRealizesSim.of_potential (R I : QSys H τ E O d) (V : τ → ℝ≥0∞)
    (hinit : R.init = I.init) (hreg : R.initReg = I.initReg)
    (hV : ∀ t e, sidist (R.step t e) (I.step t e) +
      ⨆ (p : τ × O) (_ : (I.step t e).branch p ≠ 0), V p.1 ≤ V t) :
    QRealizesSim R I QSim.id (V R.init) :=
  QRealizesSim.of_QRealizesSimQ_id (QRealizesSimQ.of_potential R I V hinit hreg hV)

/-- **One-shot realization**, against memoryless environments. -/
theorem QRealizesSim.of_oneShot (R I : QSys H τ E O d) (S : Set τ) (ε : ℝ≥0∞)
    (hinit : R.init = I.init) (hreg : R.initReg = I.initReg)
    (hagree : ∀ t, t ∉ S → ∀ e, R.step t e = I.step t e)
    (hout : ∀ t e (p : τ × O), p.1 ∈ S → (I.step t e).branch p = 0)
    (hε : ∀ t, t ∈ S → ∀ e, sidist (R.step t e) (I.step t e) ≤ ε) :
    QRealizesSim R I QSim.id ε :=
  QRealizesSim.of_QRealizesSimQ_id
    (QRealizesSimQ.of_oneShot R I S ε hinit hreg hagree hout hε)

end Hybrid

end CatCrypt.Quantum.ReactiveUC
