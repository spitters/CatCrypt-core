/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QRealizesInvariant
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Independence of a classical component of a system's state

A classical law `μ` on a finite type `W` with total mass `1` is a subinstrument on every register
(`sampleLaw μ`): its branch at `w` scales the input by `μ w`. Sampling commutes with every
subinstrument that does not depend on the sample (`sampleLaw_bind_comm`), with framing
(`sampleLaw_frame`), and discarding the sample gives the identity (`sampleLaw_bind_const`).

**Non-interference.** A system `S` whose classical state is a pair `(v, w)` is *write-only in `w`*
over a system `I` with state `v`, with conditional law `μ v` of `w` given `v`, when the step of
`S` at `(v, w)`, averaged over `w` drawn from `μ v`, is the step of `I` at `v` followed by a
fresh draw of the new `w` from `μ` at the new `v` (`QSys.WriteOnly`). This is the separating
conjunction of probabilistic separation logic for the classical component `w`: the state splits
as the law of `w` given `v`, times a part that does not depend on `w`. A step that ignores `w`
and draws the new `w` afresh is write-only (`QSys.writeOnly_of_fresh`). Under the write-only
hypothesis, the joint run of an environment with `S` from `(v, w)`, with `w` drawn from `μ v`,
is the run with `I` from `v` followed by a draw of `w` from `μ` at the final `v`
(`run_factor_of_writeOnly`): at every activation, the branch of the run at `(v, w)` is the law
of `w` given `v` times the branch at `v`.

**Substitution at a conditionally sparse set.** Let two families of subinstruments `p w` and
`q w` agree on the inputs compressed by the projector onto the basis states outside a set
`T w`, and let every basis state lie in `T w` with probability at most `δ` when `w` is drawn
from `μ`. Then the two subinstruments that draw `w` from `μ` and run `p w`, respectively `q w`,
are within `2 √δ` in diamond distance (`subst_sparse_le`). The proof applies gentle
substitution (`gentle_subst_le`) at each `w` and Jensen's inequality for the square root.

## Main definitions

* `ReactiveUC.sampleLaw` — a classical law as a subinstrument
* `ReactiveUC.QSys.WriteOnly` — a system write-only in a component of its state
* `ReactiveUC.projOff` — the diagonal projector onto the basis states outside a set

## Main results

* `ReactiveUC.run_factor_of_writeOnly` — the run factors as the law of the component times
  the run of the system without it
* `ReactiveUC.subst_sparse_le` — substitution at a conditionally sparse set

## References

* [Barbosa, Barthe, Doczkal, Don, Fehr, Grégoire, Huang, Hülsing, Lee, Wu — Fixing and
  Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium, CRYPTO 2023, ePrint
  2023/246], Proposition 1 and Lemma 5
* [Barthe, Hsu, Liao — A probabilistic separation logic, POPL 2020]
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum
open Matrix
open CatCrypt.Crypto.UCMonad.DiamondNorm
open UCMonad.QuantumUC
open scoped ENNReal NNReal ComplexOrder

/-! ## Classical laws as subinstruments -/

section Sample

variable {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C]
variable {W β γ : Type} [Fintype W]

/-- The Kraus operators `√(μ w) • 1` of a law `μ` of total mass `1` are complete. -/
theorem sampleLaw_complete (μ : W → ℝ≥0) (hμ : ∑ w, μ w = 1) :
    ∑ w, ((((NNReal.sqrt (μ w) : ℝ) : ℂ)) • (1 : Matrix A A ℂ))ᴴ *
      ((((NNReal.sqrt (μ w) : ℝ) : ℂ)) • (1 : Matrix A A ℂ)) = 1 := by
  simp only [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal,
    smul_mul_smul_comm, mul_one, ← Finset.sum_smul, ← Complex.ofReal_mul, ← NNReal.coe_mul,
    NNReal.mul_self_sqrt, ← Complex.ofReal_sum, ← NNReal.coe_sum, hμ, NNReal.coe_one,
    Complex.ofReal_one, one_smul]

/-- The classical law `μ` of total mass `1` on the finite type `W` as a subinstrument on the
register `A`: the branch at `w` scales the input by `μ w`. -/
def sampleLaw (μ : W → ℝ≥0) (hμ : ∑ w, μ w = 1) : SubInstrument A A W :=
  SubInstrument.ofKraus (fun w => (((NNReal.sqrt (μ w) : ℝ) : ℂ)) • (1 : Matrix A A ℂ))
    (sampleLaw_complete μ hμ)

/-- The branch of `sampleLaw μ` at `w` scales the input by `μ w`. -/
theorem sampleLaw_branch (μ : W → ℝ≥0) (hμ : ∑ w, μ w = 1) (w : W) (ρ : Matrix A A ℂ) :
    (sampleLaw μ hμ : SubInstrument A A W).branch w ρ = (((μ w : ℝ) : ℂ)) • ρ := by
  simp only [sampleLaw, DSubInstrument.branch_ofKraus_apply, MatrixMap.conj_apply,
    conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal,
    smul_mul_smul_comm, Matrix.smul_mul, one_mul, mul_one, ← Complex.ofReal_mul,
    ← NNReal.coe_mul, NNReal.mul_self_sqrt]

/-- Framing a classical law gives the classical law on the framed register. -/
theorem sampleLaw_frame (μ : W → ℝ≥0) (hμ : ∑ w, μ w = 1) (R : Type) [Fintype R]
    [DecidableEq R] :
    (sampleLaw μ hμ : SubInstrument A A W).frame R = sampleLaw μ hμ := by
  refine DSubInstrument.ext <| funext fun w => LinearMap.ext fun ρ => ?_
  ext x y
  simp [DSubInstrument.branch_frame_apply, MatrixMap.amplify_apply, sampleLaw_branch]

omit [DecidableEq B] in
/-- Drawing a sample and discarding it is the identity. -/
theorem sampleLaw_bind_const (μ : W → ℝ≥0) (hμ : ∑ w, μ w = 1) (p : SubInstrument A B β) :
    (sampleLaw μ hμ).bind (fun _ => p) = p := by
  refine DSubInstrument.ext <| funext fun c => LinearMap.ext fun ρ => ?_
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply, tsum_fintype]
  simp only [sampleLaw_branch, map_smul, ← Finset.sum_smul, ← Complex.ofReal_sum,
    ← NNReal.coe_sum, hμ, NNReal.coe_one, Complex.ofReal_one, one_smul]

/-- **Sampling commutes** with a subinstrument that does not depend on the sample. -/
theorem sampleLaw_bind_comm (μ : W → ℝ≥0) (hμ : ∑ w, μ w = 1) (p : SubInstrument A B β)
    (k : W → β → SubInstrument B C γ) :
    (sampleLaw μ hμ).bind (fun w => p.bind (k w)) =
      p.bind fun b => (sampleLaw μ hμ).bind fun w => k w b := by
  refine DSubInstrument.ext <| funext fun c => LinearMap.ext fun ρ => ?_
  simp only [SubInstrument.bind, DSubInstrument.branch_bind_apply, tsum_fintype,
    sampleLaw_branch, map_smul]
  have hs : ∀ w, Summable fun b => (k w b).branch c (p.branch b ρ) := fun w =>
    (p.isCPTNIFamily.comp_eval (fun b => (k w b).isCPTNIFamily) c).summable_apply ρ
  rw [Summable.tsum_finsetSum fun w _ => (hs w).const_smul (((μ w : ℝ) : ℂ))]
  exact Finset.sum_congr rfl fun w _ => ((hs w).tsum_const_smul _).symm

/-- The acceptance after a classical law is the average of the acceptances under the law. -/
theorem accept_sampleLaw (μ : W → ℝ≥0) (hμ : ∑ w, μ w = 1) (φ : W → QTest A)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    accept (sampleLaw μ hμ) φ ρ = ∑ w, (μ w : ℝ≥0∞) * (φ w).toFun ρ := by
  simp only [accept, sampleLaw_branch, tsum_fintype]
  exact Finset.sum_congr rfl fun w _ => (φ w).map_smul (μ w) ρ hρ

end Sample

/-! ## Non-interference -/

section NonInterference

variable {H K : Type} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
variable {V W ζ E O : Type} [Fintype W] {d : ℕ}

/-- The system `S` with state `(v, w)` is **write-only in `w`** over the system `I` with state
`v`, with conditional law `μ v` of `w` given `v`: the step of `S` at `(v, w)`, with `w` drawn
from `μ v`, is the step of `I` at `v` followed by a draw of the new `w` from `μ` at the new
`v`. -/
def QSys.WriteOnly (S : QSys H (V × W) E O d) (I : QSys H V E O d) (μ : V → W → ℝ≥0)
    (hμ : ∀ v, ∑ w, μ v w = 1) : Prop :=
  ∀ v e, (sampleLaw (μ v) (hμ v)).bind (fun w => S.step (v, w) e) =
    (I.step v e).bind fun p =>
      (sampleLaw (μ p.1) (hμ p.1)).bind fun w => SubInstrument.pure ((p.1, w), p.2)

/-- A system whose step at `(v, w)` ignores `w`, runs `I` at `v` and draws the new `w` from `μ`
at the new `v` is write-only in `w`. -/
theorem QSys.writeOnly_of_fresh (S : QSys H (V × W) E O d) (I : QSys H V E O d)
    (μ : V → W → ℝ≥0) (hμ : ∀ v, ∑ w, μ v w = 1)
    (hS : ∀ v w e, S.step (v, w) e = (I.step v e).bind fun p =>
      (sampleLaw (μ p.1) (hμ p.1)).bind fun w' => SubInstrument.pure ((p.1, w'), p.2)) :
    S.WriteOnly I μ hμ := by
  intro v e
  simp only [hS]
  exact sampleLaw_bind_const _ _ _

/-- **Non-interference.** If `S` is write-only in `w` over `I` with conditional law `μ`, the
joint run of an environment with `S` from `(v, w)`, with `w` drawn from `μ v`, is the joint run
with `I` from `v` followed by a draw of `w` from `μ` at the final state of `I`. -/
theorem run_factor_of_writeOnly (S : QSys H (V × W) E O d) (I : QSys H V E O d)
    (Z : QStratQ K ζ E O d) (μ : V → W → ℝ≥0) (hμ : ∀ v, ∑ w, μ v w = 1)
    (hS : S.WriteOnly I μ hμ) :
    ∀ (n : ℕ) (z : ζ) (v : V),
      (sampleLaw (μ v) (hμ v)).bind (fun w => qloopQ S Z n (z, (v, w))) =
        (qloopQ I Z n (z, v)).bind fun c =>
          (sampleLaw (μ c.2) (hμ c.2)).bind fun w => SubInstrument.pure (c.1, (c.2, w)) := by
  intro n
  induction n with
  | zero =>
    intro z v
    simp only [qloopQ, SubInstrument.pure_bind]
  | succ n ih =>
    intro z v
    simp only [qloopQ, SubInstrument.bind_assoc]
    rw [sampleLaw_bind_comm]
    refine congrArg _ (funext fun a => ?_)
    rw [← sampleLaw_frame (μ v) (hμ v) K, ← SubInstrument.bind_assoc, ← SubInstrument.frame_bind,
      hS v a.2, SubInstrument.frame_bind, SubInstrument.bind_assoc]
    refine congrArg _ (funext fun p => ?_)
    rw [SubInstrument.frame_bind, sampleLaw_frame, SubInstrument.bind_assoc]
    simp only [SubInstrument.frame_pure, SubInstrument.pure_bind]
    rw [sampleLaw_bind_comm]
    exact congrArg _ (funext fun z₁ => ih z₁ p.1)

end NonInterference

/-! ## Substitution at a conditionally sparse set -/

section Sparse

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] {α : Type}
variable {W : Type} [Fintype W]

open Classical in
/-- The diagonal projector onto the basis states outside the set `T`. -/
def projOff (T : Set A) : Matrix A A ℂ :=
  Matrix.diagonal fun x => if x ∈ T then 0 else 1

omit [Fintype A] in
/-- The projector onto the basis states outside a set is self-adjoint. -/
theorem projOff_conjTranspose (T : Set A) : (projOff T)ᴴ = projOff T := by
  unfold projOff; simp_all

/-- The projector onto the basis states outside a set is idempotent. -/
theorem projOff_mul_self (T : Set A) : projOff T * projOff T = projOff T := by
  unfold projOff; simp_all

open Classical in
/-- The weight that `1 − P ⊗ 1`, for the projector `P` onto the basis states outside `T`, gives
a matrix is the sum of its diagonal entries over the basis states in `T`. -/
theorem trace_one_sub_projOff_mul (T : Set A) (r : ℕ) (ρ : Matrix (A × Fin r) (A × Fin r) ℂ) :
    ((1 - kroneckerMap (· * ·) (projOff T) (1 : Matrix (Fin r) (Fin r) ℂ)) * ρ).trace.re =
      ∑ x, if x.1 ∈ T then (ρ x x).re else 0 := by
  simp only [projOff, Matrix.trace, Matrix.diag, Matrix.sub_mul, Matrix.one_mul,
    Matrix.sub_apply, Complex.sub_re, Finset.sum_sub_distrib]
  simp only [Complex.re_sum]
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with h <;> simp [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.diagonal_apply,
    Matrix.one_apply, Fintype.sum_prod_type, h]

open Classical in
/-- **Substitution at a conditionally sparse set.** Let `p w` and `q w` agree on the inputs
compressed by the projector onto the basis states outside `T w`, and let each basis state lie
in `T w` with probability at most `δ` when `w` is drawn from `μ`. Then drawing `w` from `μ` and
running `p w` is within `2 √δ` of drawing `w` from `μ` and running `q w`. -/
theorem subst_sparse_le (μ : W → ℝ≥0) (hμ : ∑ w, μ w = 1) (p q : W → SubInstrument A B α)
    (T : W → Set A)
    (hagree : ∀ w a (M : Matrix A A ℂ), (p w).branch a (projOff (T w) * M * projOff (T w)) =
      (q w).branch a (projOff (T w) * M * projOff (T w)))
    (δ : ℝ) (hδ : ∀ x, ∑ w, (μ w : ℝ) * (if x ∈ T w then 1 else 0) ≤ δ) :
    sidist ((sampleLaw μ hμ).bind p) ((sampleLaw μ hμ).bind q) ≤ ENNReal.ofReal (2 * √δ) := by
  refine iSup_le fun r => iSup_le fun ρ => iSup_le fun hρ => iSup_le fun htr =>
    iSup_le fun ψ => ?_
  rw [SubInstrument.frame_bind, SubInstrument.frame_bind, sampleLaw_frame, accept_bind _ _ _ hρ,
    accept_bind _ _ _ hρ, accept_sampleLaw _ _ _ hρ, accept_sampleLaw _ _ _ hρ]
  have hdiag : ∀ x, 0 ≤ (ρ x x).re := fun x => (Complex.nonneg_iff.mp hρ.diag_nonneg).1
  set t : W → ℝ := fun w => ((1 - kroneckerMap (· * ·) (projOff (T w))
    (1 : Matrix (Fin r) (Fin r) ℂ)) * ρ).trace.re with ht
  have hgap : ∀ w, absDiff ((QTest.comp ((p w).frame (Fin r)) ψ).toFun ρ)
      ((QTest.comp ((q w).frame (Fin r)) ψ).toFun ρ) ≤ ENNReal.ofReal (2 * √(t w)) := fun w =>
    gentle_subst_le (p w) (q w) (projOff (T w)) (projOff_conjTranspose _) (projOff_mul_self _)
      (hagree w) r hρ htr ψ
  have ht0 : ∀ w, 0 ≤ t w := fun w => by
    simp only [ht, trace_one_sub_projOff_mul]
    exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp [hdiag x]
  have hsum : ∑ w, (μ w : ℝ) * t w ≤ δ * ρ.trace.re := by
    calc ∑ w, (μ w : ℝ) * t w
        = ∑ x, (∑ w, (μ w : ℝ) * (if x.1 ∈ T w then 1 else 0)) * (ρ x x).re := by
          simp only [ht, trace_one_sub_projOff_mul, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => by
            split_ifs <;> simp
      _ ≤ ∑ x, δ * (ρ x x).re :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hδ x.1) (hdiag x)
      _ = δ * ρ.trace.re := by
          rw [← Finset.mul_sum, Matrix.trace, Complex.re_sum]
          rfl
  have hjensen : ∑ w, (μ w : ℝ) * √(t w) ≤ √(∑ w, (μ w : ℝ) * t w) := by
    have h := Real.strictConcaveOn_sqrt.concaveOn.le_map_sum (t := Finset.univ)
      (w := fun w => (μ w : ℝ)) (p := t) (fun w _ => (μ w).2)
      (by rw [← NNReal.coe_sum, hμ, NNReal.coe_one]) (fun w _ => ht0 w)
    simpa only [smul_eq_mul] using h
  have htr0 : 0 ≤ ρ.trace.re := hρ.trace_nonneg.1
  have hfinal : √(∑ w, (μ w : ℝ) * t w) ≤ √δ := by
    rcases le_or_gt 0 δ with h | h
    · exact Real.sqrt_le_sqrt (hsum.trans (mul_le_of_le_one_right h htr))
    · rw [Real.sqrt_eq_zero'.mpr (hsum.trans (mul_nonpos_of_nonpos_of_nonneg h.le htr0))]
      exact Real.sqrt_nonneg _
  have h2 : ∑ w, (μ w : ℝ) * (2 * √(t w)) = 2 * ∑ w, (μ w : ℝ) * √(t w) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by ring
  calc absDiff (∑ w, (μ w : ℝ≥0∞) * (QTest.comp ((p w).frame (Fin r)) ψ).toFun ρ)
        (∑ w, (μ w : ℝ≥0∞) * (QTest.comp ((q w).frame (Fin r)) ψ).toFun ρ)
      ≤ ∑ w, (μ w : ℝ≥0∞) * absDiff ((QTest.comp ((p w).frame (Fin r)) ψ).toFun ρ)
          ((QTest.comp ((q w).frame (Fin r)) ψ).toFun ρ) := by
        refine le_trans ?_ (Finset.sum_le_sum fun w _ => absDiff_mul_le _ _ _ ENNReal.coe_ne_top)
        simpa only [tsum_fintype] using absDiff_tsum_le
          (fun w => (μ w : ℝ≥0∞) * (QTest.comp ((p w).frame (Fin r)) ψ).toFun ρ)
          (fun w => (μ w : ℝ≥0∞) * (QTest.comp ((q w).frame (Fin r)) ψ).toFun ρ)
    _ ≤ ∑ w, (μ w : ℝ≥0∞) * ENNReal.ofReal (2 * √(t w)) :=
        Finset.sum_le_sum fun w _ => by gcongr; exact hgap w
    _ = ENNReal.ofReal (∑ w, (μ w : ℝ) * (2 * √(t w))) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun w _ => by positivity]
        refine Finset.sum_congr rfl fun w _ => ?_
        clear ht; simp_all
    _ ≤ ENNReal.ofReal (2 * √δ) := ENNReal.ofReal_le_ofReal (by rw [h2]; linarith)

end Sparse

end CatCrypt.Quantum.ReactiveUC
