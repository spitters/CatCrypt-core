/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.Instrument
public import CatCryptCore.Prob.SDistr
public import CatCryptCore.Crypto.UCMonad.SDistrInstance
public import CatCryptCore.Crypto.UCMonad.QuantumUC
public import CatCryptCore.Crypto.SDist
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.Normed

/-!
# Classical Embedding: SDistr → QComp d

This file defines the embedding of classical sub-distributions `SDistr α`
into quantum instruments `QComp d α`, and proves it preserves the monad
structure and statistical distance.

## Mathematical Idea

A classical sub-distribution `μ : SDistr α = PMF (Option α)` embeds into the
quantum instrument whose branch at each outcome is the identity channel scaled
by the probability of that outcome:

```
(classicalEmbed μ).branch a = (μ(some a)).toReal • LinearMap.id
```

The branch for outcome `a` maps a density matrix `ρ` to `p_a • ρ`.

## Main Results

* `classicalEmbed` — the embedding `SDistr α → QComp d α`
* `classicalEmbed_pure` — preserves pure
* `classicalEmbed_fail` — preserves fail
* `classicalEmbed_bind` — preserves bind (monad morphism)
* `IsClassical` — predicate for QComp values in the image of the embedding
* `isClassical_bind` — IsClassical closed under qbind
* `prTrue_classicalEmbed` — prTrue correspondence
* `classicalEmbed_sdist_eq` — distance preservation: `sdistD = qdist ∘ classicalEmbed`
* `ofSDistrHeapDist` — the `SPComp` distinguisher running a sub-distribution
  distinguisher on the output and the final heap of a game
* `exists_advantageA_eq_quantum_gap` — a quantum distinguisher of embedded game outputs
  has the advantage of one classical distinguisher on every pair of games
* `quantum_gap_le_of_advantage` — a classical advantage bound bounds the quantum gap

## Proof strategies

| Theorem | Strategy |
|---------|----------|
| `classicalEmbed.branch_psd` | `PosSemidef.smul` + `Complex.zero_le_real` |
| `classicalEmbed.branch_summable` | `Summable.smul_const` + norm-bounded summability |
| `classicalEmbed.branch_stp` | `trace_smul` + `tsum_mul_right` + PMF bound |
| `classicalEmbed_bind` | `QComp.ext_fun` + `tsum_smul_const` + `ofRealCLM.map_tsum` |
| `isClassical_bind` | `choose` coefficients + `tsum_smul_const` + `Complex.summable_ofReal` |
| `classicalEmbed_sdist_le` | embed D as classicalEmbed ∘ D + `prTrue_classicalEmbed` roundtrip |
| `classicalEmbed_sdist_ge` | `quantum_classical_simulation` theorem + `le_iSup_of_le` |
| `prTrue_classicalEmbed` | `trace_smul` + `DensityMatrix.tr_one` + `ofReal_re` |
-/

@[expose] public section

open scoped Matrix ComplexOrder ENNReal Matrix.Norms.Elementwise
open Matrix Classical CatCrypt.Prob CatCrypt.Quantum
open UCMonad.QuantumUC UCMonad.SDistrUC

noncomputable section

namespace CatCrypt.Quantum

variable {d : ℕ} {α β γ : Type}

/-! ## Helper lemmas for PMF summability -/

/-- The sum of a PMF over `some` values is at most 1. -/
private theorem tsum_some_le_one (μ : SDistr α) : ∑' a, μ (some a) ≤ 1 :=
  (ENNReal.tsum_comp_le_tsum_of_injective (Option.some_injective α) μ).trans
    (le_of_eq μ.tsum_coe)

/-- The sum of a PMF over `some` values is finite. -/
private theorem tsum_some_ne_top (μ : SDistr α) : ∑' a, μ (some a) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (tsum_some_le_one μ)

/-- The `toReal` of PMF weights over `some` values is summable. -/
private theorem summable_toReal_some (μ : SDistr α) :
    Summable (fun a => (μ (some a)).toReal) :=
  ENNReal.summable_toReal (tsum_some_ne_top μ)

/-- The `toReal` of PMF weights lifted to ℂ is summable. -/
private theorem summable_ofReal_toReal_some (μ : SDistr α) :
    Summable (fun a => (↑(μ (some a)).toReal : ℂ)) :=
  (summable_toReal_some μ).of_norm_bounded (fun a => by
    rw [Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg])

/-- The real-valued sum of PMF weights over `some` values is at most 1. -/
private theorem tsum_toReal_some_le_one (μ : SDistr α) :
    ∑' a, (μ (some a)).toReal ≤ 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun a =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (μ.coe_le_one (some a)))]
  calc (∑' a, μ (some a)).toReal
      ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono ENNReal.one_ne_top (tsum_some_le_one μ)
    _ = 1 := ENNReal.toReal_one

/-! ## Section 1: classicalEmbed definition -/

/-- Embed a classical sub-distribution into a quantum instrument.
    Each branch scales the identity channel by the classical probability. -/
noncomputable def classicalEmbed (μ : SDistr α) : QComp d α where
  branch a :=
    (↑(μ (some a)).toReal : ℂ) • LinearMap.id
  branch_psd a ρ hρ := by
    show ((↑(μ (some a)).toReal : ℂ) • ρ).PosSemidef
    exact hρ.smul (Complex.zero_le_real.mpr ENNReal.toReal_nonneg)
  branch_summable ρ := by
    show Summable (fun a => ((↑(μ (some a)).toReal : ℂ) • LinearMap.id) ρ)
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    exact (summable_ofReal_toReal_some μ).smul_const ρ
  branch_stp ρ hρ := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Matrix.trace_smul, smul_eq_mul]
    -- Goal: (∑' a, (↑(μ (some a)).toReal : ℂ) * ρ.trace).re ≤ ρ.trace.re
    rw [tsum_mul_right]
    -- Goal: ((∑' a, (↑(μ (some a)).toReal : ℂ)) * ρ.trace).re ≤ ρ.trace.re
    -- Show ∑' a, ↑r_a = ↑(∑' a, r_a)
    rw [show ∑' a, (↑(μ (some a)).toReal : ℂ) =
        ↑(∑' a, (μ (some a)).toReal) from
      (Complex.ofRealCLM.map_tsum (summable_toReal_some μ)).symm]
    -- Goal: (↑(∑' a, r_a) * ρ.trace).re ≤ ρ.trace.re
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    -- Goal: (∑' a, r_a) * ρ.trace.re ≤ ρ.trace.re
    calc (∑' a, (μ (some a)).toReal) * ρ.trace.re
        ≤ 1 * ρ.trace.re := by
          exact mul_le_mul_of_nonneg_right (tsum_toReal_some_le_one μ)
            (trace_re_nonneg_of_psd hρ)
      _ = ρ.trace.re := one_mul _

/-! ## Section 2: Monad morphism properties -/

/-- `classicalEmbed` preserves `pure`: point mass maps to `qpure`. -/
theorem classicalEmbed_pure (a : α) :
    (classicalEmbed (SDistr.pure a) : QComp d α) = QComp.qpure a := by
  apply QComp.ext_fun; intro a' ρ
  simp only [classicalEmbed, QComp.qpure]
  by_cases h : a' = a
  · subst h
    simp [SDistr.pure_apply_some, ENNReal.toReal_one, Complex.ofReal_one, one_smul]
  · have hne : SDistr.pure a (some a') = 0 := by
      simp [SDistr.pure_apply_some, Ne.symm h]
    simp [hne, ENNReal.toReal_zero, Complex.ofReal_zero, zero_smul, h]

/-- `classicalEmbed` preserves `fail`: failure maps to `qfail`. -/
theorem classicalEmbed_fail :
    (classicalEmbed SDistr.fail : QComp d α) = QComp.qfail := by
  apply QComp.ext_fun; intro a ρ
  simp only [classicalEmbed, QComp.qfail]
  have hzero : SDistr.fail (some a) = (0 : ℝ≥0∞) := SDistr.fail_apply_some a
  simp [hzero, ENNReal.toReal_zero, Complex.ofReal_zero, zero_smul]

/-- The bind of SDistrs at `some b` factors as a tsum over `some` values. -/
private theorem bind_some_eq (μ : SDistr α) (f : α → SDistr β) (b : β) :
    (SDistr.bind μ f) (some b) = ∑' a, μ (some a) * (f a) (some b) := by
  simp only [SDistr.bind, PMF.bind_apply]
  apply SDistr.tsum_option_none_zero
  simp [SDistr.fail_apply_some]

/-- Each term `μ(some a) * (f a)(some b)` is ≤ 1, hence ≠ ⊤. -/
private theorem bind_term_ne_top (μ : SDistr α) (f : α → SDistr β) (a : α) (b : β) :
    μ (some a) * (f a) (some b) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    ((mul_le_mul' (PMF.coe_le_one μ _) (PMF.coe_le_one (f a) _)).trans_eq (one_mul 1))

/-- Real summability of product weights. -/
private theorem summable_bind_weights (μ : SDistr α) (f : α → SDistr β) (b : β) :
    Summable (fun a => ((f a) (some b)).toReal * (μ (some a)).toReal) :=
  Summable.of_nonneg_of_le
    (fun _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (fun a => by
      calc ((f a) (some b)).toReal * (μ (some a)).toReal
          ≤ 1 * (μ (some a)).toReal :=
            mul_le_mul_of_nonneg_right
              ((ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)).trans_eq
                ENNReal.toReal_one)
              ENNReal.toReal_nonneg
        _ = (μ (some a)).toReal := one_mul _)
    (summable_toReal_some μ)

/-- `classicalEmbed` preserves `bind` (monadic composition).
    This is the key monad morphism property. -/
theorem classicalEmbed_bind (μ : SDistr α) (f : α → SDistr β) :
    (classicalEmbed (SDistr.bind μ f) : QComp d β) =
    QComp.qbind (classicalEmbed μ) (fun a => classicalEmbed (f a)) := by
  apply QComp.ext_fun; intro b ρ
  simp only [classicalEmbed, QComp.qbind, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.smul_apply, LinearMap.id_apply]
  -- LHS: (↑((SDistr.bind μ f)(some b)).toReal : ℂ) • ρ
  -- RHS: ∑' a, (↑((f a)(some b)).toReal : ℂ) • ((↑(μ(some a)).toReal : ℂ) • ρ)
  simp_rw [smul_smul, ← Complex.ofReal_mul]
  -- RHS: ∑' a, (↑(((f a)(some b)).toReal * (μ(some a)).toReal) : ℂ) • ρ
  -- Factor ρ out of tsum using tsum_smul_const
  have hsc : Summable (fun a => (↑(((f a) (some b)).toReal * (μ (some a)).toReal) : ℂ)) :=
    (summable_bind_weights μ f b).of_norm_bounded (fun a => by
      rw [Complex.norm_real, Real.norm_of_nonneg
        (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)])
  rw [show ∑' a, (↑(((f a) (some b)).toReal * (μ (some a)).toReal) : ℂ) • ρ =
      (∑' a, (↑(((f a) (some b)).toReal * (μ (some a)).toReal) : ℂ)) • ρ from
    hsc.tsum_smul_const ρ]
  -- Now both sides are (scalar) • ρ, reduce to scalar equality
  congr 1
  -- Push ℂ cast through tsum
  rw [show ∑' a, (↑(((f a) (some b)).toReal * (μ (some a)).toReal) : ℂ) =
      ↑(∑' a, ((f a) (some b)).toReal * (μ (some a)).toReal) from
    (Complex.ofRealCLM.map_tsum (summable_bind_weights μ f b)).symm]
  -- Now: ↑(bind weight).toReal = ↑(∑' products), reduce to ℝ
  congr 1
  -- Key real identity
  rw [bind_some_eq]
  -- (∑' a, μ(some a) * (f a)(some b)).toReal = ∑' a, (f a)(some b).toReal * (μ(some a)).toReal
  rw [ENNReal.tsum_toReal_eq (fun a => bind_term_ne_top μ f a b)]
  congr 1; funext a
  rw [ENNReal.toReal_mul]; ring

/-! ## Section 3: IsClassical predicate -/

/-- A quantum instrument is *classical* if every branch is a non-negative
    real scalar times the identity map. -/
def IsClassical (I : QComp d α) : Prop :=
  ∀ a, ∃ c : ℝ, 0 ≤ c ∧ I.branch a = (↑c : ℂ) • LinearMap.id

/-- `qpure a` is classical: branches are `1 • id` or `0 • id`. -/
theorem isClassical_pure (a : α) : IsClassical (QComp.qpure a : QComp d α) := by
  intro a'
  simp only [QComp.qpure]
  by_cases h : a' = a
  · exact ⟨1, zero_le_one, by simp [h, Complex.ofReal_one]⟩
  · exact ⟨0, le_refl _, by simp [h, Complex.ofReal_zero]⟩

/-- The image of `classicalEmbed` is classical by construction. -/
theorem isClassical_embed (μ : SDistr α) :
    IsClassical (classicalEmbed μ : QComp d α) := by
  intro a
  exact ⟨(μ (some a)).toReal, ENNReal.toReal_nonneg, rfl⟩

/-- `qfail` is classical: all branches are `0 • id`. -/
theorem isClassical_fail : IsClassical (QComp.qfail : QComp d α) := by
  intro a
  exact ⟨0, le_refl _, by simp [QComp.qfail, Complex.ofReal_zero]⟩

/-- If `I` is classical and all `f a` are classical, then `qbind I f` is classical. -/
theorem isClassical_bind (I : QComp d α) (f : α → QComp d β)
    (hI : IsClassical I) (hf : ∀ a, IsClassical (f a)) :
    IsClassical (QComp.qbind I f) := by
  intro b
  choose c_I hc_I using hI
  choose c_f hc_f using fun a => hf a b
  -- Witness: c = ∑' a, c_f a * c_I a (or 0 if series diverges)
  refine ⟨∑' a, c_f a * c_I a, tsum_nonneg (fun a => mul_nonneg (hc_f a).1 (hc_I a).1), ?_⟩
  apply LinearMap.ext; intro ρ
  simp only [QComp.qbind, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.smul_apply, LinearMap.id_apply]
  -- Rewrite each branch using classicality
  have key : ∀ a, (f a).branch b (I.branch a ρ) = (↑(c_f a * c_I a) : ℂ) • ρ := by
    intro a
    rw [(hc_I a).2, (hc_f a).2]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, ← Complex.ofReal_mul]
  simp_rw [key]
  -- Goal: ∑' a, ↑(c_f a * c_I a) • ρ = ↑(∑' a, c_f a * c_I a) • ρ
  by_cases hs : Summable (fun a => c_f a * c_I a)
  · -- Summable case
    have hsc : Summable (fun a => (↑(c_f a * c_I a) : ℂ)) :=
      hs.of_norm_bounded (fun a => by
        rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (hc_f a).1 (hc_I a).1)])
    rw [hsc.tsum_smul_const ρ,
        show ∑' a, (↑(c_f a * c_I a) : ℂ) = ↑(∑' a, c_f a * c_I a) from
          (Complex.ofRealCLM.map_tsum hs).symm]
  · -- Not summable: both sides are 0
    rw [tsum_eq_zero_of_not_summable hs, Complex.ofReal_zero, zero_smul]
    by_cases hρ : ρ = 0
    · simp [hρ]
    · -- ρ ≠ 0: matrix smul series also not summable → tsum = 0
      apply tsum_eq_zero_of_not_summable; intro habs; apply hs
      -- Extract scalar summability via matrix entry evaluation
      obtain ⟨i, j, hij⟩ : ∃ i j, ρ i j ≠ 0 := by
        by_contra h; push Not at h; exact hρ (Matrix.ext (fun i j => h i j))
      -- Evaluating at (i,j) gives summable scalar series
      have heval : Summable (fun a => ((↑(c_f a * c_I a) : ℂ) • ρ) i j) :=
        (Pi.summable.mp (Pi.summable.mp habs i)) j
      simp only [Matrix.smul_apply, smul_eq_mul] at heval
      -- heval : Summable (fun a => (↑(c_f a * c_I a) : ℂ) * ρ i j)
      have hsc : Summable (fun a => (↑(c_f a * c_I a) : ℂ)) := by
        rwa [show (fun a => (↑(c_f a * c_I a) : ℂ) * ρ i j) =
             (fun a => ρ i j * (↑(c_f a * c_I a) : ℂ)) from by funext; ring,
             summable_mul_left_iff hij] at heval
      exact Complex.summable_ofReal.mp hsc

/-! ## Section 4: Distance preservation -/

/-- `prTrue_Q` of `classicalEmbed μ` at any density matrix equals
    the classical probability `μ(some true)`. -/
theorem prTrue_classicalEmbed (μ : SDistr Bool) (ρ : DensityMatrix d) :
    prTrue_Q (classicalEmbed μ) ρ =
    ENNReal.ofReal (μ (some true)).toReal := by
  simp only [prTrue_Q, classicalEmbed, LinearMap.smul_apply, LinearMap.id_apply]
  congr 1
  simp only [Matrix.trace_smul, smul_eq_mul, ρ.tr_one, mul_one, Complex.ofReal_re]

/-- A density matrix exists when d > 0. The standard basis projector |0⟩⟨0|
    is PSD with trace 1. -/
private theorem nonempty_densityMatrix [NeZero d] : Nonempty (DensityMatrix d) := by
  have hd := Nat.pos_of_ne_zero (NeZero.ne d)
  let i₀ : Fin d := ⟨0, hd⟩
  refine ⟨⟨Matrix.diagonal (fun i => if i = i₀ then 1 else 0), ?_, ?_⟩⟩
  · exact Matrix.PosSemidef.diagonal (fun i => by split_ifs <;> positivity)
  · simp [Matrix.trace_diagonal, Finset.mem_univ]

/-- PMF values are ≠ ⊤. -/
private theorem pmf_ne_top (μ : SDistr α) (x : Option α) : μ x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one μ x)

/-- Classical statistical distance is at most quantum statistical distance
    when using `classicalEmbed`. Requires d > 0 for density matrix existence. -/
theorem classicalEmbed_sdist_le [NeZero d] (f g : α → SDistr β) :
    sdistD f g ≤
    qdist (fun a => classicalEmbed (f a) : α → QComp d β)
          (fun a => classicalEmbed (g a)) := by
  obtain ⟨ρ₀⟩ := nonempty_densityMatrix (d := d)
  apply iSup_le; intro D; apply iSup_le; intro a
  -- Embed classical distinguisher D as classicalEmbed ∘ D, pick ρ₀
  apply le_iSup_of_le (fun b => classicalEmbed (D b))
  apply le_iSup_of_le a
  apply le_iSup_of_le ρ₀
  -- Rewrite qbind(classicalEmbed μ, classicalEmbed ∘ D) = classicalEmbed(bind μ D)
  rw [← classicalEmbed_bind (f a) D, ← classicalEmbed_bind (g a) D]
  -- Rewrite prTrue_Q(classicalEmbed _) = ENNReal.ofReal(_.toReal)
  rw [prTrue_classicalEmbed, prTrue_classicalEmbed]
  -- Now: absDiffD(prTrueD(bind ...), prTrueD(bind ...))
  --    ≤ absDiff(ofReal(bind ...(some true).toReal), ofReal(bind ...(some true).toReal))
  -- After ofReal_toReal roundtrip, both sides are identical
  simp only [absDiffD, absDiff, prTrueD]
  rw [ENNReal.ofReal_toReal (pmf_ne_top _ _), ENNReal.ofReal_toReal (pmf_ne_top _ _)]

/-- Cauchy–Schwarz for PSD matrices on a 2×2 principal submatrix:
    for PSD `M` over `ℂ`, `‖M i j‖² ≤ (M i i).re * (M j j).re`.

    Proof sketch: the 2×2 principal submatrix on rows/cols `{i, j}` is PSD
    (`Matrix.PosSemidef.submatrix`), hence its determinant is non-negative
    (`Matrix.PosSemidef.det_nonneg`). Expanding via `det_fin_two` gives
    `M i i * M j j − M i j * M j i ≥ 0`. By Hermitian, `M j i = star (M i j)`,
    so `M i j * M j i = ↑(normSq (M i j)) = ↑‖M i j‖²`, and the diagonal
    entries are real with real part equal to themselves. -/
private theorem psd_offdiag_sq_le_diag {M : Matrix (Fin d) (Fin d) ℂ}
    (hpsd : M.PosSemidef) (i j : Fin d) :
    ‖M i j‖ ^ 2 ≤ (M i i).re * (M j j).re := by
  -- 2×2 principal submatrix via `e : Fin 2 → Fin d`, `e 0 = i`, `e 1 = j`
  let e : Fin 2 → Fin d := ![i, j]
  have hSub : (M.submatrix e e).PosSemidef := hpsd.submatrix e
  have h_det_nn : (0 : ℂ) ≤ (M.submatrix e e).det := hSub.det_nonneg
  -- Expand: det = M i i * M j j - M i j * M j i
  have h_det_eq :
      (M.submatrix e e).det = M i i * M j j - M i j * M j i := by
    rw [Matrix.det_fin_two]
    simp [Matrix.submatrix_apply, e, Matrix.cons_val_zero, Matrix.cons_val_one]
  -- Re-part of the determinant is non-negative
  have h_det_re_nn : 0 ≤ (M i i * M j j - M i j * M j i).re := by
    have := (Complex.le_def.mp h_det_nn).1
    simpa [h_det_eq, Complex.zero_re] using this
  -- Hermitian: M j i = star (M i j)
  have hHerm : M.IsHermitian := hpsd.isHermitian
  have h_ji : M j i = star (M i j) := (hHerm.apply j i).symm
  -- So M i j * M j i = ↑(normSq (M i j))
  have h_prod : M i j * M j i = ((Complex.normSq (M i j) : ℝ) : ℂ) := by
    rw [h_ji]; exact Complex.mul_conj (M i j)
  -- Diagonal entries are real: M i i = ↑((M i i).re), M j j = ↑((M j j).re)
  have h_ii_real : M i i = ((M i i).re : ℂ) := (hHerm.coe_re_apply_self i).symm
  have h_jj_real : M j j = ((M j j).re : ℂ) := (hHerm.coe_re_apply_self j).symm
  -- Substitute into h_det_re_nn and take real part
  have h_re : (M i i * M j j - M i j * M j i).re =
      (M i i).re * (M j j).re - Complex.normSq (M i j) := by
    rw [h_prod, h_ii_real, h_jj_real]
    simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [h_re] at h_det_re_nn
  -- Conclude: ‖M i j‖² = normSq (M i j) ≤ (M i i).re * (M j j).re
  rw [sq, Complex.norm_mul_self_eq_normSq]
  linarith

/-- PSD entry norm bound: for PSD M with `M.trace.re ≤ 1`, `‖M i j‖ ≤ 1`.

    Proof: use the 2×2 principal submatrix Cauchy–Schwarz
    `‖M i j‖² ≤ (M i i).re * (M j j).re` from `psd_offdiag_sq_le_diag`,
    then bound each diagonal real part by `M.trace.re` (which is the sum
    of non-negative real parts of all diagonal entries) and finally by `1`. -/
private theorem psd_entry_bound {M : Matrix (Fin d) (Fin d) ℂ}
    (hpsd : M.PosSemidef) (htr : M.trace.re ≤ 1) (i j : Fin d) :
    ‖M i j‖ ≤ 1 := by
  -- Step 1: ‖M i j‖² ≤ (M i i).re * (M j j).re
  have h_cs : ‖M i j‖ ^ 2 ≤ (M i i).re * (M j j).re :=
    psd_offdiag_sq_le_diag hpsd i j
  -- Step 2: diagonal entries are non-negative reals bounded by trace.re
  have h_diag_re_nn : ∀ k : Fin d, 0 ≤ (M k k).re := fun k =>
    (Complex.le_def.mp (hpsd.diag_nonneg (i := k))).1
  -- M.trace.re = ∑ k, (M k k).re via linearity of Complex.re
  have h_trace_re : M.trace.re = ∑ k, (M k k).re := by
    simp [Matrix.trace, Matrix.diag, Complex.re_sum]
  -- Step 3: (M k k).re ≤ M.trace.re for every k (since sum of non-negatives)
  have h_le_trace : ∀ k : Fin d, (M k k).re ≤ M.trace.re := by
    intro k
    rw [h_trace_re]
    refine Finset.single_le_sum (f := fun k' => (M k' k').re)
      (fun k' _ => h_diag_re_nn k') (Finset.mem_univ k)
  -- Step 4: (M i i).re ≤ 1 and (M j j).re ≤ 1
  have h_ii_le_one : (M i i).re ≤ 1 := (h_le_trace i).trans htr
  have h_jj_le_one : (M j j).re ≤ 1 := (h_le_trace j).trans htr
  -- Step 5: ‖M i j‖² ≤ 1
  have h_sq_le_one : ‖M i j‖ ^ 2 ≤ 1 := by
    calc ‖M i j‖ ^ 2
        ≤ (M i i).re * (M j j).re := h_cs
      _ ≤ 1 * 1 := by
          exact mul_le_mul h_ii_le_one h_jj_le_one (h_diag_re_nn j) zero_le_one
      _ = 1 := by ring
  -- Step 6: ‖M i j‖ ≤ 1 from squaring (since norm is non-negative)
  have h_norm_nn : 0 ≤ ‖M i j‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖M i j‖ - 1), sq_nonneg (‖M i j‖ + 1)]

/-- The Born-rule probability of outcome `true` for `D_Q b` at state `ρ`. -/
private def bornProb (D_Q : β → QComp d Bool) (ρ : DensityMatrix d) (b : β) : ℝ :=
  ((D_Q b).branch true ρ.val).trace.re

private theorem bornProb_nonneg (D_Q : β → QComp d Bool) (ρ : DensityMatrix d) (b : β) :
    0 ≤ bornProb D_Q ρ b :=
  trace_re_nonneg_of_psd ((D_Q b).branch_psd true ρ.val ρ.psd)

private theorem bornProb_le_one (D_Q : β → QComp d Bool) (ρ : DensityMatrix d) (b : β) :
    bornProb D_Q ρ b ≤ 1 := by
  -- ((D_Q b).branch true ρ.val).trace.re ≤ ρ.val.trace.re = 1
  -- Single branch bound, derived inline from branch_stp + non-neg diag.
  have hpsd_branch : ∀ b', ((D_Q b).branch b' ρ.val).PosSemidef := fun b' =>
    (D_Q b).branch_psd b' ρ.val ρ.psd
  have h_single : ((D_Q b).branch true ρ.val).trace.re ≤ ρ.val.trace.re := by
    calc ((D_Q b).branch true ρ.val).trace.re
        ≤ ∑' b', ((D_Q b).branch b' ρ.val).trace.re :=
          (trace_re_summable ((D_Q b).branch_summable ρ.val)).le_tsum true
            (fun b' _ => trace_re_nonneg_of_psd (hpsd_branch b'))
      _ = (∑' b', ((D_Q b).branch b' ρ.val).trace).re :=
          (Complex.re_tsum (trace_summable ((D_Q b).branch_summable ρ.val))).symm
      _ ≤ ρ.val.trace.re := (D_Q b).branch_stp ρ.val ρ.psd
  rw [show (1 : ℝ) = ((1 : ℂ).re) from Complex.one_re.symm, ← ρ.tr_one]
  exact h_single

private theorem ofReal_bornProb_le_one (D_Q : β → QComp d Bool) (ρ : DensityMatrix d) (b : β) :
    ENNReal.ofReal (bornProb D_Q ρ b) ≤ 1 := by
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
  exact ENNReal.ofReal_le_ofReal (bornProb_le_one D_Q ρ b)

/-- The classical Bernoulli distinguisher returning `true` with prob `bornProb`. -/
private noncomputable def bornDcl (D_Q : β → QComp d Bool) (ρ : DensityMatrix d) (b : β) :
    SDistr Bool :=
  PMF.ofFintype
    (fun ob : Option Bool => match ob with
      | none => 1 - ENNReal.ofReal (bornProb D_Q ρ b)
      | some true => ENNReal.ofReal (bornProb D_Q ρ b)
      | some false => 0)
    (by
      rw [Fintype.sum_option, Fintype.sum_bool]
      -- (1 - q) + (q + 0) = 1 where q = ofReal (bornProb ...)
      rw [add_zero]
      exact tsub_add_cancel_of_le (ofReal_bornProb_le_one D_Q ρ b))

private theorem bornDcl_apply_some_true (D_Q : β → QComp d Bool) (ρ : DensityMatrix d) (b : β) :
    bornDcl D_Q ρ b (some true) = ENNReal.ofReal (bornProb D_Q ρ b) := rfl

/-- For classical inputs, any quantum distinguisher can be simulated by a
    classical one: for any `D_Q : β → QComp d Bool` and density matrix `ρ`,
    there exists `D_cl : β → SDistr Bool` such that for all `μ : SDistr β`,
    `prTrue_Q(qbind(classicalEmbed μ, D_Q), ρ) = prTrueD(bind(μ, D_cl))`.

    Proof outline:
    1. Take `D_cl = bornDcl D_Q ρ`, the classical Bernoulli distinguisher
       with success probability `bornProb b := ((D_Q b).branch true ρ.val).trace.re`.
    2. LHS expands via `QComp.qbind` and linearity of `(D_Q a).branch true`
       through the scalar `(μ(some a)).toReal`, then via `trace_tsum` and
       `Complex.re_tsum` to `ofReal (∑' a, (μ(some a)).toReal * bornProb a)`.
    3. RHS expands via `bind_some_eq` to `∑' a, μ(some a) * ofReal(bornProb a)`.
    4. Bridge using `μ(some a) = ofReal((μ(some a)).toReal)`, `ofReal_mul`
       and `ofReal_tsum_of_nonneg`. -/
theorem quantum_classical_simulation (D_Q : β → QComp d Bool)
    (ρ : DensityMatrix d) :
    ∃ D_cl : β → SDistr Bool, ∀ μ : SDistr β,
    prTrue_Q (QComp.qbind (classicalEmbed μ) D_Q) ρ = prTrueD (SDistr.bind μ D_cl) := by
  refine ⟨bornDcl D_Q ρ, fun μ => ?_⟩
  -- Set short names
  set p : β → ℝ := bornProb D_Q ρ with hp_def
  -- Step A: unfold prTrue_Q and qbind on LHS
  show ENNReal.ofReal (((QComp.qbind (classicalEmbed μ) D_Q).branch true ρ.val).trace.re) =
       prTrueD (SDistr.bind μ (bornDcl D_Q ρ))
  -- Rewrite the qbind branch as the tsum
  have hbranch_eq : ((QComp.qbind (classicalEmbed μ) D_Q).branch true ρ.val) =
      ∑' a, (D_Q a).branch true ((classicalEmbed μ).branch a ρ.val) := rfl
  rw [hbranch_eq]
  -- Rewrite (classicalEmbed μ).branch a ρ.val = ofReal_a • ρ.val
  have hcb : ∀ a, (classicalEmbed μ).branch a ρ.val =
      (↑(μ (some a)).toReal : ℂ) • ρ.val := fun a => by
    simp only [classicalEmbed, LinearMap.smul_apply, LinearMap.id_apply]
  simp_rw [hcb]
  -- Push smul through (D_Q a).branch true (which is a linear map)
  have hlin : ∀ a, (D_Q a).branch true ((↑(μ (some a)).toReal : ℂ) • ρ.val) =
      (↑(μ (some a)).toReal : ℂ) • ((D_Q a).branch true ρ.val) := fun a =>
    LinearMap.map_smul _ _ _
  simp_rw [hlin]
  -- Summability of (fun a => ofReal_a • M_a) where M_a = (D_Q a).branch true ρ.val
  -- This is exactly bind_summable applied at this position; reconstruct via norms.
  have hM_psd : ∀ a, ((D_Q a).branch true ρ.val).PosSemidef := fun a =>
    (D_Q a).branch_psd true ρ.val ρ.psd
  have hM_norm_le : ∀ a, ‖((D_Q a).branch true ρ.val)‖ ≤ p a := fun a => by
    have h1 : ‖((D_Q a).branch true ρ.val)‖ ≤ ((D_Q a).branch true ρ.val).trace.re :=
      psd_norm_le_trace (hM_psd a)
    exact h1
  -- Real summability of (μ(some a)).toReal
  have hμ_summ : Summable (fun a => (μ (some a)).toReal) := summable_toReal_some μ
  -- Real summability of (μ(some a)).toReal * p a since 0 ≤ p a ≤ 1
  have hp_nn : ∀ a, 0 ≤ p a := bornProb_nonneg D_Q ρ
  have hp_le_one : ∀ a, p a ≤ 1 := bornProb_le_one D_Q ρ
  have hμp_summ : Summable (fun a => (μ (some a)).toReal * p a) := by
    apply Summable.of_nonneg_of_le
      (fun a => mul_nonneg ENNReal.toReal_nonneg (hp_nn a))
      (fun a => ?_) hμ_summ
    calc (μ (some a)).toReal * p a
        ≤ (μ (some a)).toReal * 1 := by
          exact mul_le_mul_of_nonneg_left (hp_le_one a) ENNReal.toReal_nonneg
      _ = (μ (some a)).toReal := mul_one _
  -- Summability of the matrix family: ‖ofReal_a • M_a‖ ≤ (μ(some a)).toReal * p a
  have hsum_smul :
      Summable (fun a => (↑(μ (some a)).toReal : ℂ) • ((D_Q a).branch true ρ.val)) := by
    apply Summable.of_norm_bounded
      (g := fun a => (μ (some a)).toReal * p a) hμp_summ
    intro a
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left (hM_norm_le a) ENNReal.toReal_nonneg
  -- Trace commutes with tsum
  rw [trace_tsum hsum_smul]
  -- (c • M).trace = c * M.trace
  simp_rw [Matrix.trace_smul, smul_eq_mul]
  -- Now: ofReal((∑' a, ↑(μ(some a)).toReal * M_a.trace).re) = ...
  -- Use Complex.re_tsum
  have hsum_trace : Summable (fun a => (↑(μ (some a)).toReal : ℂ) *
      ((D_Q a).branch true ρ.val).trace) := by
    have h := trace_summable hsum_smul
    simp_rw [Matrix.trace_smul, smul_eq_mul] at h
    exact h
  rw [Complex.re_tsum hsum_trace]
  -- ((↑r : ℂ) * z).re = r * z.re
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  -- Now LHS: ofReal (∑' a, (μ(some a)).toReal * ((D_Q a).branch true ρ.val).trace.re)
  -- = ofReal (∑' a, (μ(some a)).toReal * p a)
  show ENNReal.ofReal (∑' a, (μ (some a)).toReal * ((D_Q a).branch true ρ.val).trace.re) =
       prTrueD (SDistr.bind μ (bornDcl D_Q ρ))
  -- Step B: unfold RHS
  rw [prTrueD, bind_some_eq]
  -- (D_cl a)(some true) = ofReal (p a)
  simp_rw [bornDcl_apply_some_true]
  -- Step C: bridge via ofReal_mul + ofReal_tsum_of_nonneg
  -- Unfold bornProb references to match p
  show ENNReal.ofReal (∑' a, (μ (some a)).toReal * ((D_Q a).branch true ρ.val).trace.re) =
       ∑' a, μ (some a) * ENNReal.ofReal (p a)
  -- Rewrite RHS pointwise: μ(some a) * ofReal(p a) = ofReal((μ(some a)).toReal * p a)
  have hμ_top : ∀ a, μ (some a) ≠ ⊤ := fun a => pmf_ne_top μ (some a)
  have hterm_eq : ∀ a, μ (some a) * ENNReal.ofReal (p a) =
      ENNReal.ofReal ((μ (some a)).toReal * p a) := fun a => by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hμ_top a)]
  simp_rw [hterm_eq]
  -- Now RHS: ∑' a, ofReal ((μ(some a)).toReal * p a)
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun a => mul_nonneg ENNReal.toReal_nonneg (hp_nn a)) hμp_summ]
  -- Goal: ofReal(∑' a, (μ(some a)).toReal * M_a.trace.re) = ofReal(∑' a, (μ(some a)).toReal * p a)
  -- These are equal definitionally since p a = M_a.trace.re by definition of bornProb
  rfl

/-- Quantum statistical distance is at most classical statistical distance
    when inputs are `classicalEmbed`-ed.
    For classical inputs (scalar × id), trace of bind factorizes into a
    weighted sum that a classical distinguisher can replicate. -/
theorem classicalEmbed_sdist_ge (f g : α → SDistr β) :
    qdist (fun a => classicalEmbed (f a) : α → QComp d β)
          (fun a => classicalEmbed (g a)) ≤
    sdistD f g := by
  apply iSup_le; intro D_Q; apply iSup_le; intro a; apply iSup_le; intro ρ
  obtain ⟨D_cl, hD_cl⟩ := quantum_classical_simulation D_Q ρ
  rw [hD_cl (f a), hD_cl (g a)]
  -- absDiff and absDiffD have the same definition: (a - b) ⊔ (b - a)
  calc absDiff (prTrueD (SDistr.bind (f a) D_cl))
               (prTrueD (SDistr.bind (g a) D_cl))
      = absDiffD (prTrueD (SDistr.bind (f a) D_cl))
                  (prTrueD (SDistr.bind (g a) D_cl)) := by
        simp [absDiff, absDiffD]
    _ ≤ sdistD f g := le_iSup_of_le D_cl (le_iSup_of_le a le_rfl)

/-- The classical and quantum statistical distances agree on embedded distributions:
    `sdistD f g = qdist (classicalEmbed ∘ f) (classicalEmbed ∘ g)`.
    Requires d > 0. -/
theorem classicalEmbed_sdist_eq [NeZero d] (f g : α → SDistr β) :
    sdistD f g =
    qdist (fun a => classicalEmbed (f a) : α → QComp d β)
          (fun a => classicalEmbed (g a)) :=
  le_antisymm (classicalEmbed_sdist_le f g) (classicalEmbed_sdist_ge f g)

/-! ## Quantum distinguishers of embedded game outputs -/

section GameDistinguisher

open CatCrypt.Core
open CatCrypt.Crypto (prTrue Advantage AdvantageA prTrue_bind_eq_weighted)

/-- The `SPComp` distinguisher running the sub-distribution distinguisher `D` on the
output and the current heap, with the heap unchanged. -/
noncomputable def ofSDistrHeapDist (D : β × Heap → SDistr Bool) : β → SPComp Bool :=
  fun b h => (D (b, h)).map (Option.map fun x => (x, h))

/-- A sub-distribution distinguisher `D` on the run of a game from the empty heap accepts
with the probability of the `SPComp` distinguisher `ofSDistrHeapDist D` on that game. -/
theorem prTrueD_bind_eq_prTrue_bind (G : SPComp β) (D : β × Heap → SDistr Bool) :
    prTrueD (SDistr.bind (G Heap.empty) D) =
      prTrue (G.bind (ofSDistrHeapDist D)) Heap.empty := by
  have hstep : ∀ (b : β) (h' : Heap),
      prTrue (ofSDistrHeapDist D b) h' = D (b, h') (some true) := by
    intro b h'
    rw [prTrue, ofSDistrHeapDist, tsum_eq_single h' fun h hh => ?_]
    · rw [PMF.map_apply, tsum_eq_single (some true) fun o ho => ?_]
      · simp
      · rcases o with _ | _ <;> simp_all
    · rw [PMF.map_apply]
      simp [Ne.symm hh]
  rw [prTrue_bind_eq_weighted, prTrueD, SDistr.bind, PMF.bind_apply]
  refine tsum_congr fun p => ?_
  rcases p with _ | ⟨b, h'⟩
  · simp [SDistr.fail]
  · exact congrArg _ (hstep b h').symm

/-- For a quantum distinguisher `D_Q` and a state `ρ` there is one classical distinguisher
`A` such that, for any two games, the gap between the probabilities with which `D_Q`
accepts their embedded outputs from the empty heap is the advantage of `A` between them. -/
theorem exists_advantageA_eq_quantum_gap (D_Q : β × Heap → QComp d Bool)
    (ρ : DensityMatrix d) :
    ∃ A : β → SPComp Bool, ∀ G₀ G₁ : SPComp β,
      absDiff (prTrue_Q (QComp.qbind (classicalEmbed (G₀ Heap.empty)) D_Q) ρ)
          (prTrue_Q (QComp.qbind (classicalEmbed (G₁ Heap.empty)) D_Q) ρ) =
        AdvantageA G₀ G₁ A := by
  obtain ⟨D_cl, hD⟩ := quantum_classical_simulation D_Q ρ
  refine ⟨ofSDistrHeapDist D_cl, fun G₀ G₁ => ?_⟩
  rw [hD, hD, prTrueD_bind_eq_prTrue_bind, prTrueD_bind_eq_prTrue_bind]
  simp only [AdvantageA, Advantage, absDiff]

/-- A bound on the advantage of every classical distinguisher between two games bounds
the gap with which a quantum distinguisher accepts their embedded outputs, at the
classical distinguisher of `exists_advantageA_eq_quantum_gap`. -/
theorem quantum_gap_le_of_advantage (G₀ G₁ : SPComp β) (bound : (β → SPComp Bool) → ℝ≥0∞)
    (hb : ∀ A : β → SPComp Bool, AdvantageA G₀ G₁ A ≤ bound A)
    (D_Q : β × Heap → QComp d Bool) (ρ : DensityMatrix d) :
    ∃ A : β → SPComp Bool,
      absDiff (prTrue_Q (QComp.qbind (classicalEmbed (G₀ Heap.empty)) D_Q) ρ)
          (prTrue_Q (QComp.qbind (classicalEmbed (G₁ Heap.empty)) D_Q) ρ) ≤ bound A := by
  obtain ⟨A, hA⟩ := exists_advantageA_eq_quantum_gap D_Q ρ
  exact ⟨A, (hA G₀ G₁).trans_le (hb A)⟩

end GameDistinguisher

end CatCrypt.Quantum
