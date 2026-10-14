/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.CPInstrument
public import CatCryptCore.Quantum.ClassicalDiamondLift
public import CatCryptCore.Quantum.Measurement
public import CatCryptCore.Quantum.UnitaryChannel

@[expose] public section

set_option autoImplicit false

/-!
# Completely positive instruments as a programming language

`CPComp d` is a lawful monad, with the readout `CPComp.prTrue` and the
constructors of a quantum game: unitaries, measurements, classical sampling
and state preparation, each with its complete-positivity proof.

## Main definitions

* `Monad (CPComp d)`, `LawfulMonad (CPComp d)`: the Kleisli structure of
  `CPComp.qpure` and `CPComp.qbind`
* `CPComp.prTrue`: the probability of outcome `true`, `prTrue_Q` of the
  underlying instrument
* `CPComp.unitary`, `CPComp.measProj`, `CPComp.measureOps`, `CPComp.ofKraus`:
  unitary evolution and measurements
* `CPComp.sample`: a classical sub-distribution, embedded by `classicalEmbed`
* `prepMap`, `QComp.prep`, `CPComp.prep`: the replacement channel
  `ρ ↦ tr(ρ) • σ` onto a density matrix `σ`
* `CPComp.mapSum`: parallel composition on a sum type

## Main results

* `isCPMap_krausSum`: Kraus sums `ρ ↦ ∑ K ρ Kᴴ` are completely positive
* `prepMap_isCPMap`: the replacement channel is completely positive
* `CPComp.prTrue_bind`: `prTrue` of a bind as a sum over the first outcome
* `CPComp.prTrue_sample_bind`, `CPComp.prTrue_sample_uniform_bind`: sampling
  averages `prTrue` of the continuation
* `CPComp.prTrue_prep_bind`: preparing `σ` and running `G` has the readout of
  `G` at `σ`
* `CPComp.mapSum_pure_pure`, `CPComp.mapSum_pure_kleisli`: the functoriality
  laws of `mapSum`
-/

open scoped Matrix ComplexOrder ENNReal Kronecker
open Matrix

noncomputable section

namespace CatCrypt.Quantum

open CatCrypt.Prob
open CatCrypt.Quantum.TensorProduct
open CatCrypt.Crypto.IrisBridge (measureProj measureProj_branch_isCPMap)
open CatCrypt.Quantum.GentleMeasurement (Projector)

/-! ## Sums of completely positive maps -/

section Sums

variable {n : ℕ}

theorem tensorIdMap_add
    (Φ Ψ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    tensorIdMap (Φ + Ψ) k = tensorIdMap Φ k + tensorIdMap Ψ k :=
  LinearMap.ext fun _ => rfl

/-- A map given by a finite Kraus sum `ρ ↦ ∑ i, K i * ρ * (K i)ᴴ` is
completely positive. -/
theorem isCPMap_krausSum {ι : Type*} [Fintype ι]
    (K : ι → Matrix (Fin n) (Fin n) ℂ)
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hΦ : ∀ ρ, Φ ρ = ∑ i, K i * ρ * (K i)ᴴ) : IsCPMap Φ := by
  have h : Φ = ∑ i, UnitaryChannel.conjugate (K i) := by
    refine LinearMap.ext fun ρ => ?_
    rw [hΦ, LinearMap.sum_apply]
    rfl
  rw [h]
  exact isCPMap_sum _ _ fun i _ => isCPMap_conj (K i) _ fun _ => rfl

end Sums

/-! ## The replacement channel -/

section Prep

variable {d : ℕ}

/-- The replacement channel `ρ ↦ tr(ρ) • σ`. -/
def prepMap (σ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
  (Matrix.traceLinearMap (Fin d) ℂ ℂ).smulRight σ

@[simp]
theorem prepMap_apply (σ ρ : Matrix (Fin d) (Fin d) ℂ) :
    prepMap σ ρ = ρ.trace • σ := rfl

/-- The replacement channel onto a positive semidefinite `σ` is completely
positive: `id_k ⊗ prepMap σ` sends `M` to `Tr₂(M) ⊗ₖ σ`, the Kronecker
product of the partial trace of `M` with `σ`. -/
theorem prepMap_isCPMap {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : σ.PosSemidef) :
    IsCPMap (prepMap σ) := by
  intro k M hM
  set T : Matrix (Fin k) (Fin k) ℂ :=
    ∑ i : Fin d, M.submatrix (fun a => (a, i)) (fun a => (a, i)) with hT
  have hTpsd : T.PosSemidef :=
    posSemidef_sum _ fun i _ => hM.submatrix (fun a => (a, i))
  have key : tensorIdMap (prepMap σ) k M = Matrix.kroneckerMap (· * ·) T σ := by
    funext p q
    rw [tensorIdMap_apply, prepMap_apply, Matrix.kronecker_apply, hT]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.submatrix_apply,
      Matrix.trace, Matrix.diag, blockMatrix]
  rw [key]
  exact hTpsd.kronecker hσ

/-- The state preparation instrument: one outcome, branch `ρ ↦ tr(ρ) • σ`. -/
def QComp.prep (σ : DensityMatrix d) : QComp d Unit where
  branch _ := prepMap σ.val
  branch_psd _ ρ hρ := σ.psd.smul hρ.trace_nonneg
  branch_summable _ := (hasSum_fintype _).summable
  branch_stp ρ _ := by
    rw [tsum_fintype, Fintype.sum_unique, prepMap_apply, trace_smul, σ.tr_one,
      smul_eq_mul, mul_one]

end Prep

/-! ## Monad instance -/

namespace CPComp

variable {d : ℕ} {α β γ δ : Type}

instance : Monad (CPComp d) where
  pure := CPComp.qpure
  bind := CPComp.qbind

instance : LawfulMonad (CPComp d) := LawfulMonad.mk'
  (id_map := fun m => CPComp.qbind_qpure m)
  (pure_bind := fun a f => CPComp.qpure_qbind a f)
  (bind_assoc := fun m f g => CPComp.qbind_assoc m f g)

theorem pure_eq_qpure (a : α) : (pure a : CPComp d α) = qpure a := rfl

theorem bind_eq_qbind (C : CPComp d α) (f : α → CPComp d β) :
    C >>= f = C.qbind f := rfl

theorem toQComp_pure (a : α) :
    (pure a : CPComp d α).toQComp = pure a := rfl

theorem toQComp_bind (C : CPComp d α) (f : α → CPComp d β) :
    (C >>= f).toQComp = C.toQComp >>= fun a => (f a).toQComp := rfl

theorem qbind_qfail (C : CPComp d α) :
    C.qbind (fun _ => (qfail : CPComp d β)) = qfail :=
  ext (QComp.qbind_fail C.toQComp)

theorem qfail_qbind (f : α → CPComp d β) :
    (qfail : CPComp d α).qbind f = qfail :=
  ext (QComp.qfail_qbind _)

/-! ## Readout -/

/-- The probability of outcome `true` of `G` run on the state `ρ`. -/
def prTrue (G : CPComp d Bool) (ρ : DensityMatrix d) : ℝ≥0∞ :=
  prTrue_Q G.toQComp ρ

theorem prTrue_def (G : CPComp d Bool) (ρ : DensityMatrix d) :
    G.prTrue ρ = prTrue_Q G.toQComp ρ := rfl

@[simp]
theorem prTrue_pure_true (ρ : DensityMatrix d) :
    (pure true : CPComp d Bool).prTrue ρ = 1 := by
  rw [pure_eq_qpure, prTrue_def, toQComp_qpure]
  simp [prTrue_Q, QComp.qpure, ρ.tr_one]

@[simp]
theorem prTrue_pure_false (ρ : DensityMatrix d) :
    (pure false : CPComp d Bool).prTrue ρ = 0 := by
  rw [pure_eq_qpure, prTrue_def, toQComp_qpure]
  simp [prTrue_Q, QComp.qpure]

/-- `prTrue` of a bind is the sum, over the outcome `a` of `C`, of the
probability that the continuation `f a` accepts the unnormalised post-state of
branch `a`. -/
theorem prTrue_bind (C : CPComp d α) (f : α → CPComp d Bool) (ρ : DensityMatrix d) :
    (C >>= f).prTrue ρ = ∑' a, ENNReal.ofReal
      (((f a).toQComp.branch true (C.toQComp.branch a ρ.val)).trace.re) := by
  have hsum := QComp.bind_summable C.toQComp (fun a => (f a).toQComp) true ρ.val
  have hnn : ∀ a, 0 ≤ ((f a).toQComp.branch true (C.toQComp.branch a ρ.val)).trace.re :=
    fun a => trace_re_nonneg_of_psd
      ((f a).toQComp.branch_psd true _ (C.toQComp.branch_psd a ρ.val ρ.psd))
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn (trace_re_summable hsum)]
  show ENNReal.ofReal (∑' a, (f a).toQComp.branch true (C.toQComp.branch a ρ.val)).trace.re = _
  rw [trace_tsum hsum, Complex.re_tsum (trace_summable hsum)]

/-! ## Unitaries and measurements -/

/-- Unitary evolution `ρ ↦ U ρ Uᴴ`. -/
def unitary (U : Matrix.unitaryGroup (Fin d) ℂ) : CPComp d Unit where
  toQComp := UnitaryChannel.unitaryChannel U
  branch_cp _ := isCPMap_conj (U : Matrix (Fin d) (Fin d) ℂ) _ fun _ => rfl

@[simp]
theorem toQComp_unitary (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (unitary U).toQComp = UnitaryChannel.unitaryChannel U := rfl

/-- The two-outcome projective measurement `{P, 1 - P}`: outcome `true` is
`ρ ↦ P ρ P`, outcome `false` is `ρ ↦ (1 - P) ρ (1 - P)`. -/
def measProj (P : Projector d) : CPComp d Bool where
  toQComp := measureProj P
  branch_cp := measureProj_branch_isCPMap P

@[simp]
theorem toQComp_measProj (P : Projector d) :
    (measProj P).toQComp = measureProj P := rfl

end CPComp

/-- Each branch of the instrument of a family of measurement operators is
conjugation by its operator, hence completely positive. -/
theorem Measurement.measureOps_branch_isCPMap {d : ℕ} {α : Type} [Fintype α]
    (M : Measurement.MeasurementOps d α) (a : α) :
    IsCPMap ((Measurement.measureOps M).branch a) :=
  isCPMap_conj (M.op a) _ fun _ => rfl

/-- Each branch of `QComp.ofKraus M` is conjugation by `M a`, hence completely
positive. -/
theorem QComp.ofKraus_branch_isCPMap {d : ℕ} {α : Type} [Fintype α]
    (M : α → Matrix (Fin d) (Fin d) ℂ) (h : ∑ a, (M a)ᴴ * M a = 1) (a : α) :
    IsCPMap ((QComp.ofKraus M h).branch a) :=
  isCPMap_conj (M a) _ fun _ => rfl

namespace CPComp

variable {d : ℕ} {α β γ δ : Type}

/-- The instrument of a family of measurement operators `{M_a}`: branch `a` is
`ρ ↦ M_a ρ M_aᴴ`. -/
def measureOps [Fintype α] (M : Measurement.MeasurementOps d α) : CPComp d α where
  toQComp := Measurement.measureOps M
  branch_cp := Measurement.measureOps_branch_isCPMap M

@[simp]
theorem toQComp_measureOps [Fintype α] (M : Measurement.MeasurementOps d α) :
    (measureOps M).toQComp = Measurement.measureOps M := rfl

/-- The instrument with one Kraus operator per outcome: branch `a` is
`ρ ↦ M a * ρ * (M a)ᴴ`. -/
def ofKraus [Fintype α] (M : α → Matrix (Fin d) (Fin d) ℂ)
    (h : ∑ a, (M a)ᴴ * M a = 1) : CPComp d α where
  toQComp := QComp.ofKraus M h
  branch_cp := QComp.ofKraus_branch_isCPMap M h

@[simp]
theorem toQComp_ofKraus [Fintype α] (M : α → Matrix (Fin d) (Fin d) ℂ)
    (h : ∑ a, (M a)ᴴ * M a = 1) :
    (ofKraus M h).toQComp = QComp.ofKraus M h := rfl

/-! ## Classical sampling -/

/-- Sampling from a classical sub-distribution: branch `a` scales the state
by `μ (some a)`. -/
def sample (μ : SDistr α) : CPComp d α where
  toQComp := classicalEmbed μ
  branch_cp := ClassicalDiamondLift.classicalEmbed_isCPMap μ

@[simp]
theorem toQComp_sample (μ : SDistr α) :
    (sample (d := d) μ).toQComp = classicalEmbed μ := rfl

theorem sample_pure (a : α) : sample (d := d) (SDistr.pure a) = pure a :=
  ext (classicalEmbed_pure a)

theorem sample_bind (μ : SDistr α) (f : α → SDistr β) :
    sample (d := d) (SDistr.bind μ f) = sample μ >>= fun a => sample (f a) :=
  ext (classicalEmbed_bind μ f)

/-- Sampling `a` from `μ` and running `f a` accepts with the `μ`-weighted sum
of the acceptance probabilities of the `f a`. -/
theorem prTrue_sample_bind (μ : SDistr α) (f : α → CPComp d Bool)
    (ρ : DensityMatrix d) :
    (sample μ >>= f).prTrue ρ = ∑' a, μ (some a) * (f a).prTrue ρ := by
  rw [prTrue_bind]
  refine tsum_congr fun a => ?_
  show ENNReal.ofReal (((f a).toQComp.branch true
      (((μ (some a)).toReal : ℂ) • ρ.val)).trace.re) = _
  rw [map_smul, trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one μ _))]
  rfl

/-- Sampling uniformly from a finite type averages the acceptance
probabilities; the right-hand side is the uniform average `avg` of
`CatCrypt.Crypto.MLKEM.PRFOracle`, unfolded. -/
theorem prTrue_sample_uniform_bind [Fintype α] [Nonempty α]
    (f : α → CPComp d Bool) (ρ : DensityMatrix d) :
    (sample (SDistr.uniform α) >>= f).prTrue ρ =
      ∑ x, (Fintype.card α : ℝ≥0∞)⁻¹ * (f x).prTrue ρ := by
  rw [prTrue_sample_bind, tsum_fintype]
  simp only [SDistr.uniform_apply_some]

/-! ## State preparation -/

/-- Preparing the density matrix `σ`: the replacement channel `ρ ↦ tr(ρ) • σ`
with a single outcome. -/
def prep (σ : DensityMatrix d) : CPComp d Unit where
  toQComp := QComp.prep σ
  branch_cp _ := prepMap_isCPMap σ.psd

@[simp]
theorem toQComp_prep (σ : DensityMatrix d) : (prep σ).toQComp = QComp.prep σ := rfl

/-- Preparing `σ` and then running `G` accepts with the probability that `G`
accepts `σ`, on every input state. -/
theorem prTrue_prep_bind (σ : DensityMatrix d) (G : CPComp d Bool)
    (ρ : DensityMatrix d) :
    (prep σ >>= fun _ => G).prTrue ρ = G.prTrue σ := by
  rw [prTrue_bind, tsum_fintype, Fintype.sum_unique]
  show ENNReal.ofReal ((G.toQComp.branch true (prepMap σ.val ρ.val)).trace.re) = _
  rw [prepMap_apply, ρ.tr_one, one_smul]
  rfl

/-! ## Parallel composition on sums -/

/-- `mapSum f g` runs `f` on a left input and `g` on a right input, tagging the
outcome with the same side. -/
def mapSum (f : α → CPComp d β) (g : γ → CPComp d δ) : α ⊕ γ → CPComp d (β ⊕ δ)
  | .inl a => f a >>= fun b => pure (.inl b)
  | .inr c => g c >>= fun d' => pure (.inr d')

theorem mapSum_inl (f : α → CPComp d β) (g : γ → CPComp d δ) (a : α) :
    mapSum f g (.inl a) = f a >>= fun b => pure (.inl b) := rfl

theorem mapSum_inr (f : α → CPComp d β) (g : γ → CPComp d δ) (c : γ) :
    mapSum f g (.inr c) = g c >>= fun d' => pure (.inr d') := rfl

theorem toQComp_mapSum (f : α → CPComp d β) (g : γ → CPComp d δ) (x : α ⊕ γ) :
    (mapSum f g x).toQComp =
      QComp.mapSum (fun a => (f a).toQComp) (fun c => (g c).toQComp) x := by
  cases x <;> rfl

theorem mapSum_pure_pure :
    mapSum (pure : α → CPComp d α) (pure : β → CPComp d β) = pure := by
  funext x
  cases x <;> exact pure_bind _ _

theorem mapSum_pure_kleisli (f : β → CPComp d γ) (g : γ → CPComp d δ) :
    (fun x : α ⊕ β => mapSum pure f x >>= mapSum pure g) =
      mapSum pure (fun b => f b >>= g) := by
  funext x
  cases x with
  | inl a => simp only [mapSum, pure_bind]
  | inr b => simp only [mapSum, bind_assoc, pure_bind]

end CPComp

end CatCrypt.Quantum

end
