/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.CPCompMonad
public import CatCryptCore.Crypto.UCMonad.QuantumUC
public import CatCryptCore.Crypto.UCMonad.DiamondDominates

/-!
# UC over completely positive instruments

`CPComp d` carries a `UCMonad` instance whose distance `cpSdist` is the induced
distinguishing distance over completely positive distinguishers. Quantum games
`hon → CPComp d Bool` that end by resetting the register to a fixed state lift
to `UCEmulates` from a bound on their acceptance probabilities.

## Main definitions

* `cpSdist`: the supremum, over CP distinguishers `D`, inputs and input states,
  of the difference of the acceptance probabilities after `D`
* `instance : UCMonad (CPComp d)`: `CPComp.mapSum`, `CPComp.qfail` and `cpSdist`
* `CPComp.prFalse`: the probability of outcome `false`
* `CPComp.withReset σ₀ G`: run `G`, prepare `σ₀`, return the outcome of `G`
* `IsTotalQGame`, `QGameAdvBound`: totality of a game family and the bound on
  the difference of its acceptance probabilities
* `ofQGame`, `UCFromQGame`: the protocol of a game family and the derived UC
  statement

## Main results

* `cpSdist_eq_qdistCP`: `cpSdist` is `qdistCP` of the underlying instruments,
  so `qdistCP_le_qdistDiamond` bounds it by the diamond distance
* `prTrue_withReset_bind`: a distinguisher after a reset sees only the outcome
* `cpSdist_withReset_le`: for total games that end by a reset, `cpSdist` is at
  most the bound on the acceptance probabilities
* `ucFromQGame_of_total_adv`: the instance deriving `UCFromQGame`

## Choice of metric

`cpSdist` satisfies every obligation of `UCMonadMetric`: post-processing by a CP
instrument is again a CP distinguisher, and pre-composition is handled by
`absDiff_prTrue_Q_qbind_le`. It has no reference register, so it supports
sequential composition only; parallel composition and entangled environments
need `qdistDiamond`, which dominates it (`cpSdist_le_qdistDiamond`).
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal ComplexOrder
open CatCrypt.Quantum
open CatCrypt.Crypto.UCMonad.DiamondNorm
open CatCrypt.Crypto.UCMonad.DiamondDominates
open UCMonad

namespace CatCrypt.Crypto.UCMonad.CPCompUC

variable {d : ℕ}

/-! ## The distance -/

/-- The induced distance between CP Kleisli morphisms: the supremum over CP
distinguishers `D`, inputs `a` and input states `ρ` of the difference of the
acceptance probabilities of `f a >>= D` and `g a >>= D`. -/
noncomputable def cpSdist {α β : Type} (f g : α → CPComp d β) : ℝ≥0∞ :=
  ⨆ (D : β → CPComp d Bool) (a : α) (ρ : DensityMatrix d),
    absDiff ((f a >>= D).prTrue ρ) ((g a >>= D).prTrue ρ)

/-- `cpSdist` is `qdistCP` of the underlying instruments. -/
theorem cpSdist_eq_qdistCP {α β : Type} (f g : α → CPComp d β) :
    cpSdist f g = qdistCP (fun a => (f a).toQComp) (fun a => (g a).toQComp) := by
  apply le_antisymm
  · refine iSup_le fun D => iSup_le fun a => iSup_le fun ρ => ?_
    exact le_iSup_of_le (fun b => (D b).toQComp) (le_iSup_of_le (fun b => (D b).branch_cp)
      (le_iSup_of_le a (le_iSup_of_le ρ le_rfl)))
  · refine iSup_le fun D => iSup_le fun hD => iSup_le fun a => iSup_le fun ρ => ?_
    exact le_iSup_of_le (fun b => (⟨D b, hD b⟩ : CPComp d Bool))
      (le_iSup_of_le a (le_iSup_of_le ρ le_rfl))

/-- The diamond distance bounds `cpSdist`. -/
theorem cpSdist_le_qdistDiamond {α β : Type} (f g : α → CPComp d β) :
    cpSdist f g ≤ qdistDiamond (fun a => (f a).toQComp) (fun a => (g a).toQComp)
      (fun a => (f a).branch_cp) (fun a => (g a).branch_cp) := by
  rw [cpSdist_eq_qdistCP]
  exact qdistCP_le_qdistDiamond _ _ _ _

theorem cpSdist_self {α β : Type} (f : α → CPComp d β) : cpSdist f f = 0 := by
  simp [cpSdist, absDiff_self]

theorem cpSdist_sym {α β : Type} (f g : α → CPComp d β) :
    cpSdist f g = cpSdist g f := by
  simp only [cpSdist, absDiff_comm]

theorem cpSdist_triangle {α β : Type} (f g h : α → CPComp d β) :
    cpSdist f h ≤ cpSdist f g + cpSdist g h := by
  refine iSup_le fun D => iSup_le fun a => iSup_le fun ρ => ?_
  exact (absDiff_triangle _ _ _).trans (add_le_add
    (le_iSup_of_le D (le_iSup_of_le a (le_iSup_of_le ρ le_rfl)))
    (le_iSup_of_le D (le_iSup_of_le a (le_iSup_of_le ρ le_rfl))))

/-- Post-composition does not increase `cpSdist`. -/
theorem cpSdist_comp_right {α β γ : Type} (f g : α → CPComp d β)
    (k : β → CPComp d γ) :
    cpSdist (fun a => f a >>= k) (fun a => g a >>= k) ≤ cpSdist f g := by
  refine iSup_le fun D => iSup_le fun a => iSup_le fun ρ => ?_
  simp only [bind_assoc]
  exact le_iSup_of_le (fun b => k b >>= D) (le_iSup_of_le a (le_iSup_of_le ρ le_rfl))

/-- Pre-composition with a shared prefix does not increase `cpSdist`. -/
theorem cpSdist_comp_left {α β γ : Type} (f : α → CPComp d β)
    (g₁ g₂ : β → CPComp d γ) :
    cpSdist (fun a => f a >>= g₁) (fun a => f a >>= g₂) ≤ cpSdist g₁ g₂ := by
  refine iSup_le fun D => iSup_le fun a => iSup_le fun ρ => ?_
  simp only [bind_assoc]
  refine absDiff_prTrue_Q_qbind_le (f a).toQComp (fun b => (g₁ b >>= D).toQComp)
    (fun b => (g₂ b >>= D).toQComp) ρ (cpSdist g₁ g₂) fun b ρ' => ?_
  exact le_iSup_of_le D (le_iSup_of_le b (le_iSup_of_le ρ' le_rfl))

/-! ## The `UCMonad` instance -/

noncomputable instance : UCMonad (CPComp d) where
  ucMapSum := CPComp.mapSum
  ucMapSum_inl := CPComp.mapSum_inl
  ucMapSum_inr := CPComp.mapSum_inr
  ucMapSum_pure_pure := CPComp.mapSum_pure_pure
  ucMapSum_pure_kleisli := fun f g => CPComp.mapSum_pure_kleisli f g
  ucFail := CPComp.qfail
  ucBind_fail := fun c => CPComp.qbind_qfail c
  ucSdist := cpSdist
  ucSdist_self := cpSdist_self
  ucSdist_sym := cpSdist_sym
  ucSdist_triangle := cpSdist_triangle
  ucSdist_comp_right := cpSdist_comp_right
  ucSdist_comp_left := cpSdist_comp_left

theorem ucSdist_eq_cpSdist {α β : Type} (f g : α → CPComp d β) :
    UCMonadMetric.ucSdist f g = cpSdist f g := rfl

end CatCrypt.Crypto.UCMonad.CPCompUC

namespace CatCrypt.Quantum.CPComp

variable {d : ℕ}

/-! ## Outcome probabilities and reset -/

/-- The probability of outcome `false` of `G` run on the state `ρ`. -/
noncomputable def prFalse (G : CPComp d Bool) (ρ : DensityMatrix d) : ℝ≥0∞ :=
  ENNReal.ofReal ((G.toQComp.branch false ρ.val).trace.re)

/-- The acceptance probability of a CP instrument is at most one. -/
theorem prTrue_le_one (G : CPComp d Bool) (ρ : DensityMatrix d) : G.prTrue ρ ≤ 1 := by
  rw [prTrue_def, prTrue_Q, ENNReal.ofReal_le_one]
  have hsum := G.toQComp.branch_summable ρ.val
  calc (G.toQComp.branch true ρ.val).trace.re
      ≤ ∑' b, (G.toQComp.branch b ρ.val).trace.re :=
        (trace_re_summable hsum).le_tsum true
          (fun b _ => trace_re_nonneg_of_psd (G.toQComp.branch_psd b _ ρ.psd))
    _ = (∑' b, (G.toQComp.branch b ρ.val).trace).re :=
        (Complex.re_tsum (trace_summable hsum)).symm
    _ ≤ ρ.val.trace.re := G.toQComp.branch_stp _ ρ.psd
    _ = 1 := by rw [ρ.tr_one, Complex.one_re]

/-- Run `G`, prepare `σ₀` on the register, and return the outcome of `G`. -/
noncomputable def withReset (σ₀ : DensityMatrix d) (G : CPComp d Bool) : CPComp d Bool :=
  G >>= fun b => prep σ₀ >>= fun _ => pure b

/-- On a positive semidefinite `M`, the accepting branch of `prep σ >>= K` has
trace `tr M · Pr[K accepts σ]`. -/
theorem ofReal_trace_prep_bind_branch (σ : DensityMatrix d) (K : CPComp d Bool)
    {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.PosSemidef) :
    ENNReal.ofReal (((prep σ >>= fun _ => K).toQComp.branch true M).trace.re) =
      ENNReal.ofReal M.trace.re * K.prTrue σ := by
  have hbr : (prep σ >>= fun _ => K).toQComp.branch true M =
      M.trace • K.toQComp.branch true σ.val := by
    show (∑' _ : Unit, K.toQComp.branch true (prepMap σ.val M)) = _
    rw [tsum_fintype, Fintype.sum_unique, prepMap_apply, map_smul]
  have him : M.trace.im = 0 := trace_im_zero_of_hermitian hM.isHermitian
  rw [hbr, Matrix.trace_smul, smul_eq_mul, Complex.mul_re, him, zero_mul, sub_zero,
    ENNReal.ofReal_mul (trace_re_nonneg_of_psd hM)]
  rfl

/-- A distinguisher `D` run after `withReset σ₀ G` accepts with probability
`Pr[G = true] · Pr[D true accepts σ₀] + Pr[G = false] · Pr[D false accepts σ₀]`. -/
theorem prTrue_withReset_bind (σ₀ : DensityMatrix d) (G : CPComp d Bool)
    (D : Bool → CPComp d Bool) (ρ : DensityMatrix d) :
    (withReset σ₀ G >>= D).prTrue ρ =
      G.prTrue ρ * (D true).prTrue σ₀ + G.prFalse ρ * (D false).prTrue σ₀ := by
  have h : withReset σ₀ G >>= D = G >>= fun b => prep σ₀ >>= fun _ => D b := by
    simp only [withReset, bind_assoc, pure_bind]
  rw [h, prTrue_bind, tsum_fintype, Fintype.sum_bool,
    ofReal_trace_prep_bind_branch _ _ (G.toQComp.branch_psd _ _ ρ.psd),
    ofReal_trace_prep_bind_branch _ _ (G.toQComp.branch_psd _ _ ρ.psd)]
  rfl

end CatCrypt.Quantum.CPComp

namespace CatCrypt.Crypto.UCMonad.CPCompUC

variable {d : ℕ}

/-! ## Mixtures of two outcomes -/

/-- One direction of `absDiff_mix_le`. -/
theorem mix_le_mix_add_absDiff {a₁ b₁ a₂ b₂ p q : ℝ≥0∞} (h₁ : a₁ + b₁ = 1)
    (h₂ : a₂ + b₂ = 1) (hp : p ≤ 1) (hq : q ≤ 1) :
    a₁ * p + b₁ * q ≤ a₂ * p + b₂ * q + absDiff a₁ a₂ := by
  have ha₁ : a₁ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (h₁ ▸ le_self_add)
  have ha₂ : a₂ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (h₂ ▸ le_self_add)
  rcases le_total a₁ a₂ with h | h
  · have hb : b₁ = b₂ + (a₂ - a₁) := by
      refine (ENNReal.add_right_inj ha₁).mp ?_
      rw [h₁, ← h₂, add_comm b₂, ← add_assoc, add_tsub_cancel_of_le h, add_comm]
    rw [hb, add_mul, ← add_assoc]
    gcongr
    · exact mul_le_of_le_one_right' hq |>.trans (le_max_right _ _)
  · have hb : b₁ ≤ b₂ := by
      refine (ENNReal.add_le_add_iff_left ha₂).mp ?_
      rw [h₂, ← h₁]
      gcongr
    rw [← add_tsub_cancel_of_le h, add_mul]
    calc a₂ * p + (a₁ - a₂) * p + b₁ * q ≤ a₂ * p + b₂ * q + (a₁ - a₂) := by
          rw [add_right_comm]
          gcongr
          exact mul_le_of_le_one_right' hp
      _ ≤ a₂ * p + b₂ * q + absDiff (a₂ + (a₁ - a₂)) a₂ := by
          rw [add_tsub_cancel_of_le h]
          gcongr
          exact le_max_left _ _

/-- For two outcome distributions `(a₁, b₁)` and `(a₂, b₂)` on `Bool` and
acceptance weights `p, q ≤ 1`, the accepted masses differ by at most
`absDiff a₁ a₂`. -/
theorem absDiff_mix_le {a₁ b₁ a₂ b₂ p q : ℝ≥0∞} (h₁ : a₁ + b₁ = 1)
    (h₂ : a₂ + b₂ = 1) (hp : p ≤ 1) (hq : q ≤ 1) :
    absDiff (a₁ * p + b₁ * q) (a₂ * p + b₂ * q) ≤ absDiff a₁ a₂ :=
  absDiff_le_iff.mpr ⟨mix_le_mix_add_absDiff h₁ h₂ hp hq,
    absDiff_comm a₁ a₂ ▸ mix_le_mix_add_absDiff h₂ h₁ hp hq⟩

/-! ## Quantum games -/

/-- Every game of the family terminates: the outcomes `true` and `false` have
total probability one on every input state. -/
class IsTotalQGame {hon : Type} (G : hon → CPComp d Bool) : Prop where
  total : ∀ x (ρ : DensityMatrix d), (G x).prTrue ρ + (G x).prFalse ρ = 1

/-- The acceptance probabilities of `G_real` and `G_ideal` differ by at most `ε`,
uniformly in the honest input `x` and the input state `ρ`.

`ε` is an explicit index: it is fixed by the goal and provided by an assumption
instance, never synthesised by instance search. -/
class QGameAdvBound {hon : Type} (G_real G_ideal : hon → CPComp d Bool)
    (ε : ℝ≥0∞) : Prop where
  bound : ∀ x (ρ : DensityMatrix d),
    absDiff ((G_real x).prTrue ρ) ((G_ideal x).prTrue ρ) ≤ ε

/-- For total games that end by resetting the register to `σ₀`, the distance
between the reset games is at most the bound on their acceptance
probabilities. -/
theorem cpSdist_withReset_le {hon : Type} (σ₀ : DensityMatrix d)
    (G₁ G₂ : hon → CPComp d Bool) [IsTotalQGame G₁] [IsTotalQGame G₂] {ε : ℝ≥0∞}
    (h : ∀ x (ρ : DensityMatrix d), absDiff ((G₁ x).prTrue ρ) ((G₂ x).prTrue ρ) ≤ ε) :
    cpSdist (fun x => CPComp.withReset σ₀ (G₁ x)) (fun x => CPComp.withReset σ₀ (G₂ x))
      ≤ ε := by
  refine iSup_le fun D => iSup_le fun x => iSup_le fun ρ => ?_
  rw [CPComp.prTrue_withReset_bind, CPComp.prTrue_withReset_bind]
  exact (absDiff_mix_le (IsTotalQGame.total x ρ) (IsTotalQGame.total x ρ)
    ((D true).prTrue_le_one σ₀) ((D false).prTrue_le_one σ₀)).trans (h x ρ)

/-- The protocol of a game family: run the game, reset the register to `σ₀`,
and pass the outcome on the adversary channel `.inr`; the honest channel
carries `Unit`. -/
noncomputable def ofQGame {hon : Type} (σ₀ : DensityMatrix d)
    (G : hon → CPComp d Bool) : hon → CPComp d (Unit ⊕ Bool) :=
  fun x => CPComp.withReset σ₀ (G x) >>= fun o => pure (.inr o)

/-- The protocol of `G_real` UC-emulates the protocol of `G_ideal` with error `ε`
and view type `V`. A game family registers `IsTotalQGame` and `QGameAdvBound`
instances and obtains `.uc` by instance search. -/
class UCFromQGame {hon : Type} (σ₀ : DensityMatrix d) (G_real G_ideal : hon → CPComp d Bool)
    (V : Type) (ε : ℝ≥0∞) : Prop where
  uc : UCEmulates (T := CPComp d) (view := V) ε (ofQGame σ₀ G_real) (ofQGame σ₀ G_ideal)

/-- Total game families with a `QGameAdvBound` give
`UCFromQGame`, with the simulator equal to the adversary. -/
instance ucFromQGame_of_total_adv {hon V : Type} {σ₀ : DensityMatrix d} {ε : ℝ≥0∞}
    {G_real G_ideal : hon → CPComp d Bool}
    [IsTotalQGame G_real] [IsTotalQGame G_ideal] [QGameAdvBound G_real G_ideal ε] :
    UCFromQGame σ₀ G_real G_ideal V ε :=
  ⟨UCEmulates_of_sdist ε _ _ ((cpSdist_comp_right _ _ _).trans
    (cpSdist_withReset_le σ₀ G_real G_ideal QGameAdvBound.bound))⟩

/-- The UC statement of a game family that has a
`UCFromQGame` instance. -/
theorem ucEmulates_of_UCFromQGame {hon : Type} (σ₀ : DensityMatrix d) (V : Type)
    {ε : ℝ≥0∞} (G_real G_ideal : hon → CPComp d Bool) [UCFromQGame σ₀ G_real G_ideal V ε] :
    UCEmulates (T := CPComp d) (view := V) ε (ofQGame σ₀ G_real) (ofQGame σ₀ G_ideal) :=
  UCFromQGame.uc

end CatCrypt.Crypto.UCMonad.CPCompUC
