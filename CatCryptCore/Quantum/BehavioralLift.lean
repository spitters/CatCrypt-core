/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.ClassicalDiamondLift
public import CatCryptCore.Quantum.CPInstrument
public import CatCryptCore.Crypto.OracleAdversaryTimed
public import CatCryptCore.Crypto.Assumptions.CDH

@[expose] public section

set_option autoImplicit false

/-!
# Behavioral strategies of quantum adversaries with classical interfaces

A quantum adversary with a classical interface is a family `A : X → CPComp d Y` of
completely positive instruments acting on one `d`-dimensional register, started from a
density matrix `ρ`. A game or reduction that calls such an adversary is an oracle tree
`T : OracleAdv X Y α` whose `query` nodes are the calls; `interpQ A T` runs it with the
quantum adversary, so successive calls act on the evolving register.

## Main definitions

* `CPComp.outProb`, `CPComp.outD`: the output sub-distribution of an instrument run from a
  density matrix (the Born rule)
* `CPComp.postState`: the normalised post-measurement state after outcome `a`
* `CPComp.behav`: the classical stateless behaviour `x ↦ outD (A x) ρ` of a one-shot adversary
* `behavOracle`: the classical stateful strategy of a multi-round adversary, whose state is the
  posterior density matrix
* `interpQ`: the interpretation of an oracle tree with a quantum adversary
* `OracleAdv.runD`, `OracleAdv.outRunD`: the run of an oracle tree against a classical
  sub-distributional stateful oracle, and its output marginal
* `qGap`, `cGap`: the gap between two Boolean game trees, against a quantum adversary and
  against a classical stateful oracle

## Main results

* `outD_interpQ`: for every tree, the output distribution of the quantum run equals the output
  marginal of the classical run against `behavOracle A`
* `outD_interpQ_of_isQueryBound_one`: for a tree with at most one call, the stateless
  behaviour `A.behav ρ` suffices
* `interpQ_simulate`: a tree whose calls are answered by a stateless reduction `B` runs, with
  the quantum adversary `A`, as the outer tree with the quantum adversary `interpQ A ∘ B`
* `qGap_le_of_cGap_le`: a classical per-adversary bound between game trees, over all classical
  stateful oracles, holds for every quantum adversary and every initial state
* `qGap_simulate_le_of_cGap_le`: the same with the right-hand side the primitive game run against
  the quantum reduction `interpQ A ∘ B`
* `timeBound_chargeCalls`: a timed reduction of time `T` with every adversary call charged `c`
  has time at most `T + T * c`
* `cdh_le_ddh_quantum`: `cdh_le_ddh` for quantum CDH adversaries, with the DDH gap of the
  quantum reduction `x ↦ interpQ A (ddhOfCdhTree x)` on the right

## Adversary model

Each call of the adversary takes and returns a classical message. The adversary keeps quantum
memory between calls on its register; `behavOracle` carries that memory as the posterior
density matrix, the state of a classical stateful strategy.

## References

* [Song, A Note on Quantum Security for Post-Quantum Cryptography, PQCrypto 2014]
-/

open scoped ENNReal ComplexOrder
open Matrix

noncomputable section

namespace CatCrypt.Quantum

open CatCrypt.Prob CatCrypt.Crypto

variable {d : ℕ} {α β X Y X' Y' : Type}

/-! ## Sub-distributions from weights -/

/-- The sub-distribution with weight `w a` on `some a` and the missing mass on `none`. -/
def subDistr (w : α → ℝ≥0∞) (hw : ∑' a, w a ≤ 1) : SDistr α :=
  ⟨fun o => o.elim (1 - ∑' a, w a) w, ENNReal.summable.hasSum_iff.mpr (by
    rw [SDistr.tsum_option_eq_add]
    exact tsub_add_cancel_of_le hw)⟩

theorem subDistr_some (w : α → ℝ≥0∞) (hw : ∑' a, w a ≤ 1) (a : α) :
    subDistr w hw (some a) = w a := rfl

/-- The weight of `some b` under a bind is the sum over the first outcome. -/
theorem sdistr_bind_apply_some (μ : SDistr α) (f : α → SDistr β) (b : β) :
    μ.bind f (some b) = ∑' a, μ (some a) * f a (some b) := by
  rw [SDistr.bind, PMF.bind_apply, SDistr.tsum_option_eq_add]
  simp [SDistr.fail_apply_some]

/-! ## Output distribution and post-measurement state -/

namespace CPComp

/-- The probability of outcome `a` when `C` runs on `ρ`. -/
def outProb (C : CPComp d α) (ρ : DensityMatrix d) (a : α) : ℝ≥0∞ :=
  ENNReal.ofReal ((C.toQComp.branch a ρ.val).trace.re)

theorem tsum_outProb_le (C : CPComp d α) (ρ : DensityMatrix d) :
    ∑' a, C.outProb ρ a ≤ 1 := by
  have hs := C.toQComp.branch_summable ρ.val
  have hnn : ∀ a, 0 ≤ (C.toQComp.branch a ρ.val).trace.re :=
    fun a => trace_re_nonneg_of_psd (C.toQComp.branch_psd a _ ρ.psd)
  unfold outProb
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn (trace_re_summable hs),
    ← Complex.re_tsum (trace_summable hs)]
  have h := C.toQComp.branch_stp ρ.val ρ.psd
  rw [ρ.tr_one, Complex.one_re] at h
  exact ENNReal.ofReal_le_one.mpr h

/-- The output sub-distribution of `C` run on `ρ` (the Born rule). -/
def outD (C : CPComp d α) (ρ : DensityMatrix d) : SDistr α :=
  subDistr (C.outProb ρ) (C.tsum_outProb_le ρ)

theorem outD_some (C : CPComp d α) (ρ : DensityMatrix d) (a : α) :
    C.outD ρ (some a) = C.outProb ρ a := rfl

/-- The classical behaviour of a one-shot quantum adversary started from `ρ`: on input `x`
it outputs the outcome distribution of `A x` on `ρ`. -/
def behav (A : X → CPComp d Y) (ρ : DensityMatrix d) : X → SDistr Y :=
  fun x => (A x).outD ρ

/-- A positive semidefinite matrix has real trace. -/
theorem trace_eq_ofReal_re {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.PosSemidef) :
    M.trace = (M.trace.re : ℂ) :=
  Complex.eq_re_of_ofReal_le (by rw [Complex.ofReal_zero]; exact hM.trace_nonneg)

/-- A positive semidefinite matrix of nonzero trace, divided by its trace, has trace one. -/
theorem trace_inv_trace_re_smul {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.PosSemidef)
    (h : M.trace.re ≠ 0) : ((M.trace.re)⁻¹ • M).trace = 1 := by
  rw [trace_smul, Complex.real_smul]
  generalize hz : M.trace = z
  have hz' : z = (z.re : ℂ) := hz ▸ trace_eq_ofReal_re hM
  rw [hz] at h
  rw [hz', Complex.ofReal_re, ← Complex.ofReal_mul, inv_mul_cancel₀ h, Complex.ofReal_one]

/-- The normalised state after outcome `a` of `C` on `ρ`; `ρ` itself when the outcome has
probability zero. -/
def postState (C : CPComp d α) (ρ : DensityMatrix d) (a : α) : DensityMatrix d :=
  if h : (C.toQComp.branch a ρ.val).trace.re = 0 then ρ else
    { val := ((C.toQComp.branch a ρ.val).trace.re)⁻¹ • C.toQComp.branch a ρ.val
      psd := (C.toQComp.branch_psd a _ ρ.psd).smul
        (inv_nonneg.mpr (trace_re_nonneg_of_psd (C.toQComp.branch_psd a _ ρ.psd)))
      tr_one := trace_inv_trace_re_smul (C.toQComp.branch_psd a _ ρ.psd) h }

/-- The unnormalised post-measurement state is the outcome probability times the
normalised one. -/
theorem branch_eq_smul_postState (C : CPComp d α) (ρ : DensityMatrix d) (a : α) :
    C.toQComp.branch a ρ.val =
      (C.toQComp.branch a ρ.val).trace.re • (C.postState ρ a).val := by
  have hpsd := C.toQComp.branch_psd a _ ρ.psd
  unfold postState
  split_ifs with h
  · rw [h, zero_smul]
    exact hpsd.trace_eq_zero_iff.mp (by rw [trace_eq_ofReal_re hpsd, h, Complex.ofReal_zero])
  · show _ = _ • (_ • _)
    rw [smul_smul, mul_inv_cancel₀ h, one_smul]

/-- Running `Φ` on a state scaled by `p ≥ 0` scales the readout by `p`. -/
theorem ofReal_trace_re_smul (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    {p : ℝ} (hp : 0 ≤ p) (M : Matrix (Fin d) (Fin d) ℂ) :
    ENNReal.ofReal (Φ (p • M)).trace.re =
      ENNReal.ofReal p * ENNReal.ofReal (Φ M).trace.re := by
  rw [LinearMap.map_smul_of_tower, trace_smul, Complex.smul_re, smul_eq_mul,
    ENNReal.ofReal_mul hp]

/-- The probability of outcome `b` of a Kleisli composite is the sum over the first outcome. -/
theorem outProb_qbind (C : CPComp d α) (f : α → CPComp d β) (ρ : DensityMatrix d) (b : β) :
    (C.qbind f).outProb ρ b = ∑' a, ENNReal.ofReal
      (((f a).toQComp.branch b (C.toQComp.branch a ρ.val)).trace.re) := by
  have hsum := QComp.bind_summable C.toQComp (fun a => (f a).toQComp) b ρ.val
  have hnn : ∀ a, 0 ≤ ((f a).toQComp.branch b (C.toQComp.branch a ρ.val)).trace.re :=
    fun a => trace_re_nonneg_of_psd
      ((f a).toQComp.branch_psd b _ (C.toQComp.branch_psd a ρ.val ρ.psd))
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn (trace_re_summable hsum), outProb, toQComp_qbind]
  change ENNReal.ofReal (∑' a, (f a).toQComp.branch b (C.toQComp.branch a ρ.val)).trace.re = _
  rw [trace_tsum hsum, Complex.re_tsum (trace_summable hsum)]

/-- The probability of outcome `b` of a Kleisli composite: the first outcome `a` weighted by
its probability, then `f a` on the post-measurement state. -/
theorem outProb_qbind_postState (C : CPComp d α) (f : α → CPComp d β) (ρ : DensityMatrix d)
    (b : β) : (C.qbind f).outProb ρ b =
      ∑' a, C.outProb ρ a * (f a).outProb (C.postState ρ a) b := by
  rw [outProb_qbind]
  refine tsum_congr fun a => ?_
  rw [branch_eq_smul_postState C ρ a, ofReal_trace_re_smul _
    (trace_re_nonneg_of_psd (C.toQComp.branch_psd a _ ρ.psd))]
  rfl

/-- Sampling from a classical sub-distribution, as a completely positive instrument. -/
def sampleD (μ : SDistr α) : CPComp d α :=
  mk' (classicalEmbed μ) (ClassicalDiamondLift.classicalEmbed_isCPMap μ)

/-- Sampling `a` from `μ` and running `f a` gives outcome `b` with the `μ`-weighted sum of the
probabilities of `b` under the `f a`. -/
theorem outProb_sampleD_qbind (μ : SDistr α) (f : α → CPComp d β) (ρ : DensityMatrix d)
    (b : β) : ((sampleD μ).qbind f).outProb ρ b = ∑' a, μ (some a) * (f a).outProb ρ b := by
  rw [outProb_qbind]
  refine tsum_congr fun a => ?_
  rw [sampleD, toQComp_mk']
  change ENNReal.ofReal (((f a).toQComp.branch b
      (((μ (some a)).toReal : ℂ) • ρ.val)).trace.re) = _
  rw [Complex.coe_smul, ofReal_trace_re_smul _ ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one μ _))]
  rfl

theorem outProb_qpure (a b : α) (ρ : DensityMatrix d) :
    (qpure a : CPComp d α).outProb ρ b = SDistr.pure a (some b) := by
  classical
  unfold outProb
  rw [SDistr.pure_apply_some, toQComp_qpure]
  change ENNReal.ofReal ((if b = a then LinearMap.id else 0 :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) ρ.val).trace.re = _
  by_cases h : b = a
  · subst h; simp [ρ.tr_one]
  · simp [h, Ne.symm h]

end CPComp

/-! ## Oracle trees with a quantum adversary -/

/-- The run of an oracle tree with the quantum adversary `A`: each `query x` node applies the
instrument `A x` to the shared register, each `rand p` node samples classically. -/
def interpQ (A : X → CPComp d Y) : OracleAdv X Y α → CPComp d α
  | .ret a => CPComp.qpure a
  | .rand p k => (CPComp.sampleD (p.map some)).qbind fun b => interpQ A (k b)
  | .query x k => (A x).qbind fun y => interpQ A (k y)

namespace OracleAdv

/-- The joint sub-distribution of the output and the final oracle state when `T` runs against
the stateful sub-distributional oracle `O` from state `s` (the sub-distributional form of
`OracleAdv.run`). -/
def runD {S : Type} (O : S → X → SDistr (Y × S)) : OracleAdv X Y α → S → SDistr (α × S)
  | .ret a, s => SDistr.pure (a, s)
  | .rand p k, s => SDistr.bind (p.map some) fun b => runD O (k b) s
  | .query x k, s => SDistr.bind (O s x) fun r => runD O (k r.1) r.2

/-- The output marginal of `runD`. -/
def outRunD {S : Type} (O : S → X → SDistr (Y × S)) (T : OracleAdv X Y α) (s : S) :
    SDistr α :=
  SDistr.bind (runD O T s) fun r => SDistr.pure r.1

theorem outRunD_ret {S : Type} (O : S → X → SDistr (Y × S)) (a : α) (s : S) :
    outRunD O (.ret a) s = SDistr.pure a := by
  simp [outRunD, runD, SDistr.pure_bind]

theorem outRunD_rand {S β : Type} (O : S → X → SDistr (Y × S)) (p : PMF β)
    (k : β → OracleAdv X Y α) (s : S) :
    outRunD O (.rand p k) s = SDistr.bind (p.map some) fun b => outRunD O (k b) s := by
  simp only [outRunD, runD, SDistr.bind_assoc]

theorem outRunD_query {S : Type} (O : S → X → SDistr (Y × S)) (x : X)
    (k : Y → OracleAdv X Y α) (s : S) :
    outRunD O (.query x k) s = SDistr.bind (O s x) fun r => outRunD O (k r.1) r.2 := by
  simp only [outRunD, runD, SDistr.bind_assoc]

end OracleAdv

open OracleAdv

/-- The classical stateful strategy of the quantum adversary `A`: from the posterior state
`ρ`, on input `x` it outputs `y` with the Born probability of `A x` on `ρ` and moves to the
post-measurement state. -/
def behavOracle (A : X → CPComp d Y) (ρ : DensityMatrix d) (x : X) :
    SDistr (Y × DensityMatrix d) :=
  SDistr.bind ((A x).outD ρ) fun y => SDistr.pure (y, (A x).postState ρ y)

/-- **Behavioral strategy.** For every oracle tree `T`, the output distribution of `T` run
with the quantum adversary `A` from `ρ` is the output marginal of `T` run against the
classical strategy `behavOracle A`, whose state is the posterior density matrix. -/
theorem outD_interpQ (A : X → CPComp d Y) (T : OracleAdv X Y α) (ρ : DensityMatrix d) :
    (interpQ A T).outD ρ = outRunD (behavOracle A) T ρ := by
  induction T generalizing ρ with
  | ret a =>
    refine SDistr.eq_of_some_eq fun b => ?_
    rw [CPComp.outD_some, outRunD_ret]
    exact CPComp.outProb_qpure a b ρ
  | rand p k ih =>
    refine SDistr.eq_of_some_eq fun b => ?_
    rw [CPComp.outD_some, outRunD_rand, sdistr_bind_apply_some]
    simp only [interpQ, CPComp.outProb_sampleD_qbind, ← ih, CPComp.outD_some]
  | query x k ih =>
    refine SDistr.eq_of_some_eq fun b => ?_
    rw [CPComp.outD_some, outRunD_query, behavOracle, SDistr.bind_assoc]
    simp only [SDistr.pure_bind]
    rw [sdistr_bind_apply_some]
    simp only [interpQ, CPComp.outProb_qbind_postState, ← ih, CPComp.outD_some]

/-! ## One-shot adversaries -/

/-- The stateless oracle answering `x` from the sub-distribution `f x`. -/
def statelessOracle (f : X → SDistr Y) : Unit → X → SDistr (Y × Unit) :=
  fun _ x => SDistr.bind (f x) fun y => SDistr.pure (y, ())

/-- A tree without queries has an output marginal independent of the oracle and its state. -/
theorem outRunD_eq_of_isQueryBound_zero {S S' : Type} (O : S → X → SDistr (Y × S))
    (O' : S' → X → SDistr (Y × S')) {T : OracleAdv X Y α} (hT : T.IsQueryBound 0) (s : S)
    (s' : S') : outRunD O T s = outRunD O' T s' := by
  induction T with
  | ret a => rw [outRunD_ret, outRunD_ret]
  | rand p k ih =>
    rw [outRunD_rand, outRunD_rand]
    exact congrArg _ (funext fun b => ih b (hT b))
  | query x k ih => exact (hT : False).elim

/-- **One-shot behavioral strategy.** For a tree calling the adversary at most once, the
output distribution of the quantum run from `ρ` is the output marginal of the classical run
against the stateless behaviour `CPComp.behav A ρ`. -/
theorem outD_interpQ_of_isQueryBound_one (A : X → CPComp d Y) {T : OracleAdv X Y α}
    (hT : T.IsQueryBound 1) (ρ : DensityMatrix d) :
    (interpQ A T).outD ρ = outRunD (statelessOracle (CPComp.behav A ρ)) T () := by
  rw [outD_interpQ]
  induction T with
  | ret a => rw [outRunD_ret, outRunD_ret]
  | rand p k ih =>
    rw [outRunD_rand, outRunD_rand]
    exact congrArg _ (funext fun b => ih b (hT b))
  | query x k ih =>
    rw [outRunD_query, outRunD_query, behavOracle, statelessOracle, SDistr.bind_assoc,
      SDistr.bind_assoc]
    simp only [SDistr.pure_bind]
    exact congrArg _ (funext fun y => outRunD_eq_of_isQueryBound_zero _ _ (hT y) _ _)

/-! ## Substituting a reduction for the adversary calls -/

namespace OracleAdv

/-- The tree `Q` with each call `x'` answered by the stateless reduction tree `B x'`, whose own
calls go to the adversary. -/
def substQ (B : X' → OracleAdv X Y Y') : OracleAdv X' Y' α → OracleAdv X Y α
  | .ret a => .ret a
  | .rand p k => .rand p fun b => substQ B (k b)
  | .query x' k => (B x').bind fun y' => substQ B (k y')

end OracleAdv

/-- The quantum run of a sequenced tree is the Kleisli composite of the quantum runs. -/
theorem interpQ_bind (A : X → CPComp d Y) (T : OracleAdv X Y α) (f : α → OracleAdv X Y β) :
    interpQ A (T.bind f) = (interpQ A T).qbind fun a => interpQ A (f a) := by
  induction T with
  | ret a => exact (CPComp.qpure_qbind a fun a => interpQ A (f a)).symm
  | rand p k ih =>
    simp only [OracleAdv.bind, interpQ, CPComp.qbind_assoc, ih]
  | query x k ih =>
    simp only [OracleAdv.bind, interpQ, CPComp.qbind_assoc, ih]

/-- Running `Q` with each call answered by the reduction `B`, all with the quantum adversary
`A`, is running `Q` with the quantum adversary `x' ↦ interpQ A (B x')`. -/
theorem interpQ_substQ (A : X → CPComp d Y) (B : X' → OracleAdv X Y Y')
    (Q : OracleAdv X' Y' α) :
    interpQ A (OracleAdv.substQ B Q) = interpQ (fun x' => interpQ A (B x')) Q := by
  induction Q with
  | ret a => rfl
  | rand p k ih => simp only [OracleAdv.substQ, interpQ, ih]
  | query x' k ih => simp only [OracleAdv.substQ, interpQ, interpQ_bind, ih]

/-! ## Lifting per-adversary bounds -/

/-- The gap between the probabilities that the Boolean games `G₀` and `G₁` output `true` when
run with the quantum adversary `A` from `ρ`. -/
def qGap (A : X → CPComp d Y) (ρ : DensityMatrix d) (G₀ G₁ : OracleAdv X Y Bool) : ℝ≥0∞ :=
  absDiff ((interpQ A G₀).outProb ρ true) ((interpQ A G₁).outProb ρ true)

/-- The gap between the probabilities that the Boolean games `G₀` and `G₁` output `true` when
run against the classical stateful oracle `O` from state `s`. -/
def cGap {S : Type} (O : S → X → SDistr (Y × S)) (s : S) (G₀ G₁ : OracleAdv X Y Bool) :
    ℝ≥0∞ :=
  absDiff (outRunD O G₀ s (some true)) (outRunD O G₁ s (some true))

/-- The readout `outProb ρ true` of a Boolean instrument is `prTrue_Q`. -/
theorem outProb_true_eq_prTrue_Q (C : CPComp d Bool) (ρ : DensityMatrix d) :
    C.outProb ρ true = prTrue_Q C.toQComp ρ := rfl

/-- The quantum gap is the classical gap against the behavioral strategy. -/
theorem qGap_eq_cGap_behavOracle (A : X → CPComp d Y) (ρ : DensityMatrix d)
    (G₀ G₁ : OracleAdv X Y Bool) : qGap A ρ G₀ G₁ = cGap (behavOracle A) ρ G₀ G₁ := by
  simp only [qGap, cGap, ← CPComp.outD_some, outD_interpQ]

/-- **Per-adversary lift, multi-round.** A bound `gap(P₀, P₁) ≤ gap(Q₀, Q₁) + ε` that holds
against every classical stateful oracle, of any state type, holds for every quantum adversary
`A` with a classical interface and every initial state `ρ`. -/
theorem qGap_le_of_cGap_le {P₀ P₁ Q₀ Q₁ : OracleAdv X Y Bool} {ε : ℝ≥0∞}
    (hcl : ∀ (S : Type) (O : S → X → SDistr (Y × S)) (s : S),
      cGap O s P₀ P₁ ≤ cGap O s Q₀ Q₁ + ε)
    (A : X → CPComp d Y) (ρ : DensityMatrix d) :
    qGap A ρ P₀ P₁ ≤ qGap A ρ Q₀ Q₁ + ε := by
  simpa only [qGap_eq_cGap_behavOracle] using hcl (DensityMatrix d) (behavOracle A) ρ

/-- **Per-adversary lift, one-shot.** For games calling the adversary at most once, a bound
`gap(P₀, P₁) ≤ gap(Q₀, Q₁) + ε` that holds against every classical stateless adversary
`f : X → SDistr Y` holds for every quantum adversary `A` and every initial state `ρ`. -/
theorem qGap_le_of_cGap_le_of_isQueryBound_one {P₀ P₁ Q₀ Q₁ : OracleAdv X Y Bool}
    {ε : ℝ≥0∞} (hP₀ : P₀.IsQueryBound 1) (hP₁ : P₁.IsQueryBound 1) (hQ₀ : Q₀.IsQueryBound 1)
    (hQ₁ : Q₁.IsQueryBound 1)
    (hcl : ∀ f : X → SDistr Y,
      cGap (statelessOracle f) () P₀ P₁ ≤ cGap (statelessOracle f) () Q₀ Q₁ + ε)
    (A : X → CPComp d Y) (ρ : DensityMatrix d) :
    qGap A ρ P₀ P₁ ≤ qGap A ρ Q₀ Q₁ + ε := by
  have h := hcl (CPComp.behav A ρ)
  simp only [cGap, ← outD_interpQ_of_isQueryBound_one A hP₀, ← outD_interpQ_of_isQueryBound_one A hP₁,
    ← outD_interpQ_of_isQueryBound_one A hQ₀, ← outD_interpQ_of_isQueryBound_one A hQ₁,
    CPComp.outD_some] at h
  exact h

/-- **Per-adversary lift through a reduction.** If, against every classical stateful oracle,
the protocol gap is at most the primitive gap of the games `Q₀`, `Q₁` with their adversary calls
answered by the reduction `B`, plus `ε`, then for every quantum adversary `A` the protocol gap is
at most the primitive gap of `Q₀`, `Q₁` run with the quantum reduction `x' ↦ interpQ A (B x')`,
plus `ε`. -/
theorem qGap_substQ_le_of_cGap_le {P₀ P₁ : OracleAdv X Y Bool}
    {Q₀ Q₁ : OracleAdv X' Y' Bool} (B : X' → OracleAdv X Y Y') {ε : ℝ≥0∞}
    (hcl : ∀ (S : Type) (O : S → X → SDistr (Y × S)) (s : S),
      cGap O s P₀ P₁ ≤ cGap O s (OracleAdv.substQ B Q₀) (OracleAdv.substQ B Q₁) + ε)
    (A : X → CPComp d Y) (ρ : DensityMatrix d) :
    qGap A ρ P₀ P₁ ≤ qGap (fun x' => interpQ A (B x')) ρ Q₀ Q₁ + ε := by
  have h := qGap_le_of_cGap_le hcl A ρ
  simpa only [qGap, interpQ_substQ] using h

/-! ## Time of the quantum reduction -/

/-- The timed reduction `B` with every adversary call charged `c` steps, the cost of one run of
the adversary. -/
def chargeCalls (c : ℕ) (B : OracleAdv.Timed X Y Y') : OracleAdv.Timed X Y Y' :=
  OracleAdv.Timed.mapQuery id (fun _ => c) B

theorem OracleAdv.mapQuery_id (T : OracleAdv X Y α) : OracleAdv.mapQuery id T = T := by
  induction T with
  | ret a => rfl
  | rand p k ih => simp only [OracleAdv.mapQuery, ih]
  | query x k ih => simp only [OracleAdv.mapQuery, id, ih]

/-- Charging the calls leaves the erased reduction unchanged, so its quantum run with `A` is
the quantum reduction of `qGap_substQ_le_of_cGap_le`. -/
theorem erase_chargeCalls (c : ℕ) (B : OracleAdv.Timed X Y Y') :
    (chargeCalls c B).erase = B.erase := by
  rw [chargeCalls, OracleAdv.Timed.erase_mapQuery, OracleAdv.mapQuery_id]

/-- A timed reduction of time `T`, with each adversary call charged the adversary's cost `c`,
has time at most `T + T * c`: it makes at most `T` calls. -/
theorem timeBound_chargeCalls (c : ℕ) {B : OracleAdv.Timed X Y Y'} {T : ℕ}
    (hB : B.TimeBound T) : (chargeCalls c B).TimeBound (T + T * c) :=
  OracleAdv.Timed.timeBound_mapQuery id (fun _ => c) (fun _ => le_rfl) hB
    (OracleAdv.Timed.isQueryBound_of_timeBound hB)

/-! ## Worked instance: CDH from DDH against quantum adversaries -/

section CDHInstance

open CatCrypt.Core CatCrypt.Crypto.Assumptions

variable {W : Type} [SampleableType W] [DecidableEq W]

/-- The `SPComp` adversary sampling its answer from `f x`, with the heap unchanged. -/
def ofSDistrAdv (f : X → SDistr Y) (x : X) : SPComp Y :=
  fun h => (f x).bind fun y => SDistr.pure (y, h)

/-- Sampling from a sub-distribution inside a Boolean game tree; failure outputs `false`. -/
def bindD (μ : SDistr β) (k : β → OracleAdv X Y Bool) : OracleAdv X Y Bool :=
  .rand μ fun o => o.elim (.ret false) k

theorem pmf_map_some_apply (p : PMF β) (b : β) : (p.map some : SDistr β) (some b) = p b := by
  rw [PMF.map_apply, tsum_eq_single b fun b' hb' => by simp [Ne.symm hb']]
  simp

/-- A computation that samples from `μ` and leaves the heap unchanged, followed by `k`, outputs
`true` with the `μ`-weighted sum of the probabilities of `k`. -/
theorem prTrue_bind_of_eq_bind {c : SPComp β} {μ : SDistr β}
    (hc : ∀ h, c h = μ.bind fun a => SDistr.pure (a, h)) (k : β → SPComp Bool) (h : Heap) :
    CatCrypt.Crypto.prTrue (c.bind k) h =
      ∑' a, μ (some a) * CatCrypt.Crypto.prTrue (k a) h := by
  have hck : (c.bind k) h = μ.bind fun a => k a h := by
    simp only [SPComp.bind, hc, SDistr.bind_assoc, SDistr.pure_bind]
  simp only [CatCrypt.Crypto.prTrue, hck, sdistr_bind_apply_some]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]

theorem outRunD_bindD_true {S : Type} (O : S → X → SDistr (Y × S)) (μ : SDistr β)
    (k : β → OracleAdv X Y Bool) (s : S) :
    outRunD O (bindD μ k) s (some true) = ∑' a, μ (some a) * outRunD O (k a) s (some true) := by
  rw [bindD, outRunD_rand, sdistr_bind_apply_some, SDistr.tsum_option_eq_add]
  simp only [pmf_map_some_apply]
  simp [outRunD_ret, SDistr.pure_apply_some]

theorem outRunD_statelessOracle_query (f : X → SDistr Y) (x : X) (k : Y → OracleAdv X Y α)
    (b : α) : outRunD (statelessOracle f) (.query x k) () (some b) =
      ∑' y, f x (some y) * outRunD (statelessOracle f) (k y) () (some b) := by
  rw [outRunD_query, statelessOracle, SDistr.bind_assoc]
  simp only [SDistr.pure_bind]
  rw [sdistr_bind_apply_some]

/-- The key-pair distribution of `D.keygen`, which leaves the heap unchanged. -/
def keyD (D : DDHDef W) : SDistr (W × W) := Classical.choose D.keygen_isPure

omit [DecidableEq W] in
theorem keygen_eq_bind (D : DDHDef W) (h : Heap) :
    D.keygen h = (keyD D).bind fun a => SDistr.pure (a, h) :=
  Classical.choose_spec D.keygen_isPure h

/-- The CDH game as an oracle tree: the adversary is called once on `(g^a, g^b)`. -/
def cdhTree (D : DDHDef W) : OracleAdv (W × W) W Bool :=
  bindD (keyD D) fun k₁ => bindD (keyD D) fun k₂ =>
    .query (k₁.2, k₂.2) fun ans => .ret (decide (ans = D.ecdh k₁.1 k₂.2))

/-- The real DDH game as an oracle tree: the adversary is called once on `(g^a, g^b, g^{ab})`. -/
def ddhRealTree (D : DDHDef W) : OracleAdv (W × W × W) Bool Bool :=
  bindD (keyD D) fun k₁ => bindD (keyD D) fun k₂ =>
    .query (k₁.2, k₂.2, D.ecdh k₁.1 k₂.2) .ret

/-- The ideal DDH game as an oracle tree: the adversary is called once on `(g^a, g^b, c)`, `c`
uniform. -/
def ddhIdealTree (D : DDHDef W) : OracleAdv (W × W × W) Bool Bool :=
  bindD (keyD D) fun k₁ => bindD (keyD D) fun k₂ => bindD (SDistr.uniform W) fun c =>
    .query (k₁.2, k₂.2, c) .ret

/-- The reduction `ddh_of_cdh` as a tree: call the CDH adversary on `(g^a, g^b)` and compare
its answer with the challenge. -/
def ddhOfCdhTree (x : W × W × W) : OracleAdv (W × W) W Bool :=
  .query (x.1, x.2.1) fun ans => .ret (decide (ans = x.2.2))

/-- The classical CDH adversary sampling from `f`. -/
def cdhAdvOf (f : W × W → SDistr W) : CDH_Adversary W :=
  fun ga gb => ofSDistrAdv f (ga, gb)

theorem cdhAdvantage_eq_outRunD (D : DDHDef W) (f : W × W → SDistr W) :
    CDH_Advantage D (cdhAdvOf f) = outRunD (statelessOracle f) (cdhTree D) () (some true) := by
  unfold CDH_Advantage CDH_Game
  simp only [SPComp.monad_bind_eq]
  rw [prTrue_bind_of_eq_bind (keygen_eq_bind D), cdhTree, outRunD_bindD_true]
  refine tsum_congr fun k₁ => ?_
  rw [prTrue_bind_of_eq_bind (keygen_eq_bind D), outRunD_bindD_true]
  refine congrArg _ (tsum_congr fun k₂ => congrArg _ ?_)
  rw [prTrue_bind_of_eq_bind (c := cdhAdvOf f _ _) (fun _ => rfl),
    outRunD_statelessOracle_query]
  refine tsum_congr fun ans => congrArg _ ?_
  rw [outRunD_ret, CatCrypt.Crypto.ForkingLemma.prTrue_pure_bool, SDistr.pure_apply_some]

theorem substQ_bindD (B : X' → OracleAdv X Y Y') (μ : SDistr β)
    (k : β → OracleAdv X' Y' Bool) :
    OracleAdv.substQ B (bindD μ k) = bindD μ fun a => OracleAdv.substQ B (k a) := by
  simp only [bindD, OracleAdv.substQ]
  congr 1
  funext o
  cases o <;> rfl

theorem ddhReal_eq_outRunD (D : DDHDef W) (f : W × W → SDistr W) :
    CatCrypt.Crypto.prTrue (DDH_Game_Real D (ddh_of_cdh (cdhAdvOf f))) Heap.empty =
      outRunD (statelessOracle f) (OracleAdv.substQ ddhOfCdhTree (ddhRealTree D)) ()
        (some true) := by
  unfold DDH_Game_Real ddh_of_cdh
  simp only [SPComp.monad_bind_eq]
  rw [prTrue_bind_of_eq_bind (keygen_eq_bind D), ddhRealTree, substQ_bindD, outRunD_bindD_true]
  refine tsum_congr fun k₁ => ?_
  rw [prTrue_bind_of_eq_bind (keygen_eq_bind D), substQ_bindD, outRunD_bindD_true]
  refine congrArg _ (tsum_congr fun k₂ => congrArg _ ?_)
  rw [prTrue_bind_of_eq_bind (c := cdhAdvOf f _ _) (fun _ => rfl)]
  simp only [OracleAdv.substQ, ddhOfCdhTree, OracleAdv.bind]
  rw [outRunD_statelessOracle_query]
  refine tsum_congr fun ans => congrArg _ ?_
  rw [outRunD_ret, CatCrypt.Crypto.ForkingLemma.prTrue_pure_bool, SDistr.pure_apply_some]

theorem ddhIdeal_eq_outRunD (D : DDHDef W) (f : W × W → SDistr W) :
    CatCrypt.Crypto.prTrue (DDH_Game_Ideal D (ddh_of_cdh (cdhAdvOf f))) Heap.empty =
      outRunD (statelessOracle f) (OracleAdv.substQ ddhOfCdhTree (ddhIdealTree D)) ()
        (some true) := by
  unfold DDH_Game_Ideal ddh_of_cdh
  simp only [SPComp.monad_bind_eq]
  rw [prTrue_bind_of_eq_bind (keygen_eq_bind D), ddhIdealTree, substQ_bindD, outRunD_bindD_true]
  refine tsum_congr fun k₁ => ?_
  rw [prTrue_bind_of_eq_bind (keygen_eq_bind D), substQ_bindD, outRunD_bindD_true]
  refine congrArg _ (tsum_congr fun k₂ => congrArg _ ?_)
  rw [prTrue_bind_of_eq_bind (c := SPComp.sample W) (fun _ => rfl), substQ_bindD,
    outRunD_bindD_true]
  refine tsum_congr fun c => congrArg _ ?_
  rw [prTrue_bind_of_eq_bind (c := cdhAdvOf f _ _) (fun _ => rfl)]
  simp only [OracleAdv.substQ, ddhOfCdhTree, OracleAdv.bind]
  rw [outRunD_statelessOracle_query]
  refine tsum_congr fun ans => congrArg _ ?_
  rw [outRunD_ret, CatCrypt.Crypto.ForkingLemma.prTrue_pure_bool, SDistr.pure_apply_some]

theorem isQueryBound_bindD {μ : SDistr β} {k : β → OracleAdv X Y Bool} {n : ℕ}
    (hk : ∀ a, (k a).IsQueryBound n) : (bindD μ k).IsQueryBound n := by
  intro o
  cases o with
  | none => trivial
  | some a => exact hk a

/-- **CDH from DDH against quantum adversaries.** For every quantum CDH adversary `A` with a
classical interface and every initial state `ρ`, the probability that `A` computes `g^{ab}` is
at most the DDH gap of the quantum reduction `x ↦ interpQ A (ddhOfCdhTree x)` (one call of `A`
and a comparison) plus `1/|W|`. The classical statement is `cdh_le_ddh`. -/
theorem cdh_le_ddh_quantum (D : DDHDef W) (A : W × W → CPComp d W) (ρ : DensityMatrix d) :
    (interpQ A (cdhTree D)).outProb ρ true ≤
      qGap (fun x => interpQ A (ddhOfCdhTree x)) ρ (ddhRealTree D) (ddhIdealTree D) +
        (Fintype.card W : ℝ≥0∞)⁻¹ := by
  have hq : ∀ x : W × W × W, (ddhOfCdhTree x).IsQueryBound 1 := fun _ _ => trivial
  have hcl : ∀ f : W × W → SDistr W,
      cGap (statelessOracle f) () (cdhTree D) (.ret false) ≤
        cGap (statelessOracle f) () (OracleAdv.substQ ddhOfCdhTree (ddhRealTree D))
          (OracleAdv.substQ ddhOfCdhTree (ddhIdealTree D)) + (Fintype.card W : ℝ≥0∞)⁻¹ := by
    intro f
    have h := cdh_le_ddh D (cdhAdvOf f)
    rw [cdhAdvantage_eq_outRunD, DDH_Advantage, CatCrypt.Crypto.Advantage,
      ddhReal_eq_outRunD, ddhIdeal_eq_outRunD] at h
    simpa [cGap, absDiff, outRunD_ret, SDistr.pure_apply_some] using h
  have hP : (cdhTree D).IsQueryBound 1 :=
    isQueryBound_bindD fun _ => isQueryBound_bindD fun _ => fun _ => trivial
  have h0 : (interpQ A (.ret false : OracleAdv (W × W) W Bool)).outProb ρ true = 0 := by
    simp [interpQ, CPComp.outProb_qpure, SDistr.pure_apply_some]
  have h := qGap_le_of_cGap_le_of_isQueryBound_one (P₁ := .ret false) hP trivial
    (by rw [ddhRealTree, substQ_bindD]
        exact isQueryBound_bindD fun _ => by
          rw [substQ_bindD]; exact isQueryBound_bindD fun _ => fun _ => trivial)
    (by rw [ddhIdealTree, substQ_bindD]
        exact isQueryBound_bindD fun _ => by
          rw [substQ_bindD]; exact isQueryBound_bindD fun _ => by
            rw [substQ_bindD]; exact isQueryBound_bindD fun _ => fun _ => trivial)
    hcl A ρ
  simpa [qGap, interpQ_substQ, absDiff, h0] using h

end CDHInstance

end CatCrypt.Quantum
