/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.CPRun
public import CatCryptCore.Crypto.UCMonad.CPCompUC
public import CatCryptCore.Crypto.MLKEM.PRFKEMChain
public import CatCryptCore.NonUniform.Sample

/-!
# The quantum IND-CCA experiment of the FO KEM as a completely positive program

The game of `Quantum/QROM/KEMQuantumGame.lean` is a `kemSample`-weighted sum of
acceptance probabilities. This module writes it as one program in the monad
`CPComp d`: sample the input from `kemDist`, prepare the initial state of the
adversary, and run the multi-round adversary against the merged oracle and the
decapsulation rounds. The acceptance probability of the program is `prWinKEM`
on every input state, so its distinguishing advantage is `qINDCCAAdvantage`.

Every instrument of the program is total: the traces of its branches sum to the
trace of the input. The game family is therefore an `IsTotalQGame`, and with
the `QGameAdvBound` instance the distance `cpSdist` between the two reset games
is at most `qINDCCAAdvantage`.

## Main definitions

* `kemDist` — the input distribution, with weight `kemSample` on each input
* `qINDCCAGame P hpk eG eJ eKR eC eKa A b` — the IND-CCA experiment with bit `b`
* `qINDCCAGameF`, `qINDCCAGameAvg` — the experiment with the table `F` as a third
  oracle, at a fixed `F` and with `F` sampled uniformly
* `TotalQ C` — the branch traces of `C` sum to the input trace

## Main results

* `kemDist_apply_some` — `kemDist` has weight `kemSample`
* `prTrue_qINDCCAGame` — the acceptance probability is `prWinKEM`
* `absDiff_prTrue_qINDCCAGame` — the advantage of the game is `qINDCCAAdvantage`
* `totalQ_qINDCCAGame`, `isTotalQGame_qINDCCAGame` — totality
* `cpSdist_qINDCCAGame_withReset_le` — the CP distance between the reset games
  is at most `qINDCCAAdvantage`
* `prTrue_qINDCCAGameF`, `prTrue_qINDCCAGameAvg`, `cpSdist_qINDCCAGameAvg_withReset_le`
  — the same for the table game, the averaged game bounded by the average of
  `qINDCCAAdvantageF`
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.QROM CatCrypt.Quantum.UnitaryChannel
open CatCrypt.Prob
open CatCrypt.Crypto.PKE.Games (Scheme)
open CatCrypt.Crypto.UCMonad.CPCompUC
open CatCrypt.Crypto.MLKEM.PRFOracle (avg absDiff_avg_le)
open CatCrypt.Crypto.MLKEM.PRFKEMChain (prWinKEMF qINDCCAAdvantageF)

noncomputable section

namespace CatCrypt.Quantum.QROM.KEMGameCP

/-! ## Total instruments -/

section Total

variable {d : ℕ}

/-- An instrument with finitely many outcomes is total when, on every matrix,
the traces of its branches sum to the trace of the input. -/
def TotalQ {α : Type} [Fintype α] (C : QComp d α) : Prop :=
  ∀ ρ : Matrix (Fin d) (Fin d) ℂ, ∑ a, (C.branch a ρ).trace = ρ.trace

theorem totalQ_qbind {α β : Type} [Fintype α] [Fintype β] {C : QComp d α}
    {f : α → QComp d β} (hC : TotalQ C) (hf : ∀ a, TotalQ (f a)) :
    TotalQ (QComp.qbind C f) := by
  intro ρ
  show ∑ b, (∑' a, (f a).branch b (C.branch a ρ)).trace = _
  simp only [tsum_fintype, trace_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun a _ => hf a (C.branch a ρ)]
  exact hC ρ

theorem totalQ_qpure {α : Type} [Fintype α] (x : α) : TotalQ (QComp.qpure (d := d) x) := by
  intro ρ
  rw [Finset.sum_eq_single x (fun b _ hb => by simp [QComp.qpure, hb])
    (fun h => absurd (Finset.mem_univ x) h)]
  simp [QComp.qpure]

theorem totalQ_unitaryChannel (U : Matrix.unitaryGroup (Fin d) ℂ) :
    TotalQ (unitaryChannel U) := by
  intro ρ
  rw [Fintype.sum_unique]
  exact trace_mul_mul_conjTranspose_of_mem_unitaryGroup U.2 ρ

theorem totalQ_measureOps {α : Type} [Fintype α] (M : Measurement.MeasurementOps d α) :
    TotalQ (Measurement.measureOps M) := by
  intro ρ
  have h : ∀ a, ((Measurement.measureOps M).branch a ρ).trace =
      ((M.op a)ᴴ * M.op a * ρ).trace := fun a => by
    show (M.op a * ρ * (M.op a)ᴴ).trace = _
    rw [trace_mul_cycle]
  simp only [h, ← trace_sum, ← Finset.sum_mul, M.completeness, Matrix.one_mul]

theorem totalQ_roundU {c a : ℕ} (R : ClassicalRound d c a) (f : Fin c → Fin a) :
    TotalQ (roundU R f) :=
  totalQ_qbind (totalQ_measureOps _) fun _ => totalQ_qpure _

theorem totalQ_measProj (P : Matrix (Fin d) (Fin d) ℂ) (hH : Pᴴ = P) (hI : P * P = P) :
    TotalQ (measProj P hH hI) := by
  intro ρ
  have h1 : (1 - P)ᴴ = 1 - P := by rw [conjTranspose_sub, conjTranspose_one, hH]
  have h2 : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hI,
      sub_self, sub_zero]
  rw [Fintype.sum_bool, measProj_branch_true, measProj_branch_false, hH, h1,
    trace_mul_cycle P, hI, trace_mul_cycle (1 - P), h2, ← trace_add, ← add_mul,
    add_sub_cancel, Matrix.one_mul]

theorem totalQ_oracleChain (O : QComp d Unit) (hO : TotalQ O) :
    ∀ (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ), TotalQ (oracleChain O q U)
  | 0, _ => totalQ_unitaryChannel _
  | q + 1, U => totalQ_qbind (totalQ_unitaryChannel _) fun _ =>
      totalQ_qbind hO fun _ => totalQ_oracleChain O hO q (Fin.tail U)

theorem totalQ_mrChain {c a q : ℕ} (O : QComp d Unit) (hO : TotalQ O) (f : Fin c → Fin a) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a), TotalQ (mrChain O f k q₀ head tail R)
  | 0, q₀, head, _, _ => totalQ_oracleChain O hO q₀ head
  | k + 1, q₀, head, tail, R =>
      totalQ_qbind (totalQ_oracleChain O hO q₀ head) fun _ =>
        totalQ_qbind (totalQ_roundU _ _) fun _ =>
          totalQ_mrChain O hO f k q (tail 0) (Fin.tail tail) (Fin.tail R)

theorem totalQ_classicalEmbed {α : Type} [Fintype α] (μ : SDistr α)
    (hμ : ∑ a, μ (some a) = 1) : TotalQ (classicalEmbed (d := d) μ) := by
  intro ρ
  show ∑ a, (((μ (some a)).toReal : ℂ) • ρ).trace = ρ.trace
  simp only [trace_smul, smul_eq_mul, ← Finset.sum_mul]
  rw [← Complex.ofReal_sum, ← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top μ _), hμ,
    ENNReal.toReal_one, Complex.ofReal_one, one_mul]

theorem totalQ_prep (σ : DensityMatrix d) : TotalQ (QComp.prep σ) := by
  intro ρ
  rw [Fintype.sum_unique]
  show (prepMap σ.val ρ).trace = ρ.trace
  rw [prepMap_apply, trace_smul, σ.tr_one, smul_eq_mul, mul_one]

/-- A total game accepts or rejects with total probability one. -/
theorem prTrue_add_prFalse_of_totalQ (G : CPComp d Bool) (hG : TotalQ G.toQComp)
    (ρ : DensityMatrix d) : G.prTrue ρ + G.prFalse ρ = 1 := by
  have h := hG ρ.val
  rw [Fintype.sum_bool, ρ.tr_one] at h
  rw [CPComp.prTrue_def, prTrue_Q, CPComp.prFalse,
    ← ENNReal.ofReal_add (trace_re_nonneg_of_psd (G.toQComp.branch_psd _ _ ρ.psd))
      (trace_re_nonneg_of_psd (G.toQComp.branch_psd _ _ ρ.psd)),
    ← Complex.add_re, h, Complex.one_re, ENNReal.ofReal_one]

/-- Resetting the register after a total game gives a total game. -/
theorem totalQ_withReset (σ₀ : DensityMatrix d) (G : CPComp d Bool) (hG : TotalQ G.toQComp) :
    TotalQ (CPComp.withReset σ₀ G).toQComp := by
  simp only [CPComp.withReset, CPComp.toQComp_bind, CPComp.toQComp_prep, CPComp.toQComp_pure]
  exact totalQ_qbind hG fun _ => totalQ_qbind (totalQ_prep σ₀) fun _ => totalQ_qpure _

end Total

/-! ## The input distribution -/

section Game

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Fintype K] [Nonempty K] [Nonempty R]
  [DecidableEq C] (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

omit [DecidableEq C] in
/-- The distribution of the KEM game input: weight `kemSample` on each input. -/
def kemDist : SDistr (KEMInput PK SK Z M K m₁ m₂ n) :=
  CatCrypt.NonUniform.ofPMF (PMF.ofFintype (kemSample P) (kemSample_sum P eKR))

omit [DecidableEq C] in
theorem kemDist_apply_some (i : KEMInput PK SK Z M K m₁ m₂ n) :
    kemDist P eKR (some i) = kemSample P i := by
  rw [kemDist, CatCrypt.NonUniform.ofPMF_apply_some, PMF.ofFintype_apply]

omit [DecidableEq C] in
theorem sum_kemDist_apply_some :
    ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemDist P eKR (some i) = 1 := by
  simp only [kemDist_apply_some]
  exact kemSample_sum P eKR

/-- The adversary of `A` at an input and a bit: run on the public key, the
challenge ciphertext and the challenge key. -/
def kemAdvAt {m₁' m₂' : ℕ} (A : KEMQAdv m₁' m₂' n w q k c a PK C K)
    (i : KEMInput PK SK Z M K m₁ m₂ n) (b : Bool) : QAdvMR (m₁' + m₂') n (2 * w) q k c a :=
  A.run i.1.1 (kemChal P hpk eG eKR i) (kemKey hpk eG eKR i b)

/-! ## The game -/

variable [NeZero n]

/-- The quantum IND-CCA experiment of the FO KEM with bit `b`: sample the input
from `kemDist`, prepare the initial state of the adversary, and run it against
the merged oracle and the decapsulation rounds. -/
def qINDCCAGame (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    CPComp ((m₁ + m₂) * n * (2 * w)) Bool :=
  CPComp.sample (kemDist P eKR) >>= fun i =>
    CPComp.prep (kemAdvAt P hpk eG eKR A i b).init >>= fun _ =>
      cpRunMR (kemAdvAt P hpk eG eKR A i b) (kemOracle i) (kemDecaps P hpk eG eJ eKR eC eKa i)

/-- On every input state, the experiment accepts with probability `prWinKEM`. -/
theorem prTrue_qINDCCAGame (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (ρ : DensityMatrix ((m₁ + m₂) * n * (2 * w))) :
    (qINDCCAGame P hpk eG eJ eKR eC eKa A b).prTrue ρ = prWinKEM P hpk eG eJ eKR eC eKa A b := by
  rw [qINDCCAGame, CPComp.prTrue_sample_bind, tsum_fintype, prWinKEM_eq_sum_prTrue]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kemDist_apply_some, CPComp.prTrue_prep_bind]
  rfl

/-- On every input state, the distinguishing advantage of the two experiments is
`qINDCCAAdvantage`. -/
theorem absDiff_prTrue_qINDCCAGame (A : KEMQAdv m₁ m₂ n w q k c a PK C K)
    (ρ : DensityMatrix ((m₁ + m₂) * n * (2 * w))) :
    absDiff ((qINDCCAGame P hpk eG eJ eKR eC eKa A true).prTrue ρ)
      ((qINDCCAGame P hpk eG eJ eKR eC eKa A false).prTrue ρ) =
      qINDCCAAdvantage P hpk eG eJ eKR eC eKa A := by
  rw [prTrue_qINDCCAGame, prTrue_qINDCCAGame]
  rfl

/-- The experiment is a total instrument. -/
theorem totalQ_qINDCCAGame (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    TotalQ (qINDCCAGame P hpk eG eJ eKR eC eKa A b).toQComp := by
  simp only [qINDCCAGame, CPComp.toQComp_bind, CPComp.toQComp_sample, CPComp.toQComp_prep,
    toQComp_cpRunMR]
  exact totalQ_qbind (totalQ_classicalEmbed _ (sum_kemDist_apply_some P eKR)) fun _ =>
    totalQ_qbind (totalQ_prep _) fun _ =>
      totalQ_qbind (totalQ_mrChain _ (totalQ_unitaryChannel _) _ _ _ _ _ _) fun _ =>
        totalQ_measProj _ _ _

instance isTotalQGame_qINDCCAGame (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    IsTotalQGame (fun _ : Unit => qINDCCAGame P hpk eG eJ eKR eC eKa A b) :=
  ⟨fun _ => prTrue_add_prFalse_of_totalQ _ (totalQ_qINDCCAGame P hpk eG eJ eKR eC eKa A b)⟩

instance isTotalQGame_withReset_qINDCCAGame (σ₀ : DensityMatrix ((m₁ + m₂) * n * (2 * w)))
    (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    IsTotalQGame (fun _ : Unit => CPComp.withReset σ₀ (qINDCCAGame P hpk eG eJ eKR eC eKa A b)) :=
  ⟨fun _ => prTrue_add_prFalse_of_totalQ _
    (totalQ_withReset σ₀ _ (totalQ_qINDCCAGame P hpk eG eJ eKR eC eKa A b))⟩

instance qGameAdvBound_qINDCCAGame (A : KEMQAdv m₁ m₂ n w q k c a PK C K) :
    QGameAdvBound (fun _ : Unit => qINDCCAGame P hpk eG eJ eKR eC eKa A true)
      (fun _ : Unit => qINDCCAGame P hpk eG eJ eKR eC eKa A false)
      (qINDCCAAdvantage P hpk eG eJ eKR eC eKa A) :=
  ⟨fun _ ρ => (absDiff_prTrue_qINDCCAGame P hpk eG eJ eKR eC eKa A ρ).le⟩

/-- Every bound on `qINDCCAAdvantage` is a `QGameAdvBound` of the experiments. -/
theorem qGameAdvBound_qINDCCAGame_of_le (A : KEMQAdv m₁ m₂ n w q k c a PK C K) {ε : ℝ≥0∞}
    (h : qINDCCAAdvantage P hpk eG eJ eKR eC eKa A ≤ ε) :
    QGameAdvBound (fun _ : Unit => qINDCCAGame P hpk eG eJ eKR eC eKa A true)
      (fun _ : Unit => qINDCCAGame P hpk eG eJ eKR eC eKa A false) ε :=
  ⟨fun _ ρ => (absDiff_prTrue_qINDCCAGame P hpk eG eJ eKR eC eKa A ρ).le.trans h⟩

/-- The CP distinguishing distance between the two experiments followed by a
reset to `σ₀` is at most `qINDCCAAdvantage`. -/
theorem cpSdist_qINDCCAGame_withReset_le (σ₀ : DensityMatrix ((m₁ + m₂) * n * (2 * w)))
    (A : KEMQAdv m₁ m₂ n w q k c a PK C K) :
    cpSdist (fun _ : Unit => CPComp.withReset σ₀ (qINDCCAGame P hpk eG eJ eKR eC eKa A true))
      (fun _ : Unit => CPComp.withReset σ₀ (qINDCCAGame P hpk eG eJ eKR eC eKa A false)) ≤
      qINDCCAAdvantage P hpk eG eJ eKR eC eKa A :=
  cpSdist_withReset_le σ₀ _ _ fun _ ρ => (absDiff_prTrue_qINDCCAGame P hpk eG eJ eKR eC eKa A ρ).le

end Game

/-! ## The game with the table as a third oracle -/

section GameF

variable {m₁ m₂ m₃ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Fintype K] [Nonempty K] [Nonempty R]
  [DecidableEq C] (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
  [NeZero n]

/-- The IND-CCA experiment with bit `b` whose oracle answers `kemOracle i` on the
first summand and the table `F` on the second. -/
def qINDCCAGameF (P : Scheme PK SK M C R) (F : Fin m₃ → Fin n)
    (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (b : Bool) :
    CPComp ((m₁ + m₂ + m₃) * n * (2 * w)) Bool :=
  CPComp.sample (kemDist (m₁ := m₁) (m₂ := m₂) P eKR) >>= fun i =>
    CPComp.prep (kemAdvAt P hpk eG eKR A i b).init >>= fun _ =>
      cpRunMR (kemAdvAt P hpk eG eKR A i b) (mergeOracle (kemOracle i) F)
        (kemDecaps P hpk eG eJ eKR eC eKa i)

/-- On every input state, the table experiment accepts with probability
`prWinKEMF`. -/
theorem prTrue_qINDCCAGameF (P : Scheme PK SK M C R) (F : Fin m₃ → Fin n)
    (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (b : Bool)
    (ρ : DensityMatrix ((m₁ + m₂ + m₃) * n * (2 * w))) :
    (qINDCCAGameF hpk eG eJ eKR eC eKa P F A b).prTrue ρ =
      prWinKEMF P hpk eG eJ eKR eC eKa F A b := by
  rw [qINDCCAGameF, CPComp.prTrue_sample_bind, tsum_fintype, prWinKEMF]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kemDist_apply_some, CPComp.prTrue_prep_bind]
  rfl

theorem totalQ_qINDCCAGameF (P : Scheme PK SK M C R) (F : Fin m₃ → Fin n)
    (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (b : Bool) :
    TotalQ (qINDCCAGameF hpk eG eJ eKR eC eKa P F A b).toQComp := by
  simp only [qINDCCAGameF, CPComp.toQComp_bind, CPComp.toQComp_sample, CPComp.toQComp_prep,
    toQComp_cpRunMR]
  exact totalQ_qbind (totalQ_classicalEmbed _ (sum_kemDist_apply_some P eKR)) fun _ =>
    totalQ_qbind (totalQ_prep _) fun _ =>
      totalQ_qbind (totalQ_mrChain _ (totalQ_unitaryChannel _) _ _ _ _ _ _) fun _ =>
        totalQ_measProj _ _ _

/-- The table experiment with the table `F` drawn uniformly, against the scheme
`Pf F`. -/
def qINDCCAGameAvg (Pf : (Fin m₃ → Fin n) → Scheme PK SK M C R)
    (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (b : Bool) :
    CPComp ((m₁ + m₂ + m₃) * n * (2 * w)) Bool :=
  CPComp.sample (SDistr.uniform (Fin m₃ → Fin n)) >>= fun F =>
    qINDCCAGameF hpk eG eJ eKR eC eKa (Pf F) F A b

/-- On every input state, the averaged experiment accepts with the average over
`F` of `prWinKEMF`. -/
theorem prTrue_qINDCCAGameAvg (Pf : (Fin m₃ → Fin n) → Scheme PK SK M C R)
    (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (b : Bool)
    (ρ : DensityMatrix ((m₁ + m₂ + m₃) * n * (2 * w))) :
    (qINDCCAGameAvg hpk eG eJ eKR eC eKa Pf A b).prTrue ρ =
      avg fun F => prWinKEMF (Pf F) hpk eG eJ eKR eC eKa F A b := by
  rw [qINDCCAGameAvg, CPComp.prTrue_sample_uniform_bind]
  simp only [prTrue_qINDCCAGameF]
  rfl

/-- On every input state, the distinguishing advantage of the averaged
experiments is at most the average over `F` of `qINDCCAAdvantageF`. -/
theorem absDiff_prTrue_qINDCCAGameAvg_le (Pf : (Fin m₃ → Fin n) → Scheme PK SK M C R)
    (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K)
    (ρ : DensityMatrix ((m₁ + m₂ + m₃) * n * (2 * w))) :
    absDiff ((qINDCCAGameAvg hpk eG eJ eKR eC eKa Pf A true).prTrue ρ)
      ((qINDCCAGameAvg hpk eG eJ eKR eC eKa Pf A false).prTrue ρ) ≤
      avg fun F => qINDCCAAdvantageF (Pf F) hpk eG eJ eKR eC eKa F A := by
  rw [prTrue_qINDCCAGameAvg, prTrue_qINDCCAGameAvg]
  exact absDiff_avg_le _ _

theorem totalQ_qINDCCAGameAvg (Pf : (Fin m₃ → Fin n) → Scheme PK SK M C R)
    (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (b : Bool) :
    TotalQ (qINDCCAGameAvg hpk eG eJ eKR eC eKa Pf A b).toQComp := by
  simp only [qINDCCAGameAvg, CPComp.toQComp_bind, CPComp.toQComp_sample]
  exact totalQ_qbind (totalQ_classicalEmbed _ (by
      simp only [SDistr.uniform_apply_some, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (by simp [NeZero.ne n]) (ENNReal.natCast_ne_top _)))
    fun F => totalQ_qINDCCAGameF hpk eG eJ eKR eC eKa (Pf F) F A b

instance isTotalQGame_qINDCCAGameAvg (Pf : (Fin m₃ → Fin n) → Scheme PK SK M C R)
    (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (b : Bool) :
    IsTotalQGame (fun _ : Unit => qINDCCAGameAvg hpk eG eJ eKR eC eKa Pf A b) :=
  ⟨fun _ => prTrue_add_prFalse_of_totalQ _ (totalQ_qINDCCAGameAvg hpk eG eJ eKR eC eKa Pf A b)⟩

instance qGameAdvBound_qINDCCAGameAvg (Pf : (Fin m₃ → Fin n) → Scheme PK SK M C R)
    (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) :
    QGameAdvBound (fun _ : Unit => qINDCCAGameAvg hpk eG eJ eKR eC eKa Pf A true)
      (fun _ : Unit => qINDCCAGameAvg hpk eG eJ eKR eC eKa Pf A false)
      (avg fun F => qINDCCAAdvantageF (Pf F) hpk eG eJ eKR eC eKa F A) :=
  ⟨fun _ ρ => absDiff_prTrue_qINDCCAGameAvg_le hpk eG eJ eKR eC eKa Pf A ρ⟩

/-- The CP distinguishing distance between the two averaged experiments followed
by a reset to `σ₀` is at most the average over `F` of `qINDCCAAdvantageF`. -/
theorem cpSdist_qINDCCAGameAvg_withReset_le (σ₀ : DensityMatrix ((m₁ + m₂ + m₃) * n * (2 * w)))
    (Pf : (Fin m₃ → Fin n) → Scheme PK SK M C R) (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) :
    cpSdist (fun _ : Unit => CPComp.withReset σ₀ (qINDCCAGameAvg hpk eG eJ eKR eC eKa Pf A true))
      (fun _ : Unit => CPComp.withReset σ₀ (qINDCCAGameAvg hpk eG eJ eKR eC eKa Pf A false)) ≤
      avg fun F => qINDCCAAdvantageF (Pf F) hpk eG eJ eKR eC eKa F A :=
  cpSdist_withReset_le σ₀ _ _ fun _ ρ =>
    absDiff_prTrue_qINDCCAGameAvg_le hpk eG eJ eKR eC eKa Pf A ρ

end GameF

end CatCrypt.Quantum.QROM.KEMGameCP

end
