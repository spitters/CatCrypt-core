/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.O2HGeneral
public import CatCryptCore.Quantum.QROM.SparseSearch
public import CatCryptCore.Quantum.QROM.QAdvGame

/-!
# Semi-classical oracles and classical rounds for general adversaries

Four statements about a multi-round adversary `A : QAdvMRGen m n w q k c a`,
whose local operations are trace-preserving completely positive maps and whose
initial state is any density matrix.

* Congruence: `Pr[out = 1 ∧ ¬Find]` and `Pr[Find]` of the semi-classical run
  with the punctured set `S` are the same for two oracles that agree outside
  `S`. For a single-run adversary `QAdv` with a mixed initial state this is
  read off the `Find = false` branch of the semi-classical chain, which
  depends on the oracle only through `U_H (1 − Π_S)`; a general adversary is
  carried to a single-run adversary by its dilation and `toQAdv`.
* Find-to-guess: `Pr[Find] ≤ 4 ∑ⱼ guessProb B H S j` for the single-run
  adversary `B = toQAdv (dilate A) f` with `flatQ q k q` queries, on any
  initial state (Ambainis–Hamburg–Unruh, CRYPTO 2019, Theorem 2). The mixed
  initial state is a sum of rank-one states, and the pure-state inequality
  holds for vectors of any norm.
* Averaged Find: for weights `μ` on pairs `(H, S)` whose oracles agree with a
  fixed `H₀` outside `S`, with `∑_ω μ ω · [x ∈ S ω] ≤ λ` at every `x`,
  `∑_ω μ ω · Pr[Find] ≤ 4 · flatQ q k q · λ`.
* Up to bad in the rounds: if `f'` agrees with `f` outside a random set `D`
  whose law satisfies `∑_ω μ ω · [y ∈ D ω] ≤ λ` at every `y`, then
  `|Pr[out = 1 : f] − ∑_ω μ ω · Pr[out = 1 : f' ω]| ≤ k · λ`. The run with `f`
  splits at each round into the outcomes outside `D`, where the two round
  functions agree, and those in `D`, whose weight `badW` is measured in the run
  with `f`, which does not depend on `ω`.

## Main definitions

* `roundBad R D σ` — the weight `∑_{y ∈ D} tr (P_y σ)` of the outcomes in `D`
  of the measurement of the round `R` on `σ`
* `roundPart R f D σ` — the part `∑_{y ∈ D} K_y σ K_yᴴ` of the round channel
  with classical function `f` at the outcomes in `D`
* `badW O f D k q₀ head tail R σ` — the sum over the rounds of the weight of
  the outcomes in `D`, each measured on the state that the chain with `f`
  reaches before the round

## Main results

* `prOutNoFind_congr_mixed`, `prFind_congr_mixed` — congruence for `QAdv` on
  any initial state
* `prFind_le_four_sum_guess_mixed`, `guessProb_eq_sum_singleton_mixed`,
  `sum_guessProb_singleton_le_one_mixed` — Find-to-guess and the guessing
  probabilities at the singletons for `QAdv` on any initial state
* `prOutNoFindMRGen_congr`, `prFindMRGen_congr` — congruence for `QAdvMRGen`
* `prFindMRGen_le_four_sum_guess` — Find-to-guess for `QAdvMRGen`
* `prFindMRGen_avg_le` — the averaged Find bound
* `abs_eff_mrChainG_sub_le` — two round functions agreeing outside `D` change
  the value of any final measurement by at most `badW`
* `rounds_upto_bad` — the averaged round bound `k · λ`

## References

* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019, ePrint 2018/904], Theorems 1 and 2
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct CatCrypt.Quantum.UnitaryChannel

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Single-run adversaries on a mixed initial state -/

section Single

variable {m n w q : ℕ} [NeZero n]

/-- `Pr[out = 1 ∧ ¬Find]` is the same for two functions that agree outside `S`,
on any initial state. -/
theorem prOutNoFind_congr_mixed (A : QAdv m n w q) (H H' : Fin m → Fin n)
    (S : Finset (Fin m)) (hHH' : ∀ x, x ∉ S → H x = H' x) :
    prOutNoFind A H S = prOutNoFind A H' S := by
  rw [prOutNoFind_eq_trace, prOutNoFind_eq_trace,
    scChain_branch_false_congr _ _ (scOracleQ_branch_false_congr H H' S hHH') q A.U]

/-- `Pr[Find]` is the same for two functions that agree outside `S`, on any
initial state. -/
theorem prFind_congr_mixed (A : QAdv m n w q) (H H' : Fin m → Fin n) (S : Finset (Fin m))
    (hHH' : ∀ x, x ∉ S → H x = H' x) : prFind A H S = prFind A H' S := by
  rw [prFind_eq_trace, prFind_eq_trace]
  have h := scChain_trace_add _ (scOracleQ_trace_add (w := w) H S) q A.U A.init.val
  have h' := scChain_trace_add _ (scOracleQ_trace_add (w := w) H' S) q A.U A.init.val
  rw [scChain_branch_false_congr _ _ (scOracleQ_branch_false_congr H H' S hHH') q A.U] at h
  have e : ((scChain (scOracleQ m n w H S) q A.U).branch true A.init.val).trace =
      ((scChain (scOracleQ m n w H' S) q A.U).branch true A.init.val).trace := by
    linear_combination h - h'
  rw [e]

/-- On an initial state `∑ₖ ψₖ ψₖ†`, `guessProb` is the sum of the squared norms
of the projected plain states. -/
theorem guessProb_eq_sum_nrm_sq (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m))
    (j : Fin q) {ι : Type} [Fintype ι] (ψ : ι → Fin (m * n * w) → ℂ)
    (hρ : A.init.val = ∑ k, vecMulVec (ψ k) (star (ψ k))) :
    guessProb A H S j =
      ENNReal.ofReal (∑ k, nrm (projS m n w S *ᵥ plainState A H (ψ k) j) ^ 2) := by
  unfold guessProb prOut prTrue_Q
  rw [run_branch_true, runOp_zero]
  change ENNReal.ofReal ((projS m n w S * (prefixU A H j : Matrix _ _ ℂ)) * A.init.val *
    (projS m n w S * (prefixU A H j : Matrix _ _ ℂ))ᴴ).trace.re = _
  rw [hρ, trace_mul_sum_vecMulVec_mul_conjTranspose, Complex.ofReal_re]
  simp only [← mulVec_mulVec, prefixU_mulVec]

/-- The trace of `∑ₖ ψₖ ψₖ†` is `∑ₖ ‖ψₖ‖²`. -/
theorem trace_sum_vecMulVec {d : ℕ} {ι : Type} [Fintype ι] (ψ : ι → Fin d → ℂ) :
    (∑ k, vecMulVec (ψ k) (star (ψ k))).trace = ((∑ k, nrm (ψ k) ^ 2 : ℝ) : ℂ) := by
  rw [trace_sum, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [trace_vecMulVec, dotProduct_star_self]

/-- On an initial state `∑ₖ ψₖ ψₖ†`, `Pr[Find]` is the sum over `k` and the
queries of the squared norms of the projected intermediate states. -/
theorem prFind_eq_sum_nrm_sq (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m))
    {ι : Type} [Fintype ι] (ψ : ι → Fin (m * n * w) → ℂ)
    (hρ : A.init.val = ∑ k, vecMulVec (ψ k) (star (ψ k))) :
    prFind A H S =
      ENNReal.ofReal (∑ k, ∑ i, nrm (projS m n w S *ᵥ scState A H S (ψ k) i) ^ 2) := by
  rw [prFind_eq_trace]
  congr 1
  set C := chainOp ((oracleU m n w H : Matrix _ _ ℂ) * (1 - projS m n w S)) q A.U
  have htp := scChain_trace_add (scOracleQ m n w H S) (scOracleQ_trace_add H S) q A.U
    A.init.val
  rw [scChain_branch_false_eq, hρ, trace_mul_sum_vecMulVec_mul_conjTranspose,
    trace_sum_vecMulVec] at htp
  have hpy : ∀ k, nrm (C *ᵥ ψ k) ^ 2 +
      ∑ i, nrm (projS m n w S *ᵥ scState A H S (ψ k) i) ^ 2 = nrm (ψ k) ^ 2 := fun k =>
    nrm_sq_chainOp_add_sum_nrm_sq_scStates (oracleU m n w H).prop
      (projS_mul_self m n w S) (projS_conjTranspose m n w S) q A.U (ψ k)
  have hsum : ((∑ k, nrm (C *ᵥ ψ k) ^ 2 : ℝ) : ℂ) +
      ((∑ k, ∑ i, nrm (projS m n w S *ᵥ scState A H S (ψ k) i) ^ 2 : ℝ) : ℂ) =
      ((∑ k, nrm (ψ k) ^ 2 : ℝ) : ℂ) := by
    rw [← Finset.sum_congr rfl fun k _ => hpy k, Finset.sum_add_distrib]
    push_cast
    ring
  rw [hρ]
  have hre : ((scChain (scOracleQ m n w H S) q A.U).branch true
      (∑ k, vecMulVec (ψ k) (star (ψ k)))).trace =
      ((∑ k, ∑ i, nrm (projS m n w S *ᵥ scState A H S (ψ k) i) ^ 2 : ℝ) : ℂ) := by
    linear_combination htp - hsum
  rw [hre, Complex.ofReal_re]

/-- Search in a semi-classical oracle (Ambainis–Hamburg–Unruh, CRYPTO 2019,
Theorem 2) on any initial state: `Pr[Find] ≤ 4 ∑ⱼ guessProb A H S j`. -/
theorem prFind_le_four_sum_guess_mixed (A : QAdv m n w q) (H : Fin m → Fin n)
    (S : Finset (Fin m)) : prFind A H S ≤ 4 * ∑ j, guessProb A H S j := by
  obtain ⟨ψ, hρ⟩ := exists_eq_sum_vecMulVec_of_posSemidef A.init.psd
  rw [prFind_eq_sum_nrm_sq A H S ψ hρ]
  simp only [guessProb_eq_sum_nrm_sq A H S _ ψ hρ]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _),
    ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  conv_rhs => rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  unfold scState plainState
  exact sum_nrm_sq_scStates_le (oracleU m n w H).prop (projS_mul_self m n w S)
    (projS_conjTranspose m n w S) q A.U (ψ k)

/-- `guessProb A H S j = ∑ x ∈ S, guessProb A H {x} j` on any initial state. -/
theorem guessProb_eq_sum_singleton_mixed (A : QAdv m n w q) (H : Fin m → Fin n)
    (S : Finset (Fin m)) (j : Fin q) :
    guessProb A H S j = ∑ x ∈ S, guessProb A H {x} j := by
  obtain ⟨ψ, hρ⟩ := exists_eq_sum_vecMulVec_of_posSemidef A.init.psd
  simp only [guessProb_eq_sum_nrm_sq A H _ j ψ hρ]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => Finset.sum_nonneg fun k _ => sq_nonneg _)]
  congr 1
  simp only [nrm_sq_projS_eq_sum S]
  exact Finset.sum_comm

/-- The guessing probabilities at the singletons sum to at most one, on any
initial state. -/
theorem sum_guessProb_singleton_le_one_mixed (A : QAdv m n w q) (H : Fin m → Fin n)
    (j : Fin q) : ∑ x, guessProb A H {x} j ≤ 1 := by
  rw [← guessProb_eq_sum_singleton_mixed A H Finset.univ j]
  obtain ⟨ψ, hρ⟩ := exists_eq_sum_vecMulVec_of_posSemidef A.init.psd
  rw [guessProb_eq_sum_nrm_sq A H _ j ψ hρ, ENNReal.ofReal_le_one]
  have hnorm : ∑ k, nrm (ψ k) ^ 2 = 1 := by
    have h := A.init.tr_one
    rw [hρ, trace_sum_vecMulVec] at h
    exact_mod_cast h
  calc ∑ k, nrm (projS m n w Finset.univ *ᵥ plainState A H (ψ k) j) ^ 2
      ≤ ∑ k, nrm (ψ k) ^ 2 := Finset.sum_le_sum fun k _ => by
        have h1 : nrm (plainState A H (ψ k) j) = nrm (ψ k) := by
          unfold plainState
          rw [← chainOp_castLE_mulVec,
            nrm_chainOp_mulVec_eq _ (nrm_mulVec_of_mem_unitaryGroup (oracleU m n w H).prop)]
        rw [← h1]
        exact pow_le_pow_left₀ (nrm_nonneg _)
          (nrm_proj_mulVec_le (projS_mul_self m n w _) (projS_conjTranspose m n w _) _) 2
    _ = 1 := hnorm

end Single

/-! ## General multi-round adversaries: congruence and Find-to-guess -/

section General

variable {m n w q k c a : ℕ} [NeZero n] [NeZero c]

/-- `Pr[out = 1 ∧ ¬Find]` of a general adversary is that of the single-run
embedding of its dilation. -/
theorem prOutNoFindMRGen_eq_toQAdv (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (S : Finset (Fin m)) :
    prOutNoFindMRGen A H f S = prOutNoFind (toQAdv (dilate A) f) H S := by
  rw [← prOutNoFindMR_eq, ← prOutNoFindMRGen_toGen]
  unfold prOutNoFindMRGen
  rw [prSCMRGen_dilate]

/-- `Pr[Find]` of a general adversary is that of the single-run embedding of its
dilation. -/
theorem prFindMRGen_eq_toQAdv (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (S : Finset (Fin m)) :
    prFindMRGen A H f S = prFind (toQAdv (dilate A) f) H S := by
  rw [← prFindMR_eq, ← prFindMRGen_toGen]
  unfold prFindMRGen
  rw [prSCMRGen_dilate]

/-- `Pr[out = 1 ∧ ¬Find]` of a general adversary is the same for two oracles
that agree outside `S`. -/
theorem prOutNoFindMRGen_congr (A : QAdvMRGen m n w q k c a) (H H' : Fin m → Fin n)
    (f : Fin c → Fin a) (S : Finset (Fin m)) (hHH' : ∀ x, x ∉ S → H x = H' x) :
    prOutNoFindMRGen A H f S = prOutNoFindMRGen A H' f S := by
  rw [prOutNoFindMRGen_eq_toQAdv, prOutNoFindMRGen_eq_toQAdv,
    prOutNoFind_congr_mixed _ H H' S hHH']

/-- `Pr[Find]` of a general adversary is the same for two oracles that agree
outside `S`. -/
theorem prFindMRGen_congr (A : QAdvMRGen m n w q k c a) (H H' : Fin m → Fin n)
    (f : Fin c → Fin a) (S : Finset (Fin m)) (hHH' : ∀ x, x ∉ S → H x = H' x) :
    prFindMRGen A H f S = prFindMRGen A H' f S := by
  rw [prFindMRGen_eq_toQAdv, prFindMRGen_eq_toQAdv, prFind_congr_mixed _ H H' S hHH']

/-- Find-to-guess for a general multi-round adversary:
`Pr[Find] ≤ 4 ∑ⱼ guessProb B H S j` for the single-run adversary
`B = toQAdv (dilate A) f`, whose `flatQ q k q` queries are those of `A`.

References: Ambainis, Hamburg, Unruh, "Quantum security proofs using
semi-classical oracles", CRYPTO 2019, ePrint 2018/904, Theorem 2. -/
theorem prFindMRGen_le_four_sum_guess (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (S : Finset (Fin m)) :
    prFindMRGen A H f S ≤ 4 * ∑ j, guessProb (toQAdv (dilate A) f) H S j := by
  rw [prFindMRGen_eq_toQAdv]
  exact prFind_le_four_sum_guess_mixed _ H S

/-- A sum over a finset is the sum over the whole type with the indicator. -/
theorem sum_mem_eq_sum_boole_mul {α : Type} [Fintype α] [DecidableEq α] (S : Finset α)
    (g : α → ℝ≥0∞) : ∑ x ∈ S, g x = ∑ x, (if x ∈ S then 1 else 0) * g x := by
  simp [Finset.sum_ite_mem]

/-- The averaged Find bound: for weights `μ` on pairs `(H ω, S ω)` whose
oracles agree with a fixed `H₀` outside `S ω`, and `∑_ω μ ω · [x ∈ S ω] ≤ λ` at
every `x`, `∑_ω μ ω · Pr[Find] ≤ 4 · flatQ q k q · λ`. The set `S` is
independent of the oracle outside `S` (it is `H₀` there), of the round function
`f` and of the adversary. -/
theorem prFindMRGen_avg_le {Ω : Type} [Fintype Ω] (A : QAdvMRGen m n w q k c a)
    (f : Fin c → Fin a) (H : Ω → Fin m → Fin n) (S : Ω → Finset (Fin m))
    (H₀ : Fin m → Fin n) (μ : Ω → ℝ≥0∞) (lam : ℝ≥0∞)
    (hagree : ∀ ω, μ ω ≠ 0 → ∀ x, x ∉ S ω → H ω x = H₀ x)
    (hlam : ∀ x, ∑ ω, μ ω * (if x ∈ S ω then 1 else 0) ≤ lam) :
    ∑ ω, μ ω * prFindMRGen A (H ω) f (S ω) ≤ 4 * (flatQ q k q : ℝ≥0∞) * lam := by
  set B := toQAdv (dilate A) f
  calc ∑ ω, μ ω * prFindMRGen A (H ω) f (S ω)
      ≤ ∑ ω, μ ω * (4 * ∑ j, ∑ x, (if x ∈ S ω then 1 else 0) * guessProb B H₀ {x} j) := by
        refine Finset.sum_le_sum fun ω _ => ?_
        by_cases hμ : μ ω = 0
        · simp [hμ]
        gcongr
        rw [prFindMRGen_congr A (H ω) H₀ f (S ω) (hagree ω hμ)]
        refine (prFindMRGen_le_four_sum_guess A H₀ f (S ω)).trans (le_of_eq ?_)
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [guessProb_eq_sum_singleton_mixed, sum_mem_eq_sum_boole_mul]
    _ = 4 * ∑ j, ∑ x, guessProb B H₀ {x} j * ∑ ω, μ ω * (if x ∈ S ω then 1 else 0) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun ω _ => ?_
        ring
    _ ≤ 4 * ∑ j, ∑ x, guessProb B H₀ {x} j * lam := by
        gcongr with j _ x _
        exact hlam x
    _ = 4 * ∑ j, lam * ∑ x, guessProb B H₀ {x} j := by
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    _ ≤ 4 * ∑ j : Fin (flatQ q k q), lam * 1 := by
        gcongr with j _
        exact sum_guessProb_singleton_le_one_mixed B H₀ j
    _ = 4 * (flatQ q k q : ℝ≥0∞) * lam := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        ring

end General

/-! ## Classical rounds up to bad -/

section Rounds

variable {d c a : ℕ}

/-- The weight `∑_{y ∈ D} tr (P_y σ)` of the outcomes in `D` of the measurement
of the round `R` on `σ`. -/
def roundBad (R : ClassicalRound d c a) (D : Finset (Fin c)) (σ : Matrix (Fin d) (Fin d) ℂ) :
    ℝ :=
  ∑ y ∈ D, (R.P y * σ).trace.re

/-- The part `∑_{y ∈ D} K_y σ K_yᴴ`, `K_y = ans (f y) P y`, of the round channel
with classical function `f` at the outcomes in `D`. -/
def roundPart (R : ClassicalRound d c a) (f : Fin c → Fin a) (D : Finset (Fin c))
    (σ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ y ∈ D, ((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y) * σ *
    ((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y)ᴴ

theorem roundBad_add (R : ClassicalRound d c a) (D : Finset (Fin c))
    (σ τ : Matrix (Fin d) (Fin d) ℂ) : roundBad R D (σ + τ) = roundBad R D σ + roundBad R D τ := by
  simp [roundBad, Matrix.mul_add, trace_add, Finset.sum_add_distrib]

theorem roundBad_nonneg (R : ClassicalRound d c a) (D : Finset (Fin c))
    {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : σ.PosSemidef) : 0 ≤ roundBad R D σ := by
  refine Finset.sum_nonneg fun y _ => ?_
  have hP : (R.P y).PosSemidef := by
    have h := posSemidef_conjTranspose_mul_self (R.P y)
    rwa [R.P_conjTranspose, R.P_mul_self] at h
  exact (Complex.nonneg_iff.mp (trace_psd_mul_psd_nonneg _ _ hP hσ)).1

theorem roundBad_eq_sum_singleton (R : ClassicalRound d c a) (D : Finset (Fin c))
    (σ : Matrix (Fin d) (Fin d) ℂ) : roundBad R D σ = ∑ y ∈ D, roundBad R {y} σ := by
  simp [roundBad]

theorem roundBad_univ (R : ClassicalRound d c a) (σ : Matrix (Fin d) (Fin d) ℂ) :
    roundBad R Finset.univ σ = σ.trace.re := by
  unfold roundBad
  rw [← Complex.re_sum, ← trace_sum, ← Finset.sum_mul, R.P_sum, one_mul]

theorem roundU_branch_eq_add (R : ClassicalRound d c a) (f : Fin c → Fin a)
    (D : Finset (Fin c)) (σ : Matrix (Fin d) (Fin d) ℂ) :
    (roundU R f).branch () σ = roundPart R f Dᶜ σ + roundPart R f D σ := by
  rw [roundU_branch, roundPart, roundPart, add_comm]
  exact (Finset.sum_add_sum_compl D _).symm

theorem roundPart_congr (R : ClassicalRound d c a) {f f' : Fin c → Fin a}
    {D : Finset (Fin c)} (hf : ∀ y, y ∉ D → f' y = f y) (σ : Matrix (Fin d) (Fin d) ℂ) :
    roundPart R f' Dᶜ σ = roundPart R f Dᶜ σ :=
  Finset.sum_congr rfl fun y hy => by rw [hf y (Finset.mem_compl.mp hy)]

theorem roundPart_posSemidef (R : ClassicalRound d c a) (f : Fin c → Fin a)
    (D : Finset (Fin c)) {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : σ.PosSemidef) :
    (roundPart R f D σ).PosSemidef :=
  Matrix.posSemidef_sum D fun _ _ => hσ.mul_mul_conjTranspose_same _

theorem trace_roundPart (R : ClassicalRound d c a) (f : Fin c → Fin a) (D : Finset (Fin c))
    (σ : Matrix (Fin d) (Fin d) ℂ) : (roundPart R f D σ).trace.re = roundBad R D σ := by
  unfold roundPart roundBad
  rw [trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [trace_mul_cycle, conjTranspose_mul, R.P_conjTranspose, Matrix.mul_assoc (R.P y),
    ← Matrix.mul_assoc _ _ (R.P y), ← star_eq_conjTranspose, UnitaryGroup.star_mul_self,
    one_mul, R.P_mul_self]

/-- The sum over the rounds of the weight of the outcomes in `D`, each measured
on the state that the chain with the classical function `f` reaches before the
round. -/
def badW (O : QComp d Unit) (f : Fin c → Fin a) (D : Finset (Fin c)) {q : ℕ} :
    (k : ℕ) → (q₀ : ℕ) → (Fin (q₀ + 1) → QComp d Unit) →
      (Fin k → Fin (q + 1) → QComp d Unit) → (Fin k → ClassicalRound d c a) →
      Matrix (Fin d) (Fin d) ℂ → ℝ
  | 0, _, _, _, _, _ => 0
  | k + 1, q₀, head, tail, R, σ =>
    roundBad (R 0) D ((chainG O q₀ head).branch () σ) +
      badW O f D k q (tail 0) (Fin.tail tail) (Fin.tail R)
        ((roundU (R 0) f).branch () ((chainG O q₀ head).branch () σ))

variable {q : ℕ}

theorem badW_add (O : QComp d Unit) (f : Fin c → Fin a) (D : Finset (Fin c)) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → QComp d Unit) (tail : Fin k → Fin (q + 1) → QComp d Unit)
      (R : Fin k → ClassicalRound d c a) (σ τ : Matrix (Fin d) (Fin d) ℂ),
      badW O f D k q₀ head tail R (σ + τ) =
        badW O f D k q₀ head tail R σ + badW O f D k q₀ head tail R τ
  | 0, _, _, _, _, _, _ => by simp [badW]
  | k + 1, q₀, head, tail, R, σ, τ => by
    simp only [badW, map_add, roundBad_add,
      badW_add O f D k q (tail 0) (Fin.tail tail) (Fin.tail R)]
    ring

theorem badW_nonneg (O : QComp d Unit) (f : Fin c → Fin a) (D : Finset (Fin c)) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → QComp d Unit) (tail : Fin k → Fin (q + 1) → QComp d Unit)
      (R : Fin k → ClassicalRound d c a) (σ : Matrix (Fin d) (Fin d) ℂ), σ.PosSemidef →
      0 ≤ badW O f D k q₀ head tail R σ
  | 0, _, _, _, _, _, _ => le_rfl
  | k + 1, q₀, head, tail, R, σ, hσ => by
    have h₁ := (chainG O q₀ head).branch_psd () σ hσ
    exact add_nonneg (roundBad_nonneg _ _ h₁)
      (badW_nonneg O f D k q (tail 0) (Fin.tail tail) (Fin.tail R) _
        ((roundU (R 0) f).branch_psd () _ h₁))

theorem badW_le_add (O : QComp d Unit) (f : Fin c → Fin a) (D : Finset (Fin c)) (k q₀ : ℕ)
    (head : Fin (q₀ + 1) → QComp d Unit) (tail : Fin k → Fin (q + 1) → QComp d Unit)
    (R : Fin k → ClassicalRound d c a) (σ : Matrix (Fin d) (Fin d) ℂ)
    {τ : Matrix (Fin d) (Fin d) ℂ} (hτ : τ.PosSemidef) :
    badW O f D k q₀ head tail R σ ≤ badW O f D k q₀ head tail R (σ + τ) := by
  rw [badW_add]
  linarith [badW_nonneg O f D k q₀ head tail R τ hτ]

theorem badW_eq_sum_singleton (O : QComp d Unit) (f : Fin c → Fin a) (D : Finset (Fin c)) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → QComp d Unit) (tail : Fin k → Fin (q + 1) → QComp d Unit)
      (R : Fin k → ClassicalRound d c a) (σ : Matrix (Fin d) (Fin d) ℂ),
      badW O f D k q₀ head tail R σ = ∑ y ∈ D, badW O f {y} k q₀ head tail R σ
  | 0, _, _, _, _, _ => by simp [badW]
  | k + 1, q₀, head, tail, R, σ => by
    simp only [badW]
    rw [badW_eq_sum_singleton O f D k q (tail 0) (Fin.tail tail) (Fin.tail R),
      roundBad_eq_sum_singleton, ← Finset.sum_add_distrib]

/-- A `Unit` instrument does not increase the trace of a positive matrix. -/
theorem trace_re_branch_unit_le (C : QComp d Unit) {σ : Matrix (Fin d) (Fin d) ℂ}
    (hσ : σ.PosSemidef) : (C.branch () σ).trace.re ≤ σ.trace.re := by
  have h := C.branch_stp σ hσ
  simpa using h

/-- The `true` branch of a `Bool` instrument does not exceed the trace of a
positive matrix. -/
theorem trace_re_branch_true_le (E : QComp d Bool) {σ : Matrix (Fin d) (Fin d) ℂ}
    (hσ : σ.PosSemidef) : (E.branch true σ).trace.re ≤ σ.trace.re := by
  have h := E.branch_stp σ hσ
  rw [tsum_fintype, Fintype.sum_bool, Complex.add_re] at h
  have h0 := (Complex.nonneg_iff.mp (E.branch_psd false σ hσ).trace_nonneg).1
  linarith

theorem trace_re_nonneg_of_posSemidef {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : σ.PosSemidef) :
    0 ≤ σ.trace.re :=
  (Complex.nonneg_iff.mp hσ.trace_nonneg).1

theorem badW_univ_le (O : QComp d Unit) (f : Fin c → Fin a) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → QComp d Unit) (tail : Fin k → Fin (q + 1) → QComp d Unit)
      (R : Fin k → ClassicalRound d c a) (σ : Matrix (Fin d) (Fin d) ℂ), σ.PosSemidef →
      badW O f Finset.univ k q₀ head tail R σ ≤ k * σ.trace.re
  | 0, _, _, _, _, σ, _ => by simp [badW]
  | k + 1, q₀, head, tail, R, σ, hσ => by
    have h₁ := (chainG O q₀ head).branch_psd () σ hσ
    have h₂ := (roundU (R 0) f).branch_psd () _ h₁
    have ih := badW_univ_le O f k q (tail 0) (Fin.tail tail) (Fin.tail R) _ h₂
    have t₁ := trace_re_branch_unit_le (chainG O q₀ head) hσ
    have t₂ := trace_re_branch_unit_le (roundU (R 0) f) h₁
    have t₀ := trace_re_nonneg_of_posSemidef hσ
    simp only [badW, roundBad_univ]
    push_cast
    nlinarith

/-- Two classical functions of the rounds that agree outside `D` change the
value `tr (E_true (C σ))` of a final measurement `E` after the multi-round
chain `C` by at most `badW`, the weight of the outcomes in `D` in the chain
with `f`. -/
theorem abs_eff_mrChainG_sub_le (O : QComp d Unit) (E : QComp d Bool) {f f' : Fin c → Fin a}
    {D : Finset (Fin c)} (hf : ∀ y, y ∉ D → f' y = f y) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → QComp d Unit) (tail : Fin k → Fin (q + 1) → QComp d Unit)
      (R : Fin k → ClassicalRound d c a) (σ : Matrix (Fin d) (Fin d) ℂ), σ.PosSemidef →
      |(E.branch true ((mrChainG O f k q₀ head tail R).branch () σ)).trace.re -
        (E.branch true ((mrChainG O f' k q₀ head tail R).branch () σ)).trace.re| ≤
        badW O f D k q₀ head tail R σ
  | 0, _, _, _, _, _, _ => by simp [mrChainG, badW]
  | k + 1, q₀, head, tail, R, σ, hσ => by
    set σ₁ := (chainG O q₀ head).branch () σ with hσ₁def
    have hσ₁ : σ₁.PosSemidef := (chainG O q₀ head).branch_psd () σ hσ
    set rest := mrChainG O f k q (tail 0) (Fin.tail tail) (Fin.tail R)
    set rest' := mrChainG O f' k q (tail 0) (Fin.tail tail) (Fin.tail R)
    have hC : (mrChainG O f (k + 1) q₀ head tail R).branch () σ =
        rest.branch () ((roundU (R 0) f).branch () σ₁) := by
      simp only [mrChainG, qbind_unit_branch, rest, σ₁]
    have hC' : (mrChainG O f' (k + 1) q₀ head tail R).branch () σ =
        rest'.branch () ((roundU (R 0) f').branch () σ₁) := by
      simp only [mrChainG, qbind_unit_branch, rest', σ₁]
    have hs := roundU_branch_eq_add (R 0) f D σ₁
    have hs' := roundU_branch_eq_add (R 0) f' D σ₁
    rw [roundPart_congr (R 0) hf] at hs'
    have hG := roundPart_posSemidef (R 0) f Dᶜ hσ₁
    have hB := roundPart_posSemidef (R 0) f D hσ₁
    have hB' := roundPart_posSemidef (R 0) f' D hσ₁
    have ih := abs_eff_mrChainG_sub_le O E hf k q (tail 0) (Fin.tail tail) (Fin.tail R) _ hG
    have hmono := badW_le_add O f D k q (tail 0) (Fin.tail tail) (Fin.tail R)
      (roundPart (R 0) f Dᶜ σ₁) hB
    rw [← hs] at hmono
    have a₁ := trace_re_nonneg_of_posSemidef (E.branch_psd true _ (rest.branch_psd () _ hB))
    have a₁' := trace_re_nonneg_of_posSemidef (E.branch_psd true _ (rest'.branch_psd () _ hB'))
    have a₂ := (trace_re_branch_true_le E (rest.branch_psd () _ hB)).trans
      (trace_re_branch_unit_le rest hB)
    have a₂' := (trace_re_branch_true_le E (rest'.branch_psd () _ hB')).trans
      (trace_re_branch_unit_le rest' hB')
    rw [trace_roundPart] at a₂ a₂'
    rw [hC, hC', hs, hs', map_add, map_add, map_add, map_add, trace_add, trace_add,
      Complex.add_re, Complex.add_re]
    simp only [badW]
    rw [← hσ₁def]
    rw [abs_le] at ih ⊢
    constructor <;> linarith [ih.1, ih.2]

end Rounds

section RoundsAdv

variable {m n w q k c a : ℕ} [NeZero n]

/-- Two classical functions of the rounds that agree outside `D` change the
acceptance probability of a general adversary by at most `badW`, measured in
the run with `f`. -/
theorem absDiff_prOutMRGen_le_badW (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n)
    {f f' : Fin c → Fin a} {D : Finset (Fin c)} (hf : ∀ y, y ∉ D → f' y = f y) :
    absDiff (prOutMRGen A H f) (prOutMRGen A H f') ≤
      ENNReal.ofReal (badW (oracleQ m n w H) f D k q (fun i => (A.seg 0 i).toQComp)
        (fun j i => (Fin.tail A.seg j i).toQComp) A.rounds A.init.val) := by
  unfold prOutMRGen prTrue_Q runMRGen
  rw [qbind_unit_branch, qbind_unit_branch]
  have hp := A.init.psd
  have h₀ : ∀ C : QComp (m * n * w) Unit,
      0 ≤ (A.measure.branch true (C.branch () A.init.val)).trace.re := fun C =>
    trace_re_nonneg_of_posSemidef (A.measure.branch_psd true _ (C.branch_psd () _ hp))
  refine (absDiff_ofReal_le (h₀ _) (h₀ _)).trans (ENNReal.ofReal_le_ofReal ?_)
  exact abs_eff_mrChainG_sub_le _ A.measure hf k q _ _ _ _ hp

/-- Up to bad in the classical rounds: if `f' ω` agrees with `f` outside
`D ω`, and the law `μ` of `ω` satisfies `∑_ω μ ω · [y ∈ D ω] ≤ λ` at every
outcome `y`, then the acceptance probability of `A` with `f` and its average
with `f' ω` differ by at most `k · λ`. The set `D` is independent of the run
with `f`, which does not depend on `ω`. -/
theorem rounds_upto_bad {Ω : Type} [Fintype Ω] (A : QAdvMRGen m n w q k c a)
    (H : Fin m → Fin n) (f : Fin c → Fin a) (f' : Ω → Fin c → Fin a)
    (D : Ω → Finset (Fin c)) (μ : Ω → ℝ≥0∞) (lam : ℝ≥0∞) (hμ : ∑ ω, μ ω = 1)
    (hf : ∀ ω y, y ∉ D ω → f' ω y = f y)
    (hlam : ∀ y, ∑ ω, μ ω * (if y ∈ D ω then 1 else 0) ≤ lam) :
    absDiff (prOutMRGen A H f) (∑ ω, μ ω * prOutMRGen A H (f' ω)) ≤ k * lam := by
  set W : Fin c → ℝ := fun y => badW (oracleQ m n w H) f {y} k q
    (fun i => (A.seg 0 i).toQComp) (fun j i => (Fin.tail A.seg j i).toQComp) A.rounds
    A.init.val
  have hW : ∀ y, 0 ≤ W y := fun y => badW_nonneg _ _ _ _ _ _ _ _ _ A.init.psd
  have hWsum : ∑ y, W y ≤ k := by
    have h := badW_univ_le (oracleQ m n w H) f k q (fun i => (A.seg 0 i).toQComp)
      (fun j i => (Fin.tail A.seg j i).toQComp) A.rounds A.init.val A.init.psd
    rw [badW_eq_sum_singleton, A.init.tr_one, Complex.one_re, mul_one] at h
    exact h
  calc absDiff (prOutMRGen A H f) (∑ ω, μ ω * prOutMRGen A H (f' ω))
      = absDiff (∑ ω, μ ω * prOutMRGen A H f) (∑ ω, μ ω * prOutMRGen A H (f' ω)) := by
        rw [← Finset.sum_mul, hμ, one_mul]
    _ ≤ ∑ ω, absDiff (μ ω * prOutMRGen A H f) (μ ω * prOutMRGen A H (f' ω)) :=
        absDiff_sum_le _ _
    _ ≤ ∑ ω, μ ω * absDiff (prOutMRGen A H f) (prOutMRGen A H (f' ω)) :=
        Finset.sum_le_sum fun ω _ => absDiff_mul_left_le _ _ _
    _ ≤ ∑ ω, μ ω * ∑ y, (if y ∈ D ω then 1 else 0) * ENNReal.ofReal (W y) := by
        gcongr with ω
        refine (absDiff_prOutMRGen_le_badW A H (hf ω)).trans (le_of_eq ?_)
        rw [badW_eq_sum_singleton, ENNReal.ofReal_sum_of_nonneg fun y _ => hW y,
          sum_mem_eq_sum_boole_mul]
    _ = ∑ y, ENNReal.ofReal (W y) * ∑ ω, μ ω * (if y ∈ D ω then 1 else 0) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun ω _ => by ring
    _ ≤ ∑ y, ENNReal.ofReal (W y) * lam := by
        gcongr with y
        exact hlam y
    _ = ENNReal.ofReal (∑ y, W y) * lam := by
        rw [ENNReal.ofReal_sum_of_nonneg fun y _ => hW y, Finset.sum_mul]
    _ ≤ k * lam := by
        gcongr
        exact (ENNReal.ofReal_le_ofReal hWsum).trans (by simp)

end RoundsAdv

end CatCrypt.Quantum.QROM
