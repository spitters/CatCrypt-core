/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.RoundOracleLocal

/-!
# Resampling an oracle on a conditionally sparse set, by the query hybrid

A multi-round adversary `A : QAdvMRGen m n w q k c a` is run against two random
oracles `H₁ ω` and `H₂ ω` that agree outside a random set `D ω` of oracle
points, with a random round function `f ω`. If, conditioned on `(H₂ ω, f ω)`,
every point lies in `D ω` with probability at most `λ`, the averaged acceptance
probabilities differ by at most `2 Q λ^(1/2)`, with `Q = flatQ q k q` the total
query count of `A`.

The proof is the hybrid argument over the queries of the single-run embedding
of the dilated adversary. The hybrid `i` answers the first `i` queries with
`H₂` and the others with `H₁`; consecutive hybrids differ at one query, whose
input state depends on `(H₂, f)` only. Two oracles agreeing outside `D` differ
on a vector `θ` by at most `2 ‖Π_D θ‖`, so the final vectors differ by at most
`2 ∑ᵢ ‖Π_D θᵢ‖`. For vectors `x`, `y` of equal norm and an orthogonal
projector `M`, `|‖M x‖² − ‖M y‖²| ≤ ‖x‖ ‖x − y‖`, which gives the constant `2`
per query. Cauchy–Schwarz over the components of the initial state, Jensen's
inequality for the square root over `ω` and the conditional sparsity of `D`
bound the averaged term of each query by `2 λ^(1/2)`.

## Main results

* `nrm_chainOp_sub_chainOp_le` — the chains of two oracles differ by at most
  the sum of the oracle differences at the states of the second chain
* `abs_nrm_sq_proj_sub_le` — `|‖M x‖² − ‖M y‖²| ≤ ‖x‖ ‖x − y‖` for
  `‖x‖ = ‖y‖`
* `absDiff_prOut_le_two_sum_rpow_guessProb` — two oracles agreeing outside `S`
  change `Pr[out = 1]` by at most `2 ∑ⱼ guessProb_j^(1/2)`
* `prOutMRGen_resample_gentle_le` — the resampling bound `2 Q λ^(1/2)` for a
  set conditionally sparse given the second oracle and the round function

## References

* [Bennett, Bernstein, Brassard, Vazirani — Strengths and Weaknesses of Quantum
  Computing, SIAM J. Comput. 26(5), 1997], the hybrid argument
* [Barbosa, Barthe, Doczkal, Don, Fehr, Grégoire, Huang, Hülsing, Lee, Wu —
  Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and
  Dilithium, CRYPTO 2023, ePrint 2023/246], Lemma 5
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Vector bounds -/

section Vector

variable {d : ℕ}

/-- The hybrid bound for two oracles: the chains `chainOp O₁` and `chainOp O₂`
on `ψ` differ by at most `∑ᵢ ‖(O₁ − O₂) θᵢ‖`, with `θᵢ` the states before
each query of the chain of `O₂`. -/
theorem nrm_chainOp_sub_chainOp_le {O₁ : Matrix (Fin d) (Fin d) ℂ}
    (O₂ : Matrix (Fin d) (Fin d) ℂ) (hO₁ : O₁ ∈ Matrix.unitaryGroup (Fin d) ℂ) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (ψ : Fin d → ℂ) :
    nrm (chainOp O₁ q U *ᵥ ψ - chainOp O₂ q U *ᵥ ψ) ≤
      ∑ i, nrm ((O₁ - O₂) *ᵥ scStates O₂ q U ψ i) := by
  induction q generalizing ψ with
  | zero => simp [chainOp]
  | succ q ih =>
    rw [chainOp_succ_mulVec, chainOp_succ_mulVec, Fin.sum_univ_succ]
    simp only [scStates, Fin.cons_zero, Fin.cons_succ]
    set x := O₁ *ᵥ ((U 0 : Matrix _ _ ℂ) *ᵥ ψ)
    set y := O₂ *ᵥ ((U 0 : Matrix _ _ ℂ) *ᵥ ψ)
    have hxy : x - y = (O₁ - O₂) *ᵥ ((U 0 : Matrix _ _ ℂ) *ᵥ ψ) := by
      simp only [x, y, sub_mulVec]
    have hsplit : chainOp O₁ q (Fin.tail U) *ᵥ x - chainOp O₂ q (Fin.tail U) *ᵥ y =
        chainOp O₁ q (Fin.tail U) *ᵥ (x - y) +
          (chainOp O₁ q (Fin.tail U) *ᵥ y - chainOp O₂ q (Fin.tail U) *ᵥ y) := by
      rw [mulVec_sub]; abel
    rw [hsplit]
    refine (nrm_add_le _ _).trans (add_le_add (le_of_eq ?_) (ih (Fin.tail U) y))
    rw [hxy, nrm_chainOp_mulVec_eq O₁ (nrm_mulVec_of_mem_unitaryGroup hO₁)]

/-- Two unitaries that agree on the range of `1 − P` differ on `v` by at most
`2 ‖P v‖`. -/
theorem nrm_sub_mulVec_le_two_nrm_proj {O₁ O₂ P : Matrix (Fin d) (Fin d) ℂ}
    (hO₁ : O₁ ∈ Matrix.unitaryGroup (Fin d) ℂ) (hO₂ : O₂ ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hagree : O₁ * (1 - P) = O₂ * (1 - P)) (v : Fin d → ℂ) :
    nrm ((O₁ - O₂) *ᵥ v) ≤ 2 * nrm (P *ᵥ v) := by
  have hP : O₁ - O₂ = (O₁ - O₂) * P := by
    have h0 : (O₁ - O₂) * (1 - P) = 0 := by rw [sub_mul, hagree, sub_self]
    calc O₁ - O₂ = (O₁ - O₂) * P + (O₁ - O₂) * (1 - P) := by
          rw [← mul_add, add_sub_cancel, mul_one]
      _ = (O₁ - O₂) * P := by rw [h0, add_zero]
  rw [hP, ← mulVec_mulVec, sub_mulVec]
  calc nrm (O₁ *ᵥ (P *ᵥ v) - O₂ *ᵥ (P *ᵥ v))
      ≤ nrm (O₁ *ᵥ (P *ᵥ v)) + nrm (O₂ *ᵥ (P *ᵥ v)) := by
        unfold nrm
        rw [WithLp.toLp_sub]
        exact norm_sub_le _ _
    _ = 2 * nrm (P *ᵥ v) := by
        rw [nrm_mulVec_of_mem_unitaryGroup hO₁, nrm_mulVec_of_mem_unitaryGroup hO₂]
        ring

/-- The real inequality behind `abs_nrm_sq_proj_sub_le`: with `a² + c² = r²`,
`b² + e² = r²`, `|a − b| ≤ u`, `|c − e| ≤ v` and `u² + v² = T²`,
`|a² − b²| ≤ r T`. -/
theorem abs_sq_sub_sq_le_of_pythag {a b c e u v r T : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (he : 0 ≤ e) (hr : 0 ≤ r) (hT : 0 ≤ T) (hab : |a - b| ≤ u)
    (hce : |c - e| ≤ v) (hx : a ^ 2 + c ^ 2 = r ^ 2) (hy : b ^ 2 + e ^ 2 = r ^ 2)
    (ht : u ^ 2 + v ^ 2 = T ^ 2) :
    |a ^ 2 - b ^ 2| ≤ r * T := by
  have hu : 0 ≤ u := (abs_nonneg _).trans hab
  have hv : 0 ≤ v := (abs_nonneg _).trans hce
  have h1 : 2 * |a ^ 2 - b ^ 2| ≤ u * (a + b) + v * (c + e) := by
    have hid : 2 * (a ^ 2 - b ^ 2) = (a - b) * (a + b) + (e - c) * (e + c) := by
      linear_combination hx - hy
    calc 2 * |a ^ 2 - b ^ 2| = |(a - b) * (a + b) + (e - c) * (e + c)| := by
          rw [← hid, abs_mul, abs_two]
      _ ≤ |a - b| * (a + b) + |e - c| * (e + c) := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_of_nonneg (add_nonneg ha hb),
            abs_of_nonneg (add_nonneg he hc)]
      _ ≤ u * (a + b) + v * (c + e) := by
          rw [abs_sub_comm e c, add_comm e c]
          gcongr
  have h2 : (u * (a + b) + v * (c + e)) ^ 2 ≤ (u ^ 2 + v ^ 2) * ((a + b) ^ 2 + (c + e) ^ 2) := by
    nlinarith [sq_nonneg (u * (c + e) - v * (a + b))]
  have h3 : (a + b) ^ 2 + (c + e) ^ 2 ≤ 4 * r ^ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (c - e)]
  have h4 : (2 * |a ^ 2 - b ^ 2|) ^ 2 ≤ (2 * (r * T)) ^ 2 := by
    calc (2 * |a ^ 2 - b ^ 2|) ^ 2 ≤ (u * (a + b) + v * (c + e)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ ≤ (u ^ 2 + v ^ 2) * ((a + b) ^ 2 + (c + e) ^ 2) := h2
      _ ≤ T ^ 2 * (4 * r ^ 2) := by rw [ht]; gcongr
      _ = (2 * (r * T)) ^ 2 := by ring
  have h5 := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h4
  linarith

/-- For vectors of equal norm and an orthogonal projector `P`:
`|‖P x‖² − ‖P y‖²| ≤ ‖x‖ ‖x − y‖`. -/
theorem abs_nrm_sq_proj_sub_le {P : Matrix (Fin d) (Fin d) ℂ} (hI : P * P = P) (hH : Pᴴ = P)
    {x y : Fin d → ℂ} (hxy : nrm x = nrm y) :
    |nrm (P *ᵥ x) ^ 2 - nrm (P *ᵥ y) ^ 2| ≤ nrm x * nrm (x - y) := by
  have px := nrm_sq_proj_add_nrm_sq_one_sub_proj hI hH x
  have py := nrm_sq_proj_add_nrm_sq_one_sub_proj hI hH y
  have pt := nrm_sq_proj_add_nrm_sq_one_sub_proj hI hH (x - y)
  have hu : |nrm (P *ᵥ x) - nrm (P *ᵥ y)| ≤ nrm (P *ᵥ (x - y)) := by
    rw [mulVec_sub]; exact abs_nrm_sub_nrm_le _ _
  have hv : |nrm ((1 - P) *ᵥ x) - nrm ((1 - P) *ᵥ y)| ≤ nrm ((1 - P) *ᵥ (x - y)) := by
    rw [mulVec_sub]; exact abs_nrm_sub_nrm_le _ _
  rw [hxy] at px
  have h := abs_sq_sub_sq_le_of_pythag (nrm_nonneg _) (nrm_nonneg _) (nrm_nonneg _)
    (nrm_nonneg _) (nrm_nonneg y) (nrm_nonneg (x - y)) hu hv px py pt
  rwa [hxy]

end Vector

/-! ## Two oracles agreeing outside a set -/

section Adv

variable {m n w q : ℕ} [NeZero n]

/-- On a vector `ψ` of any norm, two oracles agreeing outside `S` change the
acceptance weight by at most `2 ‖ψ‖ ∑ⱼ ‖Π_S θⱼ‖`, with `θⱼ` the plain states of
the run against `H₂`. -/
theorem abs_nrm_sq_runOp_sub_le (B : QAdv m n w q) (H₁ H₂ : Fin m → Fin n)
    (S : Finset (Fin m)) (hS : ∀ x, x ∉ S → H₁ x = H₂ x) (ψ : Fin (m * n * w) → ℂ) :
    |nrm (B.final *ᵥ (runOp B H₁ *ᵥ ψ)) ^ 2 - nrm (B.final *ᵥ (runOp B H₂ *ᵥ ψ)) ^ 2| ≤
      2 * nrm ψ * ∑ j, nrm (projS m n w S *ᵥ plainState B H₂ ψ j) := by
  have hO₁ := (oracleU m n w H₁).prop
  have hO₂ := (oracleU m n w H₂).prop
  have h₁ : nrm (runOp B H₁ *ᵥ ψ) = nrm ψ :=
    nrm_chainOp_mulVec_eq _ (nrm_mulVec_of_mem_unitaryGroup hO₁) q B.U ψ
  have h₂ : nrm (runOp B H₂ *ᵥ ψ) = nrm ψ :=
    nrm_chainOp_mulVec_eq _ (nrm_mulVec_of_mem_unitaryGroup hO₂) q B.U ψ
  have hdiff : nrm (runOp B H₁ *ᵥ ψ - runOp B H₂ *ᵥ ψ) ≤
      2 * ∑ j, nrm (projS m n w S *ᵥ plainState B H₂ ψ j) := by
    refine (nrm_chainOp_sub_chainOp_le _ hO₁ q B.U ψ).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => nrm_sub_mulVec_le_two_nrm_proj hO₁ hO₂
      (oracleU_mul_one_sub_projS (w := w) H₁ H₂ S hS) _
  calc _ ≤ nrm (runOp B H₁ *ᵥ ψ) * nrm (runOp B H₁ *ᵥ ψ - runOp B H₂ *ᵥ ψ) :=
        abs_nrm_sq_proj_sub_le B.final_mul_self B.final_conjTranspose (h₁.trans h₂.symm)
    _ ≤ nrm ψ * (2 * ∑ j, nrm (projS m n w S *ᵥ plainState B H₂ ψ j)) := by
        rw [h₁]
        exact mul_le_mul_of_nonneg_left hdiff (nrm_nonneg ψ)
    _ = _ := by ring

/-- The query hybrid for an adversary with any initial state: two oracles that
agree outside `S` change `Pr[out = 1]` by at most `2 ∑ⱼ guessProb_j^(1/2)`,
with `guessProb_j` the probability that the query register of the run against
`H₂`, measured before query `j`, lies in `S`. -/
theorem absDiff_prOut_le_two_sum_rpow_guessProb (B : QAdv m n w q) (H₁ H₂ : Fin m → Fin n)
    (S : Finset (Fin m)) (hS : ∀ x, x ∉ S → H₁ x = H₂ x) :
    absDiff (prOut B H₁) (prOut B H₂) ≤ 2 * ∑ j, guessProb B H₂ S j ^ (1 / 2 : ℝ) := by
  obtain ⟨ψ, hρ⟩ := exists_eq_sum_vecMulVec_of_posSemidef B.init.psd
  have hout : ∀ H, prOut B H =
      ENNReal.ofReal (∑ k, nrm (B.final *ᵥ (runOp B H *ᵥ ψ k)) ^ 2) := by
    intro H
    unfold prOut prTrue_Q
    rw [run_branch_true, hρ, trace_mul_sum_vecMulVec_mul_conjTranspose, Complex.ofReal_re]
    simp only [mulVec_mulVec]
  have hnorm : ∑ k, nrm (ψ k) ^ 2 = 1 := by
    have h := B.init.tr_one
    rw [hρ, trace_sum_vecMulVec] at h
    exact_mod_cast h
  set δ : Fin q → Fin (m * n * w) → ℝ :=
    fun j k => nrm (projS m n w S *ᵥ plainState B H₂ (ψ k) j) with hδ
  have hguess : ∀ j, guessProb B H₂ S j = ENNReal.ofReal (∑ k, δ j k ^ 2) := fun j =>
    guessProb_eq_sum_nrm_sq B H₂ S j ψ hρ
  have hcs : ∀ j, ∑ k, nrm (ψ k) * δ j k ≤ Real.sqrt (∑ k, δ j k ^ 2) := by
    intro j
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun k => nrm (ψ k)) (δ j)
    rwa [hnorm, Real.sqrt_one, one_mul] at h
  have hreal : |∑ k, nrm (B.final *ᵥ (runOp B H₁ *ᵥ ψ k)) ^ 2 -
      ∑ k, nrm (B.final *ᵥ (runOp B H₂ *ᵥ ψ k)) ^ 2| ≤
      2 * ∑ j, Real.sqrt (∑ k, δ j k ^ 2) := by
    calc _ ≤ ∑ k, |nrm (B.final *ᵥ (runOp B H₁ *ᵥ ψ k)) ^ 2 -
          nrm (B.final *ᵥ (runOp B H₂ *ᵥ ψ k)) ^ 2| := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, 2 * nrm (ψ k) * ∑ j, δ j k :=
          Finset.sum_le_sum fun k _ => abs_nrm_sq_runOp_sub_le B H₁ H₂ S hS (ψ k)
      _ = 2 * ∑ j, ∑ k, nrm (ψ k) * δ j k := by
          simp only [Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
      _ ≤ 2 * ∑ j, Real.sqrt (∑ k, δ j k ^ 2) := by
          gcongr with j
          exact hcs j
  rw [hout, hout]
  refine (absDiff_ofReal_le (Finset.sum_nonneg fun k _ => sq_nonneg _)
    (Finset.sum_nonneg fun k _ => sq_nonneg _)).trans
    ((ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_))
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_sum_of_nonneg (fun j _ => Real.sqrt_nonneg _)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hguess j, Real.sqrt_eq_rpow,
    ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _) (by norm_num)]

end Adv

/-! ## Resampling for general multi-round adversaries -/

section Resample

variable {m n w q k c a : ℕ} [NeZero n] [NeZero c]

/-- The query hybrid for a general multi-round adversary: two oracles that
agree outside `S` change `Pr[out = 1]` by at most `2 ∑ⱼ guessProb_j^(1/2)`, for
the single-run embedding `toQAdv (dilate A) f` against `H₂`. -/
theorem absDiff_prOutMRGen_le_two_sum_rpow_guessProb (A : QAdvMRGen m n w q k c a)
    (H₁ H₂ : Fin m → Fin n) (f : Fin c → Fin a) (S : Finset (Fin m))
    (hS : ∀ x, x ∉ S → H₁ x = H₂ x) :
    absDiff (prOutMRGen A H₁ f) (prOutMRGen A H₂ f) ≤
      2 * ∑ j, guessProb (toQAdv (dilate A) f) H₂ S j ^ (1 / 2 : ℝ) := by
  rw [← prOutMR_dilate, ← prOutMR_dilate, prOutMR_eq, prOutMR_eq]
  exact absDiff_prOut_le_two_sum_rpow_guessProb _ H₁ H₂ S hS

/-- Resampling the oracle on a set conditionally sparse given the second oracle
and the round function: if `H₁ ω` and `H₂ ω` agree outside `D ω`, and for every
point `x`, oracle `h` and round function `g` the event `H₂ ω = h ∧ f ω = g ∧
x ∈ D ω` has weight at most `λ` times that of `H₂ ω = h ∧ f ω = g` under the
law `μ`, then the averaged acceptance probabilities of `A` differ by at most
`2 Q λ^(1/2)` with `Q = flatQ q k q`. -/
theorem prOutMRGen_resample_gentle_le {Ω : Type} [Fintype Ω] (A : QAdvMRGen m n w q k c a)
    (μ : Ω → ℝ≥0∞) (hμ : ∑ ω, μ ω = 1) (H₁ H₂ : Ω → Fin m → Fin n)
    (f : Ω → Fin c → Fin a) (D : Ω → Finset (Fin m)) (lam : ℝ≥0∞)
    (hagree : ∀ ω x, x ∉ D ω → H₁ ω x = H₂ ω x)
    (hsparse : ∀ x h g, ∑ ω, μ ω * (if H₂ ω = h ∧ f ω = g ∧ x ∈ D ω then 1 else 0) ≤
      lam * ∑ ω, μ ω * (if H₂ ω = h ∧ f ω = g then 1 else 0)) :
    absDiff (∑ ω, μ ω * prOutMRGen A (H₁ ω) (f ω)) (∑ ω, μ ω * prOutMRGen A (H₂ ω) (f ω)) ≤
      2 * (flatQ q k q : ℝ≥0∞) * lam ^ (1 / 2 : ℝ) := by
  set g : Ω → Fin (flatQ q k q) → Fin m → ℝ≥0∞ :=
    fun ω j x => guessProb (toQAdv (dilate A) (f ω)) (H₂ ω) {x} j with hg
  set G : Ω → Fin (flatQ q k q) → ℝ≥0∞ :=
    fun ω j => ∑ x, (if x ∈ D ω then 1 else 0) * g ω j x with hG
  have hstep : ∀ ω, absDiff (prOutMRGen A (H₁ ω) (f ω)) (prOutMRGen A (H₂ ω) (f ω)) ≤
      2 * ∑ j, G ω j ^ (1 / 2 : ℝ) := by
    intro ω
    refine (absDiff_prOutMRGen_le_two_sum_rpow_guessProb A (H₁ ω) (H₂ ω) (f ω) (D ω)
      (hagree ω)).trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [guessProb_eq_sum_singleton_mixed, sum_mem_eq_sum_boole_mul]
  have havg : ∀ j, ∑ ω, μ ω * G ω j ≤ lam := by
    intro j
    calc ∑ ω, μ ω * G ω j
        = ∑ x, ∑ ω, μ ω * (if x ∈ D ω then 1 else 0) * g ω j x := by
          simp only [G, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
      _ ≤ ∑ x, lam * ∑ ω, μ ω * g ω j x := by
          gcongr with x
          refine sum_mul_boole_mul_le_of_fiber (fun ω => (H₂ ω, f ω)) μ (fun ω => g ω j x)
            (fun ω => x ∈ D ω) lam ?_ ?_
          · intro ω ω' h
            simp only [Prod.mk.injEq] at h
            simp only [g, h.1, h.2]
          · intro ω₀
            have e₁ : ∀ ω, μ ω * (if (H₂ ω, f ω) = (H₂ ω₀, f ω₀) then 1 else 0) *
                (if x ∈ D ω then 1 else 0) =
                μ ω * (if H₂ ω = H₂ ω₀ ∧ f ω = f ω₀ ∧ x ∈ D ω then 1 else 0) := by
              intro ω
              simp only [Prod.mk.injEq]
              split_ifs <;> simp_all
            have e₂ : ∀ ω, μ ω * (if (H₂ ω, f ω) = (H₂ ω₀, f ω₀) then 1 else 0) =
                μ ω * (if H₂ ω = H₂ ω₀ ∧ f ω = f ω₀ then 1 else 0) := by
              intro ω
              simp only [Prod.mk.injEq]
            rw [Finset.sum_congr rfl fun ω _ => e₁ ω, Finset.sum_congr rfl fun ω _ => e₂ ω]
            exact hsparse x (H₂ ω₀) (f ω₀)
      _ = lam * ∑ ω, μ ω * ∑ x, g ω j x := by
          rw [← Finset.mul_sum]
          congr 1
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
      _ ≤ lam * ∑ ω, μ ω * 1 := by
          gcongr with ω
          exact sum_guessProb_singleton_le_one_mixed _ _ j
      _ = lam := by simp only [mul_one, hμ]
  have hjensen : ∀ j, ∑ ω, μ ω * G ω j ^ (1 / 2 : ℝ) ≤ lam ^ (1 / 2 : ℝ) := by
    intro j
    refine (sum_mul_rpow_half_le μ _ hμ).trans ?_
    gcongr
    exact havg j
  calc absDiff (∑ ω, μ ω * prOutMRGen A (H₁ ω) (f ω)) (∑ ω, μ ω * prOutMRGen A (H₂ ω) (f ω))
      ≤ ∑ ω, absDiff (μ ω * prOutMRGen A (H₁ ω) (f ω)) (μ ω * prOutMRGen A (H₂ ω) (f ω)) :=
        absDiff_sum_le _ _
    _ ≤ ∑ ω, μ ω * (2 * ∑ j, G ω j ^ (1 / 2 : ℝ)) := by
        gcongr with ω
        exact (absDiff_mul_left_le _ _ _).trans (by gcongr; exact hstep ω)
    _ = 2 * ∑ j, ∑ ω, μ ω * G ω j ^ (1 / 2 : ℝ) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ω _ => by ring
    _ ≤ 2 * ∑ _j : Fin (flatQ q k q), lam ^ (1 / 2 : ℝ) := by
        gcongr with j
        exact hjensen j
    _ = 2 * (flatQ q k q : ℝ≥0∞) * lam ^ (1 / 2 : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Resample

end CatCrypt.Quantum.QROM
