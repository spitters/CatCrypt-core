/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.ForkingLemma

set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-!
# General Forking Lemma (q-query)

Generalizes the forking lemma from `ForkingLemma.lean` (q = 1) to adversaries
making q >= 1 oracle queries, following Bellare-Neven (CCS 2006, Lemma 1).

## Model

A q-query adversary decomposes into:
1. **Coins** phase: probabilistic, produces commitment `c`
2. **Respond** phase: deterministic, given `c` and all q oracle responses
   (modeled as `Fin q -> R`), produces `(j, y)` where `j` identifies
   the relevant query

## Reduction

For each guess `I : Fin q`, we build a 1-query `ForkableAdversary` that
absorbs all q oracle responses into its coins phase and uses `Function.update`
to replace the I-th response with the single oracle challenge. The key
distribution lemma (`sample_update_eq_sample`) shows this replacement
preserves the uniform distribution.

## Results

* `qFork_success_ge_simple` -- simple bound: average fork >= acc^2 - acc/|R|
* `bellare_neven_aggregation` -- abstract Cauchy-Schwarz aggregation step
* `sum_acceptAtGuess_eq` -- partition of probability: sum accI = acc
* `qFork_success_ge` -- Bellare-Neven: sum of indexed forks >= acc^2/q - acc/|R|

## References

* [Bellare, Neven, *Multi-signatures in the plain public-key model*, CCS 2006]
-/

namespace CatCrypt.Crypto.GeneralForkingLemma

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.ForkingLemma
open scoped ENNReal

/-! ## q-Query Adversary Model -/

/-- A q-query adversary for the ROM forking lemma. -/
structure QForkableAdversary (X : Type) (C : Type) (R : Type) (Y : Type) (q : ℕ) where
  /-- Probabilistic commitment phase. -/
  coins : X → SPComp C
  /-- Deterministic response: given all q oracle responses, produce (index, output). -/
  respond : X → C → (Fin q → R) → Fin q × Y

variable {X C R Y : Type} {q : ℕ}

/-- Acceptance probability of a q-query adversary. -/
noncomputable def qAcceptProb [Fintype R] [Nonempty R]
    [Fintype (Fin q → R)] [Nonempty (Fin q → R)]
    (A : QForkableAdversary X C R Y q) (x : X) (accept : Fin q × Y → Bool) : ℝ≥0∞ :=
  prTrue (do
    let c ← A.coins x
    let responses ← SPComp.sample (Fin q → R)
    SPComp.pure (accept (A.respond x c responses))) Heap.empty

/-! ## Swap-at-j Equivalence -/

/-- The swap-at-j involution: `(f, e) ↦ (Function.update f j e, f j)`. -/
def swapAt [DecidableEq (Fin q)] (j : Fin q) :
    (Fin q → R) × R → (Fin q → R) × R :=
  fun ⟨f, e⟩ => (Function.update f j e, f j)

theorem swapAt_involutive [DecidableEq (Fin q)] (j : Fin q) :
    Function.Involutive (swapAt (R := R) j) := by
  intro ⟨f, e⟩
  simp only [swapAt, Prod.mk.injEq]
  refine ⟨?_, Function.update_self j e f⟩
  ext i
  simp only [Function.update_apply]
  split_ifs with h
  · subst h; simp
  · rfl

noncomputable def swapAtEquiv [DecidableEq (Fin q)] (j : Fin q) :
    (Fin q → R) × R ≃ (Fin q → R) × R :=
  (swapAt_involutive (R := R) j).toPerm (swapAt j)

@[simp] theorem swapAtEquiv_apply [DecidableEq (Fin q)] (j : Fin q)
    (p : (Fin q → R) × R) : swapAtEquiv j p = swapAt j p := rfl

/-! ## Sample-Update Distribution Lemma -/

private theorem sample_bind_const' {β : Type} (c : SPComp β)
    {α : Type} [Fintype α] [Nonempty α] :
    SPComp.bind (SPComp.sample α) (fun (_ : α) => c) = c := by
  funext h; simp only [SPComp.bind_def, SPComp.sample]
  rw [SDistr.bind_assoc]; simp only [SDistr.pure_bind]
  exact SDistr.uniform_bind_const (c h)

/-- Sampling `f : Fin q → R` and `e : R` uniformly, then applying
    `Function.update f j e`, gives the same distribution as sampling
    `g : Fin q → R` uniformly. -/
theorem sample_update_eq_sample [Fintype R] [Nonempty R] [DecidableEq (Fin q)]
    [Fintype (Fin q → R)] [Nonempty (Fin q → R)]
    (j : Fin q) {β : Type} (k : (Fin q → R) → SPComp β) :
    SPComp.bind (SPComp.sample (Fin q → R)) (fun f =>
      SPComp.bind (SPComp.sample R) (fun e =>
        k (Function.update f j e))) =
    SPComp.bind (SPComp.sample (Fin q → R)) k := by
  -- Step 1: LHS = sample ((Fin q → R) × R) >>= fun p => k (update p.1 j p.2)
  have step1 : SPComp.bind (SPComp.sample (Fin q → R)) (fun f =>
      SPComp.bind (SPComp.sample R) (fun e =>
        k (Function.update f j e))) =
    SPComp.bind (SPComp.sample ((Fin q → R) × R))
      (fun p => k (Function.update p.1 j p.2)) := by
    have : SPComp.bind (SPComp.sample (Fin q → R)) (fun f =>
        SPComp.bind (SPComp.sample R) (fun e => k (Function.update f j e)))
      = SPComp.bind (SPComp.bind (SPComp.sample (Fin q → R)) (fun f =>
          SPComp.bind (SPComp.sample R) (fun e => SPComp.pure (f, e))))
          (fun p => k (Function.update p.1 j p.2)) := by
        rw [SPComp.bind_assoc]; congr 1; funext f
        rw [SPComp.bind_assoc]; congr 1; funext e
        rw [SPComp.pure_bind]
    rw [this, ← SPComp.sample_prod_eq]
  -- Step 2: apply swap bijection
  have step2 : SPComp.bind (SPComp.sample ((Fin q → R) × R))
      (fun p => k (Function.update p.1 j p.2)) =
    SPComp.bind (SPComp.sample ((Fin q → R) × R)) (fun p => k p.1) := by
    have heq : (fun p : (Fin q → R) × R => k (Function.update p.1 j p.2)) =
        (fun a => (fun p : (Fin q → R) × R => k p.1) (swapAtEquiv (R := R) j a)) := by
      funext ⟨f, e⟩; simp [swapAt]
    rw [heq]
    exact SPComp.sample_bind_equiv (swapAtEquiv (R := R) j)
      (fun p : (Fin q → R) × R => k p.1)
  -- Step 3: RHS = sample ((Fin q → R) × R) >>= fun p => k p.1
  have step3 : SPComp.bind (SPComp.sample (Fin q → R)) k =
    SPComp.bind (SPComp.sample ((Fin q → R) × R)) (fun p => k p.1) := by
    have h1 : SPComp.bind (SPComp.sample (Fin q → R)) k
      = SPComp.bind (SPComp.bind (SPComp.sample (Fin q → R)) (fun f =>
          SPComp.bind (SPComp.sample R) (fun e => SPComp.pure (f, e))))
          (fun p => k p.1) := by
        rw [SPComp.bind_assoc]; congr 1; funext f
        rw [SPComp.bind_assoc]
        simp only [SPComp.pure_bind]
        exact (sample_bind_const' (k f)).symm
    rw [h1, ← SPComp.sample_prod_eq]
  rw [step1, step2, ← step3]

/-! ## Guess Reduction -/

/-- Given guess `I`, create a 1-query adversary by absorbing all q oracle
    responses into the coins phase and using `Function.update` at position I. -/
noncomputable def guessReduction [Fintype R] [Nonempty R] [DecidableEq (Fin q)]
    [Fintype (Fin q → R)] [Nonempty (Fin q → R)]
    (A : QForkableAdversary X C R Y q) (I : Fin q) :
    ForkableAdversary X (C × (Fin q → R)) R (Fin q × Y) where
  coins := fun x => do
    let c ← A.coins x
    let responses ← SPComp.sample (Fin q → R)
    SPComp.pure (c, responses)
  respond := fun x ⟨c, responses⟩ e =>
    A.respond x c (Function.update responses I e)

/-- Acceptance restricted to outputs whose index matches the guess. -/
def acceptAtGuess (accept : Fin q × Y → Bool) (I : Fin q) : Fin q × Y → Bool :=
  fun ⟨j, y⟩ => decide (j = I) && accept (j, y)

/-- Helper: the SPComp for the reduced adversary equals the q-query SPComp. -/
private theorem guessReduction_comp_eq [Fintype R] [Nonempty R] [DecidableEq (Fin q)]
    [Fintype (Fin q → R)] [Nonempty (Fin q → R)]
    (A : QForkableAdversary X C R Y q) (x : X)
    (I : Fin q) (P : Fin q × Y → Bool) :
    (do let c ← (guessReduction A I).coins x
        let e ← SPComp.sample R
        SPComp.pure (P ((guessReduction A I).respond x c e))) =
    (do let c ← A.coins x
        let responses ← SPComp.sample (Fin q → R)
        SPComp.pure (P (A.respond x c responses))) := by
  simp only [guessReduction, SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext c
  exact sample_update_eq_sample (R := R) I
    (fun responses => SPComp.pure (P (A.respond x c responses)))

/-- Each reduced adversary (full accept) has the same acceptance probability
    as the q-query adversary, by `sample_update_eq_sample`. -/
theorem acceptProb_guessReduction [Fintype R] [Nonempty R] [DecidableEq (Fin q)]
    [DecidableEq R] [Fintype (Fin q → R)] [Nonempty (Fin q → R)]
    (A : QForkableAdversary X C R Y q) (x : X)
    (I : Fin q) (accept : Fin q × Y → Bool) :
    acceptProb (guessReduction A I) x accept = qAcceptProb A x accept := by
  simp only [acceptProb, qAcceptProb]
  exact congrArg (prTrue · Heap.empty) (guessReduction_comp_eq A x I accept)

/-! ## Simple q-Forking Bound (Non-Indexed) -/

noncomputable def qForkSuccProbSimple [Fintype R] [Nonempty R] [DecidableEq (Fin q)]
    [DecidableEq R] [Fintype (Fin q → R)] [Nonempty (Fin q → R)]
    (A : QForkableAdversary X C R Y q) (x : X) (accept : Fin q × Y → Bool)
    (_hq : 0 < q) : ℝ≥0∞ :=
  (q : ℝ≥0∞)⁻¹ * ∑ I : Fin q, forkSuccProb (guessReduction (R := R) A I) x accept

/-- Simple bound: average fork success >= acc^2 - acc/|R|. -/
theorem qFork_success_ge_simple [Fintype R] [Nonempty R] [DecidableEq (Fin q)]
    [DecidableEq R] [Fintype (Fin q → R)] [Nonempty (Fin q → R)]
    (A : QForkableAdversary X C R Y q) (x : X) (accept : Fin q × Y → Bool)
    (hq : 0 < q) :
    qForkSuccProbSimple A x accept hq ≥
      qAcceptProb A x accept ^ 2 - qAcceptProb A x accept / Fintype.card R := by
  simp only [qForkSuccProbSimple, ge_iff_le, tsub_le_iff_right]
  set acc := qAcceptProb A x accept; set N := (Fintype.card R : ℝ≥0∞)
  set Q := (q : ℝ≥0∞)
  have hQ_ne : Q ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hq)
  have hQ_ne_top : Q ≠ ⊤ := ENNReal.natCast_ne_top q
  have h_per_I : ∀ I : Fin q,
      forkSuccProb (guessReduction A I) x accept ≥ acc ^ 2 - acc / N := by
    intro I
    have heq := acceptProb_guessReduction A x I accept
    calc acc ^ 2 - acc / N
        = acceptProb (guessReduction A I) x accept ^ 2 -
          acceptProb (guessReduction A I) x accept / N := by rw [heq]
      _ ≤ forkSuccProb (guessReduction A I) x accept := fork_success_ge _ _ _
  have h_sum : ∑ I : Fin q, forkSuccProb (guessReduction A I) x accept ≥
      Q * (acc ^ 2 - acc / N) := by
    calc Q * (acc ^ 2 - acc / N)
        = ∑ _I : Fin q, (acc ^ 2 - acc / N) := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      _ ≤ ∑ I : Fin q, forkSuccProb (guessReduction A I) x accept :=
          Finset.sum_le_sum fun I _ => h_per_I I
  calc acc ^ 2
      ≤ (acc ^ 2 - acc / N) + acc / N := tsub_le_iff_right.mp le_rfl
    _ ≤ Q⁻¹ * (∑ I, forkSuccProb (guessReduction A I) x accept) + acc / N := by
        gcongr
        calc acc ^ 2 - acc / N
            = Q⁻¹ * (Q * (acc ^ 2 - acc / N)) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel hQ_ne hQ_ne_top, one_mul]
          _ ≤ Q⁻¹ * ∑ I, forkSuccProb (guessReduction A I) x accept := by gcongr

/-- For every guess I, fork success >= acc^2 - acc/|R|. -/
theorem qFork_success_ge_existential [Fintype R] [Nonempty R] [DecidableEq (Fin q)]
    [DecidableEq R] [Fintype (Fin q → R)] [Nonempty (Fin q → R)]
    (A : QForkableAdversary X C R Y q) (x : X) (accept : Fin q × Y → Bool)
    (I : Fin q) :
    forkSuccProb (guessReduction A I) x accept ≥
      qAcceptProb A x accept ^ 2 -
      qAcceptProb A x accept / Fintype.card R := by
  have heq := acceptProb_guessReduction A x I accept
  calc qAcceptProb A x accept ^ 2 - qAcceptProb A x accept / Fintype.card R
      = acceptProb (guessReduction A I) x accept ^ 2 -
        acceptProb (guessReduction A I) x accept / Fintype.card R := by rw [heq]
    _ ≤ forkSuccProb (guessReduction A I) x accept := fork_success_ge _ _ _

/-! ## Bellare-Neven Aggregation (Abstract) -/

/-- **Bellare-Neven aggregation** (Cauchy-Schwarz step). -/
theorem bellare_neven_aggregation (hq : 0 < q)
    (a f : Fin q → ℝ≥0∞) (N : ℝ≥0∞)
    (h_per_j : ∀ j, f j ≥ a j ^ 2 - a j / N) :
    ∑ j : Fin q, f j ≥
      (∑ j : Fin q, a j) ^ 2 / q - (∑ j : Fin q, a j) / N := by
  set S := ∑ j : Fin q, a j
  have h1 : ∑ j, f j ≥ ∑ j, (a j ^ 2 - a j / N) :=
    Finset.sum_le_sum fun j _ => h_per_j j
  suffices h2 : ∑ j, (a j ^ 2 - a j / N) ≥ S ^ 2 / ↑q - S / N from
    le_trans h2 h1
  rw [ge_iff_le, tsub_le_iff_right]
  have h3 : ∀ j, a j ^ 2 ≤ (a j ^ 2 - a j / N) + a j / N :=
    fun _ => tsub_le_iff_right.mp le_rfl
  have h4 : ∑ j, a j ^ 2 ≤ ∑ j, (a j ^ 2 - a j / N) + ∑ j, a j / N := by
    calc ∑ j, a j ^ 2
        ≤ ∑ j, ((a j ^ 2 - a j / N) + a j / N) :=
          Finset.sum_le_sum fun j _ => h3 j
      _ = _ := Finset.sum_add_distrib
  have h5 : ∑ j, a j / N = S / N := by
    show ∑ j, a j / N = (∑ j, a j) / N
    simp only [div_eq_mul_inv, Finset.sum_mul]
  have h6 : ∑ j, a j ^ 2 ≤ ∑ j, (a j ^ 2 - a j / N) + S / N := by
    rw [← h5]; exact h4
  suffices hCS : S ^ 2 / ↑q ≤ ∑ j, a j ^ 2 from le_trans hCS h6
  rw [ENNReal.div_le_iff (by positivity) (by exact ENNReal.natCast_ne_top q)]
  rw [mul_comm]
  have hSS : S * S = ∑ i : Fin q, ∑ j : Fin q, a i * a j := by
    change (∑ i, a i) * (∑ j, a j) = ∑ i, ∑ j, a i * a j
    rw [Finset.sum_mul]; congr 1; funext; rw [Finset.mul_sum]
  rw [sq S, hSS]
  suffices h2mul : 2 * ∑ i : Fin q, ∑ j : Fin q, a i * a j ≤
      2 * (↑q * ∑ j, a j ^ 2) by
    exact (ENNReal.mul_le_mul_iff_right
      (show (2 : ℝ≥0∞) ≠ 0 by norm_num) (show (2 : ℝ≥0∞) ≠ ⊤ by norm_num)).mp h2mul
  calc 2 * ∑ i, ∑ j, a i * a j
      = ∑ i, ∑ j, 2 * (a i * a j) := by
        rw [Finset.mul_sum]; congr 1; funext i; rw [Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, (a i ^ 2 + a j ^ 2) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        rw [← mul_assoc]; exact ennreal_two_mul_le_add_sq (a i) (a j)
    _ = ∑ i, (↑q * a i ^ 2 + ∑ j, a j ^ 2) := by
        congr 1; funext i; rw [Finset.sum_add_distrib]; congr 1
        simp [Finset.sum_const, nsmul_eq_mul]
    _ = ↑q * ∑ i, a i ^ 2 + ↑q * ∑ j, a j ^ 2 := by
        rw [Finset.sum_add_distrib]; congr 1
        · exact (Finset.mul_sum ..).symm
        · simp [Finset.sum_const, nsmul_eq_mul]
    _ = 2 * (↑q * ∑ j, a j ^ 2) := by ring

/-! ## Indexed Forking: Partition + Main Theorem -/

/-- Algebraic partition: `∑_I acceptAtGuess(accept, I, out) = accept(out)` as Bool→ℕ. -/
private theorem sum_acceptAtGuess_bool (accept : Fin q × Y → Bool) (out : Fin q × Y) :
    (∑ I : Fin q, if acceptAtGuess accept I out then (1 : ℝ≥0∞) else 0) =
    if accept out then 1 else 0 := by
  simp only [acceptAtGuess]
  by_cases hacc : accept out
  · simp only [hacc, Bool.and_true, decide_eq_true_eq]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (Finset.univ.filter (fun I : Fin q => out.1 = I)).card = 1 := by
      rw [Finset.card_eq_one]; exact ⟨out.1, by ext i; simp [eq_comm]⟩
    exact_mod_cast this
  · simp [hacc]

/-- Partition of probability: `sum_I Pr[idx=I and accept] = Pr[accept]`. -/
theorem sum_acceptAtGuess_eq [Fintype R] [Nonempty R] [DecidableEq (Fin q)]
    [DecidableEq R] [Fintype (Fin q → R)] [Nonempty (Fin q → R)]
    (A : QForkableAdversary X C R Y q) (x : X) (accept : Fin q × Y → Bool) :
    ∑ I : Fin q,
      acceptProb (guessReduction A I) x (acceptAtGuess accept I) =
    qAcceptProb A x accept := by
  -- Rewrite each summand using the SPComp equality
  have h_rw : ∀ I : Fin q,
      acceptProb (guessReduction A I) x (acceptAtGuess accept I) =
      prTrue (do let c ← A.coins x
                 let responses ← SPComp.sample (Fin q → R)
                 SPComp.pure (acceptAtGuess accept I (A.respond x c responses))) Heap.empty := by
    intro I
    simp only [acceptProb]
    exact congrArg (prTrue · Heap.empty) (guessReduction_comp_eq A x I (acceptAtGuess accept I))
  simp_rw [h_rw]; clear h_rw
  -- Now both sides use the same computation structure
  simp only [qAcceptProb, SPComp.monad_bind_eq]
  -- Both sides have form prTrue(coins >>= fun c => sample >>= fun r => pure (...)) Heap.empty
  -- Expand both sides using prTrue_bind_eq_weighted twice
  rw [prTrue_bind_eq_weighted (A.coins x)]
  -- LHS: ∑_I prTrue(coins >>= ...) = ∑_I ∑'_p w(p) * f(I,p)
  -- We need: ∑_I ∑'_p w(p) * f(I,p) = ∑'_p w(p) * g(p)
  -- Strategy: show pointwise ∑_I f(I,p) = g(p) and use Finset.sum_tsum + tsum_congr
  conv_lhs =>
    arg 2; ext I
    rw [prTrue_bind_eq_weighted (A.coins x)]
  -- Use: ∑ I, ∑' p, f I p = ∑' p, ∑ I, f I p  (swap finite and infinite sum)
  -- For ENNReal: convert ∑ to ∑' via tsum_eq_sum, use tsum_comm, convert back
  -- Swap finite and infinite sums for ENNReal
  have swap : ∀ {β : Type} (g : Fin q → β → ℝ≥0∞),
      ∑ I, ∑' p, g I p = ∑' p, ∑ I, g I p := by
    intro β g
    trans (∑' I : Fin q, ∑' p, g I p)
    · exact ((hasSum_fintype _).tsum_eq).symm
    trans (∑' p, ∑' I : Fin q, g I p)
    · exact ENNReal.tsum_comm
    · congr 1; funext p; exact (hasSum_fintype _).tsum_eq
  rw [swap]; congr 1; funext p
  cases p with
  | none =>
    simp only [mul_zero, Finset.sum_const_zero]
  | some pc =>
    obtain ⟨c', h'⟩ := pc; simp only; rw [← Finset.mul_sum]; congr 1
    simp_rw [prTrue_bind_eq_weighted]
    rw [swap]; congr 1; funext p2
    cases p2 with
    | none =>
      simp only [mul_zero, Finset.sum_const_zero]
    | some pr =>
      obtain ⟨responses', _⟩ := pr; simp only; rw [← Finset.mul_sum]; congr 1
      simp_rw [prTrue_pure_bool]
      exact sum_acceptAtGuess_bool accept (A.respond x c' responses')

/-- Indexed q-forking success probability (sum over all guesses). -/
noncomputable def qForkSuccProb [Fintype R] [Nonempty R] [DecidableEq (Fin q)]
    [DecidableEq R] [Fintype (Fin q → R)] [Nonempty (Fin q → R)]
    (A : QForkableAdversary X C R Y q) (x : X) (accept : Fin q × Y → Bool) : ℝ≥0∞ :=
  ∑ I : Fin q,
    forkSuccProb (guessReduction (R := R) A I) x (acceptAtGuess accept I)

/-- **General Forking Lemma (Bellare-Neven 2006)**:
    `qForkSuccProb >= acc^2/q - acc/|R|`. -/
theorem qFork_success_ge [Fintype R] [Nonempty R] [DecidableEq (Fin q)]
    [DecidableEq R] [Fintype (Fin q → R)] [Nonempty (Fin q → R)]
    (A : QForkableAdversary X C R Y q) (x : X) (accept : Fin q × Y → Bool)
    (hq : 0 < q) :
    qForkSuccProb A x accept ≥
      qAcceptProb A x accept ^ 2 / q -
      qAcceptProb A x accept / Fintype.card R := by
  rw [qForkSuccProb]
  have hp := sum_acceptAtGuess_eq A x accept
  have h := bellare_neven_aggregation hq
    (fun I => acceptProb (guessReduction (R := R) A I) x (acceptAtGuess accept I))
    (fun I => forkSuccProb (guessReduction (R := R) A I) x (acceptAtGuess accept I))
    (Fintype.card R) (fun I => fork_success_ge _ x _)
  rwa [hp] at h

/-! ## Embedding q = 1 -/

/-- Convert a 1-query adversary to q=1 form. -/
def toQForkable (A : ForkableAdversary X C R Y) :
    QForkableAdversary X C R Y 1 where
  coins := A.coins
  respond := fun x c es => (0, A.respond x c (es 0))

/-- When q = 1, the bound simplifies to the original forking lemma bound. -/
theorem q1_simplification (S N : ℝ≥0∞) :
    S ^ 2 / (1 : ℝ≥0∞) - S / N = S ^ 2 - S / N := by
  simp [div_one]

end CatCrypt.Crypto.GeneralForkingLemma
