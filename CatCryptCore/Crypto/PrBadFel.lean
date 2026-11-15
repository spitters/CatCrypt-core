/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCFeedbackLaws

/-!
# The failure event lemma with a bound per step

The probability `prBad S bad Z` that a run of the environment `Z` against the system `S` reaches
a bad state is bounded by a potential: when every step from a good state of an invariant makes
the state bad with probability at most `ε`, and `ε` plus the potential of every good successor
is at most the potential of the state, then `prBad` is at most the potential of the initial
state. With the potential `∑ i ∈ [k, rounds), ε i` at round `k`, this is the failure event lemma
with a bound `ε k` that depends on the round, over the states reachable through good states.

## Main results

* `Sys.ReachAt` — the states reached after `k` steps through good states.
* `prBad_le_of_step_potential` — the bound by a potential with a cost per step.
* `prBad_le_sum_of_step` — `prBad S bad Z ≤ ∑ k ∈ Finset.range Z.input.rounds, ε k` when every
  step from a good state reached at round `k` makes the state bad with probability at most
  `ε k`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

variable {τ ζ E O : Type}

/-- The state `t` is reached after `k` steps of `S` from its initial state, through states that
are not bad: a possible outcome of a step from a good state reached after `k - 1` steps. -/
inductive Sys.ReachAt (S : Sys τ E O) (bad : τ → Bool) : ℕ → τ → Prop
  /-- The initial state is reached after `0` steps. -/
  | init : S.ReachAt bad 0 S.init
  /-- A possible successor of a good state reached after `k` steps is reached after `k + 1`. -/
  | step {k : ℕ} {t : τ} {e : E} {p : τ × O} : S.ReachAt bad k t → bad t = false →
      IsOutcome (S.step t e) p → S.ReachAt bad (k + 1) p.1

/-- The flag of a run of `n` activations from round `k`, from a good state of the invariant,
is set with probability at most the potential at round `k`. -/
theorem prTrue_loop_le_potential (S : Sys τ E O) (bad : τ → Bool) (Z : Strat ζ E O)
    (Inv : ℕ → τ → Prop) (ε : ℕ → τ → E → ℝ≥0∞) (Φ : ℕ → τ → ℝ≥0∞)
    (hpres : ∀ k t e p, k < Z.rounds → Inv k t → bad t = false → IsOutcome (S.step t e) p →
      bad p.1 = false → Inv (k + 1) p.1)
    (hstep : ∀ k t e h, k < Z.rounds → Inv k t → bad t = false →
      prTrue (SPComp.bind (S.step t e) fun p => SPComp.pure (bad p.1)) h ≤ ε k t e)
    (hle : ∀ k t e, k < Z.rounds → Inv k t → bad t = false → ε k t e ≤ Φ k t)
    (hΦ : ∀ k t e p, k < Z.rounds → Inv k t → bad t = false → IsOutcome (S.step t e) p →
      bad p.1 = false → ε k t e + Φ (k + 1) p.1 ≤ Φ k t) :
    ∀ (n k : ℕ) (z : ζ) (t : τ) (h : Heap), k + n = Z.rounds → Inv k t → bad t = false →
      prTrue (SPComp.bind (loop S bad Z n (z, t, false)) fun c => SPComp.pure c.2.2) h ≤
        Φ k t := by
  intro n
  induction n with
  | zero =>
    intro k z t h _ _ _
    simp [loop, SPComp.pure_bind, prTrue_pure]
  | succ n ih =>
    intro k z t h hkn hk ht
    have hkR : k < Z.rounds := by omega
    simp only [loop, SPComp.bind_assoc, Bool.false_or]
    refine prTrue_bind_le_const _ _ _ _ fun a h₁ => ?_
    by_cases hεt : ε k t a.2 = ⊤
    · have := hle k t a.2 hkR hk ht
      rw [hεt, top_le_iff] at this
      rw [this]
      exact le_top
    rw [prTrue_bind_split _ _ (fun p => bad p.1)]
    have hbadP : prTrue (SPComp.bind (S.step t a.2) fun p => if bad p.1 then
        SPComp.bind (Z.obs a.1 p.2) (fun z' => SPComp.bind (loop S bad Z n (z', p.1, bad p.1))
          fun c => SPComp.pure c.2.2) else SPComp.fail) h₁ ≤ ε k t a.2 := by
      refine (prTrue_bind_le_of_le _ _ _ _ fun p h' => ?_).trans (hstep k t a.2 h₁ hkR hk ht)
      cases hp : bad p.1
      · simp [prTrue_fail]
      · simpa [prTrue_pure] using prTrue_le_one _ _
    have hgoodP : prTrue (SPComp.bind (S.step t a.2) fun p => if bad p.1 then SPComp.fail else
        SPComp.bind (Z.obs a.1 p.2) (fun z' => SPComp.bind (loop S bad Z n (z', p.1, bad p.1))
          fun c => SPComp.pure c.2.2)) h₁ ≤ Φ k t - ε k t a.2 := by
      classical
      rw [bind_congr_isOutcome (g := fun p => if IsOutcome (S.step t a.2) p then
        (if bad p.1 then SPComp.fail else
          SPComp.bind (Z.obs a.1 p.2) (fun z' => SPComp.bind (loop S bad Z n (z', p.1, bad p.1))
            fun c => SPComp.pure c.2.2)) else SPComp.fail) fun p hp => by simp [hp]]
      refine prTrue_bind_le_const _ _ _ _ fun p h' => ?_
      by_cases hp : IsOutcome (S.step t a.2) p
      · cases hb : bad p.1
        · simp only [hp, ite_true, Bool.false_eq_true, ite_false]
          refine prTrue_bind_le_const _ _ _ _ fun z' h'' => ?_
          refine (ih (k + 1) z' p.1 h'' (by omega) (hpres k t a.2 p hkR hk ht hp hb) hb).trans ?_
          exact ENNReal.le_sub_of_add_le_left hεt (hΦ k t a.2 p hkR hk ht hp hb)
        · simp [hp, prTrue_fail]
      · simp [hp, prTrue_fail]
    calc _ ≤ (Φ k t - ε k t a.2) + ε k t a.2 := add_le_add hgoodP hbadP
      _ = Φ k t := tsub_add_cancel_of_le (hle k t a.2 hkR hk ht)

/-- **Failure event lemma with a potential.** Let `Inv` be an invariant indexed by the round,
kept by the steps into good states, `ε k t e` a bound on the probability that the step of `S`
on `e` from a good state `t` of the invariant at round `k` makes the state bad, and `Φ` a
potential at least `ε` that drops by `ε` along every step into a good state. Then the bad flag
is set with probability at most the potential of the initial state at round `0`. -/
theorem prBad_le_of_step_potential (S : Sys τ E O) (bad : τ → Bool) (Z : Env (Strat ζ E O) ζ)
    (Inv : ℕ → τ → Prop) (ε : ℕ → τ → E → ℝ≥0∞) (Φ : ℕ → τ → ℝ≥0∞)
    (hinit : Inv 0 S.init) (hgood : bad S.init = false)
    (hpres : ∀ k t e p, k < Z.input.rounds → Inv k t → bad t = false →
      IsOutcome (S.step t e) p → bad p.1 = false → Inv (k + 1) p.1)
    (hstep : ∀ k t e h, k < Z.input.rounds → Inv k t → bad t = false →
      prTrue (SPComp.bind (S.step t e) fun p => SPComp.pure (bad p.1)) h ≤ ε k t e)
    (hle : ∀ k t e, k < Z.input.rounds → Inv k t → bad t = false → ε k t e ≤ Φ k t)
    (hΦ : ∀ k t e p, k < Z.input.rounds → Inv k t → bad t = false →
      IsOutcome (S.step t e) p → bad p.1 = false → ε k t e + Φ (k + 1) p.1 ≤ Φ k t) :
    prBad S bad Z ≤ Φ 0 S.init := by
  unfold prBad run
  rw [hgood]
  exact prTrue_loop_le_potential S bad Z.input Inv ε Φ hpres hstep hle hΦ _ 0 _ _ _
    (by omega) hinit hgood

/-- **Failure event lemma with a bound per round.** If the initial state is good and every step
from a good state reached at round `k` makes the state bad with probability at most `ε k`, then
the run of `Z` reaches a bad state with probability at most `∑ k < Z.input.rounds, ε k`. -/
theorem prBad_le_sum_of_step (S : Sys τ E O) (bad : τ → Bool) (ε : ℕ → ℝ≥0∞)
    (hgood : bad S.init = false)
    (h : ∀ k t e h, S.ReachAt bad k t → bad t = false →
      prTrue (SPComp.bind (S.step t e) fun p => SPComp.pure (bad p.1)) h ≤ ε k)
    (Z : Env (Strat ζ E O) ζ) :
    prBad S bad Z ≤ ∑ k ∈ Finset.range Z.input.rounds, ε k := by
  have hb := prBad_le_of_step_potential S bad Z (S.ReachAt bad) (fun k _ _ => ε k)
    (fun k _ => ∑ i ∈ Finset.Ico k Z.input.rounds, ε i) .init hgood
    (fun _ _ _ _ _ hk ht hp _ => .step hk ht hp) (fun k t e h' _ hk ht => h k t e h' hk ht)
    (fun k _ _ hkR _ _ => Finset.single_le_sum (fun _ _ => bot_le)
      (Finset.mem_Ico.2 ⟨le_rfl, hkR⟩))
    (fun k _ _ _ hkR _ _ _ _ => (Finset.sum_eq_sum_Ico_succ_bot hkR ε).ge)
  rwa [Finset.range_eq_Ico]

end CatCrypt.Crypto.UCTransparent
