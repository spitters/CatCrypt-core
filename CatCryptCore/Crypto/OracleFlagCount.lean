/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleLazyMulti
public import CatCryptCore.ForMathlib.PMFOuterMeasure

/-!
# Flag probability of a run along a count

An oracle `O` on flagged states `σ × Bool` is run by an adversary asking at most `n` queries
from an unflagged state `t`. Let an invariant `I` of states hold at `t` and at every unflagged
successor of a call from an unflagged state satisfying `I`, let a measure `len` grow by at most
`ℓ` per such call, and let such a call from `t'` set the flag with probability at most
`c (len t')` for a monotone `c`. Then the run ends flagged with probability at most
`∑ i < n, c (len t + i * ℓ)`.

## Main results

* `OracleAdv.run_flag_le_sum_of_inv` — the bound for an oracle on flagged states.
* `OracleAdv.run_flagWhen_le_sum_of_inv` — the bound for `flagWhen bad O`, where the per-call
  bound is the probability of a bad transition of `O`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv

open scoped ENNReal

variable {D R σ α : Type}

/-- **Flag probability of a run along a count.** Let `O` be an oracle on flagged states. Let
every call from an unflagged state `t` satisfying `I` set the flag with probability at most
`c (len t)` for a monotone `c`, and let each of its unflagged successors satisfy `I` and have
`len` at most `len t + ℓ`. An adversary asking at most `n` queries from an unflagged state `t`
satisfying `I` sets the flag with probability at most `∑ i < n, c (len t + i * ℓ)`. -/
theorem run_flag_le_sum_of_inv (O : σ × Bool → D → PMF (R × (σ × Bool))) (I : σ → Prop)
    (len : σ → ℕ) (ℓ : ℕ) (c : ℕ → ℝ≥0∞) (hc : Monotone c)
    (hstep : ∀ t d, I t → (O (t, false) d).toOuterMeasure {x | x.2.2 = true} ≤ c (len t))
    (hlen : ∀ t d, I t → ∀ x ∈ (O (t, false) d).support, x.2.2 = false →
      I x.2.1 ∧ len x.2.1 ≤ len t + ℓ)
    (A : OracleAdv D R α) (n : ℕ) (hA : A.IsQueryBound n) (t : σ) (ht : I t) :
    (run O A (t, false)).toOuterMeasure {x | x.2.2 = true} ≤
      ∑ i ∈ Finset.range n, c (len t + i * ℓ) := by
  induction A generalizing n t with
  | ret a => simp [PMF.toOuterMeasure_pure_apply]
  | rand p k ih =>
    rw [run_rand, PMF.toOuterMeasure_bind_apply]
    calc ∑' b, p b * (run O (k b) (t, false)).toOuterMeasure _
        ≤ ∑' b, p b * ∑ i ∈ Finset.range n, c (len t + i * ℓ) :=
          tsum_le_tsum fun b => by gcongr; exact ih b n (hA b) t ht
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    cases n with
    | zero => exact hA.elim
    | succ n =>
    set T : ℝ≥0∞ := ∑ i ∈ Finset.range n, c (len t + (i + 1) * ℓ)
    rw [run_query, PMF.toOuterMeasure_bind_apply]
    have hterm : ∀ x : R × (σ × Bool), O (t, false) d x *
        (run O (k x.1) x.2).toOuterMeasure {x | x.2.2 = true} ≤
        O (t, false) d x * ((if x.2.2 = true then 1 else 0) + T) := by
      intro x
      by_cases hx : x ∈ (O (t, false) d).support
      · gcongr
        obtain ⟨r, t', fl⟩ := x
        cases fl with
        | true =>
          exact ((MeasureTheory.measure_mono (Set.subset_univ _)).trans_eq
            ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _))).trans
            (by simp)
        | false =>
          simp only [Bool.false_eq_true, ite_false, zero_add]
          obtain ⟨hI', hlen'⟩ := hlen t d ht _ hx rfl
          refine (ih r n (hA r) t' hI').trans (Finset.sum_le_sum fun i _ => hc ?_)
          grind
      · simp_all [zero_mul]
    calc ∑' x, O (t, false) d x * (run O (k x.1) x.2).toOuterMeasure {x | x.2.2 = true}
        ≤ ∑' x, O (t, false) d x * ((if x.2.2 = true then 1 else 0) + T) :=
          tsum_le_tsum hterm
      _ = (O (t, false) d).toOuterMeasure {x | x.2.2 = true} + T := by
          simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            PMF.toOuterMeasure_eq_tsum_ite]
      _ ≤ c (len t) + T := by gcongr; exact hstep t d ht
      _ = ∑ i ∈ Finset.range (n + 1), c (len t + i * ℓ) := by
          rw [Finset.sum_range_succ', zero_mul, add_zero, add_comm]

/-- **A bad flag along a count.** Let every call of `O` from a state `s` satisfying `I` reach
states satisfying `I` with `Ψ` at most `Ψ s + ℓ`, and make a bad transition with probability at
most `c (Ψ s)` for a monotone `c`. An adversary asking at most `n` queries from `s` satisfying
`I` sets the flag of `flagWhen bad O` with probability at most `∑ i < n, c (Ψ s + i * ℓ)`. -/
theorem run_flagWhen_le_sum_of_inv (O : σ → D → PMF (R × σ)) (bad : σ → D → R × σ → Prop)
    [∀ s d x, Decidable (bad s d x)] (I : σ → Prop) (Ψ : σ → ℕ) (ℓ : ℕ) (c : ℕ → ℝ≥0∞)
    (hc : Monotone c) (hI : ∀ s d, I s → ∀ x ∈ (O s d).support, I x.2 ∧ Ψ x.2 ≤ Ψ s + ℓ)
    (hbad : ∀ s d, I s → (O s d).toOuterMeasure {x | bad s d x} ≤ c (Ψ s))
    (A : OracleAdv D R α) (n : ℕ) (hA : A.IsQueryBound n) (s : σ) (hs : I s) :
    (run (flagWhen bad O) A (s, false)).toOuterMeasure {y | y.2.2 = true} ≤
      ∑ i ∈ Finset.range n, c (Ψ s + i * ℓ) := by
  refine run_flag_le_sum_of_inv (flagWhen bad O) I Ψ ℓ c hc (fun t d ht => ?_)
    (fun t d ht x hx _ => ?_) A n hA s hs
  · rw [flagWhen, PMF.toOuterMeasure_map_apply]
    refine (le_of_eq (congrArg _ ?_)).trans (hbad t d ht)
    ext x
    simp
  · simp only [flagWhen, PMF.support_map, Set.mem_image] at hx
    obtain ⟨x₀, h₀, rfl⟩ := hx
    exact hI t d ht x₀ h₀

end CatCrypt.Crypto.OracleAdv
