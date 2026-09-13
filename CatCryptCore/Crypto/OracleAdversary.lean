/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Probability.Distributions.Uniform

/-!
# Adaptive oracle adversaries

An adaptive oracle adversary is a finite interaction tree: at each node it
returns a value, flips coins from a probability mass function, or asks a query
`d : D` and continues with the answer `r : R`. The query bound
`OracleAdv.IsQueryBound A q` states that every path of `A` asks at most `q`
queries. An adversary runs against a stateful oracle
`O : S → D → PMF (R × S)`, which returns the answer and the next oracle state.

## Main definitions

* `OracleAdv D R α` — adaptive adversary with queries in `D`, answers in `R`,
  output in `α`
* `OracleAdv.IsQueryBound A q` — every path of `A` asks at most `q` queries
* `OracleAdv.run O A s` — joint distribution of the output and the final
  oracle state when `A` runs against `O` from state `s`

## Main results

* `OracleAdv.IsQueryBound.mono` — query bounds are monotone
* `OracleAdv.run_map_state` — an oracle state map that commutes with one
  oracle call commutes with a whole run
* `OracleAdv.run_map_fst_of_isQueryBound_zero` — an adversary without queries
  has an output distribution independent of the oracle
* `OracleAdv.run_flag_apply_false_of_true` — an oracle whose flag is sticky
  keeps it set through a run
* `OracleAdv.run_apply_flag_false_eq` — two oracles that agree on every
  unflagged transition give runs that agree on every unflagged outcome
  (identical until bad)
-/

@[expose] public section

namespace CatCrypt.Crypto

open scoped ENNReal

/-- An adaptive oracle adversary with queries in `D`, answers in `R` and output
in `α`: return a value (`ret`), sample `b` from a probability mass function and
continue (`rand`), or query the oracle at `d` and continue with the answer
(`query`). -/
inductive OracleAdv (D R α : Type) : Type 1 where
  /-- Return the output. -/
  | ret : α → OracleAdv D R α
  /-- Sample from `p` and continue with the sample. -/
  | rand {β : Type} (p : PMF β) (k : β → OracleAdv D R α) : OracleAdv D R α
  /-- Query the oracle at `d` and continue with the answer. -/
  | query (d : D) (k : R → OracleAdv D R α) : OracleAdv D R α

namespace OracleAdv

variable {D R α : Type}

/-- `IsQueryBound A q`: every path of `A` asks at most `q` oracle queries. -/
def IsQueryBound : OracleAdv D R α → ℕ → Prop
  | ret _, _ => True
  | rand _ k, n => ∀ b, IsQueryBound (k b) n
  | query _ _, 0 => False
  | query _ k, n + 1 => ∀ r, IsQueryBound (k r) n

theorem IsQueryBound.mono {A : OracleAdv D R α} {m n : ℕ} (h : IsQueryBound A m)
    (hmn : m ≤ n) : IsQueryBound A n := by
  induction A generalizing m n with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (h b) hmn
  | query d k ih =>
    cases m with
    | zero => exact h.elim
    | succ m =>
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      exact fun r => ih r (h r) (by omega)

/-- The joint distribution of the output and the final oracle state when `A`
runs against the stateful oracle `O` from state `s`. -/
noncomputable def run {S : Type} (O : S → D → PMF (R × S)) :
    OracleAdv D R α → S → PMF (α × S)
  | ret a, s => PMF.pure (a, s)
  | rand p k, s => p.bind fun b => run O (k b) s
  | query d k, s => (O s d).bind fun x => run O (k x.1) x.2

variable {S S' : Type}

@[simp] theorem run_ret (O : S → D → PMF (R × S)) (a : α) (s : S) :
    run O (ret a) s = PMF.pure (a, s) := rfl

@[simp] theorem run_rand (O : S → D → PMF (R × S)) {β : Type} (p : PMF β)
    (k : β → OracleAdv D R α) (s : S) :
    run O (rand p k) s = p.bind fun b => run O (k b) s := rfl

@[simp] theorem run_query (O : S → D → PMF (R × S)) (d : D) (k : R → OracleAdv D R α)
    (s : S) : run O (query d k) s = (O s d).bind fun x => run O (k x.1) x.2 := rfl

/-- A map `f` of oracle states that commutes with every oracle call commutes
with every run. -/
theorem run_map_state (O : S → D → PMF (R × S)) (O' : S' → D → PMF (R × S'))
    (f : S → S') (hO : ∀ s d, (O s d).map (Prod.map id f) = O' (f s) d)
    (A : OracleAdv D R α) (s : S) :
    (run O A s).map (Prod.map id f) = run O' A (f s) := by
  induction A generalizing s with
  | ret a => simp [PMF.pure_map]
  | rand p k ih => simp only [run_rand, PMF.map_bind, ih]
  | query d k ih =>
    simp only [run_query, PMF.map_bind, ih, ← hO s d, PMF.bind_map]
    rfl

/-- Without queries, the output distribution does not depend on the oracle or
its initial state. -/
theorem run_map_fst_of_isQueryBound_zero (O : S → D → PMF (R × S))
    (O' : S' → D → PMF (R × S')) {A : OracleAdv D R α} (hA : IsQueryBound A 0)
    (s : S) (s' : S') :
    (run O A s).map Prod.fst = (run O' A s').map Prod.fst := by
  induction A with
  | ret a => simp [PMF.pure_map]
  | rand p k ih => simp only [run_rand, PMF.map_bind, fun b => ih b (hA b)]
  | query d k ih => exact hA.elim

/-! ## Flagged oracle state -/

variable {σ : Type}

/-- If an oracle never clears its flag, a run started with the flag set assigns
probability zero to every outcome with the flag cleared. -/
theorem run_flag_apply_false_of_true (O : σ × Bool → D → PMF (R × (σ × Bool)))
    (hO : ∀ t d r t', O (t, true) d (r, (t', false)) = 0) (A : OracleAdv D R α)
    (t : σ) (a : α) (t' : σ) : run O A (t, true) (a, (t', false)) = 0 := by
  induction A generalizing t with
  | ret b => simp [PMF.pure_apply]
  | rand p k ih => simp [PMF.bind_apply, ih]
  | query d k ih =>
    rw [run_query, PMF.bind_apply]
    refine ENNReal.tsum_eq_zero.mpr fun x => ?_
    obtain ⟨r, t₁, b₁⟩ := x
    cases b₁ with
    | false => simp [hO]
    | true => simp [ih]

/-- **Identical until bad.** Two oracles on flagged states whose flags are
sticky and which agree on every transition into an unflagged state give runs
that agree on every unflagged outcome. -/
theorem run_apply_flag_false_eq (O₁ O₂ : σ × Bool → D → PMF (R × (σ × Bool)))
    (h₁ : ∀ t d r t', O₁ (t, true) d (r, (t', false)) = 0)
    (h₂ : ∀ t d r t', O₂ (t, true) d (r, (t', false)) = 0)
    (hagree : ∀ s d r t', O₁ s d (r, (t', false)) = O₂ s d (r, (t', false)))
    (A : OracleAdv D R α) (s : σ × Bool) (a : α) (t' : σ) :
    run O₁ A s (a, (t', false)) = run O₂ A s (a, (t', false)) := by
  induction A generalizing s with
  | ret b => rfl
  | rand p k ih => simp only [run_rand, PMF.bind_apply, ih]
  | query d k ih =>
    simp only [run_query, PMF.bind_apply]
    refine tsum_congr fun x => ?_
    obtain ⟨r, t₁, b₁⟩ := x
    cases b₁ with
    | false => rw [hagree, ih]
    | true =>
      simp only [run_flag_apply_false_of_true O₁ h₁, run_flag_apply_false_of_true O₂ h₂,
        mul_zero]

end OracleAdv

end CatCrypt.Crypto
