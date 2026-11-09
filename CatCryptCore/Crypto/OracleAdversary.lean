/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.PMFUniformDefs
public import CatCryptCore.ForMathlib.PMFSupport

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
* `OracleAdv.mapQuery c A` — the adversary `A` with each query `d` asked as `c d`

## Main results

* `OracleAdv.IsQueryBound.mono` — query bounds are monotone
* `OracleAdv.run_mapQuery`, `OracleAdv.isQueryBound_mapQuery` — a renamed
  adversary runs against the oracle precomposed with the renaming and keeps its
  query bound
* `OracleAdv.run_map_state` — an oracle state map that commutes with one
  oracle call commutes with a whole run
* `OracleAdv.run_support_inv` — an invariant preserved by every oracle transition
  holds on the support of every run
* `OracleAdv.run_map_eq_of_fixed` — two oracles that keep their states and answer every
  query by the same distribution give the same run
* `OracleAdv.run_map_fst_of_isQueryBound_zero` — an adversary without queries
  has an output distribution independent of the oracle
* `OracleAdv.run_eq_of_agree_level` — runs of oracles that agree below a level of a graded
  invariant, for an adversary with a query bound
* `OracleAdv.run_map_eq_pure_of_frozen`, `OracleAdv.run_map_eq_of_agree_until_stop` — runs of
  oracles that agree until a stop after which both keep an observation
* `OracleAdv.run_map_eq_of_cut` — answers replaced on the transitions into a frozen stop
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

/-! ## Renaming queries -/

/-- The adversary `A` with each query `d` asked as `c d`. -/
def mapQuery {D₀ : Type} (c : D → D₀) : OracleAdv D R α → OracleAdv D₀ R α
  | ret a => ret a
  | rand p k => rand p fun b => mapQuery c (k b)
  | query d k => query (c d) fun r => mapQuery c (k r)

/-- Running `mapQuery c A` against `O` is running `A` against `O` precomposed with `c`. -/
theorem run_mapQuery {D₀ : Type} (O : S → D₀ → PMF (R × S)) (c : D → D₀)
    (A : OracleAdv D R α) (s : S) :
    run O (mapQuery c A) s = run (fun s d => O s (c d)) A s := by
  induction A generalizing s with
  | ret a => rfl
  | rand p k ih => simp only [mapQuery, run_rand, ih]
  | query d k ih => simp only [mapQuery, run_query, ih]

/-- Renaming queries preserves query bounds. -/
theorem isQueryBound_mapQuery {D₀ : Type} (c : D → D₀) {A : OracleAdv D R α} {q : ℕ}
    (hA : A.IsQueryBound q) : (mapQuery c A).IsQueryBound q := by
  induction A generalizing q with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (hA b)
  | query d k ih =>
    cases q with
    | zero => exact hA.elim
    | succ q => exact fun r => ih r (hA r)

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

/-- An invariant of the oracle state that every transition preserves holds for
the final state of every outcome in the support of a run started in it. -/
theorem run_support_inv (O : S → D → PMF (R × S)) (Inv : S → Prop)
    (hO : ∀ s d x, Inv s → x ∈ (O s d).support → Inv x.2) (A : OracleAdv D R α) (s : S)
    (hs : Inv s) : ∀ x ∈ (run O A s).support, Inv x.2 := by
  induction A generalizing s with
  | ret a =>
    intro x hx
    rw [run_ret, PMF.mem_support_pure_iff] at hx
    subst hx
    exact hs
  | rand p k ih =>
    intro x hx
    rw [run_rand, PMF.mem_support_bind_iff] at hx
    obtain ⟨b, -, hx⟩ := hx
    exact ih b s hs x hx
  | query d k ih =>
    intro x hx
    rw [run_query, PMF.mem_support_bind_iff] at hx
    obtain ⟨y, hy, hx⟩ := hx
    exact ih y.1 y.2 (hO s d y hs hy) x hx

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

/-- **Runs against oracles with a fixed state.** Two oracles that, at the states `s` and `s'`,
answer every query `d` by the same distribution `g d` and keep the state give the same output
distribution: the run of `A` against `O` from `s`, with its final state replaced by `s'`, is
the run of `A` against `O'` from `s'`. -/
theorem run_map_eq_of_fixed (O : S → D → PMF (R × S)) (O' : S' → D → PMF (R × S'))
    (g : D → PMF R) (s : S) (s' : S') (hO : ∀ d, O s d = (g d).map fun r => (r, s))
    (hO' : ∀ d, O' s' d = (g d).map fun r => (r, s')) (A : OracleAdv D R α) :
    (run O A s).map (fun x => (x.1, s')) = run O' A s' := by
  induction A with
  | ret a => simp [PMF.pure_map]
  | rand p k ih => simp only [run_rand, PMF.map_bind, ih]
  | query d k ih =>
    simp only [run_query, hO, hO', PMF.bind_map, PMF.map_bind, Function.comp_def, ih]

/-! ## Runs of oracles that agree on part of the state space -/

/-- **Runs of oracles that agree below a level.** Let `L c` be state predicates such that every
call of `O` from a state of `L c` leads to states of `L (c + 1)`, and let `O` and `O'` agree at
the states of `L c` for `c < n`. A run of an adversary asking at most `m` queries from a state
of `L c` with `c + m ≤ n` is the same under both oracles. -/
theorem run_eq_of_agree_level (O O' : S → D → PMF (R × S)) (L : ℕ → S → Prop) (n : ℕ)
    (hO : ∀ c s d, L c s → ∀ x ∈ (O s d).support, L (c + 1) x.2)
    (hagree : ∀ c s d, c < n → L c s → O s d = O' s d) {A : OracleAdv D R α} {m : ℕ}
    (hA : A.IsQueryBound m) (c : ℕ) (s : S) (hs : L c s) (hcm : c + m ≤ n) :
    run O A s = run O' A s := by
  induction A generalizing m c s with
  | ret a => simp only [run_ret]
  | rand p k ih =>
    simp only [run_rand]
    exact congrArg _ (funext fun b => ih b (hA b) c s hs hcm)
  | query d k ih =>
    cases m with
    | zero => exact hA.elim
    | succ m =>
      rw [run_query, run_query, ← hagree c s d (by omega) hs]
      exact PMF.bind_congr_support _ _ _ fun y hy =>
        ih y.1 (hA y.1) (c + 1) y.2 (hO c s d hs y hy) (by omega)

/-- **A frozen observation.** Let every call of `O` from a state of `Fr` lead to states of `Fr`
with the same value of `g`. A run from a state of `Fr` ends with that value of `g`. -/
theorem run_map_eq_pure_of_frozen {β : Type} (O : S → D → PMF (R × S)) (Fr : S → Prop)
    (g : S → β) (hO : ∀ s d, Fr s → ∀ x ∈ (O s d).support, Fr x.2 ∧ g x.2 = g s)
    (A : OracleAdv D R α) (s : S) (hs : Fr s) :
    (run O A s).map (fun x => g x.2) = PMF.pure (g s) := by
  induction A generalizing s with
  | ret a => simp only [run_ret, PMF.pure_map]
  | rand p k ih => simp only [run_rand, PMF.map_bind, fun b => ih b s hs, PMF.bind_const]
  | query d k ih =>
    rw [run_query, PMF.map_bind, PMF.bind_congr_support _ _ (fun _ => PMF.pure (g s))
      fun y hy => by rw [ih y.1 y.2 (hO s d hs y hy).1, (hO s d hs y hy).2]]
    exact PMF.bind_const _ _

/-- **Runs that agree until a stop.** Let `O` and `O'` agree at the states outside `Stop`, and
let every call of either from a state of `Stop` lead to states of `Stop` with the same value of
`g`. The runs of an adversary against `O` and `O'` give the same distribution of the final value
of `g`. -/
theorem run_map_eq_of_agree_until_stop {β : Type} (O O' : S → D → PMF (R × S))
    (Stop : S → Prop) (g : S → β) (hagree : ∀ s d, ¬ Stop s → O s d = O' s d)
    (hO : ∀ s d, Stop s → ∀ x ∈ (O s d).support, Stop x.2 ∧ g x.2 = g s)
    (hO' : ∀ s d, Stop s → ∀ x ∈ (O' s d).support, Stop x.2 ∧ g x.2 = g s)
    (A : OracleAdv D R α) (s : S) :
    (run O A s).map (fun x => g x.2) = (run O' A s).map (fun x => g x.2) := by
  induction A generalizing s with
  | ret a => rfl
  | rand p k ih => simp only [run_rand, PMF.map_bind, fun b => ih b s]
  | query d k ih =>
    by_cases hs : Stop s
    · rw [run_map_eq_pure_of_frozen O Stop g hO _ s hs,
        run_map_eq_pure_of_frozen O' Stop g hO' _ s hs]
    · rw [run_query, run_query, PMF.map_bind, PMF.map_bind, hagree s d hs]
      exact congrArg _ (funext fun y => ih y.1 y.2)

/-- **Answers replaced at the stop.** Let every call of `O` from a state of `Stop` lead to
states of `Stop` with the same value of `g`. The oracle that answers `r₀` on every transition
into `Stop` and keeps the transitions of `O` otherwise gives the same distribution of the final
value of `g` as `O`. -/
theorem run_map_eq_of_cut {β : Type} (O : S → D → PMF (R × S)) (Stop : S → Prop)
    [DecidablePred Stop] (g : S → β) (r₀ : R)
    (hO : ∀ s d, Stop s → ∀ x ∈ (O s d).support, Stop x.2 ∧ g x.2 = g s)
    (A : OracleAdv D R α) (s : S) :
    (run (fun s d => (O s d).map fun x => if Stop x.2 then (r₀, x.2) else x) A s).map
        (fun x => g x.2) = (run O A s).map (fun x => g x.2) := by
  have hO' : ∀ s d, Stop s → ∀ x ∈ ((O s d).map fun x =>
      if Stop x.2 then (r₀, x.2) else x).support, Stop x.2 ∧ g x.2 = g s := by
    intro s d hs x hx
    rw [PMF.support_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hO s d hs y hy
    grind
  induction A generalizing s with
  | ret a => rfl
  | rand p k ih => simp only [run_rand, PMF.map_bind, fun b => ih b s]
  | query d k ih =>
    rw [run_query, run_query, PMF.map_bind, PMF.map_bind, PMF.bind_map]
    refine PMF.bind_congr_support _ _ _ fun y _ => ?_
    by_cases hy2 : Stop y.2
    · simp only [Function.comp_apply, hy2, ite_true]
      rw [run_map_eq_pure_of_frozen _ Stop g hO' _ _ hy2,
        run_map_eq_pure_of_frozen O Stop g hO _ _ hy2]
    · simp only [Function.comp_apply, hy2, ite_false]
      exact ih y.1 y.2

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
