/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleGameUpToBad

/-!
# Eager sampling of a value drawn at its first use

An oracle that draws a value of `ν` at the first call that uses it (the trigger `use`), from the
states `U` where the value is not yet drawn, has the runs of an oracle whose value is drawn
before the run. Two forms of the eager oracle occur.

* **A parametrised oracle** `O₂ x` that reads the pre-sampled value `x` at the use and agrees
  with the lazy oracle `O₁` elsewhere: a run of `O₁` from a state of `U` is the run of `O₂ x`
  for `x` drawn from `ν` first (`OracleAdv.run_eager`, and `OracleAdv.run_eager_flag` for the
  probability of a bad flag). The hypotheses: the oracles agree off the use (`hno`), the use
  from `U` draws from `ν` (`huse`), the use leaves `U` (`hnext`), a state off `U` stays off `U`
  (`hpers`), and no call off `U` is a use (`hnu`).
* **The value placed in the state** by `set x`: a run of `O` from a state `s` of `U` is the run
  of the same oracle from `set x s` for `x` drawn from `ν` first, for the output together with
  an observable of the final state that `set x` keeps (`OracleAdv.run_map_obs_eq_bind_run_set`)
  and for the probability of a bad flag (`OracleAdv.run_flag_eq_tsum_run_set`). The
  hypotheses: the use from `U` draws from `ν` and continues from `set x s` (`huse`), the other
  calls from `U` commute with `set x` (`hcomm`) and stay in `U` (`hstay`).

The flagged form `OracleAdv.run_eager_flagWhen` holds for every bad event on the transitions,
since both oracles carry the same flag; `OracleAdv.run_eager_flag` is its instance for a bad
event on the reached state.

The tactic `eager_draw U use` applies these lemmas and the lemma
`OracleAdv.run_map_fst_eq_bind_run_set_of_trigger` of `CatCryptCore.Crypto.OracleGameUpToBad`,
chosen by the shape of the goal, and leaves the side conditions it does not close. A module
that uses it imports this module both publicly and with `meta`.

## Main results

* `OracleAdv.run_eager`, `OracleAdv.run_eager_used`, `OracleAdv.run_eager_flagWhen`,
  `OracleAdv.run_eager_flag`
* `OracleAdv.run_map_obs_eq_bind_run_set`, `OracleAdv.run_flag_eq_tsum_run_set`
* the tactic `eager_draw`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv

open scoped ENNReal

section Eager

variable {σ D R α X : Type}

/-- After the use, the oracle with the pre-sampled value is the lazy oracle. -/
theorem run_eager_used (O₁ : σ → D → PMF (R × σ)) (O₂ : X → σ → D → PMF (R × σ))
    (U : σ → Prop) (use : σ → D → Prop) (hno : ∀ x s d, ¬ use s d → O₂ x s d = O₁ s d)
    (hpers : ∀ s d, ¬ U s → ∀ y ∈ (O₁ s d).support, ¬ U y.2)
    (hnu : ∀ s d, ¬ U s → ¬ use s d) (x : X) (A : OracleAdv D R α) (s : σ) (hs : ¬ U s) :
    OracleAdv.run (O₂ x) A s = OracleAdv.run O₁ A s :=
  OracleAdv.run_eq_run_of_inv O₁ (O₂ x) (fun s => ¬ U s) hpers
    (fun s d hs => hno x s d (hnu s d hs)) A s hs

/-- **Eager sampling of a value used at most once.** The lazy oracle `O₁` draws a value of `ν`
at the step that uses it (`use`), and the oracle `O₂ x` reads the pre-sampled value `x` there
and agrees with `O₁` elsewhere. When the use happens only from states where the value is
unused (`U`), makes it used, and a used value stays used, a run of `O₁` from an unused state is
the run of `O₂ x` for `x` drawn from `ν` first. -/
theorem run_eager (ν : PMF X) (O₁ : σ → D → PMF (R × σ)) (O₂ : X → σ → D → PMF (R × σ))
    (U : σ → Prop) (use : σ → D → Prop) (hno : ∀ x s d, ¬ use s d → O₂ x s d = O₁ s d)
    (huse : ∀ s d, U s → use s d → O₁ s d = ν.bind fun x => O₂ x s d)
    (hnext : ∀ x s d, U s → use s d → ∀ y ∈ (O₂ x s d).support, ¬ U y.2)
    (hpers : ∀ s d, ¬ U s → ∀ y ∈ (O₁ s d).support, ¬ U y.2)
    (hnu : ∀ s d, ¬ U s → ¬ use s d) (A : OracleAdv D R α) (s : σ) (hs : U s) :
    OracleAdv.run O₁ A s = ν.bind fun x => OracleAdv.run (O₂ x) A s :=
  OracleAdv.run_eq_bind_run_of_trigger ν O₁ O₂ U use (fun _ s => ¬ U s) huse
    (fun x s d _ hu => hno x s d hu) (fun _ _ _ _ y _ => (em (U y.2)).imp id fun h _ => h)
    hnext (fun _ => hpers) (fun x s d hs => hno x s d (hnu s d hs)) A s hs

/-- `run_eager` for flagged oracles, with a bad event on the transitions. -/
theorem run_eager_flagWhen (ν : PMF X) (O₁ : σ → D → PMF (R × σ))
    (O₂ : X → σ → D → PMF (R × σ)) (bad : σ → D → R × σ → Prop)
    [∀ s d y, Decidable (bad s d y)]
    (U : σ → Prop) (use : σ → D → Prop) (hno : ∀ x s d, ¬ use s d → O₂ x s d = O₁ s d)
    (huse : ∀ s d, U s → use s d → O₁ s d = ν.bind fun x => O₂ x s d)
    (hnext : ∀ x s d, U s → use s d → ∀ y ∈ (O₂ x s d).support, ¬ U y.2)
    (hpers : ∀ s d, ¬ U s → ∀ y ∈ (O₁ s d).support, ¬ U y.2)
    (hnu : ∀ s d, ¬ U s → ¬ use s d) (A : OracleAdv D R α) (s : σ) (b : Bool) (hs : U s) :
    (OracleAdv.run (OracleAdv.flagWhen bad O₁) A (s, b)).toOuterMeasure {y | y.2.2 = true} =
      ∑' x, ν x * (OracleAdv.run (OracleAdv.flagWhen bad (O₂ x)) A
        (s, b)).toOuterMeasure {y | y.2.2 = true} := by
  rw [run_eager ν _ (fun x => OracleAdv.flagWhen bad (O₂ x))
    (fun t => U t.1) (fun t d => use t.1 d) _ _ _ _ _ A (s, b) hs,
    PMF.toOuterMeasure_bind_apply]
  · intro x t d h
    simp only [OracleAdv.flagWhen, hno x t.1 d h]
  · intro t d ht h
    simp only [OracleAdv.flagWhen, huse t.1 d ht h, PMF.map_bind]
  · intro x t d ht h y hy
    simp only [OracleAdv.flagWhen, PMF.support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hnext x t.1 d ht h z hz
  · intro t d ht y hy
    simp only [OracleAdv.flagWhen, PMF.support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hpers t.1 d ht z hz
  · exact fun t d ht => hnu t.1 d ht

/-- `run_eager` for flagged oracles whose bad event reads the reached state. -/
theorem run_eager_flag (ν : PMF X) (O₁ : σ → D → PMF (R × σ)) (O₂ : X → σ → D → PMF (R × σ))
    (bad : σ → Prop) [DecidablePred bad]
    (U : σ → Prop) (use : σ → D → Prop) (hno : ∀ x s d, ¬ use s d → O₂ x s d = O₁ s d)
    (huse : ∀ s d, U s → use s d → O₁ s d = ν.bind fun x => O₂ x s d)
    (hnext : ∀ x s d, U s → use s d → ∀ y ∈ (O₂ x s d).support, ¬ U y.2)
    (hpers : ∀ s d, ¬ U s → ∀ y ∈ (O₁ s d).support, ¬ U y.2)
    (hnu : ∀ s d, ¬ U s → ¬ use s d) (A : OracleAdv D R α) (s : σ) (hs : U s) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ y => bad y.2) O₁) A (s, false)).toOuterMeasure
        {y | y.2.2 = true} =
      ∑' x, ν x * (OracleAdv.run (OracleAdv.flagWhen (fun _ _ y => bad y.2) (O₂ x)) A
        (s, false)).toOuterMeasure {y | y.2.2 = true} :=
  run_eager_flagWhen ν O₁ O₂ _ U use hno huse hnext hpers hnu A s false hs

end Eager

section EagerSet

variable {σ D R α β X : Type}

/-- **A value drawn at its first use, placed in the state, for an observable of the state.**
Let the oracle `O`, from the states `U` before the draw, draw the value `x` from `ν` at the
calls `use` and continue from the state `set x s`, and let the other calls from `U` stay in `U`
and commute with `set x`. Then from a state `s` of `U` the output of a run against `O`, with an
observable `g` of the final state that `set x` keeps, is that of the run from `set x s` for `x`
drawn from `ν` first. -/
theorem run_map_obs_eq_bind_run_set (ν : PMF X) (O : σ → D → PMF (R × σ)) (set : X → σ → σ)
    (g : σ → β) (hg : ∀ x s, g (set x s) = g s) (U : σ → Prop) (use : σ → D → Prop)
    (huse : ∀ s d, U s → use s d → O s d = ν.bind fun x => O (set x s) d)
    (hcomm : ∀ x s d, U s → ¬ use s d → O (set x s) d = (O s d).map (Prod.map id (set x)))
    (hstay : ∀ s d, U s → ¬ use s d → ∀ y ∈ (O s d).support, U y.2) (A : OracleAdv D R α)
    (s : σ) (hs : U s) :
    (OracleAdv.run O A s).map (fun y => (y.1, g y.2)) =
      ν.bind fun x => (OracleAdv.run O A (set x s)).map fun y => (y.1, g y.2) := by
  induction A generalizing s with
  | ret a => simp only [OracleAdv.run_ret, PMF.pure_map, hg, PMF.bind_const]
  | rand p f ih =>
    simp only [OracleAdv.run_rand, PMF.map_bind, fun b => ih b s hs]
    exact PMF.bind_comm _ _ _
  | query d f ih =>
    simp only [OracleAdv.run_query, PMF.map_bind]
    by_cases hcs : use s d
    · rw [huse s d hs hcs, PMF.bind_bind]
    · simp only [hcomm _ s d hs hcs, PMF.bind_map, Function.comp_def, Prod.map_fst,
        Prod.map_snd, id_eq]
      rw [PMF.bind_comm]
      exact PMF.bind_congr_support _ _ _ fun y hy => ih y.1 y.2 (hstay s d hs hcs y hy)

/-- **A value drawn at its first use, placed in the state, for a bad flag.** The form of
`run_map_obs_eq_bind_run_set` for an oracle on flagged states `σ × Bool` whose value lives in
the first component: the probability that the run from `(s, b)` ends with the flag set is the
average over `x` drawn from `ν` of that probability from `(set x s, b)`. -/
theorem run_flag_eq_tsum_run_set (ν : PMF X) (O : σ × Bool → D → PMF (R × (σ × Bool)))
    (set : X → σ → σ) (U : σ → Prop) (use : σ → D → Prop)
    (huse : ∀ t d, U t.1 → use t.1 d → O t d = ν.bind fun x => O (set x t.1, t.2) d)
    (hcomm : ∀ x t d, U t.1 → ¬ use t.1 d →
      O (set x t.1, t.2) d = (O t d).map (Prod.map id fun u => (set x u.1, u.2)))
    (hstay : ∀ t d, U t.1 → ¬ use t.1 d → ∀ y ∈ (O t d).support, U y.2.1)
    (A : OracleAdv D R α) (s : σ) (b : Bool) (hs : U s) :
    (OracleAdv.run O A (s, b)).toOuterMeasure {y | y.2.2 = true} =
      ∑' x, ν x * (OracleAdv.run O A (set x s, b)).toOuterMeasure {y | y.2.2 = true} := by
  have h := run_map_obs_eq_bind_run_set ν O (fun x t => (set x t.1, t.2)) Prod.snd
    (fun _ _ => rfl) (fun t => U t.1) (fun t d => use t.1 d) huse hcomm hstay A (s, b) hs
  have hm : ∀ t, (OracleAdv.run O A t).toOuterMeasure {y | y.2.2 = true} =
      ((OracleAdv.run O A t).map fun y => (y.1, y.2.2)).toOuterMeasure {z | z.2 = true} :=
    fun t => by
      rw [PMF.toOuterMeasure_map_apply]
      rfl
  rw [hm, h, PMF.toOuterMeasure_bind_apply]
  exact tsum_congr fun x => by rw [hm]

end EagerSet

end CatCrypt.Crypto.OracleAdv

namespace CatCrypt.Tactics

/-- The side conditions of the eager-sampling lemmas that close by `assumption`, by reducible
reflexivity, or after `intros` by `simp_all` or `grind` with the given lemmas. -/
syntax (name := eagerDrawSide) "eager_draw_side" (" [" ident,* "]")? : tactic

macro_rules
  | `(tactic| eager_draw_side $[[$ts,*]]?) => do
    let ts : Array Lean.Ident := (ts.map (·.getElems)).getD #[]
    `(tactic| first
        | assumption
        | (intros; with_reducible rfl)
        | ((fail_if_success intro); exact rfl)
        | (intros; simp_all [$[$ts:ident],*]; done)
        | (intros; grind [$[$ts:ident],*]))

/-- **Eager sampling of a value drawn at its first use.** `eager_draw U use` closes a goal

* `OracleAdv.run O₁ A s = ν.bind fun x => OracleAdv.run (O₂ x) A s`
  (`OracleAdv.run_eager`),
* `(run (flagWhen (fun _ _ y => bad y.2) O₁) A (s, false)).toOuterMeasure {y | y.2.2 = true} =
  ∑' x, ν x * (run (flagWhen (fun _ _ y => bad y.2) (O₂ x)) A (s, false)).toOuterMeasure …`
  (`OracleAdv.run_eager_flag`),
* `(run O A s).map (fun y => (y.1, g y.2)) = ν.bind fun x => (run O A (set x s)).map …`
  (`OracleAdv.run_map_obs_eq_bind_run_set`),
* `(run O A (s, b)).toOuterMeasure {y | y.2.2 = true} =
  ∑' x, ν x * (run O A (set x s, b)).toOuterMeasure {y | y.2.2 = true}`
  (`OracleAdv.run_flag_eq_tsum_run_set`), or
* `(run O A s).map Prod.fst = ν.bind fun x => (run O A (set x s)).map Prod.fst`
  (`OracleAdv.run_map_fst_eq_bind_run_set_of_trigger`),

where `U` is the predicate "the value is not yet drawn" on states and `use` the predicate "this
call draws it". It leaves the side conditions of the lemma that `eager_draw_side` does not
close: `assumption`, reducible reflexivity, and after `intros` `simp_all` or `grind` with the
lemmas `[ts]` (the step definitions to unfold). `eager_draw U use with set` names the map that
places the value in the state, when unification does not find it from the goal. -/
syntax (name := eagerDraw)
  "eager_draw " term:max ppSpace term:max (" with " term:max)? (" [" ident,* "]")? : tactic

macro_rules
  | `(tactic| eager_draw $U $use $[with $set?]? $[[$ts?,*]]?) => do
    let ts : Array Lean.Ident := (ts?.map (·.getElems)).getD #[]
    let set ← match set? with
      | some t => pure t
      | none => `(_)
    `(tactic| (first
        | refine CatCrypt.Crypto.OracleAdv.run_eager _ _ _ $U $use ?_ ?_ ?_ ?_ ?_ _ _ ?_
        | refine CatCrypt.Crypto.OracleAdv.run_eager_flagWhen _ _ _ _ $U $use ?_ ?_ ?_ ?_ ?_
            _ _ _ ?_
        | refine CatCrypt.Crypto.OracleAdv.run_flag_eq_tsum_run_set _ _ $set $U $use ?_ ?_ ?_
            _ _ _ ?_
        | refine CatCrypt.Crypto.OracleAdv.run_map_obs_eq_bind_run_set _ _ $set _ ?_ $U $use
            ?_ ?_ ?_ _ _ ?_
        | refine CatCrypt.Crypto.OracleAdv.run_map_fst_eq_bind_run_set_of_trigger _ _ $set $U
            $use ?_ ?_ ?_ _ _ ?_)
      <;> try eager_draw_side [$[$ts:ident],*])

end CatCrypt.Tactics
