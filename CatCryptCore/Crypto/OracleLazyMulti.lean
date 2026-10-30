/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.EagerLazyRF
public import CatCryptCore.Crypto.OracleBadDraw
public import CatCryptCore.ForMathlib.PMFSupport

/-!
# Oracles reading several points of a random function, late draws, and bad flags

Three general facts about runs of adaptive oracle adversaries (`OracleAdv.run`).

## Eager and lazy sampling behind a simulation, and oracles reading several points

A simulator program `impl s d` answers the query `d` from the state `s` by queries to a
function `P → V`. Averaged over a uniform function, the output and the final simulator state
of a run against `impl` and the keyed function are those of a run against `impl` and the lazy
random function `rfOracle`. A point-list oracle reads a function `f : D → R` at the list of
points `pts q` and answers by the deterministic step `step q ((pts q).map f)`; its eager form
`eagerPointsOracle` reads a function sampled before the run, its lazy form
`lazyPointsOracle` draws each unrecorded point when it is read.

* `OracleAdv.uniform_bind_run_simOracle_keyed_joint` — eager and lazy sampling behind a
  simulation, with the output and the final simulator state
* `OracleAdv.uniform_bind_run_eagerPointsOracle` — averaged over a uniform function, a run
  against the eager point-list oracle has the output and final state of a run against the
  lazy point-list oracle from the empty table

## Late draws

After a run, the value of a point `d` that the run left unrecorded in its table is drawn
uniformly from `V`. If the final state determines a set of at most `n` bad values, the drawn
value is bad with probability at most `n / |V|`. When each oracle call adds at most `cost q`
bad values, `n` is the total query cost.

* `OracleAdv.bind_uniform_mem_le` — a uniform value drawn after `μ` lies in a set of at most
  `n` values chosen by the outcome of `μ` with probability at most `n / |V|`
* `OracleAdv.bind_rfOracle_fresh_mem_le` — the same for a point drawn by the lazy random
  function from the final table, counted only when the point is unrecorded
* `OracleAdv.run_card_le_of_mem_support` — a counter on oracle states that grows by at most
  `cost q` per call grows by at most the total query cost in a run
* `OracleAdv.run_lateDraw_le` — the late draw of an unrecorded point is bad with probability
  at most `(m₀ + n) / |V|`, for `m₀` bad values at the start and total query cost `n`
* `OracleAdv.run_lateDraw_le_of_isQueryBound` — for `q` queries adding at most `k` bad values
  each, the bound `q · k / |V|`

## Bad flags on transitions, read in the second run

`flagWhen bad O` is the oracle `O` with a sticky flag set by every transition `(s, d, x)`
with `bad s d x`. For oracles that agree on every outcome of a step that is not bad, the
probability of an output event under the first is at most its probability under the second
plus the probability that the flagged run of the second oracle sets the flag. The flag is
computed in the second run only.

* `OracleAdv.run_toOuterMeasure_le_add_flagWhen` — up to bad, with the flag of the second run
* `OracleAdv.run_gap_le_flagWhen` — the same for the distance of the two output probabilities
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv

open CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.Constructions.ECBCPRF (uniform_bind_run_keyed_map_fst toOuterMeasure_flag_eq
  toOuterMeasure_le_add_flag)
open scoped ENNReal

/-! ## Eager and lazy sampling behind a simulation -/

section Simulation

variable {P V D R S α : Type} [DecidableEq P]

/-- **Eager and lazy sampling inside a simulation, jointly with the simulator state.** Let
`impl s d` answer the query `d` from the state `s` by queries to a function `P → V`. Averaged
over a uniform function, the output and the final simulator state of `A` against `impl` and
the keyed function are those of `A` against `impl` and the lazy random function. -/
theorem uniform_bind_run_simOracle_keyed_joint [Fintype P] [Fintype V]
    [Nonempty V] (impl : S → D → OracleAdv P V (R × S)) (A : OracleAdv D R α) (s : S) :
    (PMF.uniformFintype (P → V)).bind (fun f =>
      (run (simOracle impl (keyedOracle (fun f p => f p) f)) A (s, ())).map
        fun x => (x.1, x.2.1)) =
      (run (simOracle impl rfOracle) A (s, [])).map fun x => (x.1, x.2.1) := by
  classical
  have h := uniform_bind_run_keyed_map_fst (simulate impl A s)
  simp only [run_simulate, PMF.map_comp] at h
  exact h

end Simulation

/-! ## Oracles that read several points of a function -/

section Points

variable {Q Ans D R σ : Type} [DecidableEq D]

/-- The program that reads the function at the points `l` in order and returns the values. -/
def readPoints : List D → OracleAdv D R (List R)
  | [] => .ret []
  | d :: l => .query d fun r => (readPoints l).bind fun rs => .ret (r :: rs)

/-- The simulator program of a point-list oracle: read the points `pts q`, then the step. -/
def pointsImpl (pts : Q → List D) (step : Q → List R → σ → Ans × σ) (s : σ) (q : Q) :
    OracleAdv D R (Ans × σ) :=
  (readPoints (pts q)).bind fun rs => .ret (step q rs s)

/-- **The eager point-list oracle.** The query `q` reads the function `f` at the points
`pts q` and answers by `step q ((pts q).map f)` from the state. -/
noncomputable def eagerPointsOracle (pts : Q → List D) (step : Q → List R → σ → Ans × σ)
    (f : D → R) (s : σ) (q : Q) : PMF (Ans × σ) :=
  PMF.pure (step q ((pts q).map f) s)

/-- The lazy random function read at the points `l` in order from the table `t`: the values
and the final table. -/
noncomputable def rfPoints [Fintype R] [Nonempty R] :
    List (D × R) → List D → PMF (List R × List (D × R))
  | t, [] => PMF.pure ([], t)
  | t, d :: l => (rfOracle t d).bind fun x => (rfPoints x.2 l).map fun y => (x.1 :: y.1, y.2)

/-- **The lazy point-list oracle.** The query `q` reads the lazily sampled random function at
the points `pts q` (recorded values, or fresh uniform values that are recorded) and answers by
`step` from the first component of the state; the second component is the table. -/
noncomputable def lazyPointsOracle [Fintype R] [Nonempty R] (pts : Q → List D)
    (step : Q → List R → σ → Ans × σ) (s : σ × List (D × R)) (q : Q) :
    PMF (Ans × (σ × List (D × R))) :=
  (rfPoints s.2 (pts q)).map fun x => ((step q x.1 s.1).1, ((step q x.1 s.1).2, x.2))

omit [DecidableEq D] in
/-- Reading points from the keyed oracle of `f` returns the values of `f`. -/
theorem run_readPoints_keyed (f : D → R) (l : List D) (u : Unit) :
    run (keyedOracle (fun f d => f d) f) (readPoints l) u = PMF.pure (l.map f, ()) := by
  induction l with
  | nil => rfl
  | cons d l ih => simp [readPoints, run_bind, keyedOracle, ih]

/-- Reading points from the lazy random function is `rfPoints`. -/
theorem run_readPoints_rf [Fintype R] [Nonempty R] (l : List D)
    (t : List (D × R)) : run rfOracle (readPoints l) t = rfPoints t l := by
  induction l generalizing t with
  | nil => rfl
  | cons d l ih => simp [readPoints, run_bind, rfPoints, ih, PMF.map, Function.comp_def]

omit [DecidableEq D] in
/-- The point-list program against the keyed oracle of `f` is the eager point-list oracle. -/
theorem simOracle_pointsImpl_keyed (pts : Q → List D) (step : Q → List R → σ → Ans × σ)
    (f : D → R) (s : σ × Unit) (q : Q) :
    simOracle (pointsImpl pts step) (keyedOracle (fun f d => f d) f) s q =
      (eagerPointsOracle pts step f s.1 q).map (Prod.map id fun s' => (s', ())) := by
  simp [simOracle, pointsImpl, run_bind, run_readPoints_keyed, eagerPointsOracle, PMF.pure_map]
  rfl

/-- The point-list program against the lazy random function is the lazy point-list oracle. -/
theorem simOracle_pointsImpl_rf [Fintype R] [Nonempty R] (pts : Q → List D)
    (step : Q → List R → σ → Ans × σ) :
    simOracle (pointsImpl pts step) rfOracle = lazyPointsOracle pts step := by
  funext s q
  simp [simOracle, pointsImpl, run_bind, run_readPoints_rf, lazyPointsOracle, PMF.map,
    Function.comp_def]

/-- **Eager and lazy point-list oracles.** Averaged over a uniform function `D → R`, the
output and final state of a run against the eager point-list oracle are those of a run against
the lazy point-list oracle from the empty table. -/
theorem uniform_bind_run_eagerPointsOracle [Fintype D] [Fintype R] [Nonempty R]
    {α : Type} (pts : Q → List D) (step : Q → List R → σ → Ans × σ) (A : OracleAdv Q Ans α)
    (s : σ) :
    (PMF.uniformFintype (D → R)).bind (fun f => run (eagerPointsOracle pts step f) A s) =
      (run (lazyPointsOracle pts step) A (s, [])).map fun x => (x.1, x.2.1) := by
  have h := uniform_bind_run_simOracle_keyed_joint (pointsImpl pts step) A s
  rw [simOracle_pointsImpl_rf] at h
  rw [← h]
  refine congrArg _ (funext fun f => ?_)
  rw [← run_map_state _ _ _
    (fun s q => (simOracle_pointsImpl_keyed pts step f (s, ()) q).symm) A s, PMF.map_comp]
  exact (PMF.map_id _).symm

end Points

/-! ## Late draws -/

section LateDraw

variable {D R α Y P V S : Type}

/-- A uniform value drawn after `μ` lies in a set `B y` of at most `n` values, chosen by the
outcome `y` of `μ`, with probability at most `n / |V|`. -/
theorem bind_uniform_mem_le [Fintype V] [Nonempty V] (μ : PMF Y) (B : Y → Finset V) (n : ℕ)
    (hB : ∀ y ∈ μ.support, (B y).card ≤ n) :
    (μ.bind fun y => (PMF.uniformFintype V).map fun v => (y, v)).toOuterMeasure
      {z | z.2 ∈ B z.1} ≤ n / Fintype.card V := by
  refine (PMF.toOuterMeasure_bind_le_add μ _ μ.supportᶜ _ (n / Fintype.card V)
    fun y hy => ?_).trans_eq ?_
  · rw [Set.notMem_compl_iff] at hy
    rw [PMF.toOuterMeasure_map_apply]
    have hs : (fun v => (y, v)) ⁻¹' {z : Y × V | z.2 ∈ B z.1} = (B y : Set V) := by
      ext v; simp
    rw [hs, PMF.toOuterMeasure_uniformFintype_apply]
    gcongr
    simpa using hB y hy
  · rw [(PMF.toOuterMeasure_apply_eq_zero_iff μ _).mpr disjoint_compl_right, zero_add]

/-- The value of the point `d` read after `μ` from the lazy random function with the final
table `tab y` is, when `d` is unrecorded, in a set `B y` of at most `n` values with
probability at most `n / |V|`. -/
theorem bind_rfOracle_fresh_mem_le [DecidableEq P] [Fintype V] [Nonempty V]
    (μ : PMF Y) (tab : Y → List (P × V)) (d : P) (B : Y → Finset V) (n : ℕ)
    (hB : ∀ y ∈ μ.support, (B y).card ≤ n) :
    (μ.bind fun y => (rfOracle (tab y) d).map fun x => (y, x.1)).toOuterMeasure
      {z | List.lookup d (tab z.1) = none ∧ z.2 ∈ B z.1} ≤ n / Fintype.card V := by
  refine (PMF.toOuterMeasure_bind_le_add μ _ μ.supportᶜ _ (n / Fintype.card V)
    fun y hy => ?_).trans_eq ?_
  · rw [Set.notMem_compl_iff] at hy
    rw [PMF.toOuterMeasure_map_apply, rfOracle]
    cases h : List.lookup d (tab y) with
    | some r =>
      simp only [h, PMF.toOuterMeasure_pure_apply, Set.mem_preimage, Set.mem_ofPred_eq,
        reduceCtorEq, false_and, ite_false, zero_le]
    | none =>
      rw [PMF.toOuterMeasure_map_apply]
      have hs : (fun r => (r, (d, r) :: tab y)) ⁻¹' ((fun x : V × List (P × V) => (y, x.1)) ⁻¹'
          {z : Y × V | List.lookup d (tab z.1) = none ∧ z.2 ∈ B z.1}) = (B y : Set V) := by
        ext v; simp only [Set.mem_preimage, Set.mem_ofPred_eq, h, true_and, Finset.mem_coe]
      rw [hs, PMF.toOuterMeasure_uniformFintype_apply]
      gcongr
      simpa using hB y hy
  · rw [(PMF.toOuterMeasure_apply_eq_zero_iff μ _).mpr disjoint_compl_right, zero_add]

/-- A counter `m` on oracle states that one call at `q` raises by at most `cost q` is raised
by at most `n` in a run of total query cost at most `n`. -/
theorem run_card_le_of_mem_support (O : S → D → PMF (R × S)) (m : S → ℕ) (cost : D → ℕ)
    (hO : ∀ s d, ∀ x ∈ (O s d).support, m x.2 ≤ m s + cost d) (A : OracleAdv D R α) (n : ℕ)
    (hA : A.IsQueryBoundBy cost n) (s : S) :
    ∀ y ∈ (run O A s).support, m y.2 ≤ m s + n := by
  induction A generalizing n s with
  | ret a => simp
  | rand p k ih =>
    intro y hy
    simp only [run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, -, hy⟩ := hy
    exact ih b n (hA b) s y hy
  | query d k ih =>
    intro y hy
    simp only [run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨x, hx, hy⟩ := hy
    have h1 := ih x.1 _ (hA.2 x.1) x.2 y hy
    have h2 := hO s d x hx
    have h3 := hA.1
    omega

/-- **Late draw after a run.** Let the bad values `B s` of a state grow by at most `cost q`
in one oracle call at `q`. After a run of total query cost at most `n` from `s`, the value of
the point `d` drawn from the final table `tab`, when `d` is unrecorded, is bad with
probability at most `(|B s| + n) / |V|`. -/
theorem run_lateDraw_le [DecidableEq P] [Fintype V] [Nonempty V]
    (O : S → D → PMF (R × S)) (tab : S → List (P × V)) (d : P) (B : S → Finset V)
    (cost : D → ℕ) (hO : ∀ s q, ∀ x ∈ (O s q).support, (B x.2).card ≤ (B s).card + cost q)
    (A : OracleAdv D R α) (n : ℕ) (hA : A.IsQueryBoundBy cost n) (s : S) :
    ((run O A s).bind fun y => (rfOracle (tab y.2) d).map fun x => (y, x.1)).toOuterMeasure
      {z | List.lookup d (tab z.1.2) = none ∧ z.2 ∈ B z.1.2} ≤
        ((B s).card + n : ℕ) / Fintype.card V :=
  bind_rfOracle_fresh_mem_le (run O A s) (fun y => tab y.2) d (fun y => B y.2) _
    (run_card_le_of_mem_support O (fun s => (B s).card) cost hO A n hA s)

/-- **Late draw after `q` queries.** If one oracle call adds at most `k` bad values and the
run starts with none, after at most `q` queries the value of an unrecorded point drawn from
the final table is bad with probability at most `q · k / |V|`. -/
theorem run_lateDraw_le_of_isQueryBound [DecidableEq P] [Fintype V]
    [Nonempty V] (O : S → D → PMF (R × S)) (tab : S → List (P × V)) (d : P)
    (B : S → Finset V) (k : ℕ) (hO : ∀ s q, ∀ x ∈ (O s q).support, (B x.2).card ≤ (B s).card + k)
    (A : OracleAdv D R α) (q : ℕ) (hA : A.IsQueryBound q) (s : S) (hs : B s = ∅) :
    ((run O A s).bind fun y => (rfOracle (tab y.2) d).map fun x => (y, x.1)).toOuterMeasure
      {z | List.lookup d (tab z.1.2) = none ∧ z.2 ∈ B z.1.2} ≤
        (q * k : ℕ) / Fintype.card V := by
  have h := run_lateDraw_le O tab d B (fun _ => k) hO A (k * q)
    (by simpa using hA.isQueryBoundBy_one.mul_left k) s
  simpa [hs, Nat.mul_comm] using h

end LateDraw

/-! ## Bad flags on transitions -/

section FlagWhen

variable {D R α σ : Type}

/-- The oracle `O` with a sticky flag that every transition `(s, d, x)` with `bad s d x` sets:
the call at `d` from `s` reaching the answer and next state `x`. -/
noncomputable def flagWhen (bad : σ → D → R × σ → Prop) [∀ s d x, Decidable (bad s d x)]
    (O : σ → D → PMF (R × σ)) : σ × Bool → D → PMF (R × (σ × Bool)) :=
  fun st d => (O st.1 d).map fun x => (x.1, (x.2, st.2 || decide (bad st.1 d x)))

variable (bad : σ → D → R × σ → Prop) [∀ s d x, Decidable (bad s d x)]

/-- Forgetting the flag maps a run of `flagWhen bad O` to the run of `O`. -/
theorem run_flagWhen_map (O : σ → D → PMF (R × σ)) (A : OracleAdv D R α) (s : σ) (b : Bool) :
    (run (flagWhen bad O) A (s, b)).map (Prod.map id Prod.fst) = run O A s :=
  run_map_state (flagWhen bad O) O Prod.fst
    (fun st d => by
      simp only [flagWhen, PMF.map_comp, Function.comp_def, Prod.map, id]
      exact PMF.map_id _) A (s, b)

/-- **Identical until a bad transition, on outcomes.** Oracles that agree on every outcome of
a call that is not bad give flagged runs that agree on every outcome with the flag cleared. -/
theorem run_flagWhen_apply_false_eq (O₁ O₂ : σ → D → PMF (R × σ))
    (h : ∀ s d x, ¬ bad s d x → O₁ s d x = O₂ s d x) (A : OracleAdv D R α) (st : σ × Bool)
    (a : α) (t : σ) :
    run (flagWhen bad O₁) A st (a, (t, false)) = run (flagWhen bad O₂) A st (a, (t, false)) := by
  have hz : ∀ (O : σ → D → PMF (R × σ)) t d r t',
      flagWhen bad O (t, true) d (r, (t', false)) = 0 := by
    intro O t d r t'
    simp [flagWhen, PMF.map_apply]
  refine run_apply_flag_false_eq _ _ (hz O₁) (hz O₂) (fun s d r t' => ?_) A st a t
  simp only [flagWhen, PMF.map_apply]
  refine tsum_congr fun x => ?_
  split_ifs with hx
  · grind
  · rfl

/-- **Up to a bad transition, with the flag of the second run.** For oracles that agree on
every outcome of a call that is not bad, the probability of an output event under the first is
at most its probability under the second plus the probability that the flagged run of the
second sets the flag. -/
theorem run_toOuterMeasure_le_add_flagWhen (O₁ O₂ : σ → D → PMF (R × σ))
    (h : ∀ s d x, ¬ bad s d x → O₁ s d x = O₂ s d x) (A : OracleAdv D R α) (s : σ)
    (E : Set α) :
    (run O₁ A s).toOuterMeasure {x | x.1 ∈ E} ≤
      (run O₂ A s).toOuterMeasure {x | x.1 ∈ E} +
        (run (flagWhen bad O₂) A (s, false)).toOuterMeasure {y | y.2.2 = true} := by
  rw [← run_flagWhen_map bad O₁ A s false, ← run_flagWhen_map bad O₂ A s false,
    PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  exact toOuterMeasure_le_add_flag _ _ (run_flagWhen_apply_false_eq bad O₁ O₂ h A _) E

/-- Oracles that agree on every outcome of a call that is not bad set the flag with the same
probability. -/
theorem run_flagWhen_prob_eq (O₁ O₂ : σ → D → PMF (R × σ))
    (h : ∀ s d x, ¬ bad s d x → O₁ s d x = O₂ s d x) (A : OracleAdv D R α) (s : σ) :
    (run (flagWhen bad O₁) A (s, false)).toOuterMeasure {y | y.2.2 = true} =
      (run (flagWhen bad O₂) A (s, false)).toOuterMeasure {y | y.2.2 = true} :=
  toOuterMeasure_flag_eq _ _ (run_flagWhen_apply_false_eq bad O₁ O₂ h A _)

/-- **Distance up to a bad transition.** For oracles that agree on every outcome of a call
that is not bad, the two output probabilities of any event differ by at most the probability
that the flagged run of the second oracle sets the flag. -/
theorem run_gap_le_flagWhen (O₁ O₂ : σ → D → PMF (R × σ))
    (h : ∀ s d x, ¬ bad s d x → O₁ s d x = O₂ s d x) (A : OracleAdv D R α) (s : σ)
    (E : Set α) :
    max ((run O₁ A s).toOuterMeasure {x | x.1 ∈ E} - (run O₂ A s).toOuterMeasure {x | x.1 ∈ E})
      ((run O₂ A s).toOuterMeasure {x | x.1 ∈ E} -
        (run O₁ A s).toOuterMeasure {x | x.1 ∈ E}) ≤
      (run (flagWhen bad O₂) A (s, false)).toOuterMeasure {y | y.2.2 = true} := by
  refine max_le (tsub_le_iff_left.mpr ?_) (tsub_le_iff_left.mpr ?_)
  · exact run_toOuterMeasure_le_add_flagWhen bad O₁ O₂ h A s E
  · rw [← run_flagWhen_prob_eq bad O₁ O₂ h A s]
    exact run_toOuterMeasure_le_add_flagWhen bad O₂ O₁ (fun s d x hx => (h s d x hx).symm) A s E

end FlagWhen

end CatCrypt.Crypto.OracleAdv
