/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Constructions.ECBCPRFFlag
public import CatCryptCore.Crypto.OracleAdversaryTimed

/-!
# Eager and lazy random functions

A uniform function `D → R` sampled before a run and a lazy random function (`rfOracle`),
which draws the value at a point when the point is first queried, give an adaptive
adversary (`OracleAdv`) the same output distribution. The table oracle `tabOracle f`
answers from an eagerly sampled `f` with the table of answered queries as state; averaged
over a uniform `f` it is the lazy random function, and against a table consistent with `f`
it answers as the keyed oracle of `f`. The same holds when the random function is sampled
inside a program (`lazyRF`) or behind a simulation of the queries (`simOracle`).

## Main definitions

* `ECBCPRF.tabOracle f` — the random function evaluated from an eagerly sampled `f`,
  recording answered queries
* `SIVNonce.lazyRF X t` — `X` run against a random function sampled inside the adversary
  from the table `t`; `SIVNonce.lazyRF.timed` its costed form

## Main results

* `ECBCPRF.uniform_bind_run_tabOracle` — averaged over a uniform `f`, a run against
  `tabOracle f` is a run against the lazy random function
* `ECBCPRF.uniform_bind_run_keyed_map_fst` — the output against the keyed oracle of a uniform
  function is the output against the lazy random function
* `ECBCPRF.realGame_apply_eq_rfGame` — the real game of the family of all functions with a
  uniform key is the lazy random-function game
* `SIV.run_map_fst_eq_of_map_state` — the output of a run is invariant under a map of oracle
  states commuting with every oracle call
* `SIVNonce.run_lazyRF` — running `lazyRF X t` against any oracle is running `X` against the
  lazy random function from `t`
* `SIVNonce.uniform_bind_run_simOracle_keyed` — eager and lazy sampling behind a simulation
* `SIVNonce.timeBound_simulate_succ` — a simulation whose programs have time `t + 1` adds
  time `q * t` to an adversary with `q` queries
* `SIVNonce.lazyRF.timeBound_timed` — `lazyRF.timed X t` takes at most the time of `X`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Constructions.ECBCPRF

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open scoped ENNReal

/-! ## Eager and lazy random functions -/

section EagerLazy

variable {D R : Type} [DecidableEq D] {α : Type}

theorem lookup_cons_isSome (d d' : D) (r : R) (t : List (D × R))
    (h : (List.lookup d t).isSome) : (List.lookup d ((d', r) :: t)).isSome := by
  by_cases hd : d = d'
  · subst hd; simp
  · have hb : (d == d') = false := by simpa using hd
    simp [List.lookup_cons, hb, h]

theorem lookup_cons_self_isSome (d : D) (r : R) (t : List (D × R)) :
    (List.lookup d ((d, r) :: t)).isSome := by
  simp

/-- Random function evaluated from an eagerly sampled `f`, with the table of
answered queries as state: a recorded query returns its recorded answer, a fresh
query returns `f d` and records it. -/
noncomputable def tabOracle (f : D → R) (t : List (D × R)) (d : D) : PMF (R × List (D × R)) :=
  match List.lookup d t with
  | some r => PMF.pure (r, t)
  | none => PMF.pure (f d, (d, f d) :: t)

/-- A run of `tabOracle f` from a table recording `d` never reads `f d`. -/
theorem run_tabOracle_update (f : D → R) (d : D) (y : R) (A : OracleAdv D R α)
    (t : List (D × R)) (ht : (List.lookup d t).isSome) :
    OracleAdv.run (tabOracle (Function.update f d y)) A t = OracleAdv.run (tabOracle f) A t := by
  induction A generalizing t with
  | ret a => rfl
  | rand p k ih => simp only [OracleAdv.run_rand, ih _ t ht]
  | query d' k ih =>
    simp only [OracleAdv.run_query, tabOracle]
    cases hl : List.lookup d' t with
    | some r => simp only [PMF.pure_bind]; exact ih r t ht
    | none =>
      have hne : d' ≠ d := by
        rintro rfl; simp [hl] at ht
      simp only [PMF.pure_bind, Function.update_of_ne hne]
      grind

/-- Joint output and table of a run against the eager table oracle, averaged over a
uniform `f`, equal those of a run against the lazy random function. -/
theorem uniform_bind_run_tabOracle [Fintype D] [DecidableEq R] [Fintype R] [Nonempty R]
    (A : OracleAdv D R α) (t : List (D × R)) :
    (PMF.uniformFintype (D → R)).bind (fun f => OracleAdv.run (tabOracle f) A t) =
      OracleAdv.run rfOracle A t := by
  induction A generalizing t with
  | ret a => simp
  | rand p k ih =>
    simp only [OracleAdv.run_rand]
    rw [PMF.bind_comm]
    simp_all
  | query d k ih =>
    simp only [OracleAdv.run_query, tabOracle, rfOracle]
    cases hl : List.lookup d t with
    | some r => simp only [PMF.pure_bind]; exact ih r t
    | none =>
      simp only [PMF.pure_bind, PMF.bind_map, Function.comp_def]
      simp only [← ih]
      conv_lhs => rw [← uniform_bind_update d]
      rw [PMF.bind_bind]
      rw [PMF.bind_comm (PMF.uniformFintype R)]
      refine congrArg _ (funext fun f => ?_)
      simp only [PMF.bind_map, Function.comp_def, Function.update_self]
      refine congrArg _ (funext fun r => ?_)
      simp_all [run_tabOracle_update]

/-- Against a table consistent with `f`, the table oracle answers as the keyed
oracle `f`. -/
theorem run_tabOracle_map_fst (f : D → R) (A : OracleAdv D R α) (t : List (D × R))
    (ht : ∀ p ∈ t, p.2 = f p.1) :
    (OracleAdv.run (tabOracle f) A t).map Prod.fst =
      (OracleAdv.run (keyedOracle (fun f d => f d) f) A ()).map Prod.fst := by
  induction A generalizing t with
  | ret a => simp [PMF.pure_map]
  | rand p k ih => simp only [OracleAdv.run_rand, PMF.map_bind, ih _ t ht]
  | query d k ih =>
    simp only [OracleAdv.run_query, tabOracle, keyedOracle, PMF.pure_bind, PMF.map_bind]
    cases hl : List.lookup d t with
    | some r =>
      have hr : r = f d := by
        obtain ⟨p, hp, hpd, rfl⟩ : ∃ p ∈ t, p.1 = d ∧ p.2 = r := by
          induction t with
          | nil => simp at hl
          | cons x t iht =>
            obtain ⟨a, b⟩ := x
            by_cases hx : d = a
            · subst hx
              simp at hl
              simp_all
            · have hb : (d == a) = false := by simpa using hx
              simp only [List.lookup_cons, hb] at hl
              obtain ⟨p, hp, h1, h2⟩ := iht (fun p hp => ht p (by simp [hp])) hl
              simp_all
        grind
      simp only [PMF.pure_bind, hr]
      grind
    | none =>
      simp only [PMF.pure_bind]
      refine ih _ _ ?_
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · rfl
      · grind

/-- **Eager/lazy sampling.** The output of a run against the keyed oracle of a
uniform function `D → R` is distributed as the output of a run against the lazy
random function. -/
theorem uniform_bind_run_keyed_map_fst [Fintype D] [DecidableEq R] [Fintype R] [Nonempty R]
    (A : OracleAdv D R α) :
    (PMF.uniformFintype (D → R)).bind
        (fun f => (OracleAdv.run (keyedOracle (fun f d => f d) f) A ()).map Prod.fst) =
      (OracleAdv.run rfOracle A []).map Prod.fst := by
  rw [← uniform_bind_run_tabOracle A [], PMF.map_bind]
  refine congrArg _ (funext fun f => ?_)
  simp_all [run_tabOracle_map_fst]

/-- **Eager/lazy sampling.** The real game of the family of all functions `D → R`
with a uniform key is the lazy random-function game. -/
theorem realGame_apply_eq_rfGame [Fintype D] [DecidableEq R] [Fintype R] [Nonempty R]
    (A : OracleAdv D R Bool) :
    realGame (fun (f : D → R) d => f d) A = rfGame A := by
  unfold realGame rfGame
  rw [uniform_bind_run_keyed_map_fst]

end EagerLazy

end CatCrypt.Crypto.Constructions.ECBCPRF

namespace CatCrypt.Crypto.Constructions.SIV

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF

/-! ## Run lemmas for simulated adversaries -/

section RunLemmas

variable {D R D' R' α S S' : Type}

/-- The output of a run is invariant under a map of oracle states commuting with every
oracle call. -/
theorem run_map_fst_eq_of_map_state (O : S → D → PMF (R × S)) (O' : S' → D → PMF (R × S'))
    (f : S → S') (hO : ∀ s d, (O s d).map (Prod.map id f) = O' (f s) d)
    (A : OracleAdv D R α) (s : S) :
    (OracleAdv.run O A s).map Prod.fst = (OracleAdv.run O' A (f s)).map Prod.fst := by
  rw [← OracleAdv.run_map_state O O' f hO A s, PMF.map_comp]
  rfl

end RunLemmas

end CatCrypt.Crypto.Constructions.SIV

namespace CatCrypt.Crypto.Constructions.SIVNonce

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.Constructions.ECBCPRF

/-! ## Lazily sampled tables -/

section Lazy

variable {P V D' R' β : Type} [DecidableEq P] [Fintype V] [Nonempty V]

/-- `lazyRF X t` runs `X` against a random function `P → V` sampled inside the adversary
from the table `t`: a recorded point returns its recorded value, a new point draws a
uniform value and records it. It returns the output of `X` and the final table. -/
noncomputable def lazyRF : OracleAdv P V β → List (P × V) → OracleAdv D' R' (β × List (P × V))
  | .ret b, t => .ret (b, t)
  | .rand p k, t => .rand p fun x => lazyRF (k x) t
  | .query p k, t =>
    match List.lookup p t with
    | some v => lazyRF (k v) t
    | none => .rand (PMF.uniformFintype V) fun v => lazyRF (k v) ((p, v) :: t)

/-- Running `lazyRF X t` against any oracle is running `X` against the lazy random function
`rfOracle` from the table `t`. -/
theorem run_lazyRF [DecidableEq V] {S : Type} (O : S → D' → PMF (R' × S))
    (X : OracleAdv P V β) (t : List (P × V)) (s : S) :
    OracleAdv.run O (lazyRF X t) s = (OracleAdv.run rfOracle X t).map fun x => (x, s) := by
  induction X generalizing t with
  | ret b => simp [lazyRF, PMF.pure_map]
  | rand p k ih => simp only [lazyRF, OracleAdv.run_rand, PMF.map_bind, ih]
  | query p k ih =>
    rcases h : List.lookup p t with _ | v
    · simp only [lazyRF, h, OracleAdv.run_rand, OracleAdv.run_query, rfOracle, PMF.bind_map,
        PMF.map_bind, Function.comp_def, ih]
    · simp only [lazyRF, h, OracleAdv.run_query, rfOracle, PMF.pure_bind, ih]

/-- `lazyRF X t` asks no query. -/
theorem isQueryBound_lazyRF (X : OracleAdv P V β) (t : List (P × V)) :
    (lazyRF X t : OracleAdv D' R' _).IsQueryBound 0 := by
  induction X generalizing t with
  | ret b => trivial
  | rand p k ih => exact fun x => ih x t
  | query p k ih =>
    unfold lazyRF
    split
    · exact ih _ t
    · exact fun v => ih v _

/-- **Eager/lazy sampling inside a simulation.** Let `impl s d` answer the query `d` from the
state `s` by queries to a function `P → V`. Averaged over a uniform function, the output of
`A` against `impl` and the keyed function equals its output against `impl` and the lazy
random function. -/
theorem uniform_bind_run_simOracle_keyed [Fintype P] [DecidableEq V] {D R S α : Type}
    (impl : S → D → OracleAdv P V (R × S)) (A : OracleAdv D R α) (s : S) :
    (PMF.uniformFintype (P → V)).bind (fun f =>
      (OracleAdv.run (CatCrypt.Crypto.OracleAdv.simOracle impl
        (keyedOracle (fun f p => f p) f)) A (s, ())).map Prod.fst) =
      (OracleAdv.run (CatCrypt.Crypto.OracleAdv.simOracle impl rfOracle) A (s, [])).map
        Prod.fst := by
  have h := congrArg (PMF.map Prod.fst)
    (uniform_bind_run_keyed_map_fst (CatCrypt.Crypto.OracleAdv.simulate impl A s))
  simp only [PMF.map_bind, PMF.map_comp, CatCrypt.Crypto.OracleAdv.run_simulate] at h
  exact h

end Lazy

/-! ## Running times

The costs of `CatCryptCore.Crypto.OracleAdversaryTimed`: one unit per `rand` and per
`query` node. A value of a lazily sampled table costs one `rand` node when it is first
drawn. -/

/-- **Simulation time, the replaced query counted.** If `A` has time `T` and asks at most `q`
queries, and every program of `impl` has time at most `t + 1`, then the simulated adversary
has time at most `T + q * t`: each program replaces a query node of `A`, of cost one. -/
theorem timeBound_simulate_succ {D₁ R₁ D₂ R₂ S α : Type}
    (impl : S → D₁ → ℕ × OracleAdv.Timed D₂ R₂ (R₁ × S)) {t : ℕ}
    (himpl : ∀ s d, OracleAdv.Timed.StepTimeBound (impl s d) (t + 1))
    {A : OracleAdv.Timed D₁ R₁ α} {T q : ℕ} (hA : A.TimeBound T) (hq : A.erase.IsQueryBound q)
    (s : S) : OracleAdv.Timed.StepTimeBound (OracleAdv.Timed.simulate impl A s) (T + q * t) := by
  induction A generalizing T q s with
  | ret a => exact ⟨Nat.zero_le _, trivial⟩
  | rand p c k ih =>
    have h1 := hA.1
    simp only [OracleAdv.Timed.simulate, OracleAdv.Timed.stepTimeBound_zero,
      OracleAdv.Timed.timeBound_rand_iff]
    refine ⟨by omega, fun b => ?_⟩
    have h2 := (hA.2 b).1
    exact (OracleAdv.Timed.stepTimeBound_delay (c := c b) (ih b (hA.2 b).2 (hq b) s)).mono
      (by omega)
  | query d c k ih =>
    cases q with
    | zero => exact (hq : False).elim
    | succ q =>
      have hk : ∀ x : R₁ × S, OracleAdv.Timed.StepTimeBound
          (OracleAdv.Timed.delay (c x.1) (OracleAdv.Timed.simulate impl (k x.1) x.2))
          (T - 1 + q * t) := fun x =>
        (OracleAdv.Timed.stepTimeBound_delay (ih x.1 (hA.2 x.1).2 (hq x.1) x.2)).mono
          (by have := (hA.2 x.1).1; omega)
      have hi := himpl s d
      have h := OracleAdv.Timed.stepTimeBound_delay (c := (impl s d).1)
        (OracleAdv.Timed.timeBound_bind hi.2 hk)
      exact h.mono (by have := hi.1; have := hA.1; rw [Nat.add_mul, Nat.one_mul]; omega)

section LazyTimed

variable {P V D' R' β : Type} [DecidableEq P] [Fintype V] [Nonempty V]

/-- The costed form of `lazyRF`: the step costs of `X`, and one `rand` node for every new
point. -/
noncomputable def lazyRF.timed :
    OracleAdv.Timed P V β → List (P × V) → ℕ × OracleAdv.Timed D' R' (β × List (P × V))
  | .ret b, t => (0, .ret (b, t))
  | .rand p c k, t =>
    (0, .rand p (fun x => c x + (lazyRF.timed (k x) t).1) fun x => (lazyRF.timed (k x) t).2)
  | .query p c k, t =>
    match List.lookup p t with
    | some v => OracleAdv.Timed.delay (c v) (lazyRF.timed (k v) t)
    | none => (0, .rand (PMF.uniformFintype V)
        (fun v => c v + (lazyRF.timed (k v) ((p, v) :: t)).1)
        fun v => (lazyRF.timed (k v) ((p, v) :: t)).2)

theorem lazyRF.erase_timed (X : OracleAdv.Timed P V β) (t : List (P × V)) :
    (lazyRF.timed X t : ℕ × OracleAdv.Timed D' R' _).2.erase = lazyRF X.erase t := by
  induction X generalizing t with
  | ret b => rfl
  | rand p c k ih => simp only [lazyRF.timed, OracleAdv.Timed.erase, lazyRF, ih]
  | query p c k ih =>
    simp only [lazyRF.timed, OracleAdv.Timed.erase, lazyRF]
    split <;> simp only [OracleAdv.Timed.delay, OracleAdv.Timed.erase, ih]

/-- `lazyRF.timed X t` takes at most the time of `X`. -/
theorem lazyRF.timeBound_timed {X : OracleAdv.Timed P V β} {n : ℕ} (hX : X.TimeBound n)
    (t : List (P × V)) :
    OracleAdv.Timed.StepTimeBound (lazyRF.timed X t : ℕ × OracleAdv.Timed D' R' _) n := by
  induction X generalizing n t with
  | ret b => exact ⟨Nat.zero_le _, trivial⟩
  | rand p c k ih =>
    have h1 := hX.1
    simp only [lazyRF.timed, OracleAdv.Timed.stepTimeBound_zero,
      OracleAdv.Timed.timeBound_rand_iff]
    refine ⟨h1, fun b => ?_⟩
    have h2 := (hX.2 b).1
    exact (OracleAdv.Timed.stepTimeBound_delay (c := c b) (ih b (hX.2 b).2 t)).mono (by omega)
  | query p c k ih =>
    have h1 := hX.1
    simp only [lazyRF.timed]
    split
    · next v _ =>
      have h2 := (hX.2 v).1
      exact (OracleAdv.Timed.stepTimeBound_delay (c := c v) (ih v (hX.2 v).2 t)).mono
        (by omega)
    · simp only [OracleAdv.Timed.stepTimeBound_zero, OracleAdv.Timed.timeBound_rand_iff]
      refine ⟨h1, fun v => ?_⟩
      have h2 := (hX.2 v).1
      exact (OracleAdv.Timed.stepTimeBound_delay (c := c v) (ih v (hX.2 v).2 _)).mono
        (by omega)

end LazyTimed

end CatCrypt.Crypto.Constructions.SIVNonce
