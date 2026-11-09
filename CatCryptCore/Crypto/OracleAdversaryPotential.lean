/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.Amortized
public import CatCryptCore.Tactics.DeriveTimed.Basic

/-!
# Potential time bounds of costed oracle simulations

A reduction that answers the queries of its adversary by a stateful oracle step whose cost grows
with the state (a lazily sampled table, read at the cost companion of the table, which grows by a
`Function.update` per fresh query) has no uniform bound on the time of one query. Its time is
bounded by a potential on the costed state, as for a simulator (`derive_hybrid_time
(potential)`): a step from a state of potential at most `n` costs at most `a + b * n` and returns
states of potential at most `n + g`.

## The corollary

Let `Φ : Ŝ → ℕ` be a potential on the costed states of the handler `impl`, and let every step
from a state `s` cost at most `a + b * Φ s` and move to states `s'` with `Φ s' ≤ Φ s + g`. Then
an adversary of time `T` with at most `q` queries, simulated from the state `s₀`, has time at
most

  `T + q * (a + b * (Φ s₀ + q * g))`

(`timeBound_simulateHat_potential`). The bound is quadratic in the query count `q` when `b` and
`g` are positive.

The general form is the amortized bound `timeBound_simulateHat_amortized`, read in the
Diller–Nahm category over a state object (`CatCryptCore/Container/Amortized.lean`). The handler
is simulated by the potential step `Container.Clocked.potStep C g`, the morphism on the object of
potentials whose backward map demands `C n` clock ticks for a data token at potential `n` and
whose forward map is `n ↦ n + g`: a step from a state of potential at most `n` takes time at most
`C n` and reaches states of potential at most `n + g`. The time of the simulation is `T` plus the
cost at `n₀` of the `q`-fold composite of the potential step, `∑_{j < q} C (n₀ + j * g)`
(`Container.Clocked.iter_potStep_cost`). It is the instance of `timeBound_simulateHat_inv` (the
time of a costed simulation under a state invariant indexed by the query count,
`T + ∑_{j < q} t (i + j)`) at the invariant that the potential after `j` queries is at most
`n₀ + j * g`. It reads the potential through a predicate `Pot n s`, "the potential of `s` is at
most `n`", so that a potential that is a bound on a family (a cost companion `D → ℕ`, bounded at
every point) or that holds under an invariant needs no supremum.

`timeBound_simulateHat_potLe` is its instance at the affine demand `C n = a + b * n`, whose `q`
demands are each at most the last one (`Container.Clocked.iter_potStep_cost_le`);
`timeBound_simulateHat_potential` and `timeBound_simulateHat_table` are instances of that, and so
is the simulation rule of `derive_time_bound`, which applies `timeBound_simulateHat_potLe`.

## The costed table

A costed table is a state component `T : K → Option H` with its cost companion `c : K → ℕ`, the
cost of reading `T` at a point. A table write `Function.update T d (some h)`, unfolded, has the
companion `fun x => 2 + (if x = d then 0 else 1 + c x)` (`DeriveTimed`, costed closures), which
exceeds `c` by at most `3` at every point (`updateCompanion_le`). The step of the logged lazily
sampled random oracle `withLog roOracle`, derived by `derive_timed`, reads the table at the
query `d` (priced `2 + c d`) and either returns the state with the companion unchanged (a
defined point) or samples the answer and writes it (a fresh point). Its potential is a bound of
the companion, `Pot M s := ∀ x, comp s x ≤ M`, and its hypotheses are the derived facts of one
step: time at most `a + b * comp s (key d)` and a companion that grows by at most `g` at every
point (`timeBound_simulateHat_table`). The time of the simulation is then
`T + q * (a + b * (M₀ + q * g))` for a bound `M₀` of the initial companion. For `withLog
roOracle` from the empty table (companion `fun _ => 1`), with the unit of the call of the step,
`a = 4`, `b = 1`, `g = 3` and `M₀ = 1`: `T + q * (4 + (1 + 3 q))`.

## In `derive_time_bound`

The simulation rule of `derive_time_bound` (`CatCryptCore.Tactics.DeriveTimeBound`,
`foldSimulation?`) closes a simulation node of a costed tree by `timeBound_simulateHat_potLe`,
at the potential `Pot M s := ∀ k, c s k ≤ M` of the cost companion `c s` of the state: it derives
the step facts under the hypothesis `Pot M s` by the rules of a step (time `a + b * M`, and
`Pot (M + g)` at every leaf), so that `a`, `b`, `g` and the bound `n₀` of the initial companion
are read off the derivation. The pointwise form `timeBound_simulateHat_table` states the same
facts with the companion read at the query in place of its bound `M`.

## Main results

* `OracleAdv.Timed.timeBound_simulateHat_amortized` — the amortized bound: the handler simulated
  by the potential step of the Diller–Nahm category
* `OracleAdv.Timed.timeBound_simulateHat_potLe` — its instance at an affine cost, with the
  potential bounded by a predicate
* `OracleAdv.Timed.timeBound_simulateHat_potential` — the potential corollary for a potential
  `Φ : Ŝ → ℕ`
* `OracleAdv.Timed.timeBound_simulateHat_table` — the instance for a costed table: the potential
  is a pointwise bound of the cost companion of the table
* `OracleAdv.Timed.allRet_simulateHat_potLe` — the final states of such a simulation have
  potential at most `n₀ + q * g`
* `OracleAdv.Timed.timeBound_simulate_inv_of_isQueryBoundBy` — simulation time with a cost per
  query and a state invariant indexed by the query count
* `OracleAdv.Timed.stepTimeBound_delay_add_bind` — the time of a bind after a step-prefixed
  program, in the form `delay (c + x.1) (x.2.bind k)` of the derived costed forms
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv.Timed

variable {D R α : Type}

/-- **Amortized time bound of a costed simulation**, the general form. Let `Pot n s` state that
the costed state `s` has potential at most `n`, and let the handler be simulated by the potential
step `Container.Clocked.potStep C g` of the Diller–Nahm category, whose demand at a state of
potential `n` is `C n` clock ticks: every program of `impl` from a state of potential at most `n`
has time at most `C n` and returns states of potential at most `n + g`. Then an adversary of time
`T` with at most `q` queries, simulated from a state of potential at most `n₀`, has time at most
`T` plus the cost at `n₀` of the `q`-fold composite of the potential step. -/
theorem timeBound_simulateHat_amortized {D' R' S Ŝ : Type} (ε : Ŝ → S) (ι : S → Ŝ)
    (impl : Ŝ → D → ℕ × Timed D' R' (R × Ŝ)) (Pot : ℕ → Ŝ → Prop) (C : ℕ → ℕ) (g : ℕ)
    (himpl : ∀ n s d, Pot n s →
      StepTimeBound (impl s d) (C n) ∧ AllRet (fun y => Pot (n + g) y.2) (impl s d).2)
    {A : Timed D R α} {T q : ℕ} (hA : A.TimeBound T) (hq : A.erase.IsQueryBound q)
    {n₀ : ℕ} {s₀ : Ŝ} (hs₀ : Pot n₀ s₀) :
    StepTimeBound (simulateHat ε ι impl A s₀)
      (T + ((Container.Clocked.potStep C g).iter q).cost n₀) := by
  have h := timeBound_simulateHat_inv ε ι impl (fun i s => Pot (n₀ + i * g) s)
    (fun i => C (n₀ + i * g))
    (fun i s d hs => by
      refine ⟨(himpl _ s d hs).1, ?_⟩
      have h2 := (himpl _ s d hs).2
      rwa [show n₀ + i * g + g = n₀ + (i + 1) * g by ring] at h2)
    hA hq 0 s₀ (by simpa using hs₀)
  rw [Container.Clocked.iter_potStep_cost]
  simpa using h

/-- **Potential time bound of a costed simulation**, with the potential bounded by a predicate:
the amortized bound at the affine cost `a + b * n` of a step from a state of potential at most
`n`. Let `Pot n s` state that the costed state `s` has potential at most `n`; let every program of
`impl` from a state of potential at most `n` have time at most `a + b * n` and return states of
potential at most `n + g`. Then an adversary of time `T` with at most `q` queries, simulated
from a state of potential at most `n₀`, has time at most `T + q * (a + b * (n₀ + q * g))`. -/
theorem timeBound_simulateHat_potLe {D' R' S Ŝ : Type} (ε : Ŝ → S) (ι : S → Ŝ)
    (impl : Ŝ → D → ℕ × Timed D' R' (R × Ŝ)) (Pot : ℕ → Ŝ → Prop) (a b g : ℕ)
    (himpl : ∀ n s d, Pot n s →
      StepTimeBound (impl s d) (a + b * n) ∧ AllRet (fun y => Pot (n + g) y.2) (impl s d).2)
    {A : Timed D R α} {T q : ℕ} (hA : A.TimeBound T) (hq : A.erase.IsQueryBound q)
    {n₀ : ℕ} {s₀ : Ŝ} (hs₀ : Pot n₀ s₀) :
    StepTimeBound (simulateHat ε ι impl A s₀) (T + q * (a + b * (n₀ + q * g))) :=
  (timeBound_simulateHat_amortized ε ι impl Pot (fun n => a + b * n) g himpl hA hq hs₀).mono
    (Nat.add_le_add_left (Container.Clocked.iter_potStep_cost_le
      (fun _ _ h => Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _) g q n₀) T)

/-- **Potential time bound of a costed simulation.** Let `Φ` be a potential on the costed
states: every program of `impl` from a state `s` has time at most `a + b * Φ s` and returns
states `s'` with `Φ s' ≤ Φ s + g`. Then an adversary of time `T` with at most `q` queries,
simulated from `s₀`, has time at most `T + q * (a + b * (Φ s₀ + q * g))`. -/
theorem timeBound_simulateHat_potential {D' R' S Ŝ : Type} (ε : Ŝ → S) (ι : S → Ŝ)
    (impl : Ŝ → D → ℕ × Timed D' R' (R × Ŝ)) (Φ : Ŝ → ℕ) (a b g : ℕ)
    (himpl : ∀ s d, StepTimeBound (impl s d) (a + b * Φ s) ∧
      AllRet (fun y => Φ y.2 ≤ Φ s + g) (impl s d).2)
    {A : Timed D R α} {T q : ℕ} (hA : A.TimeBound T) (hq : A.erase.IsQueryBound q) (s₀ : Ŝ) :
    StepTimeBound (simulateHat ε ι impl A s₀) (T + q * (a + b * (Φ s₀ + q * g))) :=
  timeBound_simulateHat_potLe ε ι impl (fun n s => Φ s ≤ n) a b g
    (fun _ s d hs => ⟨(himpl s d).1.mono
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ hs) _),
      allRet_mono (fun y hy => by omega) (himpl s d).2⟩)
    hA hq (le_refl (Φ s₀))

/-- **Time of a simulation over a costed table.** Let `comp s : K → ℕ` be the cost companion of
the table of the costed state `s`, and let every program of `impl` answering `d` from `s` have
time at most `a + b * comp s (key d)`, the companion read at the point `key d`, and return
states whose companion exceeds that of `s` by at most `g` at every point (a table write adds
`3`, `updateCompanion_le`; a read leaves it unchanged). Then an adversary of time `T` with at
most `q` queries, simulated from a state whose companion is at most `M₀` at every point, has
time at most `T + q * (a + b * (M₀ + q * g))`. The hypotheses are the derived step cost and the
derived companion of the written table, as `derive_timed` gives them. -/
theorem timeBound_simulateHat_table {D' R' S Ŝ K : Type} (ε : Ŝ → S) (ι : S → Ŝ)
    (impl : Ŝ → D → ℕ × Timed D' R' (R × Ŝ)) (comp : Ŝ → K → ℕ) (key : D → K) (a b g : ℕ)
    (himpl : ∀ s d, StepTimeBound (impl s d) (a + b * comp s (key d)) ∧
      AllRet (fun y => ∀ x, comp y.2 x ≤ comp s x + g) (impl s d).2)
    {A : Timed D R α} {T q : ℕ} (hA : A.TimeBound T) (hq : A.erase.IsQueryBound q)
    {M₀ : ℕ} {s₀ : Ŝ} (hs₀ : ∀ x, comp s₀ x ≤ M₀) :
    StepTimeBound (simulateHat ε ι impl A s₀) (T + q * (a + b * (M₀ + q * g))) :=
  timeBound_simulateHat_potLe ε ι impl (fun M s => ∀ x, comp s x ≤ M) a b g
    (fun _ s d hs => ⟨(himpl s d).1.mono
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hs (key d))) _),
      allRet_mono (fun _ hy x => (hy x).trans (Nat.add_le_add_right (hs x) _)) (himpl s d).2⟩)
    hA hq hs₀

/-- **Time of a sequencing after a step-prefixed program**, in the form in which
`derive_timed` writes a bind after a call: the costs `c` and `x.1` in front of the tree `x.2`
followed by `k`. With `x` of time `m` and every `k a` of time `n`, it has time `c + m + n`. -/
theorem stepTimeBound_delay_add_bind {β : Type} {c m n : ℕ} {x : ℕ × Timed D R α}
    {k : α → ℕ × Timed D R β} (hx : StepTimeBound x m) (hk : ∀ a, StepTimeBound (k a) n) :
    StepTimeBound (delay (c + x.1) (x.2.bind k)) (c + m + n) :=
  (stepTimeBound_delay (timeBound_bind hx.2 hk)).mono (by have := hx.1; omega)

/-- **Final states of a simulation under a potential.** When every program of `impl` from a
state of potential at most `n` returns states of potential at most `n + g`, and the potential
bound is monotone, a simulation of an adversary with at most `q` queries from a state of
potential at most `n₀` returns states of potential at most `n₀ + q * g`. -/
theorem allRet_simulateHat_potLe {D' R' S Ŝ : Type} (ε : Ŝ → S) (ι : S → Ŝ)
    (impl : Ŝ → D → ℕ × Timed D' R' (R × Ŝ)) (Pot : ℕ → Ŝ → Prop) (g : ℕ)
    (himpl : ∀ n s d, Pot n s → AllRet (fun y => Pot (n + g) y.2) (impl s d).2)
    (hmono : ∀ n m s, n ≤ m → Pot n s → Pot m s)
    {A : Timed D R α} {q : ℕ} (hq : A.erase.IsQueryBound q) {n₀ : ℕ} {s₀ : Ŝ}
    (hs₀ : Pot n₀ s₀) :
    AllRet (fun y => Pot (n₀ + q * g) y.2) (simulateHat ε ι impl A s₀).2 := by
  have h := allRet_simulateHat_inv ε ι impl (fun i s => Pot (n₀ + i * g) s)
    (fun i s d hs => by
      have h2 := himpl _ s d hs
      rwa [show n₀ + i * g + g = n₀ + (i + 1) * g by ring] at h2)
    (fun i s hs => hmono _ _ s (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _) hs)
    hq 0 s₀ (by simpa using hs₀)
  simpa using h

/-- **Simulation time with a cost per query and a state invariant.** Let `Inv i` hold of the
states reached after `i` queries: a program of `impl` answering `d` from a state with `Inv i` has
time at most `t d + g i` and returns states with `Inv (i + 1)`. Then an adversary of time `T` with
at most `q` queries, whose query costs `t d` sum to at most `n` on every path, simulated from a
state with `Inv i`, has time at most `T + n + ∑_{j < q} g (i + j)`. A handler that reads a log
growing by one entry per query has such a time, with `g` linear. -/
theorem timeBound_simulate_inv_of_isQueryBoundBy {D' R' S : Type}
    (impl : S → D → ℕ × Timed D' R' (R × S)) (t : D → ℕ) (g : ℕ → ℕ) (Inv : ℕ → S → Prop)
    (himpl : ∀ i s d, Inv i s →
      StepTimeBound (impl s d) (t d + g i) ∧ AllRet (fun y => Inv (i + 1) y.2) (impl s d).2)
    {A : Timed D R α} {T n q : ℕ} (hA : A.TimeBound T)
    (hn : A.erase.IsQueryBoundBy t n) (hq : A.erase.IsQueryBound q) (i : ℕ) (s : S)
    (hs : Inv i s) :
    StepTimeBound (simulate impl A s) (T + n + ∑ j ∈ Finset.range q, g (i + j)) := by
  induction A generalizing T n q i s with
  | ret a => exact ⟨Nat.zero_le _, trivial⟩
  | rand p c k ih =>
    have h1 := hA.1
    simp only [simulate, stepTimeBound_zero, timeBound_rand_iff]
    refine ⟨by omega, fun b => ?_⟩
    have h2 := (hA.2 b).1
    exact (stepTimeBound_delay (c := c b) (ih b (hA.2 b).2 (hn b) (hq b) i s hs)).mono (by omega)
  | query d c k ih =>
    cases q with
    | zero => exact (hq : False).elim
    | succ q =>
      obtain ⟨hd, hnk⟩ := hn
      have hsum : ∑ j ∈ Finset.range (q + 1), g (i + j) =
          ∑ j ∈ Finset.range q, g (i + 1 + j) + g i := by
        rw [Finset.sum_range_succ']
        simp only [Nat.add_zero]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by rw [Nat.add_assoc, Nat.add_comm 1 j]
      rw [hsum]
      have hk : ∀ x : R × S, Inv (i + 1) x.2 →
          StepTimeBound (delay (c x.1) (simulate impl (k x.1) x.2))
            (T - 1 + (n - t d) + ∑ j ∈ Finset.range q, g (i + 1 + j)) := fun x hx =>
        (stepTimeBound_delay (ih x.1 (hA.2 x.1).2 (hnk x.1) (hq x.1) (i + 1) x.2 hx)).mono
          (by have := (hA.2 x.1).1; omega)
      have hi := himpl i s d hs
      have h := stepTimeBound_delay (c := (impl s d).1)
        (timeBound_bind_of_allRet hi.1.2 hi.2 hk)
      exact h.mono (by have := hi.1.1; have := hA.1; omega)

end CatCrypt.Crypto.OracleAdv.Timed
