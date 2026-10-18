/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleSimulation

/-!
# Oracle adversaries with step costs

`OracleAdv.Timed D R α` is the adaptive oracle adversary of `OracleAdv D R α` in which
every continuation carries a step cost: a node `rand p c k` or `query d c k` continues
from the sample or answer `x` with the node `k x`, and `c x` is the cost of computing
`k x` from `x`. Erasing the step costs gives the underlying adversary (`Timed.erase`).
The time bound `Timed.TimeBound A T` states that on every path of `A` the number of
`rand` and `query` nodes plus the step costs along the path is at most `T`.

A pair `(c, A) : ℕ × Timed D R α` is the tree `A` preceded by `c` units of computation;
sequencing and simulation produce such pairs, because the step cost of a continuation
reached at a `ret` leaf of the first part has no edge of the result to sit on. Its time
bound is `Timed.StepTimeBound`.

## Cost model

The registered primitive costs are:

* one unit per `rand` node, the sample from the probability mass function at the node
  included (`PMF β` is first-order data);
* one unit per `query` node;
* each step cost as written in the instrumented program: the cost of the local
  computation between two nodes, stated by the program's author.

## Main definitions

* `OracleAdv.Timed D R α` — adaptive adversary with a step cost on every continuation
* `OracleAdv.Timed.erase` — the underlying `OracleAdv`; `OracleAdv.Timed.ofAdv` — an
  `OracleAdv` with zero step costs
* `OracleAdv.Timed.TimeBound A T` — nodes plus step costs on every path of `A` at most `T`
* `OracleAdv.Timed.StepTimeBound x T` — the time bound of a tree preceded by a step cost
* `OracleAdv.Timed.bind`, `OracleAdv.Timed.simulate`, `OracleAdv.Timed.mapQuery` — the
  costed forms of `OracleAdv.bind`, `OracleAdv.simulate`, `OracleAdv.mapQuery`

## Main results

* `OracleAdv.Timed.erase_bind`, `erase_simulate`, `erase_mapQuery` — erasure commutes with
  sequencing, simulation and renaming
* `OracleAdv.Timed.timeBound_bind` — times add under sequencing
* `OracleAdv.Timed.timeBound_simulate` — a simulated adversary of time `T` with `q`
  queries, each answered by a program of time `t`, has time at most `T + q * t`
* `OracleAdv.Timed.timeBound_mapQuery` — renaming at cost `t` per query adds `q * t`
* `OracleAdv.Timed.isQueryBound_of_timeBound` — a time bound is a query bound
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

namespace OracleAdv

/-- An adaptive oracle adversary with a step cost on every continuation: return a value
(`ret`), sample `x` from `p` and continue with `k x` (`rand`), or query the oracle at `d`
and continue with `k x` on the answer `x` (`query`). The step cost `c x` is the cost of
computing the node `k x` from `x`. -/
inductive Timed (D R α : Type) : Type 1 where
  /-- Return the output. -/
  | ret : α → Timed D R α
  /-- Sample from `p` and continue, at step cost `c`, with `k`. -/
  | rand {β : Type} (p : PMF β) (c : β → ℕ) (k : β → Timed D R α) : Timed D R α
  /-- Query the oracle at `d` and continue, at step cost `c`, with `k`. -/
  | query (d : D) (c : R → ℕ) (k : R → Timed D R α) : Timed D R α

namespace Timed

variable {D R D' R' α β : Type}

/-- The adversary `A` with its step costs erased. -/
def erase : Timed D R α → OracleAdv D R α
  | ret a => .ret a
  | rand p _ k => .rand p fun b => erase (k b)
  | query d _ k => .query d fun r => erase (k r)

/-- The adversary `A` with zero step costs. -/
def ofAdv : OracleAdv D R α → Timed D R α
  | .ret a => ret a
  | .rand p k => rand p (fun _ => 0) fun b => ofAdv (k b)
  | .query d k => query d (fun _ => 0) fun r => ofAdv (k r)

@[simp] theorem erase_ofAdv (A : OracleAdv D R α) : (ofAdv A).erase = A := by
  induction A with
  | ret a => rfl
  | rand p k ih => simp only [ofAdv, erase, ih]
  | query d k ih => simp only [ofAdv, erase, ih]

/-- `TimeBound A T`: on every path of `A`, the number of `rand` and `query` nodes plus
the step costs of the continuations taken is at most `T`. A node costs one unit, and its
continuation must fit its step cost and its subtree in the remaining time. -/
def TimeBound : Timed D R α → ℕ → Prop
  | ret _, _ => True
  | rand _ c k, n => 1 ≤ n ∧ ∀ b, c b ≤ n - 1 ∧ TimeBound (k b) (n - 1 - c b)
  | query _ c k, n => 1 ≤ n ∧ ∀ r, c r ≤ n - 1 ∧ TimeBound (k r) (n - 1 - c r)

/-- `StepTimeBound (c, A) T`: the step cost `c` followed by `A` takes time at most `T`. -/
def StepTimeBound (x : ℕ × Timed D R α) (n : ℕ) : Prop :=
  x.1 ≤ n ∧ x.2.TimeBound (n - x.1)

theorem timeBound_rand_iff {γ : Type} (p : PMF γ) (c : γ → ℕ) (k : γ → Timed D R α)
    (n : ℕ) : (rand p c k).TimeBound n ↔ 1 ≤ n ∧ ∀ b, StepTimeBound (c b, k b) (n - 1) :=
  Iff.rfl

theorem timeBound_query_iff (d : D) (c : R → ℕ) (k : R → Timed D R α) (n : ℕ) :
    (query d c k).TimeBound n ↔ 1 ≤ n ∧ ∀ r, StepTimeBound (c r, k r) (n - 1) :=
  Iff.rfl

/-- The step cost `c` added in front of a step-prefixed tree. -/
def delay (c : ℕ) (x : ℕ × Timed D R α) : ℕ × Timed D R α := (c + x.1, x.2)

theorem TimeBound.mono {A : Timed D R α} {m n : ℕ} (h : A.TimeBound m) (hmn : m ≤ n) :
    A.TimeBound n := by
  induction A generalizing m n with
  | ret a => trivial
  | rand p c k ih =>
    exact ⟨h.1.trans hmn, fun b => ⟨(h.2 b).1.trans (by omega), ih b (h.2 b).2 (by omega)⟩⟩
  | query d c k ih =>
    exact ⟨h.1.trans hmn, fun r => ⟨(h.2 r).1.trans (by omega), ih r (h.2 r).2 (by omega)⟩⟩

theorem StepTimeBound.mono {x : ℕ × Timed D R α} {m n : ℕ} (h : StepTimeBound x m)
    (hmn : m ≤ n) : StepTimeBound x n :=
  ⟨h.1.trans hmn, h.2.mono (Nat.sub_le_sub_right hmn _)⟩

theorem stepTimeBound_zero {A : Timed D R α} {n : ℕ} :
    StepTimeBound (0, A) n ↔ A.TimeBound n := by
  simp [StepTimeBound]

theorem stepTimeBound_delay {c : ℕ} {x : ℕ × Timed D R α} {n : ℕ}
    (h : StepTimeBound x n) : StepTimeBound (delay c x) (c + n) := by
  refine ⟨Nat.add_le_add_left h.1 c, ?_⟩
  have e : c + n - (c + x.1) = n - x.1 := by omega
  simpa only [delay, e] using h.2

/-- A time bound is a query bound: every query node costs at least one unit. -/
theorem isQueryBound_of_timeBound {A : Timed D R α} {n : ℕ} (h : A.TimeBound n) :
    A.erase.IsQueryBound n := by
  induction A generalizing n with
  | ret a => trivial
  | rand p c k ih => exact fun b => (ih b (h.2 b).2).mono (by omega)
  | query d c k ih =>
    cases n with
    | zero => exact absurd h.1 (by omega)
    | succ n => exact fun r => (ih r (h.2 r).2).mono (by omega)

/-! ## Sequencing -/

/-- Run `A`, then continue with `f` on its output; the step cost of `f a` is added to the
edge into the leaf `ret a`, or precedes the result when `A` is `ret a`. -/
def bind : Timed D R α → (α → ℕ × Timed D R β) → ℕ × Timed D R β
  | ret a, f => f a
  | rand p c k, f => (0, rand p (fun b => c b + (bind (k b) f).1) fun b => (bind (k b) f).2)
  | query d c k, f => (0, query d (fun r => c r + (bind (k r) f).1) fun r => (bind (k r) f).2)

/-- Erasure commutes with sequencing. -/
theorem erase_bind (A : Timed D R α) (f : α → ℕ × Timed D R β) :
    (A.bind f).2.erase = A.erase.bind fun a => (f a).2.erase := by
  induction A with
  | ret a => rfl
  | rand p c k ih => simp only [bind, erase, OracleAdv.bind, ih]
  | query d c k ih => simp only [bind, erase, OracleAdv.bind, ih]

/-- Times add under sequencing (the time analogue of `OracleAdv.isQueryBound_bind`). -/
theorem timeBound_bind {A : Timed D R α} {f : α → ℕ × Timed D R β} {m n : ℕ}
    (hA : A.TimeBound m) (hf : ∀ a, StepTimeBound (f a) n) :
    StepTimeBound (A.bind f) (m + n) := by
  induction A generalizing m with
  | ret a => exact (hf a).mono (Nat.le_add_left n m)
  | rand p c k ih =>
    have h1 := hA.1
    simp only [bind, stepTimeBound_zero, timeBound_rand_iff]
    refine ⟨by omega, fun b => ?_⟩
    have h2 := (hA.2 b).1
    exact (stepTimeBound_delay (c := c b) (ih b (hA.2 b).2)).mono (by omega)
  | query d c k ih =>
    have h1 := hA.1
    simp only [bind, stepTimeBound_zero, timeBound_query_iff]
    refine ⟨by omega, fun r => ?_⟩
    have h2 := (hA.2 r).1
    exact (stepTimeBound_delay (c := c r) (ih r (hA.2 r).2)).mono (by omega)

/-! ## Simulation -/

/-- The adversary `A` with every query `d` answered by the step-prefixed program
`impl s d` from the current simulator state `s` (the costed form of
`OracleAdv.simulate`). -/
def simulate {S : Type} (impl : S → D → ℕ × Timed D' R' (R × S)) :
    Timed D R α → S → ℕ × Timed D' R' (α × S)
  | ret a, s => (0, ret (a, s))
  | rand p c k, s =>
    (0, rand p (fun b => c b + (simulate impl (k b) s).1) fun b => (simulate impl (k b) s).2)
  | query d c k, s => delay (impl s d).1
      ((impl s d).2.bind fun x => delay (c x.1) (simulate impl (k x.1) x.2))

/-- Erasure commutes with simulation. -/
theorem erase_simulate {S : Type} (impl : S → D → ℕ × Timed D' R' (R × S))
    (A : Timed D R α) (s : S) :
    (simulate impl A s).2.erase =
      OracleAdv.simulate (fun s d => (impl s d).2.erase) A.erase s := by
  induction A generalizing s with
  | ret a => rfl
  | rand p c k ih => simp only [simulate, erase, OracleAdv.simulate, ih]
  | query d c k ih => simp only [simulate, delay, erase, OracleAdv.simulate, erase_bind, ih]

/-- **Simulation time.** If `A` has time `T` and asks at most `q` queries, and every
program of `impl` has time at most `t`, then the simulated adversary has time at most
`T + q * t` (the time analogue of `OracleAdv.isQueryBound_simulate`). -/
theorem timeBound_simulate {S : Type} (impl : S → D → ℕ × Timed D' R' (R × S)) {t : ℕ}
    (himpl : ∀ s d, StepTimeBound (impl s d) t) {A : Timed D R α} {T q : ℕ}
    (hA : A.TimeBound T) (hq : A.erase.IsQueryBound q) (s : S) :
    StepTimeBound (simulate impl A s) (T + q * t) := by
  induction A generalizing T q s with
  | ret a => exact ⟨Nat.zero_le _, trivial⟩
  | rand p c k ih =>
    have h1 := hA.1
    simp only [simulate, stepTimeBound_zero, timeBound_rand_iff]
    refine ⟨by omega, fun b => ?_⟩
    have h2 := (hA.2 b).1
    exact (stepTimeBound_delay (c := c b) (ih b (hA.2 b).2 (hq b) s)).mono (by omega)
  | query d c k ih =>
    cases q with
    | zero => exact (hq : False).elim
    | succ q =>
      have hk : ∀ x : R × S, StepTimeBound (delay (c x.1) (simulate impl (k x.1) x.2))
          (T - 1 + q * t) := fun x =>
        (stepTimeBound_delay (ih x.1 (hA.2 x.1).2 (hq x.1) x.2)).mono
          (by have := (hA.2 x.1).1; omega)
      have hi := himpl s d
      have h := stepTimeBound_delay (c := (impl s d).1) (timeBound_bind hi.2 hk)
      exact h.mono (by have := hi.1; have := hA.1; rw [Nat.add_mul, Nat.one_mul]; omega)

/-! ## Renaming queries -/

/-- The adversary `A` with each query `d` asked as `ren d`, computing `ren d` at cost
`t d`, charged on the continuation of the renamed query. -/
def mapQuery {D₀ : Type} (ren : D → D₀) (t : D → ℕ) : Timed D R α → Timed D₀ R α
  | ret a => ret a
  | rand p c k => rand p c fun b => mapQuery ren t (k b)
  | query d c k => query (ren d) (fun r => c r + t d) fun r => mapQuery ren t (k r)

/-- Erasure commutes with renaming. -/
theorem erase_mapQuery {D₀ : Type} (ren : D → D₀) (t : D → ℕ) (A : Timed D R α) :
    (mapQuery ren t A).erase = OracleAdv.mapQuery ren A.erase := by
  induction A with
  | ret a => rfl
  | rand p c k ih => simp only [mapQuery, erase, OracleAdv.mapQuery, ih]
  | query d c k ih => simp only [mapQuery, erase, OracleAdv.mapQuery, ih]

/-- Renaming at cost at most `t₀` per query adds at most `q * t₀` to the time of an
adversary with at most `q` queries. -/
theorem timeBound_mapQuery {D₀ : Type} (ren : D → D₀) (t : D → ℕ) {t₀ : ℕ}
    (ht : ∀ d, t d ≤ t₀) {A : Timed D R α} {T q : ℕ} (hA : A.TimeBound T)
    (hq : A.erase.IsQueryBound q) : (mapQuery ren t A).TimeBound (T + q * t₀) := by
  induction A generalizing T q with
  | ret a => trivial
  | rand p c k ih =>
    exact ⟨by have := hA.1; omega, fun b =>
      ⟨by have := hA.1; have := (hA.2 b).1; omega,
        (ih b (hA.2 b).2 (hq b)).mono (by have := hA.1; have := (hA.2 b).1; omega)⟩⟩
  | query d c k ih =>
    cases q with
    | zero => exact (hq : False).elim
    | succ q =>
      have hd := ht d
      have h1 := hA.1
      have hmul : (q + 1) * t₀ = q * t₀ + t₀ := by rw [Nat.add_mul, Nat.one_mul]
      simp only [mapQuery, timeBound_query_iff, StepTimeBound]
      refine ⟨by omega, fun r => ?_⟩
      have h2 := (hA.2 r).1
      exact ⟨by omega, (ih r (hA.2 r).2 (hq r)).mono (by omega)⟩

end Timed

end OracleAdv

end CatCrypt.Crypto
