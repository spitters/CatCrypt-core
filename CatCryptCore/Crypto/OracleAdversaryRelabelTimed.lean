/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleAdversaryTimed

/-!
# Relabelling the queries and answers of an oracle adversary, with step costs

`OracleAdv.mapQueryAnswer g h A` is the adversary `A` with each query `d` asked as `g d` and
each answer `r'` read as `h r'`. Its costed form `OracleAdv.Timed.mapQueryAnswer g t h u A`
charges `t d` for computing `g d` and `u r'` for computing `h r'` on the continuation of the
relabelled query. Renaming the queries only (`OracleAdv.mapQuery`) is the case `h = id`.

## Cost model

The registered costs of `CatCryptCore.Crypto.OracleAdversaryTimed`: one unit per `rand` and
per `query` node. The costs `t` and `u` of the two relabellings are parameters.

## Main definitions

* `OracleAdv.mapQueryAnswer g h A` — `A` with queries relabelled by `g`, answers by `h`
* `OracleAdv.Timed.mapQueryAnswer g t h u A` — its costed form
* `OracleAdv.mapQueryAnswer.timed` — the costed form registered for `derive_timed`

## Main results

* `OracleAdv.run_mapQueryAnswer` — running the relabelled adversary is running `A` against
  the relabelled oracle
* `OracleAdv.isQueryBound_mapQueryAnswer` — relabelling keeps the query bound
* `OracleAdv.Timed.erase_mapQueryAnswer` — erasure commutes with relabelling
* `OracleAdv.mapQueryAnswer.timed`, `OracleAdv.mapQueryAnswer.erase_timed`,
  `OracleAdv.mapQueryAnswer.timeBound_timed` — the costed form in the binder convention of
  `derive_timed`, its erasure and its time
* `OracleAdv.Timed.timeBound_mapQueryAnswer` — relabelling at cost at most `t₀ + u₀` per
  query adds at most `q * (t₀ + u₀)` to the time of an adversary with at most `q` queries
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

namespace OracleAdv

variable {D D' R R' α : Type}

/-- The adversary `A` with each query `d` asked as `g d` and each answer `r'` read as
`h r'`. -/
def mapQueryAnswer (g : D → D') (h : R' → R) : OracleAdv D R α → OracleAdv D' R' α
  | .ret a => .ret a
  | .rand p k => .rand p fun b => mapQueryAnswer g h (k b)
  | .query d k => .query (g d) fun r => mapQueryAnswer g h (k (h r))

/-- Running the relabelled adversary against `O` is running `A` against the oracle that asks
`g d` of `O` and reads the answer through `h`. -/
theorem run_mapQueryAnswer {S : Type} (O : S → D' → PMF (R' × S)) (g : D → D') (h : R' → R)
    (A : OracleAdv D R α) (s : S) :
    run O (mapQueryAnswer g h A) s =
      run (fun s d => (O s (g d)).map fun x => (h x.1, x.2)) A s := by
  induction A generalizing s with
  | ret a => rfl
  | rand p k ih => simp only [mapQueryAnswer, run_rand, ih]
  | query d k ih => simp only [mapQueryAnswer, run_query, PMF.bind_map, Function.comp_def, ih]

/-- Relabelling keeps the query bound. -/
theorem isQueryBound_mapQueryAnswer (g : D → D') (h : R' → R) {A : OracleAdv D R α} {q : ℕ}
    (hA : A.IsQueryBound q) : (mapQueryAnswer g h A).IsQueryBound q := by
  induction A generalizing q with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (hA b)
  | query d k ih =>
    cases q with
    | zero => exact hA.elim
    | succ q => exact fun r => ih (h r) (hA (h r))

namespace Timed

/-- The costed adversary `A` with each query `d` asked as `g d`, at cost `t d`, and each
answer `r'` read as `h r'`, at cost `u r'`; both costs are charged on the continuation of the
relabelled query. -/
def mapQueryAnswer (g : D → D') (t : D → ℕ) (h : R' → R) (u : R' → ℕ) :
    Timed D R α → Timed D' R' α
  | ret a => ret a
  | rand p c k => rand p c fun b => mapQueryAnswer g t h u (k b)
  | query d c k => query (g d) (fun r => c (h r) + (t d + u r)) fun r =>
      mapQueryAnswer g t h u (k (h r))

/-- Erasure commutes with relabelling. -/
theorem erase_mapQueryAnswer (g : D → D') (t : D → ℕ) (h : R' → R) (u : R' → ℕ)
    (A : Timed D R α) :
    (mapQueryAnswer g t h u A).erase = OracleAdv.mapQueryAnswer g h A.erase := by
  induction A with
  | ret a => rfl
  | rand p c k ih => simp only [mapQueryAnswer, erase, OracleAdv.mapQueryAnswer, ih]
  | query d c k ih => simp only [mapQueryAnswer, erase, OracleAdv.mapQueryAnswer, ih]

/-- Relabelling at cost at most `t₀ + u₀` per query adds at most `q * (t₀ + u₀)` to the
time of an adversary with at most `q` queries. -/
theorem timeBound_mapQueryAnswer (g : D → D') (t : D → ℕ) (h : R' → R) (u : R' → ℕ)
    {t₀ u₀ : ℕ} (ht : ∀ d, t d ≤ t₀) (hu : ∀ r, u r ≤ u₀) {A : Timed D R α} {T q : ℕ}
    (hA : A.TimeBound T) (hq : A.erase.IsQueryBound q) :
    (mapQueryAnswer g t h u A).TimeBound (T + q * (t₀ + u₀)) := by
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
      have hmul : (q + 1) * (t₀ + u₀) = q * (t₀ + u₀) + (t₀ + u₀) := by
        rw [Nat.add_mul, Nat.one_mul]
      simp only [mapQueryAnswer, timeBound_query_iff, StepTimeBound]
      refine ⟨by omega, fun r => ?_⟩
      have h2 := (hA.2 (h r)).1
      have hr := hu r
      exact ⟨by omega, (ih (h r) (hA.2 (h r)).2 (hq (h r))).mono (by omega)⟩

end Timed

/-- The costed form of `mapQueryAnswer` in the binder convention of `derive_timed`: the
relabellings `g` and `h` come with their cost companions `gCost` and `hCost`, and relabelling
a query `d` costs one unit plus `gCost d`, an answer `r` one unit plus `hCost r`. -/
def mapQueryAnswer.timed (g : D → D') (gCost : D → ℕ) (h : R' → R) (hCost : R' → ℕ)
    (W : Timed D R α) : ℕ × Timed D' R' α :=
  (0, W.mapQueryAnswer g (fun d => 1 + gCost d) h fun r => 1 + hCost r)

/-- Erasing the step costs of `mapQueryAnswer.timed` gives the relabelling of the erased
adversary. -/
theorem mapQueryAnswer.erase_timed (g : D → D') (gCost : D → ℕ) (h : R' → R)
    (hCost : R' → ℕ) (W : Timed D R α) :
    (mapQueryAnswer.timed g gCost h hCost W).2.erase = W.erase.mapQueryAnswer g h :=
  Timed.erase_mapQueryAnswer _ _ _ _ W

/-- Relabellings of cost at most `a` (queries) and `b` (answers) add at most
`q * ((1 + a) + (1 + b))` to the time of an adversary with at most `q` queries. -/
theorem mapQueryAnswer.timeBound_timed (g : D → D') {gCost : D → ℕ} (h : R' → R)
    {hCost : R' → ℕ} {a b : ℕ} (hg : ∀ d, gCost d ≤ a) (hh : ∀ r, hCost r ≤ b)
    {W : Timed D R α} {T q : ℕ} (hW : W.TimeBound T) (hq : W.erase.IsQueryBound q) :
    Timed.StepTimeBound (mapQueryAnswer.timed g gCost h hCost W)
      (T + q * ((1 + a) + (1 + b))) :=
  Timed.stepTimeBound_zero.2 <| Timed.timeBound_mapQueryAnswer g _ h _
    (fun d => Nat.add_le_add_left (hg d) 1) (fun r => Nat.add_le_add_left (hh r) 1) hW hq

end OracleAdv

end CatCrypt.Crypto
