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

## Main results

* `OracleAdv.Timed.erase_mapQueryAnswer` — erasure commutes with relabelling
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

end OracleAdv

end CatCrypt.Crypto
