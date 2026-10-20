/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Prob.BirthdayBound
public import CatCryptCore.Crypto.OracleCollision
public import CatCryptCore.Consensus.PoSNSB.Prob.Slots

/-!
# PoS-NSB: collisions of a random oracle queried adaptively

The hash function of the PoS-NSB model is modelled as a random oracle: a function
`f : D → R` drawn uniformly from all functions from a finite domain `D` to a finite range `R`
with `N = |R|` elements. An adaptive oracle algorithm is a `Querier`: the next query as a
function of the transcript of the previous queries and their answers. Its `k`-th query is
`query next f k`.

## Main results

* `transcript_congr`: the first `k` queries depend only on the values of `f` at those queries.
* `prob_ROCollision_le` (**birthday bound**): the probability that two distinct points among
  the first `q` queries have the same answer is at most `q (q - 1) / 2 / N`, the instance of
  `CatCrypt.Crypto.OracleAdv.prob_evalOn_collision_le` at the oracle adversary
  `OracleAdv.ofQuerier next [] q`.

The uniform key of the keyed family `HashScheme.randomFun D R` of
`CatCryptCore/Crypto/Assumptions/CR.lean` is a draw from `uniformFun D R`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open scoped ENNReal

variable {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

/-- An adaptive oracle algorithm: the next query, as a function of the list of the previous
queries and their answers. -/
abbrev Querier (D R : Type) := List (D × R) → D

/-- The transcript of the first `k` queries of `next` to `f`. -/
def transcript (next : Querier D R) (f : D → R) : ℕ → List (D × R)
  | 0 => []
  | k + 1 => transcript next f k ++
      [(next (transcript next f k), f (next (transcript next f k)))]

/-- The `k`-th query of `next` to `f` (counting from `0`). -/
def query (next : Querier D R) (f : D → R) (k : ℕ) : D := next (transcript next f k)

/-- The first `q` queries. -/
def queries (next : Querier D R) (f : D → R) (q : ℕ) : List D :=
  (List.range q).map (query next f)

theorem transcript_eq (next : Querier D R) (f : D → R) (k : ℕ) :
    transcript next f k = (List.range k).map fun j => (query next f j, f (query next f j)) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [transcript, List.range_succ, List.map_append, ← ih]; rfl

/-- The first `k` queries are determined by the values of `f` at those queries. -/
theorem transcript_congr (next : Querier D R) (f g : D → R) (k : ℕ)
    (h : ∀ j < k, g (query next f j) = f (query next f j)) :
    transcript next g k = transcript next f k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih := ih fun j hj => h j (by omega)
    simp only [transcript, ih]
    have := h k (by omega)
    simp only [query] at this
    rw [this]

/-- The first `k` queries and their answers are unchanged when `f` is changed at a point that
is not among them. -/
theorem transcript_update (next : Querier D R) (f : D → R) (k : ℕ) (x : D) (y : R)
    (hx : ∀ j < k, query next f j ≠ x) :
    transcript next (Function.update f x y) k = transcript next f k :=
  transcript_congr next f _ k fun j hj => Function.update_of_ne (hx j hj) _ _

/-- The first `k + 1` queries are unchanged when `f` is changed at a point that is not among
the first `k` queries. -/
theorem query_update (next : Querier D R) (f : D → R) (k : ℕ) (x : D) (y : R)
    (hx : ∀ j < k, query next f j ≠ x) :
    ∀ j ≤ k, query next (Function.update f x y) j = query next f j := by
  intro j hj
  simp only [query]
  rw [transcript_update next f j x y fun i hi => hx i (by omega)]

/-- Two distinct points among the first `q` queries have the same answer. -/
def ROCollision (next : Querier D R) (q : ℕ) (f : D → R) : Prop :=
  ∃ a < q, ∃ b < q, query next f a ≠ query next f b ∧ f (query next f a) = f (query next f b)

/-! ## The birthday bound -/

/-- The uniform distribution on the functions from `D` to `R`. -/
noncomputable def uniformFun (D R : Type) [Fintype D] [DecidableEq D] [Fintype R] [Nonempty R] :
    PMF (D → R) :=
  PMF.uniformOfFintype (D → R)

/-- **Birthday bound for an adaptive querier (part 2).** For a uniformly random function
`f : D → R` and any adaptive querier `next`, the probability that two distinct points among the
first `q` queries have the same value is at most `q (q - 1) / 2 / |R|`. -/
theorem prob_ROCollision_le [Nonempty R] (next : Querier D R) (q : ℕ) :
    (uniformFun D R).toOuterMeasure {f | ROCollision next q f} ≤
      ((q * (q - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card R := by
  have hev : ∀ (f : D → R) (k n : ℕ), (CatCrypt.Crypto.OracleAdv.evalOn f
      (CatCrypt.Crypto.OracleAdv.ofQuerier next (transcript next f k) n)).2 =
        (List.range' k n).map (query next f) := by
    intro f k n
    induction n generalizing k with
    | zero => rfl
    | succ n ih =>
      simp only [CatCrypt.Crypto.OracleAdv.ofQuerier, CatCrypt.Crypto.OracleAdv.evalOn_query,
        List.range'_succ, List.map_cons]
      exact congrArg _ (ih (k + 1))
  have hset : {f | ROCollision next q f} = {f | CatCrypt.Crypto.OracleAdv.QueryCollision f
      (CatCrypt.Crypto.OracleAdv.evalOn f (CatCrypt.Crypto.OracleAdv.ofQuerier next [] q)).2} := by
    ext f
    have h := hev f 0 q
    simp only [transcript] at h
    simp only [Set.mem_ofPred_eq, h, ROCollision, CatCrypt.Crypto.OracleAdv.QueryCollision,
      List.mem_map, List.mem_range'_1]
    grind
  rw [hset, uniformFun]
  exact CatCrypt.Crypto.OracleAdv.prob_evalOn_collision_le _
    (CatCrypt.Crypto.OracleAdv.ofQuerier_noRand _ _ _) q
    (CatCrypt.Crypto.OracleAdv.ofQuerier_isQueryBound _ _ _)

end CatCryptCore.Consensus.PoSNSB
