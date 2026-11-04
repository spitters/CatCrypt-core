/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleProfile

/-!
# The caching handler of an oracle adversary

`OracleAdv.cacheImpl` is the simulator program that answers a query from a cache, a list of
pairs (query, answer): a recorded query is answered from the cache without a call, and a new
query is forwarded once to the inner oracle and its answer recorded. Running an adversary through
it, `simulate cacheImpl A c`, makes one inner call for each distinct query of `A` outside the
initial cache.

The laws are stated on the query profile (`OracleAdv.profile`): each path of the cached run has as
its multiset of inner calls the set of distinct queries of a path of `A` with the same result,
less the keys of the initial cache. The cost of a path is therefore the sum of the cost over its
distinct new keys, and the number of inner calls is the growth of the cache (amortized form).

## Main definitions

* `OracleAdv.cacheKeys c` — the set of queries recorded in the cache `c`;
* `OracleAdv.cacheImpl` — the caching handler;
* `OracleAdv.IsDistinctQueryBoundBy cost A K n` — on each path of `A` the cost of the distinct
  queries outside `K` is at most `n`.

## Main results

* `mem_profile_simulate_cacheImpl` — the inner calls of a path are the distinct new queries of a
  path of `A`, and the final cache keys are the initial ones together with the queries of `A`;
* `charge_profile_simulate_cacheImpl`, `card_profile_simulate_cacheImpl_le` — the charge of a
  path is the charge of its distinct new keys, and the number of inner calls is at most the
  number of distinct queries and at most the number of queries;
* `card_profile_simulate_cacheImpl_eq_growth` — the number of inner calls is the growth of the
  cache;
* `isQueryBoundBy_simulate_cacheImpl`, `isQueryBound_simulate_cacheImpl` — a bound on the
  distinct queries of `A` is a bound on the inner calls; `isQueryBound_simulate_cacheImpl_of`
  — the query bound of `A` transfers.

Search words: cache, memoization, distinct queries, amortized query bound, lazy table.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv

variable {D R α : Type} [DecidableEq D]

/-- The set of queries recorded in the cache `c`. -/
def cacheKeys (c : List (D × R)) : Finset D := (c.map Prod.fst).toFinset

/-- Unfolding lemma of `cacheKeys` at a recorded pair. -/
@[simp] theorem cacheKeys_cons (d : D) (r : R) (c : List (D × R)) :
    cacheKeys ((d, r) :: c) = insert d (cacheKeys c) := by
  simp [cacheKeys]

/-- A query is outside the cache exactly when the lookup fails. -/
theorem lookup_eq_none_iff_not_mem_cacheKeys {c : List (D × R)} {d : D} :
    c.lookup d = none ↔ d ∉ cacheKeys c := by
  simp only [cacheKeys, List.lookup_eq_none_iff, List.mem_toFinset, List.mem_map]
  grind

/-- The caching handler: answer a recorded query from the cache `c`, and forward a new query
once, recording its answer. -/
def cacheImpl (c : List (D × R)) (d : D) : OracleAdv D R (R × List (D × R)) :=
  match c.lookup d with
  | some r => ret (r, c)
  | none => query d fun r => ret (r, (d, r) :: c)

/-- The exact path law of the caching handler: a path of `simulate cacheImpl A c` with inner
calls `x.1` and final cache `x.2.2` comes from a path of `A` with queries `q` and the same result,
the inner calls are the distinct queries of `q` outside the cache `c`, each once, and the final
cache records the keys of `c` and the queries of `q`. -/
theorem mem_profile_simulate_cacheImpl {A : OracleAdv D R α} {c : List (D × R)}
    {x : Multiset D × (α × List (D × R))} (hx : x ∈ profile (simulate cacheImpl A c)) :
    ∃ q, (q, x.2.1) ∈ profile A ∧ x.1 = (q.toFinset \ cacheKeys c).val ∧
      cacheKeys x.2.2 = cacheKeys c ∪ q.toFinset := by
  induction A generalizing c x with
  | ret a =>
    obtain rfl := hx
    exact ⟨0, rfl, by simp, by simp⟩
  | rand p k ih =>
    obtain ⟨b, hb⟩ := mem_profile_rand.1 hx
    obtain ⟨q, hq, h₁, h₂⟩ := ih b hb
    exact ⟨q, mem_profile_rand.2 ⟨b, hq⟩, h₁, h₂⟩
  | query d k ih =>
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_profile_bind.1 hx
    unfold cacheImpl at hy
    split at hy
    · rename_i r hr
      obtain rfl := hy
      obtain ⟨q, hq, h₁, h₂⟩ := ih r hz
      have hd : d ∈ cacheKeys c := by
        by_contra h
        rw [← lookup_eq_none_iff_not_mem_cacheKeys] at h
        simp [h] at hr
      refine ⟨d ::ₘ q, mem_profile_query.2 ⟨r, (q, z.2.1), hq, rfl⟩, ?_, ?_⟩
      · dsimp only
        rw [zero_add, h₁]
        congr 1
        ext e
        simp only [Finset.mem_sdiff, Multiset.mem_toFinset, Multiset.mem_cons]
        grind
      · rw [h₂]
        ext e
        simp only [Finset.mem_union, Multiset.mem_toFinset, Multiset.mem_cons]
        grind
    · rename_i hn
      obtain ⟨r, y', rfl, rfl⟩ := mem_profile_query.1 hy
      obtain ⟨q, hq, h₁, h₂⟩ := ih r hz
      have hd : d ∉ cacheKeys c := lookup_eq_none_iff_not_mem_cacheKeys.1 hn
      refine ⟨d ::ₘ q, mem_profile_query.2 ⟨r, (q, z.2.1), hq, rfl⟩, ?_, ?_⟩
      · have hnd : d ∉ q.toFinset \ insert d (cacheKeys c) := by simp
        have he : (d ::ₘ q).toFinset \ cacheKeys c =
            Finset.cons d (q.toFinset \ insert d (cacheKeys c)) hnd := by
          ext e
          simp only [Finset.mem_sdiff, Multiset.mem_toFinset, Multiset.mem_cons, Finset.mem_cons,
            Finset.mem_insert]
          grind
        dsimp only
        rw [h₁, cacheKeys_cons, he, Finset.cons_val]
        simp
      · rw [h₂, cacheKeys_cons]
        ext e
        simp only [Finset.mem_union, Finset.mem_insert, Multiset.mem_toFinset, Multiset.mem_cons]
        grind

/-- The charge of the inner calls of a path of the cached run is the sum of the charge over the
distinct queries of a path of `A` outside the initial cache. -/
theorem charge_profile_simulate_cacheImpl (cost : D → ℕ) {A : OracleAdv D R α}
    {c : List (D × R)} {x : Multiset D × (α × List (D × R))}
    (hx : x ∈ profile (simulate cacheImpl A c)) :
    ∃ q, (q, x.2.1) ∈ profile A ∧ charge cost x.1 = ∑ d ∈ q.toFinset \ cacheKeys c, cost d := by
  obtain ⟨q, hq, h₁, -⟩ := mem_profile_simulate_cacheImpl hx
  exact ⟨q, hq, by rw [h₁, charge, Finset.sum_eq_multiset_sum]⟩

/-- A path of the cached run makes at most as many inner calls as a path of `A` with the same
result has distinct queries, and these are at most its queries. -/
theorem card_profile_simulate_cacheImpl_le {A : OracleAdv D R α} {c : List (D × R)}
    {x : Multiset D × (α × List (D × R))} (hx : x ∈ profile (simulate cacheImpl A c)) :
    ∃ q, (q, x.2.1) ∈ profile A ∧ Multiset.card x.1 ≤ q.toFinset.card ∧
      q.toFinset.card ≤ Multiset.card q := by
  obtain ⟨q, hq, h₁, -⟩ := mem_profile_simulate_cacheImpl hx
  refine ⟨q, hq, ?_, Multiset.toFinset_card_le q⟩
  rw [h₁, Finset.card_val]
  exact Finset.card_le_card Finset.sdiff_subset

/-- Amortized form: the number of inner calls of a path of the cached run is the number of keys
the cache gains, and the cache only grows. -/
theorem card_profile_simulate_cacheImpl_eq_growth {A : OracleAdv D R α} {c : List (D × R)}
    {x : Multiset D × (α × List (D × R))} (hx : x ∈ profile (simulate cacheImpl A c)) :
    Multiset.card x.1 = (cacheKeys x.2.2 \ cacheKeys c).card ∧
      cacheKeys c ⊆ cacheKeys x.2.2 := by
  obtain ⟨q, -, h₁, h₂⟩ := mem_profile_simulate_cacheImpl hx
  rw [h₁, h₂, Finset.card_val, Finset.union_sdiff_left]
  exact ⟨rfl, Finset.subset_union_left⟩

/-- `IsDistinctQueryBoundBy cost A K n`: on each path of `A` the cost summed over the distinct
queries outside `K` is at most `n`. -/
def IsDistinctQueryBoundBy (cost : D → ℕ) (A : OracleAdv D R α) (K : Finset D) (n : ℕ) :
    Prop :=
  ∀ x ∈ profile A, ∑ d ∈ x.1.toFinset \ K, cost d ≤ n

/-- A cost bound bounds the cost of the distinct queries outside any set. -/
theorem IsQueryBoundBy.isDistinctQueryBoundBy {cost : D → ℕ} {A : OracleAdv D R α} {n : ℕ}
    (hA : A.IsQueryBoundBy cost n) (K : Finset D) : A.IsDistinctQueryBoundBy cost K n := by
  intro x hx
  have h := hA.charge_le x hx
  have h₁ : ∑ d ∈ x.1.toFinset \ K, cost d ≤ ∑ d ∈ x.1.toFinset, cost d :=
    Finset.sum_le_sum_of_subset Finset.sdiff_subset
  have h₂ : ∑ d ∈ x.1.toFinset, cost d ≤ charge cost x.1 := by
    rw [Finset.sum_eq_multiset_sum, charge, Multiset.toFinset_val]
    obtain ⟨u, hu⟩ :=
      Multiset.le_iff_exists_add.1 (Multiset.map_le_map (f := cost) (Multiset.dedup_le x.1))
    rw [hu, Multiset.sum_add]
    omega
  omega

/-- The cached run has cost at most `n` at the cost `cost` when the distinct queries of `A`
outside the initial cache cost at most `n`. -/
theorem isQueryBoundBy_simulate_cacheImpl [Nonempty R] {cost : D → ℕ} {A : OracleAdv D R α}
    {c : List (D × R)} {n : ℕ} (hA : A.IsDistinctQueryBoundBy cost (cacheKeys c) n) :
    (simulate cacheImpl A c).IsQueryBoundBy cost n := by
  rw [isQueryBoundBy_iff_profile]
  intro x hx
  obtain ⟨q, hq, h⟩ := charge_profile_simulate_cacheImpl cost hx
  exact h ▸ hA _ hq

/-- The cached run makes at most `n` inner calls when `A` asks at most `n` distinct queries
outside the initial cache on each path. -/
theorem isQueryBound_simulate_cacheImpl [Nonempty R] {A : OracleAdv D R α} {c : List (D × R)}
    {n : ℕ} (hA : A.IsDistinctQueryBoundBy (fun _ => 1) (cacheKeys c) n) :
    (simulate cacheImpl A c).IsQueryBound n :=
  isQueryBound_iff_isQueryBoundBy_one.2 (isQueryBoundBy_simulate_cacheImpl hA)

/-- The query bound of `A` is a bound of the inner calls of the cached run, through the bound on
its distinct queries. -/
theorem isQueryBound_simulate_cacheImpl_of [Nonempty R] {A : OracleAdv D R α}
    {c : List (D × R)} {n : ℕ} (hA : A.IsQueryBound n) :
    (simulate cacheImpl A c).IsQueryBound n :=
  isQueryBound_simulate_cacheImpl
    ((isQueryBound_iff_isQueryBoundBy_one.1 hA).isDistinctQueryBoundBy _)

end CatCrypt.Crypto.OracleAdv
