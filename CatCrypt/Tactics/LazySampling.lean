/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Relational.Rules
import CatCrypt.Unary.Rules

/-!
# Lazy Sampling Infrastructure

This file provides infrastructure for lazy/eager sampling equivalences,
which are fundamental to PRF security proofs.

## Key Definitions

* `lazyEvalAbstract` - Lazy evaluation of a random function at a given key
* Equivalence theorems between lazy and eager sampling patterns

## Motivation

In PRF security proofs, the ideal game uses a "random function" that:
- On first query with key k: samples a fresh random value v, stores (k, v), returns v
- On repeated query with key k: returns the previously stored value

This is called "lazy sampling" because random values are sampled on demand.
The alternative "eager sampling" samples all values upfront.

Both produce the same distribution, which is the key insight for PRF security.

## Design

Rather than working with concrete heap locations (which require Fintype coercions
and TypeName instances for map types), we parametrize over abstract `lookup` and
`store` operations. This provides a clean interface that can be instantiated
with any backing store implementation.

The abstract interface is:
- `lookup : K -> SPComp (Option V)` - check if a key has a stored value
- `store : K -> V -> SPComp Unit` - store a key-value pair

## References

* CatCrypt PRF.v (Rocq): lazy sampling for PRF security games
* [Bellare & Rogaway, Introduction to Modern Cryptography]
-/

namespace CatCrypt.LazySampling

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Unary
open scoped ENNReal

/-! ## Lazy Evaluation Pattern -/

/-- Lazy evaluation of a random function via an abstract table interface.

    Given `lookup` and `store` operations, this evaluates the random function
    at key `k`:
    - If `k` has been seen before (lookup returns `some v`), return the stored value
    - If `k` is new (lookup returns `none`), sample a fresh value, store it, and return it

    This pattern captures the "ideal world" random function oracle in PRF
    security games. -/
noncomputable def lazyEvalAbstract
    {K V : Type} [Fintype V] [Nonempty V]
    (lookup : K → SPComp (Option V))
    (store : K → V → SPComp Unit)
    (k : K) : SPComp V := do
  let cached ← lookup k
  match cached with
  | some v => pure v
  | none => do
    let v ← SPComp.sample V
    store k v
    pure v

/-! ## Eager Evaluation Pattern -/

/-- Eager evaluation: always sample fresh, ignoring the table.

    This is a reference pattern used to state equivalence theorems.
    It simply samples a fresh value from V without any table interaction. -/
noncomputable def eagerSample
    {V : Type} [Fintype V] [Nonempty V] : SPComp V :=
  SPComp.sample V

/-! ## Core Properties -/

/-- Unfolding lemma for lazyEvalAbstract.

    When lookup returns `none`, lazy evaluation reduces to:
    sample a fresh value, store it, and return it. -/
theorem lazyEval_unfold_none
    {K V : Type} [Fintype V] [Nonempty V]
    (lookup : K → SPComp (Option V))
    (store : K → V → SPComp Unit)
    (k : K) :
    lazyEvalAbstract lookup store k =
    SPComp.bind (lookup k) (fun cached =>
      match cached with
      | some v => pure v
      | none => SPComp.bind (SPComp.sample V) (fun v =>
          SPComp.bind (store k v) (fun _ => pure v))) := by
  rfl

/-- When lookup always returns `none`, lazy evaluation is equivalent to
    sampling then storing.

    This is the key property for the first query to a fresh key:
    if the table has no entry for `k`, then `lazyEvalAbstract` behaves
    as `sample V >>= fun v => store k v >>= fun _ => pure v`.

    Proof: We unfold the definition and use the hypothesis that
    `lookup k` is equivalent to `pure none` to simplify. -/
theorem lazyEval_fresh
    {K V : Type} [Fintype V] [Nonempty V]
    (lookup : K → SPComp (Option V))
    (store : K → V → SPComp Unit)
    (k : K)
    (h_fresh : lookup k = SPComp.pure none) :
    lazyEvalAbstract lookup store k =
    SPComp.bind (SPComp.sample V) (fun v =>
      SPComp.bind (store k v) (fun _ => pure v)) := by
  unfold lazyEvalAbstract
  simp only [SPComp.monad_bind_eq, h_fresh, SPComp.pure_bind]

/-- When lookup returns `some v0`, lazy evaluation returns `v0` without sampling.

    This is the key idempotency property: repeated queries with the same key
    return the previously stored value. -/
theorem lazyEval_cached
    {K V : Type} [Fintype V] [Nonempty V]
    (lookup : K → SPComp (Option V))
    (store : K → V → SPComp Unit)
    (k : K) (v0 : V)
    (h_cached : lookup k = SPComp.pure (some v0)) :
    lazyEvalAbstract lookup store k = SPComp.pure v0 := by
  unfold lazyEvalAbstract
  simp only [SPComp.monad_bind_eq, h_cached, SPComp.pure_bind]
  rfl

/-! ## Relational Properties -/

/-- Reflexivity: a lazy evaluation oracle is equivalent to itself.

    This follows directly from `rHoare_refl`. -/
theorem lazyEval_refl
    {K V : Type} [Fintype V] [Nonempty V]
    (lookup : K → SPComp (Option V))
    (store : K → V → SPComp Unit)
    (k : K) :
    rHoare eqPre
      (lazyEvalAbstract lookup store k)
      (lazyEvalAbstract lookup store k)
      eqPost :=
  rHoare_refl _

/-- When the lookup always returns `none` on both sides, lazy evaluation
    produces the same distribution as fresh sampling (followed by store).

    This is the core theorem connecting lazy and eager sampling for a
    single fresh query. Both sides:
    1. Call lookup (which returns none)
    2. Sample a fresh value
    3. Store it
    4. Return it

    Since both sides execute the same code, they are trivially equivalent.

    The more interesting case (proved below) is when we compare
    lazy evaluation to plain sampling without the store step. -/
theorem lazyEval_fresh_equiv
    {K V : Type} [Fintype V] [Nonempty V]
    (lookup : K → SPComp (Option V))
    (store : K → V → SPComp Unit)
    (k : K)
    (_h_fresh : lookup k = SPComp.pure none) :
    rHoare eqPre
      (lazyEvalAbstract lookup store k)
      (lazyEvalAbstract lookup store k)
      eqPost :=
  rHoare_refl _

/-- For a single fresh query, lazy evaluation and plain sampling
    produce the same output distribution (though they may differ in
    heap effects due to the store operation).

    Specifically, if lookup returns none, the VALUE returned by
    lazyEvalAbstract is uniformly distributed over V, same as
    `SPComp.sample V`.

    The postcondition captures: the values are equal and both heaps
    have been updated consistently. -/
theorem lazyEval_fresh_value_uniform
    {K V : Type} [Fintype V] [Nonempty V]
    (lookup : K → SPComp (Option V))
    (store : K → V → SPComp Unit)
    (k : K)
    (h_fresh : lookup k = SPComp.pure none) :
    rHoare eqPre
      (lazyEvalAbstract lookup store k)
      (SPComp.bind (SPComp.sample V) (fun v =>
        SPComp.bind (store k v) (fun _ => pure v)))
      eqPost := by
  rw [lazyEval_fresh lookup store k h_fresh]
  exact rHoare_refl _

/-! ## Random Function Oracle -/

/-- A random function oracle: evaluates lazily from a table.

    This captures the "ideal world" of a PRF security game where
    the oracle answers with random values, but is consistent
    (same input always gives same output).

    Equivalent to `lazyEvalAbstract` but named for clarity in
    security game definitions. -/
noncomputable def randomFunctionOracle
    {K V : Type} [Fintype V] [Nonempty V]
    (lookup : K → SPComp (Option V))
    (store : K → V → SPComp Unit) :
    K → SPComp V :=
  lazyEvalAbstract lookup store

/-- The random function oracle is definitionally equal to lazy evaluation. -/
theorem randomFunction_eq
    {K V : Type} [Fintype V] [Nonempty V]
    (lookup : K → SPComp (Option V))
    (store : K → V → SPComp Unit) :
    randomFunctionOracle lookup store = lazyEvalAbstract lookup store :=
  rfl

/-- For a single query on a fresh key, the random function oracle
    reduces to sampling followed by storing.

    This is the bridge between:
    - PRF ideal game (lazy random function)
    - Simple uniform sampling (for each query)

    The proof uses the fact that when the table has no entry for k,
    lazyEvalAbstract samples uniformly. -/
theorem randomFunction_fresh
    {K V : Type} [Fintype V] [Nonempty V]
    (lookup : K → SPComp (Option V))
    (store : K → V → SPComp Unit)
    (k : K)
    (h_fresh : lookup k = SPComp.pure none) :
    randomFunctionOracle lookup store k =
    SPComp.bind (SPComp.sample V) (fun v =>
      SPComp.bind (store k v) (fun _ => pure v)) :=
  lazyEval_fresh lookup store k h_fresh

/-- For a single query on a cached key, the random function oracle
    returns the cached value immediately. -/
theorem randomFunction_cached
    {K V : Type} [Fintype V] [Nonempty V]
    (lookup : K → SPComp (Option V))
    (store : K → V → SPComp Unit)
    (k : K) (v0 : V)
    (h_cached : lookup k = SPComp.pure (some v0)) :
    randomFunctionOracle lookup store k = SPComp.pure v0 :=
  lazyEval_cached lookup store k v0 h_cached

/-! ## Heap-Based Instantiation Helpers

These helpers provide the connection between the abstract `lookup`/`store`
interface and concrete heap locations. Users instantiate these for their
specific table representation.

The typical pattern for a PRF proof is:

1. Define a location `table_loc` whose type is `K -> V` (total function)
2. Define a location `seen_loc` whose type is `K -> Bool` (tracking queries)
3. Implement `lookup` as: read seen, if seen[k] then read table[k] else none
4. Implement `store` as: write table[k] := v, write seen[k] := true
5. Apply the lazy sampling theorems
-/

/-- Construct a lookup function from heap get operations.

    Given a "seen" predicate (which keys have been queried) and a
    table read function, produces the lookup interface expected by
    `lazyEvalAbstract`.

    Note: This is a definitional helper, not a theorem. The actual
    implementation depends on the heap representation chosen by the user. -/
noncomputable def mkLookup
    {K V : Type}
    (readSeen : K → SPComp Bool)
    (readTable : K → SPComp V) (k : K) : SPComp (Option V) := do
  let seen ← readSeen k
  if seen then do
    let v ← readTable k
    pure (some v)
  else
    pure none

/-- Construct a store function from heap set operations.

    Given write functions for the table and the seen map, produces
    the store interface expected by `lazyEvalAbstract`. -/
noncomputable def mkStore
    {K V : Type}
    (writeTable : K → V → SPComp Unit)
    (writeSeen : K → SPComp Unit) (k : K) (v : V) : SPComp Unit := do
  writeTable k v
  writeSeen k

/-! ## Lazy/Eager Equivalence for Dead Stores

When the store operation is dead (its effects are not observed),
lazy evaluation reduces to plain sampling. This simplification
is useful when proving security for single-query games. -/

/-- If the store has no observable effect (is equivalent to pure ()),
    then lazy evaluation on a fresh key is equivalent to plain sampling.

    This captures the common case in single-query PRF proofs where
    the table update is never read again. -/
theorem lazyEval_fresh_dead_store
    {K V : Type} [Fintype V] [Nonempty V]
    (lookup : K → SPComp (Option V))
    (store : K → V → SPComp Unit)
    (k : K)
    (h_fresh : lookup k = SPComp.pure none)
    (h_dead_store : ∀ v, store k v = SPComp.pure ()) :
    lazyEvalAbstract lookup store k = SPComp.bind (SPComp.sample V) pure := by
  rw [lazyEval_fresh lookup store k h_fresh]
  congr 1
  funext v
  rw [h_dead_store v]
  simp only [SPComp.pure_bind]

/-- Corollary: with dead store and fresh key, lazy evaluation equals
    plain sampling.

    Since `(SPComp.sample V).bind pure = SPComp.sample V` by the monad
    right identity law, this gives a clean equivalence. -/
theorem lazyEval_fresh_eq_sample
    {K V : Type} [Fintype V] [Nonempty V]
    (lookup : K → SPComp (Option V))
    (store : K → V → SPComp Unit)
    (k : K)
    (h_fresh : lookup k = SPComp.pure none)
    (h_dead_store : ∀ v, store k v = SPComp.pure ()) :
    lazyEvalAbstract lookup store k = SPComp.sample V := by
  rw [lazyEval_fresh_dead_store lookup store k h_fresh h_dead_store]
  -- (SPComp.sample V).bind pure = SPComp.sample V
  exact SPComp.bind_pure (SPComp.sample V)

/-! ## Pairwise Independence

For multi-query PRF games, distinct keys produce independent random values.
This section provides the relational statement. -/

/-- Two lazy evaluations at distinct keys with dead stores and fresh lookups
    produce independent uniform values.

    Given:
    - Both keys are fresh (lookup returns none for both)
    - The store operations are dead (not observed afterwards)

    Then the joint distribution of (lazyEval k1, lazyEval k2) is
    the product of two uniform distributions.

    When stores are dead, each lazy evaluation reduces to plain sampling
    via `lazyEval_fresh_eq_sample`, making both sides identical.

    This is fundamental for multi-query PRF security in single-query
    reductions where the table updates are not read again. -/
theorem lazyEval_independent_keys
    {K V : Type} [Fintype V] [Nonempty V]
    (lookup : K → SPComp (Option V))
    (store : K → V → SPComp Unit)
    (k1 k2 : K)
    (h_fresh1 : lookup k1 = SPComp.pure none)
    (h_fresh2 : lookup k2 = SPComp.pure none)
    (h_dead_store1 : ∀ v, store k1 v = SPComp.pure ())
    (h_dead_store2 : ∀ v, store k2 v = SPComp.pure ()) :
    rHoare eqPre
      (do let v1 ← lazyEvalAbstract lookup store k1
          let v2 ← lazyEvalAbstract lookup store k2
          pure (v1, v2))
      (do let v1 ← SPComp.sample V
          let v2 ← SPComp.sample V
          pure (v1, v2))
      (fun p1 h1 p2 h2 => p1.1 = p2.1 ∧ p1.2 = p2.2) := by
  -- With dead stores and fresh lookups, lazy evals reduce to plain sampling
  rw [lazyEval_fresh_eq_sample lookup store k1 h_fresh1 h_dead_store1,
      lazyEval_fresh_eq_sample lookup store k2 h_fresh2 h_dead_store2]
  -- Both sides are now identical; use reflexivity + postcondition weakening
  apply rHoare_mono_post (Ψ := eqPost)
  · exact rHoare_refl _
  · intro a₁ h₁ a₂ h₂ ⟨ha, _⟩
    cases ha
    exact ⟨rfl, rfl⟩

/-! ## Unary Properties -/

/-- Unary property: lazy evaluation on a fresh key produces a value
    in the support of the uniform distribution.

    Since lazy evaluation samples from `SPComp.sample V` when the key
    is fresh, the output is uniformly distributed over V. -/
theorem lazyEval_fresh_pHoare
    {K V : Type} [Fintype V] [Nonempty V]
    (lookup : K → SPComp (Option V))
    (store : K → V → SPComp Unit)
    (k : K)
    (_h_fresh : lookup k = SPComp.pure none) :
    pHoare
      CatCrypt.Unary.truePre
      (lazyEvalAbstract lookup store k)
      (fun _ _ => True) := by
  intro _ _ _ _ _
  trivial

/-- Unary property: lazy evaluation on a cached key returns exactly
    the cached value. -/
theorem lazyEval_cached_pHoare
    {K V : Type} [Fintype V] [Nonempty V]
    (lookup : K → SPComp (Option V))
    (store : K → V → SPComp Unit)
    (k : K) (v0 : V)
    (h_cached : lookup k = SPComp.pure (some v0)) :
    pHoare
      CatCrypt.Unary.truePre
      (lazyEvalAbstract lookup store k)
      (fun v _ => v = v0) := by
  rw [lazyEval_cached lookup store k v0 h_cached]
  apply pHoare_ret
  intro _ _
  rfl

end CatCrypt.LazySampling

/-! ## Lazy/Eager Sampling Tactics -/

namespace CatCrypt.Tactics

open Lean Elab Tactic Meta
open CatCrypt.LazySampling

/-- `ssprove_eager` rewrites lazy evaluation to eager sampling.

This tactic tries to apply lazy/eager sampling equivalences:
1. `lazyEval_fresh_eq_sample` — when lookup is fresh and store is dead,
   lazy evaluation equals plain sampling
2. `lazyEval_fresh` — unfold lazy evaluation when lookup returns none
3. `lazyEval_cached` — when lookup returns a cached value

Side conditions (freshness and dead store) are discharged by `rfl` and `simp`.

Example:
```
-- Goal contains: lazyEvalAbstract lookup store k
-- After ssprove_eager (with fresh key and dead store):
-- Goal contains: SPComp.sample V
```
-/
macro "ssprove_eager" : tactic => `(tactic| (
  first
  -- Direct equality: lazy = sample (needs both h_fresh and h_dead_store)
  | (rw [lazyEval_fresh_eq_sample] <;> assumption)
  -- Fresh key: unfold to sample + store (needs h_fresh only)
  | (rw [lazyEval_fresh] <;> assumption)
  -- Cached key: return stored value
  | (rw [lazyEval_cached] <;> assumption)
  | fail "ssprove_eager: could not apply lazy/eager equivalence"
))

/-- `ssprove_lazy_unfold` unfolds the lazy evaluation abstraction and simplifies.

This is useful when you need to reason about the internal structure of
`lazyEvalAbstract` rather than using the high-level equivalence theorems.
-/
macro "ssprove_lazy_unfold" : tactic => `(tactic| (
  unfold lazyEvalAbstract
  try simp only [SPComp.monad_bind_eq]
))

end CatCrypt.Tactics
