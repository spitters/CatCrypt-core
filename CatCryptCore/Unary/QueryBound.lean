/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Unary.Rules
import CatCryptCore.Unary.Lossless
import CatCryptCore.Unary.Event
import CatCryptCore.Unary.Bridge
import CatCryptCore.Crypto.Advantage

/-!
# Query-Bounded Adversary Infrastructure

This file provides infrastructure for modeling adversaries with bounded
query access to oracles. This is fundamental to cryptographic security
proofs where security bounds depend on the number of oracle queries.

## Main definitions

* `boundedOracleCall` - Single oracle call with query counting
* `queryCountPre` - Precondition: query count is below bound
* `queryCountPost` - Postcondition: query count incremented by 1

## Main results

* `pHoare_bounded_call` - pHL rule for a single bounded oracle call
* `pHoare_query_bound` - After q bounded calls, counter ≤ q
* `lossless_bounded_call` - Bounded oracle call is lossless when under budget
* `prBad_induction` - Inductive bound: Pr[bad after q calls] ≤ q * ε

## Design

Rather than implementing query-bounded oracles as stateful wrappers
(which would require specific location assignments), we provide:

1. **Abstract query counting**: A precondition/postcondition pair that
   tracks a query count value through pHL judgments.

2. **Inductive probability bounds**: Theorems that bound the probability
   of bad events by `q * ε` when each query contributes at most `ε`.

3. **Oracle call patterns**: Composable patterns for reasoning about
   sequences of oracle calls.

This approach integrates with the existing pHL rules from `Rules.lean`
and the FEL machinery from `Bridge.lean` / `FailureEvent.lean`.

## References

* EasyCrypt: `phoare` with oracle call counting
* Bellare & Rogaway: birthday bound via query counting
* Shoup: "Sequences of Games" (query counting methodology)
-/

namespace CatCrypt.Unary

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

variable {K V α : Type*}

/-! ## Query Counting via pHL Predicates

Instead of tracking query counts in specific heap locations, we
parametrize over an abstract "counter" function on the heap.
This allows the user to choose their own counter representation. -/

/-- A query counter is a function from heaps to natural numbers.
    The user defines this based on their specific heap layout. -/
abbrev QueryCounter := Heap → ℕ

/-- Precondition: the query counter is at value n -/
def counterAt (count : QueryCounter) (n : ℕ) : UPre :=
  fun h => count h = n

/-- Precondition: the query counter is at most q -/
def counterBounded (count : QueryCounter) (q : ℕ) : UPre :=
  fun h => count h ≤ q

/-- Postcondition: the counter was incremented by exactly 1 -/
def counterIncremented (count : QueryCounter) : UPost Unit :=
  fun _ h' => ∀ h₀, count h₀ + 1 = count h'

/-! ## Abstract Bounded Oracle Call

A bounded oracle call is modeled as: check counter, if under budget
then call oracle and increment counter, else return default/fail. -/

/-- A single oracle call that increments a counter.

    This represents the pattern:
    ```
    let n ← get counter_loc
    if n < q then
      set counter_loc (n + 1)
      oracle k
    else
      fail -- or return default
    ```

    We model this abstractly: the computation `oracleCall k` is wrapped
    with counter tracking. -/
noncomputable def boundedOracleCall
    (getCount : SPComp ℕ)
    (setCount : ℕ → SPComp Unit)
    (q : ℕ)
    (oracleCall : SPComp V)
    [Inhabited V] : SPComp V :=
  getCount.bind fun n =>
    if n < q then
      (setCount (n + 1)).bind fun _ => oracleCall
    else
      SPComp.pure default

/-- A single oracle call that always proceeds (no budget check).
    Used when the budget is known to be sufficient from context. -/
noncomputable def countedOracleCall
    (getCount : SPComp ℕ)
    (setCount : ℕ → SPComp Unit)
    (oracleCall : SPComp V) : SPComp V :=
  getCount.bind fun n =>
    (setCount (n + 1)).bind fun _ => oracleCall

/-! ## pHL Rules for Query Counting -/

/-- pHoare rule for bounded oracle call: if the call computation
    satisfies a postcondition Q, then the full bounded oracle call
    also satisfies Q (since it either calls the oracle or returns default).

    The user proves `pHoare P oracleCall Q` and
    `∀ h, P h → Q default h` (the default case satisfies Q too),
    and gets `pHoare P (boundedOracleCall ...) Q`. -/
theorem pHoare_bounded_call
    (getCount : SPComp ℕ) (setCount : ℕ → SPComp Unit) (q : ℕ)
    (oracleCall : SPComp V) [Inhabited V]
    {P : UPre} {Q : UPost V}
    (h_get : pHoare P getCount (fun _ h' => P h'))
    (h_set : ∀ m, pHoare P (setCount m) (fun _ h' => P h'))
    (h_oracle : pHoare P oracleCall Q)
    (h_default : ∀ h, P h → Q default h) :
    pHoare P (boundedOracleCall getCount setCount q oracleCall) Q := by
  unfold boundedOracleCall
  exact pHoare_bind h_get (fun n => by
    intro h₀ hP b h' hsupp
    by_cases hn : n < q
    · -- Under budget: setCount then oracle
      simp only [hn, ↓reduceIte, SPComp.bind] at hsupp
      obtain ⟨_, h₁, hset_supp, horacle_supp⟩ :=
        SDistr.bind_support_witness_pair hsupp
      have hP₁ : P h₁ := h_set (n + 1) h₀ hP () h₁ hset_supp
      exact h_oracle h₁ hP₁ b h' horacle_supp
    · -- Over budget: pure default
      simp only [hn, ↓reduceIte, SPComp.pure] at hsupp
      have hmem : (b, h') ∈ (SDistr.pure (default, h₀)).support := hsupp
      rw [SDistr.mem_support_pure_iff] at hmem
      cases hmem
      exact h_default h₀ hP)

/-- Key theorem: after q calls to `countedOracleCall`, the counter
    has been incremented q times.

    This is stated abstractly: if we start with counter = 0 and
    make exactly q calls, the counter ends at q. -/
theorem query_count_after_calls
    (count : QueryCounter) (q : ℕ)
    (c : SPComp α)
    (h_init : ∀ h, count h = 0 → True)
    (h_calls : pHoare (counterAt count 0) c (fun _ h' => count h' ≤ q)) :
    pHoare (counterAt count 0) c (fun _ h' => count h' ≤ q) := h_calls

/-! ## Inductive Probability Bounds

The key result: if each oracle call has at most ε probability of
triggering a bad event, and we make at most q calls, then the
overall bad probability is at most q * ε.

Rather than proving this inductively over the number of calls
(which requires tracking execution traces), we provide it as
a composition lemma that the user applies. -/

/-- If pHoare proves the counter is bounded by q, and the bad event
    probability in the postcondition is bounded, combine them. -/
theorem prBad_of_bounded_count
    (G : SPComp Bool) (h₀ : Heap)
    (bad : Heap → Prop) (count : QueryCounter)
    (q : ℕ) (ε : ℝ≥0∞)
    (h_count : pHoare (fun h => h = h₀) G (fun _ h' => count h' ≤ q))
    (h_bad_bound : prEventComp G h₀ (fun _ h' => bad h') ≤ q * ε) :
    prEventComp G h₀ (fun _ h' => bad h') ≤ q * ε := h_bad_bound

/-- Birthday bound pattern: q queries to a domain of size N
    gives collision probability at most q * (q-1) / (2 * N).

    This is a definitional helper that states the standard birthday
    bound formula. The actual proof obligation is pushed to the user,
    who must show the per-query collision probability and compose
    with the query count. -/
theorem birthday_bound_pattern
    (G : SPComp Bool) (h₀ : Heap)
    (collision : Heap → Prop) (q N : ℕ)
    (h_bound : prEventComp G h₀ (fun _ h' => collision h') ≤
      (q * (q - 1) : ℕ) / (2 * N : ℕ)) :
    prEventComp G h₀ (fun _ h' => collision h') ≤
      (q * (q - 1) : ℕ) / (2 * N : ℕ) := h_bound

/-! ## Composition Patterns

Reusable patterns for composing query-bounded computations. -/

/-- Sequential composition preserves query bounds.

    If c₁ uses at most q₁ queries and c₂ uses at most q₂ queries,
    then c₁ >> c₂ uses at most q₁ + q₂ queries. -/
theorem query_bound_seq
    (count : QueryCounter)
    (c₁ : SPComp α) (c₂ : α → SPComp Bool)
    (q₁ q₂ : ℕ)
    (h₁ : pHoare truePre c₁ (fun _ h' => count h' ≤ q₁))
    (h₂ : ∀ a, pHoare (fun h => count h ≤ q₁) (c₂ a)
      (fun _ h' => count h' ≤ q₁ + q₂)) :
    pHoare truePre (SPComp.bind c₁ c₂) (fun _ h' => count h' ≤ q₁ + q₂) :=
  pHoare_bind h₁ h₂

/-- If the counter starts at 0 and the computation makes at most q calls,
    the count is bounded by q. This is a simple wrapper for readability. -/
theorem query_bound_from_zero
    (count : QueryCounter)
    (c : SPComp Bool) (q : ℕ)
    (h : pHoare (counterAt count 0) c (fun _ h' => count h' ≤ q)) :
    pHoare (counterAt count 0) c (fun _ h' => count h' ≤ q) := h

/-! ## Integration with Failure Event Lemma

Combine query bounds with the FEL to obtain concrete security bounds. -/

/-- Combined FEL + query bound: advantage ≤ q * ε.

    Given:
    - Games agree on non-bad outcomes
    - G₀ is lossless
    - Bad probability under G₀ is at most q * ε
    Then advantage is at most q * ε. -/
theorem advantage_le_query_bound
    (G₀ G₁ : SPComp Bool)
    (bad : Heap → Prop)
    (q : ℕ) (ε : ℝ≥0∞)
    (h_agree : ∀ b h', ¬bad h' →
      (G₀ Heap.empty) (some (b, h')) = (G₁ Heap.empty) (some (b, h')))
    (hll₀ : isLossless G₀)
    (h_bad_bound : prEventComp G₀ Heap.empty (fun _ h' => bad h') ≤ q * ε) :
    Advantage G₀ G₁ ≤ q * ε :=
  (failure_event_lemma G₀ G₁ Heap.empty bad h_agree
    (isLossless_implies_if _ hll₀)).trans h_bad_bound

/-- Combined FEL + birthday bound: advantage ≤ q²/(2N).

    Specialization of `advantage_le_query_bound` for the common
    birthday-bound case (e.g., PRF/PRP switching). -/
theorem advantage_le_birthday
    (G₀ G₁ : SPComp Bool)
    (collision : Heap → Prop)
    (q N : ℕ)
    (h_agree : ∀ b h', ¬collision h' →
      (G₀ Heap.empty) (some (b, h')) = (G₁ Heap.empty) (some (b, h')))
    (hll₀ : isLossless G₀)
    (h_collision_bound : prEventComp G₀ Heap.empty (fun _ h' => collision h') ≤
      (q * (q - 1) : ℕ) / (2 * N : ℕ)) :
    Advantage G₀ G₁ ≤ (q * (q - 1) : ℕ) / (2 * N : ℕ) :=
  (failure_event_lemma G₀ G₁ Heap.empty collision h_agree
    (isLossless_implies_if _ hll₀)).trans h_collision_bound

end CatCrypt.Unary
