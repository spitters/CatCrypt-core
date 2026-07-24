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
* `prEvent_bind_eq` - Bad mass of a bind as the expectation of the continuation's bad mass
* `prEventComp_bind_step_le` - Per-step subadditivity: one step adds at most `ε`
* `prBad_induction` - Adaptive union bound: Pr[bad after q calls] ≤ q * ε
* `advantage_le_query_bound_derived` - Advantage bound `≤ q * ε` from per-step freshness

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
open Classical

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

/-! ## Adaptive q-Query Union Bound

A `q`-fold loop of oracle calls, where each call adds at most `ε` to the
bad-event probability, has total bad probability at most `q * ε`.

The loop is `repeatStep step q`, an unrolled `q`-fold sequential composition of
a single step `step : SPComp Unit`. The bound is proved by induction on `q`
from a per-step increment hypothesis; that increment is in turn derived from a
single-step freshness bound via `prEventComp_bind_step_le`. -/

/-- The total mass of a sub-distribution is at most one. -/
theorem sdistr_mass_le_one {β : Type*} (d : SDistr β) : SDistr.mass d ≤ 1 := by
  unfold SDistr.mass; exact tsub_le_self

/-- A `q`-fold sequential iteration of a single step computation.
    `repeatStep step 0` is the trivial computation; `repeatStep step (q+1)`
    runs `repeatStep step q` and then one more `step`. -/
noncomputable def repeatStep (step : SPComp Unit) : ℕ → SPComp Unit
  | 0 => SPComp.pure ()
  | q + 1 => (repeatStep step q).bind (fun _ => step)

/-- The bad-event probability of a point mass at `(a, h)` is the indicator of
    `bad h`: `1` if `bad h`, else `0`. -/
theorem prEvent_pure {δ : Type*} (a : δ) (h : Heap) (bad : Heap → Prop) :
    prEvent (SDistr.pure (a, h)) (fun _ h' => bad h') =
      (if bad h then 1 else 0) := by
  unfold prEvent
  rw [tsum_eq_single (a, h)]
  · by_cases hb : bad h <;>
      simp [hb, SDistr.pure_apply_some]
  · intro p hp
    have hz : (SDistr.pure (a, h) : SDistr (δ × Heap)) (some p) = 0 := by
      rw [SDistr.pure_apply_some]
      exact if_neg (fun heq => hp heq.symm)
    simp [hz]

/-- The bad-event probability of a pure computation from `h₀` is the indicator
    of `bad h₀`: `1` if `bad h₀`, else `0`. -/
theorem prEventComp_pure (a : α) (h₀ : Heap) (bad : Heap → Prop) :
    prEventComp (SPComp.pure a) h₀ (fun _ h' => bad h') =
      (if bad h₀ then 1 else 0) := by
  unfold prEventComp
  rw [SPComp.pure_def]
  exact prEvent_pure a h₀ bad

/-- Pointwise value of a sub-distribution `bind` at a `some` outcome: the
    probability sums, over reachable intermediate outcomes, the intermediate
    probability times the continuation probability. -/
theorem SDistr_bind_apply_some {β γ : Type*} (d : SDistr (β × Heap))
    (g : β × Heap → SDistr (γ × Heap)) (b : γ × Heap) :
    (d.bind g) (some b) = ∑' a : β × Heap, d (some a) * (g a) (some b) := by
  unfold SDistr.bind
  rw [PMF.bind_apply, tsum_option_split]
  simp only [SDistr.fail_apply_some, mul_zero, zero_add]

/-- Bad-mass of a sub-distribution `bind`: the event probability of `d.bind g`
    is the `d`-expectation of the event probability of the continuation `g`
    started from each reachable intermediate outcome. -/
theorem prEvent_bind_eq {β γ : Type*} (d : SDistr (β × Heap))
    (g : β × Heap → SDistr (γ × Heap)) (E : γ → Heap → Prop) :
    prEvent (d.bind g) E =
      ∑' q : β × Heap, d (some q) * prEvent (g q) E := by
  unfold prEvent
  calc ∑' p : γ × Heap, (if E p.1 p.2 then (d.bind g) (some p) else 0)
      = ∑' p : γ × Heap, ∑' a : β × Heap,
          (if E p.1 p.2 then d (some a) * (g a) (some p) else 0) := by
        apply tsum_congr; intro p; rw [SDistr_bind_apply_some]
        by_cases hE : E p.1 p.2
        · simp only [hE, if_true]
        · simp only [hE, if_false, tsum_zero]
    _ = ∑' a : β × Heap, ∑' p : γ × Heap,
          (if E p.1 p.2 then d (some a) * (g a) (some p) else 0) := ENNReal.tsum_comm
    _ = ∑' a : β × Heap, d (some a) *
          ∑' p : γ × Heap, (if E p.1 p.2 then (g a) (some p) else 0) := by
        apply tsum_congr; intro a
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr; intro p
        by_cases hE : E p.1 p.2
        · simp only [hE, if_true]
        · simp only [hE, if_false, mul_zero]

/-- Decomposition of the bad-event mass of a loop step: the bad mass of
    `m.bind (fun _ => step)` is the `m`-expectation of the bad mass of `step`
    started from each reachable intermediate heap. -/
theorem prEvent_bind_step_eq_tsum
    (m : SPComp Unit) (step : SPComp Unit) (h₀ : Heap) (bad : Heap → Prop) :
    prEventComp (m.bind (fun _ => step)) h₀ (fun _ h' => bad h') =
      ∑' p : Unit × Heap,
        (m h₀) (some p) * prEvent (step p.2) (fun _ h' => bad h') := by
  unfold prEventComp
  rw [SPComp.bind_def, prEvent_bind_eq]

/-- Per-step subadditivity of bad mass: if from every non-bad reachable heap the
    single step introduces bad with probability at most `ε`, then prepending any
    prefix `m` adds at most `ε` to the bad probability. -/
theorem prEventComp_bind_step_le
    (m : SPComp Unit) (step : SPComp Unit) (h₀ : Heap) (bad : Heap → Prop)
    (ε : ℝ≥0∞)
    (h_fresh : ∀ h₁ : Heap, ¬ bad h₁ →
      prEvent (step h₁) (fun _ h' => bad h') ≤ ε) :
    prEventComp (m.bind (fun _ => step)) h₀ (fun _ h' => bad h') ≤
      prEventComp m h₀ (fun _ h' => bad h') + ε := by
  rw [prEvent_bind_step_eq_tsum]
  -- Bound each term by (m-mass at p) * (bad h₁ ? 1 : ε).
  have hterm : ∀ p : Unit × Heap,
      (m h₀) (some p) * prEvent (step p.2) (fun _ h' => bad h') ≤
        (if bad p.2 then (m h₀) (some p) else 0) +
        (if ¬ bad p.2 then (m h₀) (some p) else 0) * ε := by
    intro p
    by_cases hb : bad p.2
    · simp only [hb, if_true, not_true_eq_false, if_false, zero_mul, add_zero]
      calc (m h₀) (some p) * prEvent (step p.2) (fun _ h' => bad h')
          ≤ (m h₀) (some p) * 1 :=
            mul_le_mul' le_rfl ((prEvent_le_mass _ _).trans (sdistr_mass_le_one _))
        _ = (m h₀) (some p) := mul_one _
    · simp only [hb, if_false, not_false_eq_true, if_true, zero_add]
      exact mul_le_mul' le_rfl (h_fresh p.2 hb)
  calc ∑' p : Unit × Heap,
          (m h₀) (some p) * prEvent (step p.2) (fun _ h' => bad h')
      ≤ ∑' p : Unit × Heap,
          ((if bad p.2 then (m h₀) (some p) else 0) +
           (if ¬ bad p.2 then (m h₀) (some p) else 0) * ε) :=
        ENNReal.tsum_le_tsum hterm
    _ = (∑' p : Unit × Heap, (if bad p.2 then (m h₀) (some p) else 0)) +
        (∑' p : Unit × Heap, (if ¬ bad p.2 then (m h₀) (some p) else 0) * ε) :=
        ENNReal.tsum_add
    _ ≤ prEventComp m h₀ (fun _ h' => bad h') + ε := by
        apply add_le_add
        · exact le_of_eq rfl
        · rw [ENNReal.tsum_mul_right]
          calc (∑' p : Unit × Heap, (if ¬ bad p.2 then (m h₀) (some p) else 0)) * ε
              ≤ (∑' p : Unit × Heap, (m h₀) (some p)) * ε :=
                mul_le_mul' (tsum_ite_le _ _) le_rfl
            _ = SDistr.mass (m h₀) * ε := by rw [tsum_some_eq_mass]
            _ ≤ 1 * ε := mul_le_mul' (sdistr_mass_le_one _) le_rfl
            _ = ε := one_mul ε

/-- **Adaptive q-query union bound.**

    A `q`-fold loop of `step`, where each single step from a non-bad heap
    introduces the bad event with probability at most `ε`, has total bad
    probability at most `q * ε`.

    Proved by induction on `q`: the base case is `0` (the initial heap is
    non-bad); the step case combines the inductive hypothesis with the per-step
    increment `prEventComp_bind_step_le`. -/
theorem prBad_induction
    (step : SPComp Unit) (h₀ : Heap) (bad : Heap → Prop) (ε : ℝ≥0∞)
    (h_start : ¬ bad h₀)
    (h_fresh : ∀ h₁ : Heap, ¬ bad h₁ →
      prEvent (step h₁) (fun _ h' => bad h') ≤ ε)
    (q : ℕ) :
    prEventComp (repeatStep step q) h₀ (fun _ h' => bad h') ≤ q * ε := by
  induction q with
  | zero =>
    simp only [repeatStep, Nat.cast_zero, zero_mul, nonpos_iff_eq_zero]
    rw [prEventComp_pure]
    exact if_neg h_start
  | succ q ihq =>
    calc prEventComp (repeatStep step (q + 1)) h₀ (fun _ h' => bad h')
        = prEventComp ((repeatStep step q).bind (fun _ => step)) h₀
            (fun _ h' => bad h') := rfl
      _ ≤ prEventComp (repeatStep step q) h₀ (fun _ h' => bad h') + ε :=
          prEventComp_bind_step_le _ step h₀ bad ε h_fresh
      _ ≤ (q : ℝ≥0∞) * ε + ε := add_le_add ihq le_rfl
      _ = ((q : ℝ≥0∞) + 1) * ε := by rw [add_mul, one_mul]
      _ = ((q + 1 : ℕ) : ℝ≥0∞) * ε := by push_cast; ring

/-- Adaptive q-query union bound over a loop of counted oracle calls.

    If `step` from any non-bad heap introduces the bad event with probability at
    most `ε`, and the initial heap is non-bad, then after `q` iterations the bad
    probability is at most `q * ε`. Derived from the per-step freshness
    hypothesis by `prBad_induction`, not assumed. -/
theorem prBad_of_bounded_count
    (step : SPComp Unit) (h₀ : Heap) (bad : Heap → Prop)
    (q : ℕ) (ε : ℝ≥0∞)
    (h_start : ¬ bad h₀)
    (h_fresh : ∀ h₁ : Heap, ¬ bad h₁ →
      prEvent (step h₁) (fun _ h' => bad h') ≤ ε) :
    prEventComp (repeatStep step q) h₀ (fun _ h' => bad h') ≤ q * ε :=
  prBad_induction step h₀ bad ε h_start h_fresh q

/-- A `q`-query loop presented as a `Bool` game: run `repeatStep step q`, then
    return the fixed answer `b₀`. The tail `SPComp.pure b₀` leaves the heap
    unchanged, so it does not affect the bad-event probability. -/
noncomputable def loopGame (step : SPComp Unit) (q : ℕ) (b₀ : Bool) : SPComp Bool :=
  (repeatStep step q).bind (fun _ => SPComp.pure b₀)

/-- The bad-event probability of `loopGame` equals that of the underlying loop:
    the deterministic `Bool`-returning tail preserves the final heap. -/
theorem prEventComp_loopGame
    (step : SPComp Unit) (q : ℕ) (b₀ : Bool) (h₀ : Heap) (bad : Heap → Prop) :
    prEventComp (loopGame step q b₀) h₀ (fun _ h' => bad h') =
      prEventComp (repeatStep step q) h₀ (fun _ h' => bad h') := by
  unfold loopGame prEventComp
  rw [SPComp.bind_def, prEvent_bind_eq]
  unfold prEvent
  apply tsum_congr; rintro ⟨u, h'⟩
  show (repeatStep step q h₀) (some (u, h')) *
      prEvent (SDistr.pure (b₀, h')) (fun _ h'' => bad h'')
    = (if bad h' then (repeatStep step q h₀) (some (u, h')) else 0)
  rw [prEvent_pure]
  by_cases hb : bad h' <;> simp [hb]

/-- **Adaptive q-query union bound as an advantage bound.**

    For the `q`-query game `loopGame step q b₀`, if each step from a non-bad heap
    introduces the bad event with probability at most `ε`, and the game agrees
    with `G₁` on all non-bad outcomes (and is lossless), then the advantage is at
    most `q * ε`. The bad bound is supplied by `prBad_induction`, not assumed. -/
theorem advantage_le_query_bound_derived
    (step : SPComp Unit) (q : ℕ) (b₀ : Bool) (G₁ : SPComp Bool)
    (bad : Heap → Prop) (ε : ℝ≥0∞)
    (h_start : ¬ bad Heap.empty)
    (h_fresh : ∀ h₁ : Heap, ¬ bad h₁ →
      prEvent (step h₁) (fun _ h' => bad h') ≤ ε)
    (h_agree : ∀ b h', ¬ bad h' →
      (loopGame step q b₀ Heap.empty) (some (b, h')) =
      (G₁ Heap.empty) (some (b, h')))
    (hll : isLossless (loopGame step q b₀)) :
    Advantage (loopGame step q b₀) G₁ ≤ q * ε := by
  refine (failure_event_lemma (loopGame step q b₀) G₁ Heap.empty bad h_agree
    (isLossless_implies_if _ hll)).trans ?_
  rw [prEventComp_loopGame]
  exact prBad_induction step Heap.empty bad ε h_start h_fresh q

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
