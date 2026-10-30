/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PAKE.CPaceH1
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Running time of the match-recording reduction

`derive_reduction matchWrap` builds the costed form of the reduction from the CPace
experiment to the double-match game (`CatCryptCore.Crypto.PAKE.CPaceH1`).

## Main results

* `List.find?.timedCost_le` — a search with a test of cost at most `k` costs at most `k + 4`
  per element and one more
* `matchWrap.timeBound_timed` — with the CPace adversary of time at most `T`, at most `q`
  queries and call cost at most `a`, and generator lookups of cost at most `h`: time at most
  `1 + a + (T + q (h + 4)) + 12 (q + 1)²`

## Cost model

The cost model of `derive_timed` on costed oracle adversaries: one unit per node, the stated
time and call cost of the adversary, the stated cost of a generator lookup, and the registered
costs of the list operations of the log search.
-/

@[expose] public section

set_option autoImplicit false

/-! ## The cost of a list search

This section belongs upstream, in `CatCryptCore.Tactics.StdCosts`. -/

derive_cost List.find?

/-- A search with a test of cost at most `k` costs at most `k + 4` per element and one more. -/
theorem List.find?.timedCost_le {β : Type} (p : β → Bool) (pCost : β → ℕ) {k : ℕ}
    (hp : ∀ b, pCost b ≤ k) (l : List β) :
    List.find?.timedCost p pCost l ≤ (k + 4) * l.length + 1 := by
  induction l with
  | nil => simp [List.find?.timedCost]
  | cons b l ih => have := hp b; simp [List.find?.timedCost, Nat.mul_succ]; split <;> omega

namespace CatCrypt.Crypto.PAKE.CPaceH1

open CatCrypt.Core OracleAdv.Timed

derive_reduction matchWrap

/-- **Time of the match-recording reduction.** A CPace adversary of time at most `T` with at
    most `q` queries and call cost at most `a`, with generator lookups of cost at most `h`,
    gives a double-match adversary of time at most `1 + a + (T + q (h + 4)) + 12 (q + 1)²`:
    a constant per query, and the search of the log of at most `q` matches for a double match,
    quadratic in `q`. -/
theorem matchWrap.timeBound_timed {W Pw : Type} [DecidableEq W] [DecidableEq Pw] [Inhabited Pw]
    {α : Type} (A : W → OracleAdv.Timed (Query W Pw) (Answer W) α) (ACost : W → ℕ) (X : W)
    (H : Pw → W) (HCost : Pw → ℕ) {T q a h : ℕ} (hA : ∀ X, (A X).TimeBound T)
    (hq : ∀ X, (A X).erase.IsQueryBound q) (hAc : ∀ X, ACost X ≤ a) (hH : ∀ pw, HCost pw ≤ h) :
    StepTimeBound (matchWrap.timed A ACost X H HCost)
      (1 + a + (T + q * (h + 4)) + 12 * (q + 1) * (q + 1)) := by
  have hstep : ∀ (i : ℕ) (log : MatchLog W Pw) (d : Query W Pw), log.length ≤ i →
      StepTimeBound (delay 1 (wrapImpl.timed H HCost log d)) (h + 4) ∧
        AllRet (fun y => y.2.length ≤ i + 1) (delay 1 (wrapImpl.timed H HCost log d)).2 := by
    intro i log d hl
    rcases d with pw | m
    · have := hH pw
      refine ⟨⟨?_, trivial⟩, ?_⟩
      · simp only [delay, wrapImpl.timed]; omega
      · simp only [delay, wrapImpl.timed, AllRet]; omega
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [delay, wrapImpl.timed]; omega
      · simp only [delay, wrapImpl.timed, timeBound_query_iff]
        exact ⟨by omega, fun r => ⟨by omega, trivial⟩⟩
      · simp only [delay, wrapImpl.timed, AllRet]
        intro r; split <;> grind
  have hsim := timeBound_simulateHat_inv id id
    (fun log d => delay 1 (wrapImpl.timed H HCost log d)) (fun i (log : MatchLog W Pw) =>
      log.length ≤ i) (fun _ => h + 4) (fun i s d hs => hstep i s d hs) (hA X) (hq X) 0 []
    (by simp)
  have hall := allRet_simulateHat_inv id id
    (fun log d => delay 1 (wrapImpl.timed H HCost log d)) (fun i (log : MatchLog W Pw) =>
      log.length ≤ i) (fun i s d hs => (hstep i s d hs).2) (fun i s hs => by omega) (hq X) 0 []
    (by simp)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, zero_add] at hsim hall
  unfold simulateHat at hsim hall
  unfold matchWrap.timed
  obtain ⟨h1, h2⟩ := hsim
  have := hAc X
  refine (stepTimeBound_delay (timeBound_bind_of_allRet (n := 12 * (q + 1) * (q + 1)) h2 hall
    fun x hx => ⟨?_, ?_⟩)).mono (by omega)
  rotate_left
  · trivial
  · have hlp : (logPairs x.2).length = x.2.length * x.2.length := by
      simp [logPairs, List.length_flatMap]
    have e1 := List.find?.timedCost_le (fun p => decide (p.1.2.1 = p.2.2.1 ∧ p.1.1 ≠ p.2.1))
      (fun _ => 1) (k := 1) (fun _ => le_rfl) (logPairs x.2)
    have e2 := List.flatten.timedCost_le x.2.length
      (List.map (fun a => List.map (fun b => (a, b)) x.2) x.2) fun l hl => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hl
        simp
    have e3 := List.map.timedCost_le (fun a => List.map (fun b => (a, b)) x.2)
      (fun a => 1 + List.map.timedCost (fun b => (a, b)) (fun _ => 0) x.2)
      (k := 3 * x.2.length + 2) (fun a => by
        have := List.map.timedCost_le (fun b => (a, b)) (fun _ => 0) (k := 0) (fun _ => le_rfl)
          x.2
        omega) x.2
    simp only [List.length_map, hlp] at e1 e2 e3
    have hnn := Nat.mul_le_mul hx hx
    nlinarith

end CatCrypt.Crypto.PAKE.CPaceH1
