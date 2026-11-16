/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.StdCosts

/-!
# Costs of list scans bounded on the members scanned

The cost `List.all.timedCost` of `List.all`, derived by `derive_cost`, with its bound linear in
the length, and the member-restricted bounds `f.timedCost_le_mem` of the scans `List.all`,
`List.any`, `List.find?`, `List.findSome?`, `List.filter`, `List.filterMap`, `List.map` and
`List.foldl`: the premise bounds the cost of the function argument only on the members of the
list scanned, `∀ a ∈ l, fCost a ≤ k`, in place of `∀ a, fCost a ≤ k` of `f.timedCost_le`
(`CatCryptCore.Tactics.StdCosts`). A per-element cost that reads the element (a membership test
in a list held by the element) is bounded under a hypothesis on the members of the list, and
`derive_time_bound` reads these bounds after `f.timedCost_eq` and `f.timedCost_le`.

## Main results

* `List.all.timedCost_le` — `(k + 5) * l.length + 1` for predicate costs at most `k`
* `List.all.timedCost_le_mem`, `List.any.timedCost_le_mem` — the same bound for predicate costs
  at most `k` on the members of `l`
* `List.find?.timedCost_le_mem`, `List.findSome?.timedCost_le_mem`,
  `List.filter.timedCost_le_mem`, `List.filterMap.timedCost_le_mem` — `(k + 4) * l.length + 1`
* `List.map.timedCost_le_mem`, `List.foldl.timedCost_le_mem` — `(k + 3) * l.length + 1`
-/

@[expose] public section

set_option autoImplicit false

derive_cost List.all

section

variable {α β : Type}

/-- `List.all` with a predicate of cost at most `k` on each member of the list costs at most
`k + 5` units per element and one more. -/
theorem List.all.timedCost_le_mem (l : List α) (p : α → Bool) (pCost : α → ℕ) {k : ℕ}
    (hp : ∀ a ∈ l, pCost a ≤ k) : List.all.timedCost l p pCost ≤ (k + 5) * l.length + 1 := by
  induction l with
  | nil => simp [List.all.timedCost]
  | cons a l ih =>
    have := hp a List.mem_cons_self
    have := ih fun b hb => hp b (List.mem_cons_of_mem _ hb)
    simp only [List.all.timedCost, List.length_cons] at this ⊢
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-- `List.all` with a predicate of cost at most `k` costs at most `k + 5` units per element and
one more. -/
theorem List.all.timedCost_le (l : List α) (p : α → Bool) (pCost : α → ℕ) {k : ℕ}
    (hp : ∀ a, pCost a ≤ k) : List.all.timedCost l p pCost ≤ (k + 5) * l.length + 1 :=
  List.all.timedCost_le_mem l p pCost fun a _ => hp a

/-- `List.any` with a predicate of cost at most `k` on each member of the list costs at most
`k + 5` units per element and one more. -/
theorem List.any.timedCost_le_mem (l : List α) (p : α → Bool) (pCost : α → ℕ) {k : ℕ}
    (hp : ∀ a ∈ l, pCost a ≤ k) : List.any.timedCost l p pCost ≤ (k + 5) * l.length + 1 := by
  induction l with
  | nil => simp [List.any.timedCost]
  | cons a l ih =>
    have := hp a List.mem_cons_self
    have := ih fun b hb => hp b (List.mem_cons_of_mem _ hb)
    simp only [List.any.timedCost, List.length_cons] at this ⊢
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-- A search with a test of cost at most `k` on each member of the list costs at most `k + 4`
per element and one more. -/
theorem List.find?.timedCost_le_mem (p : α → Bool) (pCost : α → ℕ) {k : ℕ} (l : List α)
    (hp : ∀ a ∈ l, pCost a ≤ k) : List.find?.timedCost p pCost l ≤ (k + 4) * l.length + 1 := by
  induction l with
  | nil => simp [List.find?.timedCost]
  | cons a l ih =>
    have := hp a List.mem_cons_self
    have := ih fun b hb => hp b (List.mem_cons_of_mem _ hb)
    simp [List.find?.timedCost, Nat.mul_succ]
    split <;> omega

/-- `List.findSome?` with a function of cost at most `k` on each member of the list costs at
most `k + 4` per element and one more. -/
theorem List.findSome?.timedCost_le_mem (f : α → Option β) (fCost : α → ℕ) {k : ℕ} (l : List α)
    (hf : ∀ a ∈ l, fCost a ≤ k) :
    List.findSome?.timedCost f fCost l ≤ (k + 4) * l.length + 1 := by
  induction l with
  | nil => simp [List.findSome?.timedCost]
  | cons a l ih =>
    have := hf a List.mem_cons_self
    have := ih fun b hb => hf b (List.mem_cons_of_mem _ hb)
    simp [List.findSome?.timedCost, Nat.mul_succ]
    split <;> omega

/-- Filtering with a predicate of cost at most `k` on each member of the list costs at most
`k + 4` per element and one more. -/
theorem List.filter.timedCost_le_mem (p : α → Bool) (pCost : α → ℕ) {k : ℕ} (l : List α)
    (hp : ∀ a ∈ l, pCost a ≤ k) :
    List.filter.timedCost p pCost l ≤ (k + 4) * l.length + 1 := by
  induction l with
  | nil => simp [List.filter.timedCost]
  | cons a l ih =>
    have := hp a List.mem_cons_self
    have := ih fun b hb => hp b (List.mem_cons_of_mem _ hb)
    simp [List.filter.timedCost, Nat.mul_succ]
    grind

/-- `List.filterMap` with a function of cost at most `k` on each member of the list costs at
most `k + 4` per element and one more. -/
theorem List.filterMap.timedCost_le_mem (f : α → Option β) (fCost : α → ℕ) {k : ℕ}
    (l : List α) (hf : ∀ a ∈ l, fCost a ≤ k) :
    List.filterMap.timedCost f fCost l ≤ (k + 4) * l.length + 1 := by
  induction l with
  | nil => simp [List.filterMap.timedCost]
  | cons a l ih =>
    have := hf a List.mem_cons_self
    have := ih fun b hb => hf b (List.mem_cons_of_mem _ hb)
    simp [List.filterMap.timedCost, Nat.mul_succ]
    grind

/-- Mapping a function of cost at most `k` on each member of the list costs at most `k + 3` per
element and one more. -/
theorem List.map.timedCost_le_mem (f : α → β) (fCost : α → ℕ) {k : ℕ} (l : List α)
    (hf : ∀ a ∈ l, fCost a ≤ k) : List.map.timedCost f fCost l ≤ (k + 3) * l.length + 1 := by
  induction l with
  | nil => simp [List.map.timedCost]
  | cons a l ih =>
    have := hf a List.mem_cons_self
    have := ih fun b hb => hf b (List.mem_cons_of_mem _ hb)
    simp [List.map.timedCost, Nat.mul_succ]
    omega

/-- A left fold with a step of cost at most `k` at each member of the list costs at most `k + 3`
per element and one more. -/
theorem List.foldl.timedCost_le_mem (f : α → β → α) (fCost : α → β → ℕ) {k : ℕ} (l : List β)
    (hf : ∀ a, ∀ b ∈ l, fCost a b ≤ k) (init : α) :
    List.foldl.timedCost f fCost init l ≤ (k + 3) * l.length + 1 := by
  induction l generalizing init with
  | nil => simp [List.foldl.timedCost]
  | cons b l ih =>
    have := hf init b List.mem_cons_self
    have := ih (fun a c hc => hf a c (List.mem_cons_of_mem _ hc)) (f init b)
    simp [List.foldl.timedCost, Nat.mul_succ]
    omega

end
