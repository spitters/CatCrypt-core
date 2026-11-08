/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.Nat.Find
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.Range

/-!
# Bounded search and unique-witness choice as list computations

Two classical definitions have computable list forms.

* The least witness `Nat.find` of a decidable predicate on `ℕ` with a witness bound `b` is the
  first hit of `find?` on `List.range (b + 1)`, with default `0`.
* The `Classical.choose` of a unique witness of a predicate whose witnesses lie in a list `L` is
  the sole element of `(L.filter p).dedup`.

## Main results

* `leastOr0_eq` — the bounded search equals the classical least witness (or `0`)
* `findIdx_range_succ_le` — the bounded search inspects at most `b + 1` elements
* `chooseOpt_eq_filter_dedup` — unique-witness choice equals the singleton filter match
* `length_filter_dedup_le` — the list searched by the unique-witness form has length at most
  that of `L`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCryptCore.ForMathlib

/-- The bounded search over `List.range (b + 1)` equals the classical least witness of `P`, or
`0` when there is none, provided every witness is dominated by a witness at most `b`. -/
theorem leastOr0_eq (P : Nat → Prop) [DecidablePred P] (b : Nat)
    (hb : ∀ k, P k → ∃ j, j ≤ b ∧ P j) :
    (((List.range (b + 1)).find? (fun k => decide (P k))).getD 0) =
      (by classical exact if h : ∃ k, P k then Nat.find h else 0) := by
  classical
  by_cases h : ∃ k, P k
  · rw [dite_eq_left_of_eq_true (eq_true h)]
    obtain ⟨k, hk⟩ := h
    obtain ⟨j, hjb, hj⟩ := hb k hk
    have hex : ∃ k, P k := ⟨j, hj⟩
    have hle : Nat.find hex ≤ j := Nat.find_min' hex hj
    have hfb : Nat.find hex < b + 1 := by omega
    have hP : P (Nat.find hex) := Nat.find_spec hex
    have hdec : ∀ i, i < Nat.find hex → ¬ P i := fun i hi => Nat.find_min hex hi
    have hmem : (List.range (b + 1)).find? (fun k => decide (P k)) = some (Nat.find hex) := by
      rw [List.find?_eq_some_iff_getElem]
      refine ⟨by simpa using hP, Nat.find hex, ?_⟩
      refine ⟨by simpa using hfb, by simp, ?_⟩
      intro i hi
      have : ¬ P i := hdec i hi
      simpa using this
    simp [hmem]
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    have hnone : (List.range (b + 1)).find? (fun k => decide (P k)) = none := by
      rw [List.find?_eq_none]
      intro x _ hx
      exact h ⟨x, by simpa using hx⟩
    simp [hnone]

/-- The bounded search inspects at most `b + 1` elements of `List.range (b + 1)`. -/
theorem findIdx_range_succ_le (q : Nat → Bool) (b : Nat) :
    (List.range (b + 1)).findIdx q ≤ b + 1 := by
  grind [List.findIdx_le_length]

/-- Choice of the unique witness of `p`, whose witnesses lie in `L`, equals the match on the
deduplicated filter of `L`. -/
theorem chooseOpt_eq_filter_dedup {α : Type*} [DecidableEq α] (p : α → Prop) [DecidablePred p]
    (L : List α) (hL : ∀ a, p a → a ∈ L) :
    (by classical exact if h : ∃! a, p a then some h.exists.choose else none) =
      (match (L.filter (fun a => decide (p a))).dedup with
        | [a] => some a
        | _ => none) := by
  classical
  by_cases h : ∃! a, p a
  · rw [dite_eq_left_of_eq_true (eq_true h)]
    obtain ⟨a, ha, huniq⟩ := id h
    have hc : (ExistsUnique.exists h).choose = a :=
      huniq _ (Classical.choose_spec (ExistsUnique.exists h))
    have hl : (L.filter (fun a => decide (p a))).dedup = [a] := by
      have hnd : (L.filter (fun a => decide (p a))).dedup.Nodup := List.nodup_dedup _
      have hmem : ∀ x, x ∈ (L.filter (fun a => decide (p a))).dedup ↔ x = a := by
        intro x
        simp only [List.mem_dedup, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro ⟨_, hx⟩
          exact huniq x hx
        · rintro rfl
          exact ⟨hL _ ha, ha⟩
      generalize (L.filter (fun a => decide (p a))).dedup = l at hnd hmem
      match l, hnd, hmem with
      | [], _, hm => exact absurd ((hm a).2 rfl) (by simp)
      | [x], _, hm => simp [(hm x).1 (by simp)]
      | x :: y :: t, hn, hm =>
        have hx := (hm x).1 (by simp)
        have hy := (hm y).1 (by simp)
        subst hx; subst hy
        simp at hn
    rw [hl, hc]
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    cases hl : (L.filter (fun a => decide (p a))).dedup with
    | nil => rfl
    | cons x t =>
      cases t with
      | cons y t' => rfl
      | nil =>
        exfalso
        apply h
        have hx : x ∈ (L.filter (fun a => decide (p a))).dedup := by rw [hl]; simp
        simp only [List.mem_dedup, List.mem_filter, decide_eq_true_eq] at hx
        refine ⟨x, hx.2, fun y hy => ?_⟩
        have hy' : y ∈ (L.filter (fun a => decide (p a))).dedup := by
          simp only [List.mem_dedup, List.mem_filter, decide_eq_true_eq]
          exact ⟨hL y hy, hy⟩
        rw [hl] at hy'
        simpa using hy'

/-- The deduplicated filter of `L` has length at most `L.length`. -/
theorem length_filter_dedup_le {α : Type*} [DecidableEq α] (q : α → Bool) (L : List α) :
    (L.filter q).dedup.length ≤ L.length := by
  grind [List.length_filter_le, List.Sublist.length_le, List.dedup_sublist]

end CatCryptCore.ForMathlib
