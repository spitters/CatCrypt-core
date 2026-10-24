/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Runtime
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Reasoning API for `Hax.foldRange`

`Hax.foldRange` is the loop form every haxpipe extraction emits, and it is sealed
`@[irreducible]` (unfolding it inside the large `mutual` blocks haxpipeT produces
is what blows past the heartbeat limit). This module is the reasoning interface:
each lemma `unseal`s locally, so downstream proofs never have to.

Four ways to reason about such a loop, in increasing order of what they need:

* `foldRange_step` / `foldRange_stop`, stated in `Runtime` — peel one iteration,
  or finish. Unrolls a concrete-bound loop.
* `foldRange_rel_bounded` — relational congruence, with the step relation
  required only for indices *inside* the range (`Hax.foldRange_rel` in `Runtime`
  demands it everywhere, which is often false at out-of-range indices).
* `foldRange_induct` — a running-index invariant `P i acc`, for when the
  post-condition mentions how far the loop has got.
* `foldRange_finFoldl_rel` — bridges an extraction loop to a reference stated
  with `Fin.foldl`, which is how the clean specs are written.

For the index-writing fold `foldRange 0 hi acc (fun i r => array_update r i (g i))`,
the form of every extracted pointwise array operation, `size_foldRange_update` and
`index_foldRange_update` give its size and its entries.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax

variable {α β : Type}

/-! ## Unrolling

`Hax.foldRange_step` and `Hax.foldRange_stop` (peel one iteration, or finish) are
stated in `HaxLean.Runtime`. -/

/-- Reindex the step function by shifting both endpoints. -/
theorem go_shift (fa : Int → α → α) :
    ∀ (m : Nat) (s : Int) (b : α),
      Hax.foldRange.go fa m (s + 1) b = Hax.foldRange.go (fun i => fa (i + 1)) m s b := by
  intro m
  induction m with
  | zero => intro s b; rfl
  | succ m ih =>
    intro s b
    show Hax.foldRange.go fa m (s + 1 + 1) (fa (s + 1) b)
        = Hax.foldRange.go (fun i => fa (i + 1)) m (s + 1) (fa (s + 1) b)
    exact ih (s + 1) (fa (s + 1) b)

unseal Hax.foldRange in
/-- Shift both endpoints by one, reindexing the step. -/
theorem foldRange_shift (lo hi : Int) (b : α) (fa : Int → α → α) :
    Hax.foldRange (lo + 1) (hi + 1) b fa
      = Hax.foldRange lo hi b (fun i => fa (i + 1)) := by
  show Hax.foldRange.go fa ((hi + 1) - (lo + 1)).toNat (lo + 1) b
      = Hax.foldRange.go (fun i => fa (i + 1)) (hi - lo).toNat lo b
  have he : ((hi + 1) - (lo + 1)).toNat = (hi - lo).toNat := by omega
  rw [he]; exact go_shift fa (hi - lo).toNat lo b

/-! ## Relational congruence and invariants -/

unseal Hax.foldRange in
/-- Relational congruence needing the step relation only on `[lo, hi)`. -/
theorem foldRange_rel_bounded {R : α → β → Prop} {lo hi : Int}
    {fa : Int → α → α} {fb : Int → β → β} {ia : α} {ib : β}
    (h0 : R ia ib)
    (hstep : ∀ i, lo ≤ i → i < hi → ∀ a b, R a b → R (fa i a) (fb i b)) :
    R (Hax.foldRange lo hi ia fa) (Hax.foldRange lo hi ib fb) := by
  show R (Hax.foldRange.go fa (hi - lo).toNat lo ia) (Hax.foldRange.go fb (hi - lo).toNat lo ib)
  suffices H : ∀ (n : Nat) (s : Int) a b, lo ≤ s → s + n ≤ hi → R a b →
      R (Hax.foldRange.go fa n s a) (Hax.foldRange.go fb n s b) by
    by_cases hle : lo ≤ hi
    · exact H _ lo ia ib (le_refl _) (by omega) h0
    · rw [show (hi - lo).toNat = 0 from by omega]; exact h0
  intro n
  induction n with
  | zero => intro s a b _ _ hab; exact hab
  | succ n ih =>
    intro s a b hs hsn hab
    show R (Hax.foldRange.go fa n (s + 1) (fa s a)) (Hax.foldRange.go fb n (s + 1) (fb s b))
    exact ih (s + 1) (fa s a) (fb s b) (by omega) (by omega) (hstep s hs (by omega) a b hab)

unseal Hax.foldRange in
/-- A running-index invariant: `P lo` of the initial value, advanced by each
    in-range step, yields `P hi` of the fold. -/
theorem foldRange_induct {P : Int → α → Prop} {lo hi : Int}
    {f : Int → α → α} {init : α} (hle : lo ≤ hi) (h0 : P lo init)
    (hstep : ∀ i a, lo ≤ i → i < hi → P i a → P (i + 1) (f i a)) :
    P hi (Hax.foldRange lo hi init f) := by
  show P hi (Hax.foldRange.go f (hi - lo).toNat lo init)
  suffices H : ∀ (n : Nat) (s : Int) a, lo ≤ s → s + n = hi → P s a →
      P hi (Hax.foldRange.go f n s a) by
    exact H _ lo init (le_refl _) (by omega) h0
  intro n
  induction n with
  | zero => intro s a _ hsn ha; rw [show hi = s by omega]; exact ha
  | succ n ih =>
    intro s a hs hsn ha
    show P hi (Hax.foldRange.go f n (s + 1) (f s a))
    exact ih (s + 1) (f s a) (by omega) (by omega) (hstep s a hs (by omega) ha)

/-! ## Bridging to a `Fin.foldl` reference -/

/-- `foldRange 0 0` with a `Nat`-cast bound. -/
theorem foldRange_zero_cast (ia : α) (fa : Int → α → α) :
    Hax.foldRange 0 ((0 : Nat) : Int) ia fa = ia := by
  rw [Nat.cast_zero]; exact foldRange_stop 0 0 ia fa (by norm_num)

/-- Peel the first index off `foldRange 0 (n+1)` with a `Nat`-cast bound. -/
theorem foldRange_succ_cast (n : Nat) (ia : α) (fa : Int → α → α) :
    Hax.foldRange 0 ((n + 1 : Nat) : Int) ia fa
      = Hax.foldRange 0 ((n : Nat) : Int) (fa 0 ia) (fun i => fa (i + 1)) := by
  rw [show ((n + 1 : Nat) : Int) = ((n : Nat) : Int) + 1 by push_cast; ring,
      foldRange_step 0 (((n : Nat) : Int) + 1) ia fa (by omega)]
  exact foldRange_shift 0 ((n : Nat) : Int) (fa 0 ia) fa

/-- Relate an extraction's `foldRange 0 n` to a reference's `Fin.foldl n`: both
    visit `0, 1, …, n-1` in order, so per-index step compatibility suffices. -/
theorem foldRange_finFoldl_rel {R : α → β → Prop} :
    ∀ (n : Nat) {fa : Int → α → α} {gb : β → Fin n → β} {ia : α} {ib : β},
      R ia ib →
      (∀ (i : Nat) (hi : i < n) a b, R a b → R (fa (i : Int) a) (gb b ⟨i, hi⟩)) →
      R (Hax.foldRange 0 (n : Int) ia fa) (Fin.foldl n gb ib) := by
  intro n
  induction n with
  | zero =>
    intro fa gb ia ib h0 _
    rw [foldRange_zero_cast, Fin.foldl_zero]; exact h0
  | succ n ih =>
    intro fa gb ia ib h0 hstep
    rw [foldRange_succ_cast, Fin.foldl_succ]
    refine ih (fa := fun i => fa (i + 1)) (gb := fun x i => gb x i.succ)
      (ia := fa 0 ia) (ib := gb ib 0) ?_ ?_
    · have := hstep 0 (Nat.zero_lt_succ n) ia ib h0
      simpa using this
    · intro i hi a b hab
      have := hstep (i + 1) (Nat.succ_lt_succ hi) a b hab
      simpa [Fin.succ, Nat.add_comm] using this

/-! ## Index-writing folds

A fold whose step writes `g i` at the loop index `i`, the form of every pointwise
array operation in an extraction. -/

/-- The index-writing fold worker preserves the accumulator size. -/
theorem go_update_size (g : Int → α) :
    ∀ (n i0 : Nat) (acc : Array α),
      (Hax.foldRange.go (fun i r => Hax.array_update r i (g i)) n (i0 : Int) acc).size
        = acc.size := by
  intro n
  induction n with
  | zero => intro i0 acc; rfl
  | succ n ih =>
    intro i0 acc
    show (Hax.foldRange.go (fun i r => Hax.array_update r i (g i)) n ((i0 : Int) + 1)
          (Hax.array_update acc (i0 : Int) (g (i0 : Int)))).size = _
    rw [show ((i0 : Int) + 1) = ((i0 + 1 : Nat) : Int) by push_cast; ring,
      ih (i0 + 1), size_array_update_eq]

/-- The index-writing fold worker stores `g j` at every visited in-bounds position
    `j` and leaves every other position at its accumulator value. -/
theorem go_update_getElem? (g : Int → α) :
    ∀ (n i0 : Nat) (acc : Array α) (j : Nat),
      (Hax.foldRange.go (fun i r => Hax.array_update r i (g i)) n (i0 : Int) acc)[j]?
        = if i0 ≤ j ∧ j < i0 + n ∧ j < acc.size then some (g (j : Int)) else acc[j]? := by
  intro n
  induction n with
  | zero =>
    intro i0 acc j
    rw [ite_eq_right (by omega)]; rfl
  | succ n ih =>
    intro i0 acc j
    show (Hax.foldRange.go (fun i r => Hax.array_update r i (g i)) n ((i0 : Int) + 1)
          (Hax.array_update acc (i0 : Int) (g (i0 : Int))))[j]? = _
    rw [show ((i0 : Int) + 1) = ((i0 + 1 : Nat) : Int) by push_cast; ring,
      ih (i0 + 1), size_array_update_eq]
    have hset : (Hax.array_update acc (i0 : Int) (g (i0 : Int)))[j]?
        = if i0 = j then (if i0 < acc.size then some (g (i0 : Int)) else none)
          else acc[j]? := by
      show (acc.setIfInBounds (i0 : Int).toNat (g (i0 : Int)))[j]? = _
      rw [Int.toNat_natCast]
      exact Array.getElem?_setIfInBounds
    rw [hset]
    rcases Nat.lt_trichotomy i0 j with h | h | h
    · by_cases hO : j < i0 + 1 + n ∧ j < acc.size
      · rw [ite_eq_left ⟨by omega, hO.1, hO.2⟩, ite_eq_left ⟨by omega, by omega, hO.2⟩]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    · subst h
      rw [ite_eq_right (by omega), ite_eq_left rfl]
      by_cases hs : i0 < acc.size
      · rw [ite_eq_left hs, ite_eq_left ⟨le_refl _, by omega, hs⟩]
      · rw [ite_eq_right hs, ite_eq_right (by omega), Array.getElem?_eq_none (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

unseal Hax.foldRange in
/-- The index-writing fold over `[0, hi)` preserves the accumulator size. -/
theorem size_foldRange_update (g : Int → α) (hi : Int) (acc : Array α) :
    (Hax.foldRange 0 hi acc (fun i r => Hax.array_update r i (g i))).size = acc.size :=
  go_update_size g _ 0 acc

unseal Hax.foldRange in
/-- The index-writing fold over `[0, hi)` stores `g j` at every in-bounds position
    `j < hi`. -/
theorem getElem?_foldRange_update (g : Int → α) (hi : Int) (acc : Array α) (j : Nat)
    (hj : (j : Int) < hi) (hacc : j < acc.size) :
    (Hax.foldRange 0 hi acc (fun i r => Hax.array_update r i (g i)))[j]?
      = some (g (j : Int)) := by
  have H := go_update_getElem? g (hi - 0).toNat 0 acc j
  rw [ite_eq_left ⟨Nat.zero_le _, by omega, hacc⟩] at H
  exact H

/-- `Hax.index` of the index-writing fold over `[0, hi)` at an in-bounds position
    `j < hi` is `g j`. -/
theorem index_foldRange_update [Inhabited α] (g : Int → α) (hi : Int) (acc : Array α)
    (j : Nat) (hj : (j : Int) < hi) (hacc : j < acc.size) :
    Hax.index (Hax.foldRange 0 hi acc (fun i r => Hax.array_update r i (g i))) (j : Int)
      = g (j : Int) := by
  have hjs : j < (Hax.foldRange 0 hi acc (fun i r => Hax.array_update r i (g i))).size := by
    rw [size_foldRange_update]; exact hacc
  rw [index_eq_getElem (by simpa using hjs), ← Option.some_inj]
  simp only [Int.toNat_natCast]
  rw [← Array.getElem?_eq_getElem hjs, getElem?_foldRange_update g hi acc j hj hacc]

/-- `Hax.index` at an in-bounds natural index is `getElem`. -/
theorem index_natCast [Inhabited α] (a : Array α) (i : Nat) (h : i < a.size) :
    Hax.index a (i : Int) = a[i] := by
  rw [index_eq_getElem (by simpa using h)]
  simp

/-- At an in-bounds position the container read `Array.getD` and `Hax.index` agree,
    whatever the default. -/
theorem getD_eq_index [Inhabited α] (arr : Array α) (i : Nat) (d : α) (h : i < arr.size) :
    arr.getD i d = Hax.index arr (i : Int) := by
  rw [index_natCast arr i h]
  simp [Array.getD, h]

/-- Two arrays of length `n` with the same `Hax.index` reads below `n` are equal. -/
theorem ext_index [Inhabited α] {a b : Array α} (n : Nat) (ha : a.size = n) (hb : b.size = n)
    (h : ∀ i : Nat, i < n → Hax.index a (i : Int) = Hax.index b (i : Int)) : a = b := by
  apply Array.ext (ha.trans hb.symm)
  intro i hia hib
  rw [← index_natCast a i hia, ← index_natCast b i hib]
  exact h i (ha ▸ hia)

end Hax
