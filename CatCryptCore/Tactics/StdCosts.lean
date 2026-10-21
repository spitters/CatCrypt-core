/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveCost

/-!
# Derived costs of list and array functions

The costs `f.timedCost` of the list and array functions that reductions use for bookkeeping,
derived by `derive_cost` from the bodies Lean keeps for their equation lemmas, so that
`derive_timed` and `derive_reduction` price their calls. Each cost is bounded by a closed form
in the length of the list or the size of the array; for a function with a function argument
the bound assumes a constant bound `k` on the cost companion of that argument.

`List.lookup` is derived with `BEq.beq` on its local instance at one unit (`derive_cost
(unit := BEq.beq)`), a trusted statement about the equality test of the keys.

An array is its list of elements: `Array.size`, `Array.push` and `Array.getD` are priced by
their definitions through `Array.toList`, so their costs are linear in the size.

## Main results

* `List.append.timedCost_eq` — `List.append.timedCost l₁ l₂ = 2 * l₁.length + 1`
* `List.length.timedCost_eq`, `List.reverse.timedCost_eq`, `Array.size.timedCost_eq`
* `List.take.timedCost_le`, `List.drop.timedCost_le`, `List.getD.timedCost_le`,
  `List.get.timedCost_le`, `List.lookup.timedCost_le`, `List.concat.timedCost_le`,
  `List.replicate.timedCost_le`, `List.range.timedCost_le`, `List.zip.timedCost_le` — linear
  bounds in the length
* `List.map.timedCost_le`, `List.foldl.timedCost_le`, `List.foldr.timedCost_le`,
  `List.zipWith.timedCost_le` — `(k + c) * l.length + 1` for function costs at most `k`
* `Array.push.timedCost_le`, `Array.getD.timedCost_le`, `Array.get!Internal.timedCost_le` —
  linear bounds in the size
* `Finset.sum.timedCost_eq_list`, `Finset.prod.timedCost_eq_list` — the registered cost of a
  sum or product over `s` is that of a fold over `s.toList`
* `Finset.sum.timedCost_le`, `Finset.prod.timedCost_le` — `(k + 1) * s.card` for summand costs
  at most `k`; `Finset.univ.timedCost_fin` — enumerating `Fin n` costs `n`

The panics `panicWithPosWithDecl` and `panicWithPos` (the failing branch of `l[i]!`) are
registered at cost zero beyond the call: the message they build is a diagnostic, not part of
the computation.

The costs of `List.findIdx`, `List.idxOf` and `List.elem` are derived; the last two with
`BEq.beq` at one unit.
-/

@[expose] public section

set_option autoImplicit false

timed_cost panicWithPosWithDecl := fun (α : Sort _) [Inhabited α] (_ _ : String) (_ _ : ℕ)
  (_ : String) => 0

timed_cost panicWithPos := fun (α : Sort _) [Inhabited α] (_ : String) (_ _ : ℕ)
  (_ : String) => 0

derive_cost List.append
derive_cost List.length
derive_cost List.take
derive_cost List.drop
derive_cost List.get?Internal
derive_cost List.getD
derive_cost (unit := BEq.beq) List.lookup
derive_cost List.map
derive_cost List.foldl
derive_cost List.foldr
derive_cost List.reverseAux
derive_cost List.reverse
derive_cost List.concat
derive_cost List.get
derive_cost Array.push
derive_cost Array.size
derive_cost Array.getD
derive_cost List.get!Internal
derive_cost Array.get!Internal
derive_cost List.replicate
derive_cost List.zipWith
derive_cost List.zip
derive_cost List.range.loop
derive_cost List.range

section

variable {α β γ : Type}

/-- Appending costs two units per element of the first list and one more. -/
theorem List.append.timedCost_eq (l₁ l₂ : List α) :
    List.append.timedCost l₁ l₂ = 2 * l₁.length + 1 := by
  induction l₁ with
  | nil => simp [List.append.timedCost]
  | cons a l ih => simp [List.append.timedCost, ih]; omega

/-- The length costs three units per element and one more. -/
theorem List.length.timedCost_eq (l : List α) :
    List.length.timedCost l = 3 * l.length + 1 := by
  induction l with
  | nil => simp [List.length.timedCost]
  | cons a l ih => simp [List.length.timedCost, ih]; omega

/-- A prefix costs at most two units per element and one more. -/
theorem List.take.timedCost_le (n : ℕ) (l : List α) :
    List.take.timedCost n l ≤ 2 * l.length + 1 := by
  induction l generalizing n with
  | nil => cases n <;> simp [List.take.timedCost]
  | cons a l ih =>
    cases n
    · simp [List.take.timedCost]
    · have := ih ‹_›; simp [List.take.timedCost]; omega

/-- A suffix costs at most two units per element and one more. -/
theorem List.drop.timedCost_le (n : ℕ) (l : List α) :
    List.drop.timedCost n l ≤ 2 * l.length + 1 := by
  induction l generalizing n with
  | nil => cases n <;> simp [List.drop.timedCost]
  | cons a l ih =>
    cases n
    · simp [List.drop.timedCost]
    · have := ih ‹_›; simp [List.drop.timedCost]; omega

/-- The optional lookup `l[i]?` costs at most two units per element and one more. -/
theorem List.get?Internal.timedCost_le (l : List α) (i : ℕ) :
    List.get?Internal.timedCost l i ≤ 2 * l.length + 1 := by
  induction l generalizing i with
  | nil => cases i <;> simp [List.get?Internal.timedCost]
  | cons a l ih =>
    cases i
    · simp [List.get?Internal.timedCost]
    · have := ih ‹_›; simp [List.get?Internal.timedCost]; omega

/-- The lookup with a default costs at most two units per element and four more. -/
theorem List.getD.timedCost_le (l : List α) (i : ℕ) (d : α) :
    List.getD.timedCost l i d ≤ 2 * l.length + 4 := by
  have := List.get?Internal.timedCost_le l i
  simp only [List.getD.timedCost]
  split <;> omega

/-- The lookup in an association list costs at most five units per entry and one more, with
each key comparison at one unit. -/
theorem List.lookup.timedCost_le [BEq α] (a : α) (l : List (α × β)) :
    List.lookup.timedCost a l ≤ 5 * l.length + 1 := by
  induction l with
  | nil => simp [List.lookup.timedCost]
  | cons p l ih => simp [List.lookup.timedCost]; split <;> omega

/-- Mapping a function of cost at most `k` costs at most `k + 3` per element and one more. -/
theorem List.map.timedCost_le (f : α → β) (fCost : α → ℕ) {k : ℕ} (hf : ∀ a, fCost a ≤ k)
    (l : List α) : List.map.timedCost f fCost l ≤ (k + 3) * l.length + 1 := by
  induction l with
  | nil => simp [List.map.timedCost]
  | cons a l ih => have := hf a; simp [List.map.timedCost, Nat.mul_succ]; omega

/-- A left fold with a step of cost at most `k` costs at most `k + 3` per element and one
more. -/
theorem List.foldl.timedCost_le (f : α → β → α) (fCost : α → β → ℕ) {k : ℕ}
    (hf : ∀ a b, fCost a b ≤ k) (init : α) (l : List β) :
    List.foldl.timedCost f fCost init l ≤ (k + 3) * l.length + 1 := by
  induction l generalizing init with
  | nil => simp [List.foldl.timedCost]
  | cons b l ih =>
    have := hf init b; have := ih (f init b)
    simp [List.foldl.timedCost, Nat.mul_succ]; omega

/-- A right fold with a step of cost at most `k` costs at most `k + 4` per element and one
more. -/
theorem List.foldr.timedCost_le (f : α → β → β) (fCost : α → β → ℕ) {k : ℕ}
    (hf : ∀ a b, fCost a b ≤ k) (init : β) (l : List α) :
    List.foldr.timedCost f fCost init l ≤ (k + 4) * l.length + 1 := by
  induction l with
  | nil => simp [List.foldr.timedCost]
  | cons a l ih =>
    have := hf a (List.foldr f init l)
    simp [List.foldr.timedCost, Nat.mul_succ]; omega

/-- Reversing onto an accumulator costs two units per element and one more. -/
theorem List.reverseAux.timedCost_eq (l r : List α) :
    List.reverseAux.timedCost l r = 2 * l.length + 1 := by
  induction l generalizing r with
  | nil => simp [List.reverseAux.timedCost]
  | cons a l ih => simp [List.reverseAux.timedCost, ih]; omega

/-- Reversing costs two units per element and two more. -/
theorem List.reverse.timedCost_eq (l : List α) :
    List.reverse.timedCost l = 2 * l.length + 2 := by
  simp [List.reverse.timedCost, List.reverseAux.timedCost_eq]; omega

/-- Appending one element costs at most two units per element and one more. -/
theorem List.concat.timedCost_le (l : List α) (a : α) :
    List.concat.timedCost l a ≤ 2 * l.length + 1 := by
  induction l with
  | nil => simp [List.concat.timedCost]
  | cons b l ih => simp [List.concat.timedCost]; omega

/-- The lookup at an index in range costs at most two units per element and one more. -/
theorem List.get.timedCost_le (l : List α) (i : Fin l.length) :
    List.get.timedCost l i ≤ 2 * l.length + 1 := by
  induction l with
  | nil => exact i.elim0
  | cons b l ih =>
    rcases i with ⟨_ | i, hi⟩
    · simp [List.get.timedCost]
    · have := ih ⟨i, by simpa using hi⟩
      simp [List.get.timedCost]; omega

/-- The size of an array costs three units per element and two more. -/
theorem Array.size.timedCost_eq (a : Array α) :
    Array.size.timedCost a = 3 * a.size + 2 := by
  simp [Array.size.timedCost, List.length.timedCost_eq]; omega

/-- Pushing an element costs at most two units per element and two more. -/
theorem Array.push.timedCost_le (a : Array α) (v : α) :
    Array.push.timedCost a v ≤ 2 * a.size + 2 := by
  have := List.concat.timedCost_le a.toList v
  simp only [Array.push.timedCost, Array.length_toList] at *; omega

/-- The lookup with a default costs at most eight units per element and eight more. -/
theorem Array.getD.timedCost_le (a : Array α) (i : ℕ) (v : α) :
    Array.getD.timedCost a i v ≤ 8 * a.size + 8 := by
  simp only [Array.getD.timedCost, Array.size.timedCost_eq]
  split
  · next h =>
    have := List.get.timedCost_le a.toList ⟨i, by simpa using h⟩
    simp only [Array.length_toList] at this; omega
  · omega

/-- The lookup `a[i]!` costs at most eight units per element and nine more. -/
theorem Array.get!Internal.timedCost_le [Inhabited α] (a : Array α) (i : ℕ) :
    Array.get!Internal.timedCost a i ≤ 8 * a.size + 9 := by
  have := Array.getD.timedCost_le a i default
  simp only [Array.get!Internal.timedCost]; omega

/-- The lookup `l[i]!` costs at most two units per element and four more. -/
theorem List.get!Internal.timedCost_le [Inhabited α] (l : List α) (i : ℕ) :
    List.get!Internal.timedCost l i ≤ 2 * l.length + 4 := by
  induction l generalizing i with
  | nil => cases i <;> simp [List.get!Internal.timedCost, panicWithPosWithDecl.timedCost]
  | cons a l ih =>
    cases i
    · simp [List.get!Internal.timedCost]
    · have := ih ‹_›; simp [List.get!Internal.timedCost]; omega

/-- `n` copies cost at most three units each and one more. -/
theorem List.replicate.timedCost_le (n : ℕ) (a : α) :
    List.replicate.timedCost n a ≤ 3 * n + 1 := by
  induction n with
  | zero => simp [List.replicate.timedCost]
  | succ n ih => simp [List.replicate.timedCost]; omega

/-- Zipping with a function of cost at most `k` costs at most `k + 3` per element of the first
list and one more. -/
theorem List.zipWith.timedCost_le (f : α → β → γ) (fCost : α → β → ℕ) {k : ℕ}
    (hf : ∀ a b, fCost a b ≤ k) (l₁ : List α) (l₂ : List β) :
    List.zipWith.timedCost f fCost l₁ l₂ ≤ (k + 3) * l₁.length + 1 := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp [List.zipWith.timedCost]
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp [List.zipWith.timedCost]
    | cons b l₂ =>
      have := hf a b; have := ih l₂
      simp [List.zipWith.timedCost, Nat.mul_succ]; omega

/-- Zipping costs at most three units per element of the first list and two more. -/
theorem List.zip.timedCost_le (l₁ : List α) (l₂ : List β) :
    List.zip.timedCost l₁ l₂ ≤ 3 * l₁.length + 2 := by
  have := List.zipWith.timedCost_le Prod.mk (fun _ _ => 0) (k := 0) (fun _ _ => le_rfl) l₁ l₂
  simp only [List.zip.timedCost] at *; omega

/-- The loop of `List.range` costs at most four units per step and one more. -/
theorem List.range.loop.timedCost_le (n : ℕ) (l : List ℕ) :
    List.range.loop.timedCost n l ≤ 4 * n + 1 := by
  induction n generalizing l with
  | zero => simp [List.range.loop.timedCost]
  | succ n ih => have := ih (n :: l); simp [List.range.loop.timedCost]; omega

/-- `List.range n` costs at most four units per element and two more. -/
theorem List.range.timedCost_le (n : ℕ) :
    List.range.timedCost n ≤ 4 * n + 2 := by
  have := List.range.loop.timedCost_le n []
  simp only [List.range.timedCost]; omega

end

/-! ## Finite sums and enumerations

Registered costs: enumerating `Finset.univ` costs one unit per element of the type and
enumerating `Finset.range n` costs `n` units; a sum or a product over `s` costs, beyond the
call and the enumeration of `s`, one unit and the cost of the summand per element. The cost of
a sum is that of a fold over any list enumerating `s` (`Finset.sum.timedCost_eq_list`), so it
is well defined on the quotient. -/

timed_cost Finset.univ := fun (α : Type _) [Fintype α] => Fintype.card α

timed_cost Finset.range := fun (n : ℕ) => n

timed_cost Finset.sum := fun (α β : Type _) [AddCommMonoid β] (s : Finset α) (_f : α → β)
  (fCost : α → ℕ) => ∑ i ∈ s, (1 + fCost i)

timed_cost Finset.prod := fun (α β : Type _) [CommMonoid β] (s : Finset α) (_f : α → β)
  (fCost : α → ℕ) => ∑ i ∈ s, (1 + fCost i)

section

variable {α β : Type*}

/-- The cost of a sum is the cost of a fold over any list enumerating `s`. -/
theorem Finset.sum.timedCost_eq_list [AddCommMonoid β] (s : Finset α) (f : α → β)
    (fCost : α → ℕ) :
    Finset.sum.timedCost α β s f fCost = (s.toList.map fun i => 1 + fCost i).sum := by
  grind only [Finset.sum.timedCost, = Finset.sum_map_toList]

/-- The cost of a product is the cost of a fold over any list enumerating `s`. -/
theorem Finset.prod.timedCost_eq_list [CommMonoid β] (s : Finset α) (f : α → β)
    (fCost : α → ℕ) :
    Finset.prod.timedCost α β s f fCost = (s.toList.map fun i => 1 + fCost i).sum := by
  grind only [Finset.prod.timedCost, = Finset.sum_map_toList]

/-- With summands of cost at most `k`, a sum costs at most `k + 1` units per element. -/
theorem Finset.sum.timedCost_le [AddCommMonoid β] (s : Finset α) (f : α → β)
    (fCost : α → ℕ) {k : ℕ} (hf : ∀ i, fCost i ≤ k) :
    Finset.sum.timedCost α β s f fCost ≤ (k + 1) * s.card := by
  simp only [Finset.sum.timedCost]
  exact (Finset.sum_le_sum fun i _ => (by have := hf i; omega : 1 + fCost i ≤ k + 1)).trans
    (by simp [mul_comm])

/-- With factors of cost at most `k`, a product costs at most `k + 1` units per element. -/
theorem Finset.prod.timedCost_le [CommMonoid β] (s : Finset α) (f : α → β)
    (fCost : α → ℕ) {k : ℕ} (hf : ∀ i, fCost i ≤ k) :
    Finset.prod.timedCost α β s f fCost ≤ (k + 1) * s.card := by
  simp only [Finset.prod.timedCost]
  exact (Finset.sum_le_sum fun i _ => (by have := hf i; omega : 1 + fCost i ≤ k + 1)).trans
    (by simp [mul_comm])

/-- Enumerating `Fin n` costs `n` units. -/
theorem Finset.univ.timedCost_fin (n : ℕ) : Finset.univ.timedCost (Fin n) = n := by
  simp [Finset.univ.timedCost]

end

derive_cost List.findIdx.go
derive_cost List.findIdx
derive_cost (unit := BEq.beq) List.idxOf
derive_cost (unit := BEq.beq) List.elem
