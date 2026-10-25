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
* `List.flatten.timedCost_le` — `(2 w + 4) * L.length + 1` for lists of length at most `w`
* `Fin.foldr.loop.timedCost_le` — the loop of `Fin.foldr` from index `i` costs at most
  `(k + 3) * i + 4` for step costs at most `k`
* `Fin.foldl.timedCost_le`, `Fin.foldl.timedCost_const` — the fold over `Fin n` costs at most
  `(k + 3) * n + 1` for step costs at most `k` (a registered cost defined by recursion in the
  order of `Fin.foldl_succ`, so that it does not depend on the definition of `Fin.foldl`)
* `Finset.toList.timedCost_eq` — enumerating `s` costs `s.card + 1`
* `Array.push.timedCost_le`, `Array.getD.timedCost_le`, `Array.get!Internal.timedCost_le` —
  linear bounds in the size
* `Finset.sum.timedCost_eq_list`, `Finset.prod.timedCost_eq_list` — the registered cost of a
  sum or product over `s` is that of a fold over `s.toList`
* `Finset.sum.timedCost_le`, `Finset.prod.timedCost_le` — `(k + 1) * s.card` for summand costs
  at most `k`; `Finset.univ.timedCost_fin` — enumerating `Fin n` costs `n`
* `Finset.empty.timedCost_eq`, `Multiset.cons.timedCost_eq` — the empty set and adding an
  element to a multiset cost one unit

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
derive_cost Fin.foldr.loop
derive_cost List.flatten

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
  omega

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

/-- Flattening a list of lists, each of length at most `w`, costs at most `2 w + 4` units per
list and one more. -/
theorem List.flatten.timedCost_le (w : ℕ) (L : List (List α)) (hL : ∀ l ∈ L, l.length ≤ w) :
    List.flatten.timedCost L ≤ (2 * w + 4) * L.length + 1 := by
  induction L with
  | nil => simp [List.flatten.timedCost]
  | cons l L ih =>
    rw [List.flatten.timedCost.eq_2, List.append.timedCost_eq]
    have h1 := hL l (by simp)
    have h2 := ih fun l' hl' => hL l' (by simp [hl'])
    simp only [List.length_cons]
    nlinarith

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

/-- The loop of `Fin.foldr` (the fold behind `List.ofFn`) from index `i` costs at most `k + 3`
units per remaining index and four more, for step costs at most `k`. -/
theorem Fin.foldr.loop.timedCost_le (n : ℕ) (f : Fin n → α → α) (fCost : Fin n → α → ℕ)
    {k : ℕ} (hf : ∀ i x, fCost i x ≤ k) (i : ℕ) (h : i ≤ n) (x : α) :
    Fin.foldr.loop.timedCost n f fCost i h x ≤ (k + 3) * i + 4 := by
  induction i generalizing x with
  | zero => simp [Fin.foldr.loop.timedCost]
  | succ i ih =>
    simp only [Fin.foldr.loop.timedCost]
    have := ih (by omega) (f ⟨i, h⟩ x)
    have := hf ⟨i, h⟩ x
    grind

end

/-! ## Finite sums and enumerations

Registered costs: enumerating `Finset.univ` costs one unit per element of the type and
enumerating `Finset.range n` costs `n` units; the empty set and adding an element to a
multiset (`Multiset.cons`, the step of a `Finset` literal) cost one unit; removing an element
from `s` costs `s.card` units, one comparison per element; a sum or a product over `s` costs, beyond the
call and the enumeration of `s`, one unit and the cost of the summand per element. The cost of
a sum is that of a fold over any list enumerating `s` (`Finset.sum.timedCost_eq_list`), so it
is well defined on the quotient. -/

timed_cost Finset.univ := fun (α : Type _) [Fintype α] => Fintype.card α

timed_cost Finset.range := fun (n : ℕ) => n

timed_cost Finset.empty := fun (_ : Type _) => 1

timed_cost Multiset.cons := fun (α : Type _) (_a : α) (_s : Multiset α) => 1

timed_cost Finset.erase := fun (α : Type _) [DecidableEq α] (s : Finset α) (_a : α) => s.card

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

/-- The empty set costs one unit. -/
theorem Finset.empty.timedCost_eq (α : Type*) : Finset.empty.timedCost α = 1 := by
  simp [Finset.empty.timedCost]

/-- Adding an element to a multiset costs one unit. -/
theorem Multiset.cons.timedCost_eq (α : Type*) (a : α) (s : Multiset α) :
    Multiset.cons.timedCost α a s = 1 := by
  simp [Multiset.cons.timedCost]

/-- Enumerating `Fin n` costs `n` units. -/
theorem Finset.univ.timedCost_fin (n : ℕ) : Finset.univ.timedCost (Fin n) = n := by
  simp [Finset.univ.timedCost]

end

derive_cost List.findIdx.go
derive_cost List.findIdx
derive_cost (unit := BEq.beq) List.idxOf
derive_cost (unit := BEq.beq) List.elem

timed_cost Finset.toList := fun (α : Type _) (s : Finset α) => s.card + 1

/-! Registered costs of deduplication. Deduplicating a list of length `n` (`List.dedup`, a right
fold of `List.pwFilter`) compares each element with at most `n` kept elements and costs one unit
per element and one more. The cost of `Multiset.toFinset` is that of `List.toFinset` on any list
representing the multiset; it depends on the multiset through its cardinality, so it is well
defined on the quotient. -/
timed_cost List.toFinset := fun (α : Type _) [DecidableEq α] (l : List α) =>
  l.length * (l.length + 1) + 1
timed_cost Multiset.toFinset := fun (α : Type _) [DecidableEq α] (s : Multiset α) =>
  Multiset.card s * (Multiset.card s + 1) + 1

/-- Enumerating `s` as a list costs one unit per element and one more. -/
theorem Finset.toList.timedCost_eq {α : Type*} (s : Finset α) :
    Finset.toList.timedCost α s = s.card + 1 := by
  simp [Finset.toList.timedCost]

/-- The registered cost of `Fin.foldl n f init`, with the cost companion `fCost` of the step
`f`: three units and the step cost per index, in the order of `Fin.foldl_succ`, and one unit
at the end. A registered cost is a trusted statement about the cost of `Fin.foldl`. -/
noncomputable def Fin.foldl.timedCost (α : Sort _) :
    (n : ℕ) → (α → Fin n → α) → (α → Fin n → ℕ) → α → ℕ
  | 0, _, _, _ => 1
  | n + 1, f, fCost, init =>
    fCost init 0 + 3 +
      Fin.foldl.timedCost α n (fun x i => f x i.succ) (fun x i => fCost x i.succ) (f init 0)

section

variable {α : Sort _}

/-- The fold over `Fin 0` costs one unit. -/
theorem Fin.foldl.timedCost_zero (f : α → Fin 0 → α) (fCost : α → Fin 0 → ℕ) (init : α) :
    Fin.foldl.timedCost α 0 f fCost init = 1 := by
  simp [Fin.foldl.timedCost]

/-- The fold over `Fin (n + 1)` costs the step at index `0` and three units more than the fold
of the shifted step over `Fin n` from `f init 0`. -/
theorem Fin.foldl.timedCost_succ (n : ℕ) (f : α → Fin (n + 1) → α)
    (fCost : α → Fin (n + 1) → ℕ) (init : α) :
    Fin.foldl.timedCost α (n + 1) f fCost init =
      fCost init 0 + 3 +
        Fin.foldl.timedCost α n (fun x i => f x i.succ) (fun x i => fCost x i.succ)
          (f init 0) := by
  simp [Fin.foldl.timedCost]

/-- A fold with step costs at most `k` costs at most `k + 3` units per index and one more. -/
theorem Fin.foldl.timedCost_le (n : ℕ) (f : α → Fin n → α) (fCost : α → Fin n → ℕ) {k : ℕ}
    (hf : ∀ x i, fCost x i ≤ k) (init : α) :
    Fin.foldl.timedCost α n f fCost init ≤ (k + 3) * n + 1 := by
  induction n generalizing init with
  | zero => simp [Fin.foldl.timedCost]
  | succ n ih =>
    have h1 := hf init 0
    have h2 := ih (fun x i => f x i.succ) (fun x i => fCost x i.succ)
      (fun x i => hf x i.succ) (f init 0)
    rw [Fin.foldl.timedCost_succ, Nat.mul_succ]; omega

/-- A fold with a step of constant cost `c` costs `c + 3` units per index and one more. -/
theorem Fin.foldl.timedCost_const (n : ℕ) (f : α → Fin n → α) (c : ℕ) (init : α) :
    Fin.foldl.timedCost α n f (fun _ _ => c) init = (c + 3) * n + 1 := by
  induction n generalizing init with
  | zero => simp [Fin.foldl.timedCost]
  | succ n ih =>
    have h := ih (fun x i => f x i.succ) (f init 0)
    rw [Fin.foldl.timedCost_succ, h, Nat.mul_succ]; omega

end
