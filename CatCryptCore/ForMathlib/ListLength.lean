/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.List.Basic

/-!
# Length bounds of flattened lists

Bounds of the length of a flat map and of a flattened list by the length of its source, for a
function (resp. a list of lists) whose values have length at most `w`. They belong next to
`List.length_flatMap` and `List.length_flatten` in `Init/Data/List/Lemmas.lean` (Lean core) or
in `Mathlib/Data/List/Basic.lean`.

## Main results

* `List.length_flatMap_le_mul` — `(l.flatMap f).length ≤ w * l.length` when every `f a` with
  `a ∈ l` has length at most `w`
* `List.length_flatten_le_mul` — `L.flatten.length ≤ w * L.length` when every member of `L`
  has length at most `w`
-/

@[expose] public section

set_option autoImplicit false

namespace List

variable {α β : Type*}

/-- A flattened list of lists of length at most `w` has length at most `w` times their
number. -/
theorem length_flatten_le_mul {w : ℕ} (L : List (List α)) (hL : ∀ l ∈ L, l.length ≤ w) :
    L.flatten.length ≤ w * L.length := by
  induction L with
  | nil => simp
  | cons l L ih =>
    have h1 := hL l (mem_cons_self ..)
    have h2 := ih fun l' hl' => hL l' (mem_cons_of_mem _ hl')
    simp only [flatten_cons, length_append, length_cons, Nat.mul_succ]
    omega

/-- A flat map by a function whose values on `l` have length at most `w` has length at most
`w` times the length of `l`. -/
theorem length_flatMap_le_mul {f : α → List β} {w : ℕ} (l : List α)
    (hf : ∀ a ∈ l, (f a).length ≤ w) : (l.flatMap f).length ≤ w * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := hf a (mem_cons_self ..)
    have h2 := ih fun a' ha' => hf a' (mem_cons_of_mem _ ha')
    simp only [flatMap_cons, length_append, length_cons, Nat.mul_succ]
    omega

end List
