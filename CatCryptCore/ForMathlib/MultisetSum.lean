/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.Multiset.Bind

/-!
# Multisets over a sum

A multiset over `α ⊕ β` is the sum of its left part and its right part, and a sum of a multiset
of left elements and a multiset of right elements has these as its parts. These facts give the
Seely isomorphism `!(P × Q) ≅ !P ⊗ !Q` of the multiset comonad and the contraction rule of the
Gödel fibration of the Diller–Nahm category (`CatCryptCore.Container.GodelFibration`).

## Main results

* `Multiset.map_filterMap_getLeft_add_getRight` — a multiset over a sum is the sum of its parts;
* `Multiset.filterMap_getLeft_map_add`, `Multiset.filterMap_getRight_map_add` — the parts of a
  sum of left and right elements;
* `Multiset.filterMap_const_none` — filtering by the constant `none` gives `0`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Multiset

variable {α β : Type u}

/-- A multiset over a sum is the sum of its left part and its right part. -/
theorem map_filterMap_getLeft_add_getRight (m : Multiset (α ⊕ β)) :
    (m.filterMap Sum.getLeft?).map Sum.inl + (m.filterMap Sum.getRight?).map Sum.inr = m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    cases a <;> simp [Multiset.filterMap_cons, Sum.getLeft?, Sum.getRight?, Multiset.add_cons,
      Multiset.cons_add, ih]

/-- Filtering by the constant `none` gives the empty multiset. -/
theorem filterMap_const_none (s : Multiset α) :
    s.filterMap (fun _ => (none : Option β)) = 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.filterMap_cons_none, ih]

/-- The left part of a sum of multisets of left and right elements. -/
theorem filterMap_getLeft_map_add (a : Multiset α) (b : Multiset β) :
    (a.map Sum.inl + b.map Sum.inr).filterMap Sum.getLeft? = a := by
  simp [Multiset.filterMap_add, Multiset.filterMap_map, Function.comp_def, filterMap_const_none]

/-- The right part of a sum of multisets of left and right elements. -/
theorem filterMap_getRight_map_add (a : Multiset α) (b : Multiset β) :
    (a.map Sum.inl + b.map Sum.inr).filterMap Sum.getRight? = b := by
  simp [Multiset.filterMap_add, Multiset.filterMap_map, Function.comp_def, filterMap_const_none]

end Multiset

end
