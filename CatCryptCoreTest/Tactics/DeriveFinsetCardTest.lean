/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.StdCosts
public import CatCryptCore.Core.SPTree

/-!
# Tests for the registered cost of `Finset.card`

The cardinality of a finite set is priced by its registered cost, one unit per element and one
more (`Finset.card.timedCost_eq`), in `derive_cost` and in `derive_timed`:

* the cardinality of a range;
* a threshold test on the cardinality of a filtered set, as a condition of an `if`;
* a tree that returns the cardinality of a set computed from its input.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveFinsetCardTest

open CatCrypt.Core

/-- The number of elements of `range n`. -/
def rangeCard (n : ℕ) : ℕ := (Finset.range n).card

derive_cost rangeCard

example (n : ℕ) : rangeCard.timedCost n = 2 * n + 3 := by
  simp [rangeCard.timedCost, Finset.card.timedCost_eq, Finset.range.timedCost]; omega

/-- Whether at least `k` elements of `s` exceed `t`. -/
def manyAbove (k t : ℕ) (s : Finset ℕ) : Bool := if k ≤ (s.filter fun n => t < n).card then
  true else false

derive_cost manyAbove

example (k t : ℕ) (s : Finset ℕ) :
    manyAbove.timedCost k t s ≤ 2 * s.card + 6 := by
  have h := Finset.card_filter_le s fun n => t < n
  simp only [manyAbove.timedCost, Finset.card.timedCost_eq, Finset.filter.timedCost_eq]
  simp; omega

/-- A tree that returns the number of elements of `range n`. -/
noncomputable def cardTree (n : ℕ) : SPTree ℕ := SPTree.ret (Finset.range n).card

derive_timed cardTree

example (n : ℕ) : (cardTree.timed n).1 = 2 * n + 3 := by
  simp [cardTree.timed, Finset.card.timedCost_eq, Finset.range.timedCost]; omega

example (n : ℕ) : (cardTree.timed n).2.erase = cardTree n := cardTree.erase_timed n

end CatCrypt.Tactics.DeriveFinsetCardTest
