/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting elements of `ZMod n` by their representative

For `m ≤ n`, exactly `m` elements of `ZMod n` have a canonical representative `x.val`
below `m`: the representative is a bijection onto `{0, …, m - 1}`.

## Main results

* `ZMod.natCard_val_lt` — `Nat.card {x : ZMod n // x.val < m} = m` for `m ≤ n`.
-/

@[expose] public section

set_option autoImplicit false

namespace ZMod

/-- For `m ≤ n`, the elements of `ZMod n` whose canonical representative is below `m`
    are in bijection with the natural numbers below `m`. -/
def valLtEquiv {n : ℕ} [NeZero n] {m : ℕ} (hm : m ≤ n) :
    {x : ZMod n // x.val < m} ≃ {i : ℕ // i < m} where
  toFun x := ⟨x.1.val, x.2⟩
  invFun i := ⟨(i.1 : ZMod n), by rw [ZMod.val_cast_of_lt (lt_of_lt_of_le i.2 hm)]; exact i.2⟩
  left_inv x := Subtype.ext (ZMod.natCast_zmod_val x.1)
  right_inv i := Subtype.ext (ZMod.val_cast_of_lt (lt_of_lt_of_le i.2 hm))

/-- For `m ≤ n`, exactly `m` elements of `ZMod n` have a canonical representative below
    `m`. -/
theorem natCard_val_lt {n : ℕ} [NeZero n] {m : ℕ} (hm : m ≤ n) :
    Nat.card {x : ZMod n // x.val < m} = m := by
  rw [Nat.card_congr ((valLtEquiv hm).trans Fin.equivSubtype.symm), Nat.card_eq_fintype_card,
    Fintype.card_fin]

end ZMod
