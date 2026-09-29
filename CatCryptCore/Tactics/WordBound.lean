/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public section

set_option autoImplicit false

/-!
# `word_bound`

`word_bound` closes a strict numeric upper bound on a word-shaped natural-number
term: `a % n < n` for a literal `n`, `x.toNat < 2 ^ w` for `x : BitVec w`, the
bitwise `&&&` / `^^^` / `|||` of bounded operands below `2 ^ n`, a right shift of
a bounded operand, a `Fin` value divided or reduced by a literal, and any bound
`omega` decides after these facts. It is a first-match cascade:

1. `assumption`;
2. `Nat.mod_lt` with the positivity side goal by `decide`;
3. `BitVec.isLt`;
4. `omega`, then `bv_omega`;
5. `Nat.and_lt_two_pow` (either operand bounded), `Nat.xor_lt_two_pow`,
   `Nat.or_lt_two_pow`, `Nat.shiftRight_le`, each recursing on the operand
   bounds;
6. `decide`.

## Examples

```
example (a b : Nat) : a % 2 ^ 64 ^^^ b % 2 ^ 64 < 2 ^ 64 := by word_bound
example (x : BitVec 64) : x.toNat >>> 16 &&& 65535 < 2 ^ 16 := by word_bound
example (i : Fin 25) : i.val / 5 < 5 := by word_bound
```
-/

/-- Close a strict upper bound on a word-shaped `Nat` term (a residue, a
    `BitVec.toNat`, a bitwise combination or shift of bounded operands), by the
    cascade in the module docstring. -/
syntax (name := wordBound) "word_bound" : tactic

macro_rules
  | `(tactic| word_bound) => `(tactic| first
      | assumption
      | exact Nat.mod_lt _ (by decide)
      | exact BitVec.isLt _
      | omega
      | bv_omega
      | (apply Nat.and_lt_two_pow; word_bound)
      | (rw [Nat.and_comm]; apply Nat.and_lt_two_pow; word_bound)
      | (apply Nat.xor_lt_two_pow <;> word_bound)
      | (apply Nat.or_lt_two_pow <;> word_bound)
      | (apply Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _); word_bound)
      | decide)

example (a : Nat) : a % 2 ^ 64 < 2 ^ 64 := by word_bound
example (a b : Nat) : (a % 2 ^ 64) &&& b < 2 ^ 64 := by word_bound
example (a b : Nat) : a % 2 ^ 64 ^^^ b % 2 ^ 64 < 2 ^ 64 := by word_bound
example (a b : Nat) : a % 2 ^ 64 ||| b % 2 ^ 64 < 2 ^ 64 := by word_bound
example (a : Nat) : (a % 2 ^ 64) >>> 3 < 2 ^ 64 := by word_bound
example (x : BitVec 64) : x.toNat / 2 < 2 ^ 64 := by word_bound
example (x : BitVec 64) : x.toNat >>> 16 &&& 65535 < 2 ^ 16 := by word_bound
example (i : Fin 25) : (i.val % 5 + 3 * (i.val / 5)) % 5 < 5 := by word_bound

end
