/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.ForkingLemma

/-!
# Covering bounds for `prTrue` of pure Booleans

The probability that `SPComp.pure b` returns `true` is `1` or `0` according to `b`
(`ForkingLemma.prTrue_pure_bool`). An implication between Booleans therefore gives an
inequality between these probabilities, and a cover of `b₁` by `b₂ ∨ b₃` gives a
union bound.

## Main results

- `prTrue_pure_le_of_imp`: if `b = true → c = true`, then
  `prTrue (pure b) ≤ prTrue (pure c)`.
- `prTrue_pure_le_add`: if `b₁ = true → b₂ = true ∨ b₃ = true`, then
  `prTrue (pure b₁) ≤ prTrue (pure b₂) + prTrue (pure b₃)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob

/-- The `true`-probability of `pure b` is at most that of `pure c` when `b` implies `c`. -/
theorem prTrue_pure_le_of_imp {b c : Bool} (h : b = true → c = true) (hp : Heap) :
    prTrue (SPComp.pure b) hp ≤ prTrue (SPComp.pure c) hp := by
  rw [ForkingLemma.prTrue_pure_bool, ForkingLemma.prTrue_pure_bool]
  cases b with
  | false => simp
  | true => simp [h rfl]

/-- The `true`-probability of `pure b₁` is at most that of `pure b₂` plus that of
`pure b₃` when `b₁` implies `b₂ ∨ b₃`. -/
theorem prTrue_pure_le_add (b₁ b₂ b₃ : Bool) (hp : Heap)
    (hb : b₁ = true → b₂ = true ∨ b₃ = true) :
    prTrue (SPComp.pure b₁) hp ≤ prTrue (SPComp.pure b₂) hp + prTrue (SPComp.pure b₃) hp := by
  rw [ForkingLemma.prTrue_pure_bool, ForkingLemma.prTrue_pure_bool,
    ForkingLemma.prTrue_pure_bool]
  cases b₁ <;> cases b₂ <;> cases b₃ <;> simp at hb <;> simp

end CatCrypt.Crypto
