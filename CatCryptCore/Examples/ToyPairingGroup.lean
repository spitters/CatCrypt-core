/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PairingGroup
public import Mathlib.Data.ZMod.Basic

/-!
# The pairing group of the additive group of `ZMod p`

For a prime `p`, the three groups are `Multiplicative (ZMod p)`, the generators are `1`
of `ZMod p`, and the pairing is the product of `ZMod p`. The pairing is bilinear because the
product distributes over the sum, and non-degenerate because `1 * 1 ≠ 0`. The discrete
logarithm is trivial in this group; it serves as a concrete instance at which the statements
over an arbitrary `PairingGroup` apply.

## Main definitions

* `zmodPairingGroup` — the pairing group of `ZMod p` for a prime `p`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples

open CatCrypt.Crypto

/-- The pairing group of `ZMod p` for a prime `p`: each group is `Multiplicative (ZMod p)`,
each generator is `ofAdd 1`, and the pairing sends `(a, b)` to `ofAdd (toAdd a * toAdd b)`. -/
@[instance_reducible]
noncomputable def zmodPairingGroup (p : ℕ) [Fact p.Prime] : PairingGroup where
  G₁ := Multiplicative (ZMod p)
  G₂ := Multiplicative (ZMod p)
  GT := Multiplicative (ZMod p)
  p := p
  cardG₁ := by simp
  cardG₂ := by simp
  g₁ := Multiplicative.ofAdd 1
  g₂ := Multiplicative.ofAdd 1
  g₁_generates x := ⟨(Multiplicative.toAdd x).val, by simp [← ofAdd_zsmul]⟩
  g₂_generates x := ⟨(Multiplicative.toAdd x).val, by simp [← ofAdd_zsmul]⟩
  e a b := Multiplicative.ofAdd (Multiplicative.toAdd a * Multiplicative.toAdd b)
  e_mul_left a b y := by simp [add_mul, ofAdd_add]
  e_mul_right x a b := by simp [mul_add, ofAdd_add]
  e_nondeg := by simp

end CatCrypt.Examples
