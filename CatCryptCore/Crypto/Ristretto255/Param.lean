/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCryptCore.Crypto.Ristretto255.FinGroup
public import CatCryptCore.Examples.GroupParam

/-!
# `GroupParam` instance for ristretto255

Port of `Commitments/theories/Ristretto255_SSProve.v : RistrettoParam` to
Lean 4 + Mathlib.

We instantiate CatCrypt's abstract `GroupParam` structure with
`G = Scalar = ZMod curve25519_l`, using `1` as the generator and the additive
group structure of `ZMod l` (written multiplicatively to match the abstract
`GroupParam` interface).  All field laws follow from `ZMod l` being a
commutative group of order `l = curve25519_l` (a prime).

The concrete representation is justified by the fact that any cyclic group of
prime order `l` is isomorphic to `ZMod l`, and SSProve's Schnorr / Sigma
proofs only depend on this abstract structure.

## Field convention

We model the group multiplicatively using the *additive* structure of
`ZMod l`:

| `GroupParam` field | Concrete |
|---|---|
| `G`                | `ZMod curve25519_l`         |
| `Scalar`           | `ZMod curve25519_l`         |
| `generator`        | `(1 : ZMod l)`              |
| `identity`         | `(0 : ZMod l)` (additive)   |
| `groupMul a b`     | `a + b`                     |
| `groupInv a`       | `-a`                        |
| `exp s`            | `s · 1 = s`                 |
| `groupExp h s`     | `s · h` (i.e. `s · h` in `ZMod l`, multiplication) |

Note that `exp` and `groupExp` use scalar *multiplication* in `ZMod l`,
because the multiplicative power `g^s` in a generic group corresponds to
the additive operation `s · g` in `ZMod l`. This matches the standard
discrete-log encoding for cyclic groups.
-/

@[expose] public section

namespace CatCrypt.Crypto.Ristretto255

open CatCrypt.Examples

set_option autoImplicit false

/-- Concrete `GroupParam` instance for ristretto255. -/
@[implicit_reducible]
noncomputable def RistrettoParam : GroupParam where
  G := ZMod curve25519_l
  Scalar := ZMod curve25519_l
  finG := inferInstance
  neG := ⟨0⟩
  decG := inferInstance
  finScalar := inferInstance
  neScalar := ⟨0⟩
  decScalar := inferInstance
  generator := 1
  identity := 0
  exp s := s * 1
  groupExp h s := s * h
  scalarAdd a b := a + b
  scalarMul a b := a * b
  scalarSub a b := a - b
  scalarDiv a b := a * b⁻¹
  scalarNeg a := -a
  scalarZero := 0
  groupMul a b := a + b
  groupInv a := -a
  scalarOne := 1
  exp_add x y := by ring
  exp_zero := by simp
  div_mul_cancel x y hy := by
    haveI : Fact (Nat.Prime curve25519_l) := ⟨curve25519_l_prime⟩
    field_simp
  groupExp_generator x := by rfl
  groupExp_exp w e := by ring
  groupExp_one h := by simp
  groupExp_add h a b := by ring
  scalarSub_ne_zero a b hab hsub := by
    apply hab
    have : a - b = 0 := hsub
    linear_combination this
  groupMul_identity a := by simp
  identity_groupMul a := by simp
  groupMul_inv a := by simp
  inv_groupMul a := by simp
  groupMul_assoc a b c := by ring
  groupExp_zero h := by simp
  scalarMul_one a := by simp
  groupInv_groupExp h e := by ring
  scalarSub_eq a b := by ring
  scalarAdd_neg a := by simp
  exp_surj h := ⟨h, by simp⟩
  exp_inj x y hxy := by
    simpa using hxy
  scalarAdd_comm a b := by ring
  scalarAdd_assoc a b c := by ring
  scalarMul_add a b c := by ring
  scalarAdd_mul a b c := by ring
  scalarMul_comm a b := by ring
  scalarAdd_zero a := by simp
  scalarZero_add a := by simp
  scalarNeg_add a := by simp
  scalarNeg_zero := by simp
  scalarNeg_add_distrib a b := by ring
  scalarMul_zero a := by simp
  scalarZero_mul a := by simp
  mul_div_cancel a b hb := by
    haveI : Fact (Nat.Prime curve25519_l) := ⟨curve25519_l_prime⟩
    field_simp
  scalarMul_assoc a b c := by ring

end CatCrypt.Crypto.Ristretto255
