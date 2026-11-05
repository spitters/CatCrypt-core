/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.CryptoWord
public import CatCryptCore.Hax.CType

/-!
# Concrete Instances for `Vector UInt8 n`

`CryptoWord` and `SampleableType` instances on byte vectors, which instantiate the abstract
security proofs at libcrux-specs and other byte-level Rust implementations.

## Overview

The security proofs are parametric over `CryptoWord W`. Concrete implementations
(X25519, HKDF-SHA256, AES-GCM, etc.) operate on byte arrays, and this file provides
`CryptoWord (Vector UInt8 n)` with componentwise XOR.

## Main definitions

| Definition | Type |
|-----|------|
| `vectorXor` | componentwise XOR on byte vectors |
| `instCryptoWordVector` | `CryptoWord (Vector UInt8 n)` |
| `instSampleableTypeVector` | `SampleableType (Vector UInt8 n)` |

## References

* `CatCryptCore.Crypto.CryptoWord` -- base type classes
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Libcrux.ConcreteInstances

open CatCrypt.Crypto

/-! ## Fintype / Nonempty / Inhabited instances

Provided globally by `CatCryptCore.Hax.CType`:
- `CType.instGlobalFintypeUInt8` : `Fintype UInt8`
- `CType.instGlobalFintypeVectorUInt8 n` : `Fintype (Vector UInt8 n)`
- `CType.instGlobalNonemptyVectorUInt8 n` : `Nonempty (Vector UInt8 n)`
- `Inhabited (Vector UInt8 n)` via `Vector.instInhabited`
-/

/-! ## Componentwise XOR -/

/-- XOR on byte vectors: componentwise XOR. -/
def vectorXor (n : Nat) (a b : Vector UInt8 n) : Vector UInt8 n :=
  Vector.zipWith (· ^^^ ·) a b

/-- BitVec XOR is involutive: `(a ^^^ b) ^^^ b = a`. -/
theorem bitvec8_xor_cancel (a b : BitVec 8) : (a ^^^ b) ^^^ b = a := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- UInt8 XOR is involutive: `(a ^^^ b) ^^^ b = a`. -/
theorem uint8_xor_cancel (a b : UInt8) : (a ^^^ b) ^^^ b = a := by
  cases a with | ofBitVec av =>
  cases b with | ofBitVec bv =>
  change UInt8.ofBitVec ((av ^^^ bv) ^^^ bv) = UInt8.ofBitVec av
  rw [bitvec8_xor_cancel]

/-- XOR is involutive on byte vectors. -/
theorem vectorXor_cancel (n : Nat) (a b : Vector UInt8 n) :
    vectorXor n (vectorXor n a b) b = a := by
  simp only [vectorXor]
  ext i
  simp only [Vector.getElem_zipWith]
  have h := uint8_xor_cancel a[i] b[i]
  exact h

/-- UInt8 XOR is commutative. -/
theorem uint8_xor_comm (a b : UInt8) : (a ^^^ b) = (b ^^^ a) := by
  cases a with | ofBitVec av =>
  cases b with | ofBitVec bv =>
  change UInt8.ofBitVec (av ^^^ bv) = UInt8.ofBitVec (bv ^^^ av)
  rw [BitVec.xor_comm]

/-- XOR is commutative on byte vectors. -/
theorem vectorXor_comm (n : Nat) (a b : Vector UInt8 n) :
    vectorXor n a b = vectorXor n b a := by
  simp only [vectorXor]
  ext i
  simp only [Vector.getElem_zipWith]
  have h := uint8_xor_comm a[i] b[i]
  exact h

/-! ## CryptoWord / SampleableType instances -/

/-- `SampleableType` instance for `Vector UInt8 n`. -/
noncomputable instance instSampleableTypeVector (n : Nat) :
    SampleableType (Vector UInt8 n) where
  fintype := inferInstance
  nonempty := inferInstance
  deceq := inferInstance
  inhabited := inferInstance

/-- `CryptoWord` instance for `Vector UInt8 n` with componentwise XOR.
    The security proofs parametric over `CryptoWord W` are instantiated at the
    byte-vector level through it. -/
noncomputable instance instCryptoWordVector (n : Nat) :
    CryptoWord (Vector UInt8 n) where
  toSampleableType := instSampleableTypeVector n
  wxor := vectorXor n
  wxor_cancel := vectorXor_cancel n
  wxor_comm := vectorXor_comm n

end CatCrypt.Crypto.Libcrux.ConcreteInstances
