/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Libcrux.GroupOps
public import CatCryptCore.Crypto.EdDSA.Extraction.Eddsa_haxpipe
public import CatCryptCore.Hax.ReprBridge

/-!
# EdDSA Bridge: GroupOps -> EddsaDeps Instance

Instantiates the `EddsaDeps` type class required by the hax-extracted EdDSA code in
`Eddsa_haxpipe.lean` with the opaque Ed25519 group operations of `Libcrux/GroupOps.lean`.

## Architecture

```
Libcrux/GroupOps.lean              (ed25519_group_mul, ed25519_scalar_add, ...)
        |  type conversion (Vector UInt8 32 <-> Array Int)
EdDSA/Bridge.lean (this file)      (instance EddsaDeps)
        |  EddsaDeps interface
Extraction/Eddsa_haxpipe.lean      (sign, verify, keygen)
```

## Type Conversion

The hax extraction pipeline produces code operating on `Array Int` (from
Rust `Vec<i64>`), while the opaque group operations use `Vector UInt8 32`.
The conversions are:
- `vecToArrayInt` (`CatCryptCore.Hax.ReprBridge`): `Vector UInt8 32 -> Array Int`
  (zero-extend each byte)
- `arrayIntToVector`: `Array Int -> Vector UInt8 32` (truncate each int to byte)

## References

* RFC 8032 -- Edwards-Curve Digital Signature Algorithm (EdDSA)
* `Libcrux/GroupOps.lean` -- opaque Ed25519 group operations
* `Extraction/Eddsa_haxpipe.lean` -- hax-extracted EdDSA code
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.EdDSA.Bridge

open CatCrypt.Crypto.Libcrux.GroupOps
open CatCrypt.Hax.ReprBridge (vecToArrayInt)

/-! ## Type Conversion -/

/-- Convert an `Array Int` to `Vector UInt8 32` by truncating each element.
    Pads with zeros if the array is shorter than 32, truncates if longer. -/
def arrayIntToVector (a : Array Int) : Vector UInt8 32 :=
  Vector.ofFn (fun i =>
    if h : i.val < a.size
    then UInt8.ofNat (a[i.val]'h).toNat
    else 0)

/-- Lift a binary operation on `Vector UInt8 32` to `Array Int -> Array Int -> Array Int`. -/
def liftBinOp (f : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32)
    (a b : Array Int) : Array Int :=
  vecToArrayInt (f (arrayIntToVector a) (arrayIntToVector b))

/-- Lift a ternary operation on `Vector UInt8 32` to `Array Int` arguments. -/
def liftTernaryOp
    (f : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32)
    (a b c : Array Int) : Array Int :=
  vecToArrayInt (f (arrayIntToVector a) (arrayIntToVector b) (arrayIntToVector c))

/-- Lift a unary operation on `Vector UInt8 32` to `Array Int -> Array Int`. -/
def liftUnaryOp (f : Vector UInt8 32 → Vector UInt8 32)
    (a : Array Int) : Array Int :=
  vecToArrayInt (f (arrayIntToVector a))

/-- Lift a constant `Vector UInt8 32` to `Array Int`. -/
def liftConst (c : Vector UInt8 32) : Array Int :=
  vecToArrayInt c

/-! ## EddsaDeps Instance -/

/-- `EddsaDeps` instance from the opaque Ed25519 group operations of `GroupOps.lean`.

    Maps each dependency of the hax-extracted EdDSA code to the
    corresponding operation, lifted to `Array Int` through `vecToArrayInt` and
    `arrayIntToVector`:
    - `group_mul` -> `ed25519_group_mul` (scalar-point multiplication)
    - `generator` -> `ed25519_base_point`
    - `hash_challenge` -> `ed25519_hash_challenge`
    - `scalar_mul` -> `ed25519_scalar_mul`
    - `scalar_add` -> `ed25519_scalar_add`
    - `group_add` -> `ed25519_point_add` -/
instance concreteEddsaDeps : Eddsa.EddsaDeps where
  group_mul := liftBinOp ed25519_group_mul
  generator := liftConst ed25519_base_point
  hash_challenge := liftTernaryOp ed25519_hash_challenge
  scalar_mul := liftBinOp ed25519_scalar_mul
  scalar_add := liftBinOp ed25519_scalar_add
  group_add := liftBinOp ed25519_point_add

/-! ## Verification -/

-- The EddsaDeps instance fields map to the expected operations
example : @Eddsa.EddsaDeps.group_mul concreteEddsaDeps =
    liftBinOp ed25519_group_mul := rfl

example : @Eddsa.EddsaDeps.generator concreteEddsaDeps =
    liftConst ed25519_base_point := rfl

end CatCrypt.Crypto.EdDSA.Bridge
