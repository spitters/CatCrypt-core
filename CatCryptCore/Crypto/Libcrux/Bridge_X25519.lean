/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Libcrux.Extraction.Libcrux_specs
public import CatCryptCore.Crypto.Libcrux.ConcreteInstances
public import CatCryptCore.Crypto.Assumptions.DDH

/-!
# X25519 Bridge: X25519 → DDH Definition

Bridges the opaque X25519 Diffie-Hellman constants of `Libcrux_specs` to the abstract
`DDHDef` type class.

## Architecture

```
Extraction/Libcrux_specs.lean          (x25519_scalarmult, x25519_base)
        ↓  field assignment
Bridge_X25519.lean (this file)         (concreteDDH_X25519 : DDHDef)
        ↓  explicit DDH reductions
protocol security proofs
```

## The ideal DDH game at X25519

The core `DDH_Game_Ideal` samples its third value uniformly from `Vector UInt8 32`, which
outputs of RFC 7748 X25519 never are (on public keys they are u-coordinates of Curve25519
points, below `2^255 - 19`), so the DDH advantage at `concreteDDH_X25519` is not small for
every adversary. The theorems over
`concreteDDH_X25519` use this advantage only at the explicit reductions they name.

## Key Results

| Definition / Theorem | Role |
|-----|------|
| `concreteDDH_X25519` | `DDHDef (Vector UInt8 32)` for X25519, key pairs `(sk, X25519(sk, 9))` |
| `X25519Commutes` | the functional fact `X25519(a, X25519(b, 9)) = X25519(b, X25519(a, 9))` |
| `concreteDDH_X25519_symmetric` | `ECDHSymmetric concreteDDH_X25519` from `X25519Commutes` |

## Commutativity

`x25519_scalarmult` and `x25519_base` are `opaque` constants, so no Lean
theorem relates them to the Curve25519 group model of core
`CatCryptCore.Crypto.KeyAgreement.Curve25519` (where `x25519_commute` is proved) without an
axiom. Commutativity is therefore the single named hypothesis
`X25519Commutes`, a correctness property of X25519 (RFC 7748 §6.1), not a
hardness assumption; every statement that needs it takes it as an explicit
argument.

## References

* RFC 7748 — Elliptic Curves for Security
* `CatCryptCore.Crypto.Assumptions.DDH` — abstract DDH definition
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Libcrux.Bridge_X25519

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.Libcrux.Extraction.Libcrux_specs
open CatCrypt.Crypto.Libcrux.ConcreteInstances
open scoped ENNReal

/-! ## Concrete DDH Definition -/

/-- Concrete X25519 DDH definition from libcrux-specs.

- `ecdh`: `x25519_scalarmult(private_key, public_key)` computes the shared secret
- `keygen`: a uniform private key `sk` and its public key `x25519_base sk`,
  the u-coordinate of `[clamp sk]·9` (RFC 7748 §6.1). -/
noncomputable def concreteDDH_X25519 : DDHDef (Vector UInt8 32) where
  ecdh := x25519_scalarmult
  keygen := (SPComp.sample (Vector UInt8 32)).bind
    (fun sk => SPComp.pure (sk, x25519_base sk))
  keygen_isPure :=
    SPComp.bind_isPure (SPComp.sample_isPure _) (fun _ => SPComp.pure_isPure _)

/-! ## Commutativity -/

/-- X25519 Diffie-Hellman correctness: scalar multiplications of the base
point commute, `X25519(a, X25519(b, 9)) = X25519(b, X25519(a, 9))`.

Both sides are the u-coordinate of `[clamp a]·[clamp b]·9` on Curve25519
(RFC 7748 §6.1). This is a functional property of the two opaque
libcrux-specs constants, stated once here and passed explicitly to every
statement that uses it. -/
def X25519Commutes : Prop :=
  ∀ a b : Vector UInt8 32,
    x25519_scalarmult a (x25519_base b) = x25519_scalarmult b (x25519_base a)

/-- Under `X25519Commutes`, `concreteDDH_X25519` satisfies the keypair form of
Diffie-Hellman commutativity, with public-key map `x25519_base`. -/
theorem concreteDDH_X25519_symmetric (hX : X25519Commutes) :
    Assumptions.ECDHSym.ECDHSymmetric concreteDDH_X25519 :=
  ⟨x25519_base, rfl, hX⟩

/-! ## Connecting Lemmas -/

/-- The `ecdh` field of `concreteDDH_X25519` is `x25519_scalarmult`. -/
@[simp]
theorem concreteDDH_X25519_ecdh_eq :
    concreteDDH_X25519.ecdh = x25519_scalarmult := rfl

/-! ## Verification -/

-- concreteDDH_X25519 ecdh field is definitionally equal to extraction function
example : concreteDDH_X25519.ecdh = x25519_scalarmult := rfl

end CatCrypt.Crypto.Libcrux.Bridge_X25519
