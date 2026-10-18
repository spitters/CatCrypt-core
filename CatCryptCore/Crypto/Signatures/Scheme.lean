/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Advantage

/-!
# Generic Digital Signature Scheme

Abstract digital signature scheme definition, parameterized over message,
public key, secret key, and signature types.

## Main definitions

* `SigScheme` — abstract signature scheme (keygen, sign, verify)
* `SigScheme.Consistent` — perfect correctness: signing produces verifying signatures

## References

* [Cohen, Lindell, Osborn, Shany — ePrint 2024/1807]
* [Goldreich — Foundations of Cryptography, Vol. 2]
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

namespace CatCrypt.Crypto.Signatures

/-! ## Signature Scheme -/

/-- Abstract digital signature scheme.

    Parameterized by:
    - `Msg` : message type
    - `PK`  : public key type
    - `SK`  : secret key type
    - `Sig` : signature type -/
structure SigScheme (Msg PK SK Sig : Type) where
  /-- Key generation: sample a public/secret key pair -/
  keygen : SPComp (PK × SK)
  /-- Signing: given secret key and message, produce a signature -/
  sign : SK → Msg → SPComp Sig
  /-- Verification: deterministic check of (pk, msg, sig) -/
  verify : PK → Msg → Sig → Bool

namespace SigScheme

variable {Msg PK SK Sig : Type}

/-- Perfect correctness (consistency): for a key pair drawn from `keygen`
    and any message, signing produces signatures that verify.

    Expressed as program equality over the keygen draw:
    `keygen >>= λ (pk, sk). sign(sk, m) >>= λ σ. pure(verify(pk, m, σ))`
    `= keygen >>= λ (pk, sk). sign(sk, m) >>= λ _. pure(true)`

    The public key `ks.1` and secret key `ks.2` come from the same `keygen`
    draw, so the check reads a `pk` that matches the `sk` used to sign. This
    means every `(pk, sk)` in the support of `keygen` and every σ in the
    support of `sign sk m` satisfies `verify pk m σ = true`.

    Consistency is over keygen-produced key pairs — the correctness content
    is the key-pair relationship (e.g. `pk = f(sk)`) that `keygen` establishes.

    The F_SIG UC theorem (Cohen et al. 2024) requires consistency. -/
def Consistent (S : SigScheme Msg PK SK Sig) : Prop :=
  ∀ (m : Msg),
    SPComp.bind S.keygen (fun ks =>
      SPComp.bind (S.sign ks.2 m) (fun σ => SPComp.pure (S.verify ks.1 m σ))) =
    SPComp.bind S.keygen (fun ks =>
      SPComp.bind (S.sign ks.2 m) (fun _ => SPComp.pure true))

/-- Keygen is heap-independent (IsPure). -/
def KeygenIsPure (S : SigScheme Msg PK SK Sig) : Prop :=
  SPComp.IsPure S.keygen

/-- Signing is heap-independent (IsPure) for all keys and messages. -/
def SignIsPure (S : SigScheme Msg PK SK Sig) : Prop :=
  ∀ (sk : SK) (m : Msg), SPComp.IsPure (S.sign sk m)

end SigScheme

end CatCrypt.Crypto.Signatures
