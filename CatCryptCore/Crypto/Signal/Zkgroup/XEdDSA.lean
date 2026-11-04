/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.Schnorr
public import CatCryptCore.Crypto.Ristretto255.Param

/-!
# XEdDSA as the Fiat–Shamir Schnorr signature

XEdDSA is Signal's Schnorr signature with X25519 keys. With secret scalar `a`, public key
`A = a·G` and hash `H`, a signature on `m` is `(R, s)` with

    R = r·G,   s = r + H(R, m)·a   (mod l),

and it verifies when `s·G = R + H(R, m)·A`. This is the Fiat–Shamir signature of the
Schnorr Σ-protocol `FiatShamirROM.schnorrSigma`, here over `RistrettoParam`.

## What is modelled

* The group is `RistrettoParam`: a cyclic group of prime order `l = curve25519_l`,
  represented as `ZMod l`. The Fiat–Shamir bounds use only its group structure and order,
  not the Edwards curve or the ristretto255 encoding.
* The hash takes `(R, m)`. XEdDSA hashes `R ‖ A ‖ m`; the public key `A` is fixed in the
  signature game, so a random oracle on `(R, m)` per key models it.
* The nonce `r` is uniform. XEdDSA derives it as `H(a ‖ m ‖ Z)` with 64 random bytes `Z`;
  modelling this hash as a random oracle unqueried by the adversary makes `r` uniform.
* The conversion of a Montgomery key to an Edwards key (and the sign-bit normalisation of
  `a`) is a bijection on key pairs and is not modelled.

## Main definitions

* `xeddsaSigma` — the Schnorr Σ-protocol over `RistrettoParam`.
* `xeddsaSign`, `xeddsaVerify` — signing with a uniform nonce, and verification.

## Main results

* `xeddsaVerify_sign` — every signature produced by `xeddsaSign` verifies.
* EUF-CMA in the random-oracle model, by the forking reduction to the discrete logarithm,
  is `FiatShamirROM.schnorr_fs_rom_eufcma RistrettoParam`; special soundness, perfect HVZK
  and the commitment bound are `schnorrSigma_specialSound`, `schnorrSigma_perfectHVZK` and
  `schnorrSigma_commitBound` at `RistrettoParam`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.Zkgroup.XEdDSA

open CatCrypt.Crypto.FiatShamirROM CatCrypt.Crypto.Ristretto255

/-- The Σ-protocol of XEdDSA: Schnorr over `RistrettoParam`. -/
noncomputable abbrev xeddsaSigma : Sigma := schnorrSigma RistrettoParam

/-- An XEdDSA signature: the commitment `R` and the response `s`. -/
abbrev XEdDSASignature : Type := RistrettoParam.G × RistrettoParam.Scalar

/-- Sign `m` with the secret scalar `a` and the hash `H`: a uniform nonce `r`, the
commitment `R = r·G` and the response `r + H(R, m)·a`. -/
noncomputable def xeddsaSign {M : Type} (H : RistrettoParam.G → M → RistrettoParam.Scalar)
    (a : RistrettoParam.Scalar) (m : M) : PMF XEdDSASignature :=
  (PMF.uniformFintype RistrettoParam.Scalar).map fun r =>
    let R := xeddsaSigma.commit (RistrettoParam.exp a) a r
    (R, xeddsaSigma.respond (RistrettoParam.exp a) a r (H R m))

/-- Verify the signature `(R, s)` on `m` under the public key `A`: the Σ-protocol verifier
on the transcript `(R, H(R, m), s)`. -/
noncomputable def xeddsaVerify {M : Type} (H : RistrettoParam.G → M → RistrettoParam.Scalar)
    (A : RistrettoParam.G) (m : M) (σ : XEdDSASignature) : Bool :=
  xeddsaSigma.verify A σ.1 (H σ.1 m) σ.2

/-- Every signature produced by `xeddsaSign` verifies under the matching public key. -/
theorem xeddsaVerify_sign {M : Type} (H : RistrettoParam.G → M → RistrettoParam.Scalar)
    (a : RistrettoParam.Scalar) (m : M) {σ : XEdDSASignature}
    (hσ : σ ∈ (xeddsaSign H a m).support) : xeddsaVerify H (RistrettoParam.exp a) m σ = true := by
  obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hσ
  exact schnorrSigma_complete RistrettoParam _ a rfl r _

end CatCrypt.Crypto.Signal.Zkgroup.XEdDSA
