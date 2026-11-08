/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHSquare
public import CatCryptCore.Crypto.FiatShamirROM.DHGroupParam

/-!
# X3DH with a joint identity and signing key

In the joint-key model of X3DH the identity key `ik` is both the Diffie–Hellman key and the
signing key: the public identity key `pub ik` is the verification key of a Fiat–Shamir
signature over a Σ-protocol for the key relation, with witness `ik`. `JointSigAKEAlg S W`
is an `AKEAlg S W` together with such a Σ-protocol `P` (statements `W`, witnesses `S`) whose
relation holds between `pub s` and `s`. `x3dhJointAlg G` is X3DH over the Diffie–Hellman
group `G` with `P` the Schnorr Σ-protocol at `GroupParam.ofDHGroup G`. XEdDSA is a later
concrete instance of the same record.

## Main definitions

* `JointSigAKEAlg S W` — the algorithms of an AKE with a Σ-protocol for the key relation
* `x3dhJointAlg G` — X3DH over `G` with Schnorr as the key Σ-protocol
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquare

open CatCrypt.Crypto CatCrypt.Crypto.FiatShamirROM CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Examples

/-- **The algorithms of an AKE whose identity key is its signing key.** An `AKEAlg S W` with a
Fiat–Shamir Σ-protocol `P` whose statements are the public keys `W` and whose witnesses are the
secrets `S`; the identity secret `s` is a witness for its public key `pub s`. -/
structure JointSigAKEAlg (S W : Type) extends AKEAlg S W where
  /-- The Σ-protocol of the signature scheme. -/
  P : Sigma
  /-- The statements of `P` are the public keys. -/
  stmt_eq : P.Stmt = W
  /-- The witnesses of `P` are the secrets. -/
  wit_eq : P.Wit = S
  /-- The identity key is the signing key. -/
  rel_pub : ∀ s : S, P.rel (stmt_eq ▸ pub s) (wit_eq ▸ s)

/-- X3DH over the Diffie–Hellman group `G` with the Schnorr Σ-protocol at
`GroupParam.ofDHGroup G` as the signature scheme of the identity key. -/
noncomputable def x3dhJointAlg {S W : Type} [Field S] [Fintype S] [DecidableEq S]
    [DecidableEq W] (G : DHGroup S W) : JointSigAKEAlg S W where
  toAKEAlg := x3dhAlg G
  P := schnorrSigma (GroupParam.ofDHGroup G)
  stmt_eq := rfl
  wit_eq := rfl
  rel_pub _ := rfl

end CatCrypt.Crypto.AKE.X3DHSquare
