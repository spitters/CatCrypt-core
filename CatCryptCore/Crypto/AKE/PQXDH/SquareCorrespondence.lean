/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDH.Extraction.Pqxdh_haxpipe
public import CatCryptCore.Crypto.AKE.PQXDHSquare

/-!
# The extracted PQXDH handshake and the key-derivation input of the square model

The square model `CatCryptCore.Crypto.AKE.PQXDHSquare` derives the key of a session from an
input `PInp W SS`: the input `Inp W` of X3DH (the session, the initiator, the responder and the
four Diffie-Hellman values over a group `G : DHGroup S W`) and the shared secret of the KEM
`P : Scheme PK SK SS C`. The extracted functions `Pqxdh.initiate` and `Pqxdh.respond` of the
Rust crate `pqxdh-hax` compute the four Diffie-Hellman values, encapsulate with explicit
randomness or decapsulate, and apply the KDF of the `Pqxdh.PqxdhDeps` instance, which takes no
session context.

`PqxdhSquareHom` gives encodings of the scalars, the group elements, the KEM values, the
encapsulation randomness and the keys under which the operations of the instance are those of
the square model: `dh_pub` is `G.pub`, `dh` is `G.exp`, `kem_encaps` at encoded randomness is a
deterministic encapsulation `encaps` whose image of the randomness distribution `coins` is
`P.encaps`, `kem_decaps` returns the encoding of an accepted decapsulation of `P`, and `kdf` is
the encoding of a model key derivation `H : PInp W SS → K` at every session context. Under it the
session key of `initiate` is the encoding of `H` at `aliceInp` and the encapsulated secret, and
the key of `respond` the encoding of `H` at `bobInp` and the decapsulated secret.

The equations are stated with the one-time prekey (`use_opk = true`), as for X3DH
(`CatCryptCore.Crypto.AKE.X3DH.SquareCorrespondence`).

## Main definitions

* `PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H`

## Main results

* `initiate_square_enc` — the session key of `initiate` is the encoding of
  `H (aliceInp G sid a b ik ek IKB SPKB OPKB, (encaps pk m).1)`.
* `initiate_msg_square_enc` — the message of `initiate` holds the encoded public keys and the
  encoded encapsulation.
* `respond_square_enc` — on an encapsulation that `P` decapsulates to `ss`, the key of `respond`
  is the encoding of `H (bobInp G sid a b IKA E ik spk opk, ss)`.
* `respond_square_agree` — the responder's key from the initiator's message is the initiator's
  key when `P` decapsulates the encapsulation to its secret.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.PQXDH.SquareCorrespondence

open CatCrypt.Crypto.PAKE.DHExtract (DHGroup)
open CatCrypt.Crypto.UCTransparent.FAKE (SessionId PartyId)
open CatCrypt.Crypto.AKE.X3DHSquare (Inp aliceInp bobInp aliceInp_eq_bobInp)
open CatCrypt.Crypto.AKE.PQXDHSquare (PInp)
open CatCrypt.Crypto.KEM.Games (Scheme)

variable {S W K PK SK SS C M : Type} [Field S]

/-- Encodings of the scalars, the group elements, the KEM public keys, secret keys,
encapsulations and shared secrets, the encapsulation randomness and the keys that carry the
operations of the `Pqxdh.PqxdhDeps` instance in scope to the square model: `dh_pub` to
`G.pub`, `dh` of a scalar and a group element to `G.exp`, `kem_encaps` at encoded randomness to
the deterministic encapsulation `encaps`, whose image of `coins` is `P.encaps`, `kem_decaps` to
the accepted decapsulations of `P`, and `kdf` to the key derivation `H` at the input of every
session context. -/
structure PqxdhSquareHom [Pqxdh.PqxdhDeps] (G : DHGroup S W) (P : Scheme PK SK SS C)
    (encS : S → Array Int) (encW : W → Array Int) (encPK : PK → Array Int)
    (encSK : SK → Array Int) (encC : C → Array Int) (encSS : SS → Array Int)
    (encM : M → Array Int) (encK : K → Array Int) (encaps : PK → M → SS × C) (coins : PMF M)
    (H : PInp W SS → K) : Prop where
  dh_pub : ∀ x, Pqxdh.dh_pub (encS x) = encW (G.pub x)
  dh : ∀ x Y, Pqxdh.dh (encS x) (encW Y) = encW (G.exp Y x)
  kem_encaps : ∀ pk m,
    Pqxdh.kem_encaps (encPK pk) (encM m) = (encC (encaps pk m).2, encSS (encaps pk m).1)
  encaps_coins : ∀ pk, P.encaps pk = coins.map (encaps pk)
  kem_decaps : ∀ sk c ss, P.decaps sk c = some ss →
    Pqxdh.kem_decaps (encSK sk) (encC c) = encSS ss
  kdf : ∀ sid a b d1 d2 d3 d4 ss,
    Pqxdh.kdf (encW d1) (encW d2) (encW d3) (encW d4) (encSS ss) =
      encK (H (⟨sid, a, b, d1, d2, d3, d4⟩, ss))

variable [Pqxdh.PqxdhDeps] {G : DHGroup S W} {P : Scheme PK SK SS C} {encS : S → Array Int}
  {encW : W → Array Int} {encPK : PK → Array Int} {encSK : SK → Array Int}
  {encC : C → Array Int} {encSS : SS → Array Int} {encM : M → Array Int}
  {encK : K → Array Int} {encaps : PK → M → SS × C} {coins : PMF M} {H : PInp W SS → K}

/-- **Initiator key.** With the one-time prekey, the session key of `initiate` at the encoded
identity and ephemeral secrets `ik`, `ek`, a bundle of the encoded public keys `IKB`, `SPKB`,
`OPKB` and the encoded KEM public key `pk`, and the encoded randomness `m`, is the encoding of
the key derivation at the initiator's input `aliceInp G sid a b ik ek IKB SPKB OPKB` and the
encapsulated secret, for every session context `(sid, a, b)`. -/
theorem initiate_square_enc
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (sid : SessionId) (a b : PartyId) (ik ek : S) (IKB SPKB OPKB : W) (pk : PK) (m : M)
    (sig₁ sig₂ : Array Int) :
    (Pqxdh.initiate (encS ik) (encS ek) (encW IKB, encW SPKB, encW OPKB, encPK pk, sig₁, sig₂)
        (encM m) true).1 =
      encK (H (aliceInp G sid a b ik ek IKB SPKB OPKB, (encaps pk m).1)) := by
  simp only [Pqxdh.initiate, Pqxdh.«.ik», Pqxdh.«.spk», Pqxdh.«.opk», Pqxdh.«.pqpk»,
    ↓reduceIte, h.dh, h.kem_encaps, h.kdf sid a b, aliceInp]

/-- The message of `initiate` with the one-time prekey at encoded secrets, a bundle with an
encoded KEM public key and encoded randomness holds the encoded public keys, the encoded
encapsulation and the identifier of the one-time prekey. -/
theorem initiate_msg_square_enc
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (ik ek : S) (pk : PK) (m : M) (IKB SPKB OPKB sig₁ sig₂ : Array Int) :
    (Pqxdh.initiate (encS ik) (encS ek) (IKB, SPKB, OPKB, encPK pk, sig₁, sig₂) (encM m)
        true).2.1 =
      (encW (G.pub ik), encW (G.pub ek), encC (encaps pk m).2, #[0, 0, 0, 1]) := by
  simp only [Pqxdh.initiate, Pqxdh.PqxdhInitMessage, Pqxdh.«.pqpk», ↓reduceIte, h.dh_pub,
    h.kem_encaps]

/-- **Responder key.** With the one-time prekey, on an encapsulation `c` that `P` decapsulates
under `sk` to `ss`, the key of `respond` at the encoded secrets `ik`, `spk`, `opk`, `sk` and a
message of the encoded public keys `IKA`, `E` and `c` is the encoding of the key derivation at
the responder's input `bobInp G sid a b IKA E ik spk opk` and `ss`, for every session context
`(sid, a, b)`. -/
theorem respond_square_enc
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (sid : SessionId) (a b : PartyId) (IKA E : W) (ik spk opk : S) (sk : SK) (c : C) (ss : SS)
    (hd : P.decaps sk c = some ss) (opk_id : Array Int) :
    Pqxdh.respond (encS ik) (encS spk) (encS opk) (encSK sk) (encW IKA, encW E, encC c, opk_id)
        true =
      encK (H (bobInp G sid a b IKA E ik spk opk, ss)) := by
  simp only [Pqxdh.respond, Pqxdh.«.ik_a», Pqxdh.«.ek_a», Pqxdh.«.kem_ct», ↓reduceIte, h.dh,
    h.kem_decaps sk c ss hd, h.kdf sid a b, bobInp]

/-- **Key agreement.** With the one-time prekey, when `P` decapsulates the encapsulation of the
initiator under the responder's secret key `sk` to the encapsulated secret, the key of
`respond` of `b` on the message of `initiate` of `a` is the initiator's key. -/
theorem respond_square_agree
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (ikA ek ikB spkB opkB : S) (pk : PK) (sk : SK) (m : M)
    (hd : P.decaps sk (encaps pk m).2 = some (encaps pk m).1) (sig₁ sig₂ : Array Int) :
    Pqxdh.respond (encS ikB) (encS spkB) (encS opkB) (encSK sk)
        (Pqxdh.initiate (encS ikA) (encS ek)
          (encW (G.pub ikB), encW (G.pub spkB), encW (G.pub opkB), encPK pk, sig₁, sig₂)
          (encM m) true).2.1
        true =
      (Pqxdh.initiate (encS ikA) (encS ek)
        (encW (G.pub ikB), encW (G.pub spkB), encW (G.pub opkB), encPK pk, sig₁, sig₂)
        (encM m) true).1 := by
  rw [initiate_msg_square_enc h, initiate_square_enc h 0 0 0,
    respond_square_enc h 0 0 0 _ _ _ _ _ _ _ _ hd, aliceInp_eq_bobInp]

end CatCrypt.Crypto.AKE.PQXDH.SquareCorrespondence
