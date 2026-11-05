/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDH.Extraction.Pqxdh_haxpipe
public import CatCryptCore.Crypto.AKE.PQXDHPassiveHops
public import CatCryptCore.Crypto.AdvantageMap

/-!
# The extracted PQXDH handshake and the passive model

The haxpipeT extraction of the Rust crate `pqxdh-hax` (`Pqxdh.create_bundle`, `Pqxdh.initiate`,
`Pqxdh.respond`) computes on byte arrays under an instance of `Pqxdh.PqxdhDeps`. An encoding
`E` of the model's values (Diffie-Hellman values and KEM secrets, KEM public keys, secret keys,
encapsulations and seeds) that carries the Diffie-Hellman, KEM and KDF operations of the
instance to those of the model parameters `P` (`PqxdhHom`) makes the extracted functions
compute the encodings of the model's session keys, and the extracted session the encoding of
the model session `pqxdh_real P`. The signatures of the bundle, and the message
`kem_pk_encode pqpk` that the second of them signs, do not enter the session key or the
transcript, so `PqxdhHom` constrains neither `sign`, `verify` nor `kem_pk_encode`.

## The model statement

The extracted computation is one honest session with a KDF that is a fixed function, so its
model is the passive single-session game `CatCryptCore.Crypto.AKE.PQXDHPassive`, whose real
session draws the same key pairs, KEM seed and message and applies the same KDF. The real side
of the multi-session square `CatCryptCore.Crypto.AKE.PQXDHSquare` models the KDF as a lazily
sampled random function and runs every session as an oracle query of the adversary; the
extracted code, whose KDF is a function of the `Pqxdh.PqxdhDeps` instance, is not equal to
that game.

## Main definitions

* `PqxdhEnc` — the five encodings into byte arrays.
* `PqxdhHom P E pub` — the equations of `dh_pub`, `dh`, `kem_keygen`, `kem_encaps`,
  `kem_decaps` and `kdf` on encoded arguments.
* `encOut E` — the encoding of a session key and a transcript.
* `pqxdh_extracted P E` — five key generations, a KEM seed and message, `create_bundle` and
  `initiate` (with the one-time prekey) on the encoded values; the session key and the
  transcript read from the message and the bundle.

## Main results

* `initiate_enc`, `respond_enc` — the extracted session keys at encoded values are the
  encodings of the model's KDF of the four Diffie-Hellman values and the KEM secret.
* `respond_agree` — the keys of the initiator and the responder coincide when `P.dh.ecdh`
  commutes on public keys and the model's KEM is correct.
* `pqxdh_extracted_eq` — `pqxdh_extracted P E = (pqxdh_real P).map (encOut E)`.
* `pqxdh_extracted_advantage_le` — the advantage of every distinguisher `D` between the
  extracted session and the encoded ideal session is at most `pqxdhKIReductionBound` at the KI
  adversary of `D ∘ encOut E`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.PQXDH.ExtractedCorrespondence

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.Signal.PQXDHPassive
open scoped ENNReal

/-- Encodings of the model's values into the byte arrays of the extraction: Diffie-Hellman
values, KEM messages and secrets (`w`), KEM public keys, secret keys, encapsulations and key
generation seeds. -/
structure PqxdhEnc (W PK SK C Sd : Type) where
  /-- Diffie-Hellman values, KEM messages and KEM secrets. -/
  w : W → Array Int
  /-- KEM public keys. -/
  pk : PK → Array Int
  /-- KEM secret keys. -/
  sk : SK → Array Int
  /-- KEM encapsulations. -/
  ct : C → Array Int
  /-- KEM key generation seeds. -/
  seed : Sd → Array Int

variable {W PK SK C Sd : Type} [SampleableType W] [SampleableType Sd]

/-- An encoding `E` of the model's values that carries the operations of the
`Pqxdh.PqxdhDeps` instance in scope to those of `P`: `dh_pub` to the public-key map `pub`,
`dh` to `P.dh.ecdh`, the KEM operations to those of `P` and `kdf` to `P.kdf`. -/
structure PqxdhHom [Pqxdh.PqxdhDeps] (P : PassiveParams W PK SK C Sd)
    (E : PqxdhEnc W PK SK C Sd) (pub : W → W) : Prop where
  dh_pub : ∀ x, Pqxdh.dh_pub (E.w x) = E.w (pub x)
  dh : ∀ x y, Pqxdh.dh (E.w x) (E.w y) = E.w (P.dh.ecdh x y)
  kem_keygen : ∀ sd, Pqxdh.kem_keygen (E.seed sd) =
    (E.pk (P.kemKeygen sd).1, E.sk (P.kemKeygen sd).2)
  kem_encaps : ∀ pk m, Pqxdh.kem_encaps (E.pk pk) (E.w m) =
    (E.ct (P.kemEncaps pk m).1, E.w (P.kemEncaps pk m).2)
  kem_decaps : ∀ sk c, Pqxdh.kem_decaps (E.sk sk) (E.ct c) = E.w (P.kemDecaps sk c)
  kdf : ∀ a b c d k,
    Pqxdh.kdf (E.w a) (E.w b) (E.w c) (E.w d) (E.w k) = E.w (P.kdf a b c d k)

/-- The transcript of the extracted session: seven byte arrays. -/
abbrev ExtractedTranscript := PQXDHTranscript (Array Int) (Array Int) (Array Int)

/-- The encoding of a session key and a transcript. -/
def encOut (E : PqxdhEnc W PK SK C Sd) (p : W × PQXDHTranscript W PK C) :
    Array Int × ExtractedTranscript :=
  (E.w p.1, E.w p.2.1, E.w p.2.2.1, E.w p.2.2.2.1, E.w p.2.2.2.2.1, E.w p.2.2.2.2.2.1,
    E.pk p.2.2.2.2.2.2.1, E.ct p.2.2.2.2.2.2.2)

variable [Pqxdh.PqxdhDeps] {P : PassiveParams W PK SK C Sd} {E : PqxdhEnc W PK SK C Sd}
  {pub : W → W}

omit [SampleableType Sd] in
/-- The extracted bundle of encoded private keys and seed holds the encoded public keys, the
encoded KEM public key and the signatures of the signed prekey and of `kem_pk_encode` of the
KEM public key; the second component is the encoded KEM secret key. -/
theorem create_bundle_enc (h : PqxdhHom P E pub) (b s o : W) (sd : Sd) :
    Pqxdh.create_bundle (E.w b) (E.w s) (E.w o) (E.seed sd) =
      ((E.w (pub b), E.w (pub s), E.w (pub o), E.pk (P.kemKeygen sd).1,
        Pqxdh.sign (E.w b) (E.w (pub s)),
        Pqxdh.sign (E.w b) (Pqxdh.kem_pk_encode (E.pk (P.kemKeygen sd).1))),
        E.sk (P.kemKeygen sd).2) := by
  simp only [Pqxdh.create_bundle, Pqxdh.PqxdhPreKeyBundle, h.dh_pub, h.kem_keygen]

omit [SampleableType Sd] in
/-- **Initiator key.** With the one-time prekey, the session key of `initiate` at encoded
private keys, a bundle of encoded public keys and an encoded KEM message is the encoding of the
model's KDF of the four Diffie-Hellman values and the encapsulated secret. -/
theorem initiate_enc (h : PqxdhHom P E pub) (a e B S O m : W) (pk : PK)
    (sig₁ sig₂ : Array Int) :
    (Pqxdh.initiate (E.w a) (E.w e) (E.w B, E.w S, E.w O, E.pk pk, sig₁, sig₂) (E.w m)
        true).1 =
      E.w (P.kdf (P.dh.ecdh a S) (P.dh.ecdh e B) (P.dh.ecdh e S) (P.dh.ecdh e O)
        (P.kemEncaps pk m).2) := by
  simp only [Pqxdh.initiate, Pqxdh.«.ik», Pqxdh.«.spk», Pqxdh.«.opk», Pqxdh.«.pqpk»,
    ↓reduceIte, h.dh, h.kem_encaps, h.kdf]

omit [SampleableType Sd] in
/-- The message of `initiate` at encoded private keys, a bundle with an encoded KEM public key
and an encoded KEM message holds the encoded public keys, the encoded encapsulation and the
identifier of the one-time prekey. -/
theorem initiate_msg_enc (h : PqxdhHom P E pub) (a e m : W) (pk : PK)
    (ik spk opk sig₁ sig₂ : Array Int) :
    (Pqxdh.initiate (E.w a) (E.w e) (ik, spk, opk, E.pk pk, sig₁, sig₂) (E.w m) true).2.1 =
      (E.w (pub a), E.w (pub e), E.ct (P.kemEncaps pk m).1, #[0, 0, 0, 1]) := by
  simp only [Pqxdh.initiate, Pqxdh.PqxdhInitMessage, Pqxdh.«.pqpk», ↓reduceIte,
    h.dh_pub, h.kem_encaps]

omit [SampleableType Sd] in
/-- **Responder key.** With the one-time prekey, the session key of `respond` at encoded private
keys, an encoded KEM secret key and a message of encoded public keys and an encoded
encapsulation is the encoding of the model's KDF of the four Diffie-Hellman values and the
decapsulated secret. -/
theorem respond_enc (h : PqxdhHom P E pub) (b s o A Ek : W) (sk : SK) (c : C)
    (opk_id : Array Int) :
    Pqxdh.respond (E.w b) (E.w s) (E.w o) (E.sk sk) (E.w A, E.w Ek, E.ct c, opk_id) true =
      E.w (P.kdf (P.dh.ecdh s A) (P.dh.ecdh b Ek) (P.dh.ecdh s Ek) (P.dh.ecdh o Ek)
        (P.kemDecaps sk c)) := by
  simp only [Pqxdh.respond, Pqxdh.«.ik_a», Pqxdh.«.ek_a», Pqxdh.«.kem_ct»,
    ↓reduceIte, h.dh, h.kem_decaps, h.kdf]

omit [SampleableType Sd] in
/-- **Key agreement.** When `P.dh.ecdh` commutes on the public keys of `pub` and the KEM of `P`
is correct, the responder's key from the bundle's KEM secret key and the initiator's message
is the initiator's key. -/
theorem respond_agree (h : PqxdhHom P E pub) (hc : ECDHSym.CommutesOnPub P.dh.ecdh pub)
    (hk : P.KemCorrect) (a e b s o m : W) (sd : Sd) :
    Pqxdh.respond (E.w b) (E.w s) (E.w o)
        (Pqxdh.create_bundle (E.w b) (E.w s) (E.w o) (E.seed sd)).2
        (Pqxdh.initiate (E.w a) (E.w e)
          (Pqxdh.create_bundle (E.w b) (E.w s) (E.w o) (E.seed sd)).1 (E.w m) true).2.1
        true =
      (Pqxdh.initiate (E.w a) (E.w e)
        (Pqxdh.create_bundle (E.w b) (E.w s) (E.w o) (E.seed sd)).1 (E.w m) true).1 := by
  rw [create_bundle_enc h, initiate_msg_enc h, initiate_enc h, respond_enc h, hk sd m,
    hc s a, hc b e, hc s e, hc o e]

/-- The extracted session: five key generations, a uniform KEM seed and message,
`create_bundle` and `initiate` with the one-time prekey on the encoded values, the session key
and the transcript `(ik_A, ik_B, ek, spk_B, opk_B, pk, ct)` read from the message and the
bundle. -/
noncomputable def pqxdh_extracted (P : PassiveParams W PK SK C Sd)
    (E : PqxdhEnc W PK SK C Sd) : SPComp (Array Int × ExtractedTranscript) :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b =>
  P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  P.dh.keygen.bind fun ek =>
  (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
  SPComp.pure
    (let bundle := (Pqxdh.create_bundle (E.w ik_b.1) (E.w spk_b.1) (E.w opk_b.1) (E.seed sd)).1
     let r := Pqxdh.initiate (E.w ik_a.1) (E.w ek.1) bundle (E.w m) true
     (r.1, Pqxdh.«.ik_a» r.2.1, Pqxdh.«.ik» bundle, Pqxdh.«.ek_a» r.2.1, Pqxdh.«.spk» bundle,
       Pqxdh.«.opk» bundle, Pqxdh.«.pqpk» bundle, Pqxdh.«.kem_ct» r.2.1))

/-- **The extracted session is the encoded model session.** When key generation returns pairs
`(x, pub x)`, the extracted session is `pqxdh_real P` followed by the encoding. -/
theorem pqxdh_extracted_eq (h : PqxdhHom P E pub)
    (hkg : P.dh.keygen = (SPComp.sample W).bind (fun x => SPComp.pure (x, pub x))) :
    pqxdh_extracted P E = (pqxdh_real P).map (encOut E) := by
  have hk : ∀ (a b s o e m : W) (sd : Sd),
      (let bundle := (Pqxdh.create_bundle (E.w b) (E.w s) (E.w o) (E.seed sd)).1
       let r := Pqxdh.initiate (E.w a) (E.w e) bundle (E.w m) true
       (r.1, Pqxdh.«.ik_a» r.2.1, Pqxdh.«.ik» bundle, Pqxdh.«.ek_a» r.2.1, Pqxdh.«.spk» bundle,
         Pqxdh.«.opk» bundle, Pqxdh.«.pqpk» bundle, Pqxdh.«.kem_ct» r.2.1)) =
      encOut E (P.kdf (P.dh.ecdh a (pub s)) (P.dh.ecdh e (pub b)) (P.dh.ecdh e (pub s))
        (P.dh.ecdh e (pub o)) (P.kemEncaps (P.kemKeygen sd).1 m).2,
        (pub a, pub b, pub e, pub s, pub o, (P.kemKeygen sd).1,
          (P.kemEncaps (P.kemKeygen sd).1 m).1)) := by
    intro a b s o e m sd
    simp only [create_bundle_enc h, initiate_msg_enc h, initiate_enc h, encOut,
      Pqxdh.«.ik_a», Pqxdh.«.ik», Pqxdh.«.ek_a», Pqxdh.«.spk», Pqxdh.«.opk», Pqxdh.«.pqpk»,
      Pqxdh.«.kem_ct»]
  simp only [pqxdh_extracted, pqxdh_real, pqxdh_hyb, realDH, SPComp.map,
    ECDHSym.keygen_bind hkg, SPComp.bind_assoc, SPComp.pure_bind]
  simp only [hk]

/-- **Key indistinguishability of the extracted session.** When key generation returns pairs
`(x, pub x)` and `P.dh.ecdh` commutes on public keys, the advantage of every distinguisher `D`
between the extracted session and the encoded ideal session is at most
`pqxdhKIReductionBound` at the KI adversary of `D ∘ encOut E`: the KEM advantage of `kemRed`,
the DDH advantages of the four hop reductions and the KDF advantage of `kdfReduction`. -/
theorem pqxdh_extracted_advantage_le (h : PqxdhHom P E pub)
    (hkg : P.dh.keygen = (SPComp.sample W).bind (fun x => SPComp.pure (x, pub x)))
    (hc : ECDHSym.CommutesOnPub P.dh.ecdh pub)
    (D : Array Int × ExtractedTranscript → SPComp Bool) :
    AdvantageA (pqxdh_extracted P E) ((pqxdh_ideal P).map (encOut E)) D ≤
      pqxdhKIReductionBound P (kiAdversaryOfDistinguisher P (D ∘ encOut E)) := by
  rw [pqxdh_extracted_eq h hkg, advantageA_map]
  exact pqxdh_advantage_le P ⟨pub, hkg, hc⟩ (D ∘ encOut E)

end CatCrypt.Crypto.Signal.PQXDH.ExtractedCorrespondence
