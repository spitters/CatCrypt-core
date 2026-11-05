/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DH.Extraction.X3dh_haxpipe
public import CatCryptCore.Crypto.AKE.X3DHPassiveHops
public import CatCryptCore.Crypto.AdvantageMap

/-!
# The extracted X3DH handshake and the passive model

The haxpipeT extraction of the Rust crate `x3dh-hax` (`X3dh.create_bundle`, `X3dh.initiate`,
`X3dh.respond`) computes on byte arrays under an instance of `X3dh.X3dhDeps`. An encoding
`enc : W → Array Int` of the model's values that carries the three Diffie-Hellman and KDF
operations of the instance to those of the model parameters `P` (`X3dhHom`) makes the extracted
functions compute the encodings of the model's session keys, and the extracted session the
encoding of the model session `x3dh_real P`.

## Main definitions

* `X3dhHom P enc pub` — the equations of `dh_pub`, `dh` and `kdf` on encoded arguments.
* `encOut enc` — the encoding of a session key and a transcript.
* `x3dh_extracted P enc` — five key generations, `create_bundle` and `initiate` (with the
  one-time prekey) on the encoded private keys; the session key and the transcript read from
  the message and the bundle.

## Main results

* `initiate_enc`, `respond_enc` — the extracted session keys at encoded keys are the encodings
  of the model's KDF of the four Diffie-Hellman values.
* `respond_agree` — the keys of the initiator and the responder coincide when `P.dh.ecdh`
  commutes on public keys.
* `x3dh_extracted_eq` — `x3dh_extracted P enc = (x3dh_real P).map (encOut enc)`.
* `x3dh_extracted_advantage_le` — the advantage of every distinguisher `D` between the
  extracted session and the encoded ideal session is at most `x3dhKIReductionBound` at the
  KI adversary of `D ∘ encOut enc`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.X3DH.ExtractedCorrespondence

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.Signal.X3DH
open CatCrypt.Crypto.Signal.Session.X3DHHops
open scoped ENNReal

variable {W : Type} [SampleableType W]

/-- An encoding `enc` of the model's values that carries the operations of the
`X3dh.X3dhDeps` instance in scope to those of `P`: `dh_pub` to the public-key map `pub`, `dh`
to `P.dh.ecdh` and `kdf` to `P.kdf`. -/
structure X3dhHom [X3dh.X3dhDeps] (P : X3DHParams W) (enc : W → Array Int) (pub : W → W) :
    Prop where
  dh_pub : ∀ x, X3dh.dh_pub (enc x) = enc (pub x)
  dh : ∀ x y, X3dh.dh (enc x) (enc y) = enc (P.dh.ecdh x y)
  kdf : ∀ a b c d, X3dh.kdf (enc a) (enc b) (enc c) (enc d) = enc (P.kdf a b c d)

/-- The encoding of a session key and a transcript. -/
def encOut (enc : W → Array Int) (p : W × X3DHTranscript W) :
    Array Int × X3DHTranscript (Array Int) :=
  (enc p.1, enc p.2.1, enc p.2.2.1, enc p.2.2.2.1, enc p.2.2.2.2.1, enc p.2.2.2.2.2)

variable [X3dh.X3dhDeps] {P : X3DHParams W} {enc : W → Array Int} {pub : W → W}

/-- The extracted bundle of encoded private keys holds the encoded public keys. -/
theorem create_bundle_enc (h : X3dhHom P enc pub) (b s o : W) :
    X3dh.create_bundle (enc b) (enc s) (enc o) =
      (enc (pub b), enc (pub s), enc (pub o), X3dh.sign (enc b) (enc (pub s))) := by
  simp only [X3dh.create_bundle, X3dh.X3dhPreKeyBundle, h.dh_pub]

/-- **Initiator key.** With the one-time prekey, the session key of `initiate` at encoded
private keys and a bundle of encoded public keys is the encoding of the model's KDF of the four
Diffie-Hellman values. -/
theorem initiate_enc (h : X3dhHom P enc pub) (a e B S O : W) (sig : Array Int) :
    (X3dh.initiate (enc a) (enc e) (enc B, enc S, enc O, sig) true).1 =
      enc (P.kdf (P.dh.ecdh a S) (P.dh.ecdh e B) (P.dh.ecdh e S) (P.dh.ecdh e O)) := by
  simp only [X3dh.initiate, X3dh.«.ik», X3dh.«.spk», X3dh.«.opk», ↓reduceIte,
    h.dh, h.kdf]

/-- The message of `initiate` at encoded private keys holds the encoded public keys and the
identifier of the one-time prekey. -/
theorem initiate_msg_enc (h : X3dhHom P enc pub) (a e : W)
    (bundle : X3dh.X3dhPreKeyBundle_T) :
    (X3dh.initiate (enc a) (enc e) bundle true).2.1 =
      (enc (pub a), enc (pub e), #[0, 0, 0, 1]) := by
  simp only [X3dh.initiate, X3dh.X3dhInitMessage, ↓reduceIte, h.dh_pub]

/-- **Responder key.** With the one-time prekey, the session key of `respond` at encoded
private keys and a message of encoded public keys is the encoding of the model's KDF of the
four Diffie-Hellman values. -/
theorem respond_enc (h : X3dhHom P enc pub) (b s o A E : W) (opk_id : Array Int) :
    X3dh.respond (enc b) (enc s) (enc o) (enc A, enc E, opk_id) true =
      enc (P.kdf (P.dh.ecdh s A) (P.dh.ecdh b E) (P.dh.ecdh s E) (P.dh.ecdh o E)) := by
  simp only [X3dh.respond, X3dh.«.ik_a», X3dh.«.ek_a», ↓reduceIte, h.dh,
    h.kdf]

/-- **Key agreement.** When `P.dh.ecdh` commutes on the public keys of `pub`, the responder's
key from the initiator's message is the initiator's key. -/
theorem respond_agree (h : X3dhHom P enc pub) (hc : ECDHSym.CommutesOnPub P.dh.ecdh pub)
    (a e b s o : W) :
    X3dh.respond (enc b) (enc s) (enc o)
        (X3dh.initiate (enc a) (enc e) (X3dh.create_bundle (enc b) (enc s) (enc o)) true).2.1
        true =
      (X3dh.initiate (enc a) (enc e) (X3dh.create_bundle (enc b) (enc s) (enc o)) true).1 := by
  rw [initiate_msg_enc h, create_bundle_enc h, initiate_enc h, respond_enc h,
    hc s a, hc b e, hc s e, hc o e]

/-- The extracted session at the flag `use_opk`: five key generations, `create_bundle` and
`initiate` at `use_opk` on the encoded private keys, the session key and the transcript
`(ik_A, ik_B, ek, spk_B, opk_B)` read from the message and the bundle. -/
noncomputable def x3dh_extractedAt (P : X3DHParams W) (enc : W → Array Int) (use_opk : Bool) :
    SPComp (Array Int × X3DHTranscript (Array Int)) :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b =>
  P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  P.dh.keygen.bind fun ek =>
  SPComp.pure
    (let bundle := X3dh.create_bundle (enc ik_b.1) (enc spk_b.1) (enc opk_b.1)
     let r := X3dh.initiate (enc ik_a.1) (enc ek.1) bundle use_opk
     (r.1, X3dh.«.ik_a» r.2.1, X3dh.«.ik» bundle, X3dh.«.ek_a» r.2.1, X3dh.«.spk» bundle,
       X3dh.«.opk» bundle))

/-- The extracted session with the one-time prekey. -/
noncomputable def x3dh_extracted (P : X3DHParams W) (enc : W → Array Int) :
    SPComp (Array Int × X3DHTranscript (Array Int)) :=
  x3dh_extractedAt P enc true

/-- **The extracted session is the encoded model session.** When key generation returns pairs
`(x, pub x)`, the extracted session is `x3dh_real P` followed by the encoding. -/
theorem x3dh_extracted_eq (h : X3dhHom P enc pub)
    (hkg : P.dh.keygen = (SPComp.sample W).bind (fun x => SPComp.pure (x, pub x))) :
    x3dh_extracted P enc = (x3dh_real P).map (encOut enc) := by
  have hk : ∀ a b s o e : W,
      (let bundle := X3dh.create_bundle (enc b) (enc s) (enc o)
       let r := X3dh.initiate (enc a) (enc e) bundle true
       (r.1, X3dh.«.ik_a» r.2.1, X3dh.«.ik» bundle, X3dh.«.ek_a» r.2.1, X3dh.«.spk» bundle,
         X3dh.«.opk» bundle)) =
      encOut enc (P.kdf (P.dh.ecdh a (pub s)) (P.dh.ecdh e (pub b)) (P.dh.ecdh e (pub s))
        (P.dh.ecdh e (pub o)), (pub a, pub b, pub e, pub s, pub o)) := by
    intro a b s o e
    simp only [create_bundle_enc h, initiate_msg_enc h, initiate_enc h, encOut,
      X3dh.«.ik_a», X3dh.«.ik», X3dh.«.ek_a», X3dh.«.spk», X3dh.«.opk»]
  simp only [x3dh_extracted, x3dh_extractedAt, x3dh_real, x3dh_hyb, SPComp.map,
    ECDHSym.keygen_bind hkg, SPComp.bind_assoc, SPComp.pure_bind]
  simp only [hk]

/-- **Key indistinguishability of the extracted session.** When key generation returns pairs
`(x, pub x)` and `P.dh.ecdh` commutes on public keys, the advantage of every distinguisher `D`
between the extracted session and the encoded ideal session is at most
`x3dhKIReductionBound` at the KI adversary of `D ∘ encOut enc`. -/
theorem x3dh_extracted_advantage_le (h : X3dhHom P enc pub)
    (hkg : P.dh.keygen = (SPComp.sample W).bind (fun x => SPComp.pure (x, pub x)))
    (hc : ECDHSym.CommutesOnPub P.dh.ecdh pub)
    (D : Array Int × X3DHTranscript (Array Int) → SPComp Bool) :
    AdvantageA (x3dh_extracted P enc) ((x3dh_ideal P).map (encOut enc)) D ≤
      x3dhKIReductionBound P (kiAdversaryOfDistinguisher P (D ∘ encOut enc)) := by
  rw [x3dh_extracted_eq h hkg, advantageA_map]
  exact x3dh_advantage_le P ⟨pub, hkg, hc⟩ (D ∘ encOut enc)

/-! ## The session without the one-time prekey

At `use_opk = false` the extraction computes three Diffie-Hellman values and applies `kdf3`.
The extracted session at `false` equals the model session of the parameters
`noOpkParams P kdf3`, whose KDF applies `kdf3` to its first three arguments; the transcript
still carries `opk_B`. -/

/-- The parameters `P` with the KDF `kdf3` of the first three Diffie-Hellman values. -/
def noOpkParams (P : X3DHParams W) (kdf3 : W → W → W → W) : X3DHParams W where
  dh := P.dh
  kdf a b c _ := kdf3 a b c

/-- The encoding `enc` carries `kdf3` of the `X3dh.X3dhDeps` instance in scope to `kdf3`. -/
def X3dhKdf3Hom (enc : W → Array Int) (kdf3 : W → W → W → W) : Prop :=
  ∀ a b c, X3dh.kdf3 (enc a) (enc b) (enc c) = enc (kdf3 a b c)

variable {kdf3 : W → W → W → W}

/-- **Initiator key without the one-time prekey.** The session key of `initiate` at encoded
private keys and a bundle of encoded public keys is the encoding of `kdf3` of the three
Diffie-Hellman values. -/
theorem initiate_noOpk_enc (h : X3dhHom P enc pub) (h3 : X3dhKdf3Hom enc kdf3)
    (a e B S O : W) (sig : Array Int) :
    (X3dh.initiate (enc a) (enc e) (enc B, enc S, enc O, sig) false).1 =
      enc (kdf3 (P.dh.ecdh a S) (P.dh.ecdh e B) (P.dh.ecdh e S)) := by
  simp only [X3dh.initiate, X3dh.«.ik», X3dh.«.spk», Bool.false_eq_true, ↓reduceIte, h.dh,
    h3 _ _ _]

/-- The message of `initiate` without the one-time prekey holds the encoded public keys and
the identifier `0`. -/
theorem initiate_msg_noOpk_enc (h : X3dhHom P enc pub) (a e : W)
    (bundle : X3dh.X3dhPreKeyBundle_T) :
    (X3dh.initiate (enc a) (enc e) bundle false).2.1 =
      (enc (pub a), enc (pub e), #[0, 0, 0, 0]) := by
  simp only [X3dh.initiate, X3dh.X3dhInitMessage, Bool.false_eq_true, ↓reduceIte, h.dh_pub]

/-- **Responder key without the one-time prekey.** The session key of `respond` at encoded
private keys and a message of encoded public keys is the encoding of `kdf3` of the three
Diffie-Hellman values. -/
theorem respond_noOpk_enc (h : X3dhHom P enc pub) (h3 : X3dhKdf3Hom enc kdf3)
    (b s o A E : W) (opk_id : Array Int) :
    X3dh.respond (enc b) (enc s) (enc o) (enc A, enc E, opk_id) false =
      enc (kdf3 (P.dh.ecdh s A) (P.dh.ecdh b E) (P.dh.ecdh s E)) := by
  simp only [X3dh.respond, X3dh.«.ik_a», X3dh.«.ek_a», Bool.false_eq_true, ↓reduceIte, h.dh,
    h3 _ _ _]

/-- **Key agreement without the one-time prekey.** When `P.dh.ecdh` commutes on the public
keys of `pub`, the responder's key from the initiator's message is the initiator's key. -/
theorem respond_noOpk_agree (h : X3dhHom P enc pub) (h3 : X3dhKdf3Hom enc kdf3)
    (hc : ECDHSym.CommutesOnPub P.dh.ecdh pub) (a e b s o : W) :
    X3dh.respond (enc b) (enc s) (enc o)
        (X3dh.initiate (enc a) (enc e) (X3dh.create_bundle (enc b) (enc s) (enc o)) false).2.1
        false =
      (X3dh.initiate (enc a) (enc e) (X3dh.create_bundle (enc b) (enc s) (enc o)) false).1 := by
  rw [initiate_msg_noOpk_enc h, create_bundle_enc h, initiate_noOpk_enc h h3,
    respond_noOpk_enc h h3, hc s a, hc b e, hc s e]

/-- **The extracted session without the one-time prekey is the encoded model session** of
`noOpkParams P kdf3`, when key generation returns pairs `(x, pub x)`. -/
theorem x3dh_extracted_noOpk_eq (h : X3dhHom P enc pub) (h3 : X3dhKdf3Hom enc kdf3)
    (hkg : P.dh.keygen = (SPComp.sample W).bind (fun x => SPComp.pure (x, pub x))) :
    x3dh_extractedAt P enc false = (x3dh_real (noOpkParams P kdf3)).map (encOut enc) := by
  have hk : ∀ a b s o e : W,
      (let bundle := X3dh.create_bundle (enc b) (enc s) (enc o)
       let r := X3dh.initiate (enc a) (enc e) bundle false
       (r.1, X3dh.«.ik_a» r.2.1, X3dh.«.ik» bundle, X3dh.«.ek_a» r.2.1, X3dh.«.spk» bundle,
         X3dh.«.opk» bundle)) =
      encOut enc (kdf3 (P.dh.ecdh a (pub s)) (P.dh.ecdh e (pub b)) (P.dh.ecdh e (pub s)),
        (pub a, pub b, pub e, pub s, pub o)) := by
    intro a b s o e
    simp only [create_bundle_enc h, initiate_msg_noOpk_enc h, initiate_noOpk_enc h h3, encOut,
      X3dh.«.ik_a», X3dh.«.ik», X3dh.«.ek_a», X3dh.«.spk», X3dh.«.opk»]
  simp only [x3dh_extractedAt, x3dh_real, x3dh_hyb, noOpkParams, SPComp.map,
    ECDHSym.keygen_bind hkg, SPComp.bind_assoc, SPComp.pure_bind]
  simp only [hk]

/-- **Key indistinguishability of the extracted session without the one-time prekey.** When
key generation returns pairs `(x, pub x)` and `P.dh.ecdh` commutes on public keys, the
advantage of every distinguisher `D` between the extracted session at `use_opk = false` and the
encoded ideal session is at most `x3dhKIReductionBound` of `noOpkParams P kdf3` at the KI
adversary of `D ∘ encOut enc`. -/
theorem x3dh_extracted_noOpk_advantage_le (h : X3dhHom P enc pub) (h3 : X3dhKdf3Hom enc kdf3)
    (hkg : P.dh.keygen = (SPComp.sample W).bind (fun x => SPComp.pure (x, pub x)))
    (hc : ECDHSym.CommutesOnPub P.dh.ecdh pub)
    (D : Array Int × X3DHTranscript (Array Int) → SPComp Bool) :
    AdvantageA (x3dh_extractedAt P enc false) ((x3dh_ideal P).map (encOut enc)) D ≤
      x3dhKIReductionBound (noOpkParams P kdf3)
        (kiAdversaryOfDistinguisher (noOpkParams P kdf3) (D ∘ encOut enc)) := by
  rw [x3dh_extracted_noOpk_eq h h3 hkg, advantageA_map]
  exact x3dh_advantage_le (noOpkParams P kdf3) ⟨pub, hkg, hc⟩ (D ∘ encOut enc)

end CatCrypt.Crypto.Signal.X3DH.ExtractedCorrespondence
