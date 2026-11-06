/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DH.Extraction.X3dh_haxpipe
public import CatCryptCore.Crypto.AKE.X3DHPassiveHops
public import CatCryptCore.Crypto.AKE.FAKESys
public import CatCryptCore.Crypto.AdvantageMap

/-!
# The extracted X3DH handshake and the passive model

The haxpipeT extraction of the Rust crate `x3dh-hax` (`X3dh.create_bundle`, `X3dh.initiate`,
`X3dh.respond`) computes on byte arrays under an instance of `X3dh.X3dhDeps`. Its key
derivation takes a session context, the session identifier, the initiator and the responder,
as its first argument. An encoding `enc : W → Array Int` of the model's values and an encoding
`encCtx` of the contexts that carry the Diffie-Hellman and KDF operations of the instance to a
Diffie-Hellman record `dh` and a context KDF `kdfCtx` (`X3dhHom`) make the extracted functions
at the context `encCtx (sid, a, b)` compute the encodings of the model's session keys, and the
extracted session the encoding of the model session `x3dh_real` of the parameters
`ctxParams dh kdfCtx (sid, a, b)`, whose four-argument KDF is `kdfCtx` at that context.

## Main definitions

* `X3dhCtx` — a session context: the session, the initiator and the responder.
* `X3dhHom dh encCtx kdfCtx enc pub` — the equations of `dh_pub`, `dh` and `kdf` on encoded
  arguments.
* `ctxParams dh kdfCtx c` — the passive-model parameters with the KDF `kdfCtx c`.
* `encOut enc` — the encoding of a session key and a transcript.
* `x3dh_extracted dh enc ctx` — five key generations, `create_bundle` and `initiate` (with the
  one-time prekey) at the context `ctx` on the encoded private keys; the session key and the
  transcript read from the message and the bundle.

## Main results

* `initiate_enc`, `respond_enc` — the extracted session keys at encoded keys and an encoded
  context are the encodings of the context KDF of the four Diffie-Hellman values.
* `respond_agree` — the keys of the initiator and the responder coincide when `dh.ecdh`
  commutes on public keys.
* `x3dh_extracted_eq` — at the context `encCtx (sid, a, b)`, the extracted session is
  `(x3dh_real (ctxParams dh kdfCtx (sid, a, b))).map (encOut enc)`.
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
open CatCrypt.Crypto.UCTransparent.FAKE (SessionId PartyId)
open scoped ENNReal

/-- A session context: the session identifier, the initiator and the responder. -/
abbrev X3dhCtx := SessionId × PartyId × PartyId

variable {W : Type} [SampleableType W]

/-- An encoding `enc` of the model's values and an encoding `encCtx` of the contexts that carry
the operations of the `X3dh.X3dhDeps` instance in scope to the model: `dh_pub` to the
public-key map `pub`, `dh` to `dh.ecdh` and `kdf` at the context `encCtx c` to `kdfCtx c`. -/
structure X3dhHom [X3dh.X3dhDeps] (dh : DDHDef W) (encCtx : X3dhCtx → Array Int)
    (kdfCtx : X3dhCtx → W → W → W → W → W) (enc : W → Array Int) (pub : W → W) :
    Prop where
  dh_pub : ∀ x, X3dh.dh_pub (enc x) = enc (pub x)
  dh : ∀ x y, X3dh.dh (enc x) (enc y) = enc (dh.ecdh x y)
  kdf : ∀ c a b d e,
    X3dh.kdf (encCtx c) (enc a) (enc b) (enc d) (enc e) = enc (kdfCtx c a b d e)

/-- The parameters of the passive model at the context `c`: the Diffie-Hellman record `dh` and
the four-argument KDF `kdfCtx c`. -/
def ctxParams (dh : DDHDef W) (kdfCtx : X3dhCtx → W → W → W → W → W) (c : X3dhCtx) :
    X3DHParams W where
  dh := dh
  kdf d1 d2 d3 d4 := kdfCtx c d1 d2 d3 d4

/-- The encoding of a session key and a transcript. -/
def encOut (enc : W → Array Int) (p : W × X3DHTranscript W) :
    Array Int × X3DHTranscript (Array Int) :=
  (enc p.1, enc p.2.1, enc p.2.2.1, enc p.2.2.2.1, enc p.2.2.2.2.1, enc p.2.2.2.2.2)

variable [X3dh.X3dhDeps] {dh : DDHDef W} {encCtx : X3dhCtx → Array Int}
  {kdfCtx : X3dhCtx → W → W → W → W → W} {enc : W → Array Int} {pub : W → W}

/-- The extracted bundle of encoded private keys holds the encoded public keys. -/
theorem create_bundle_enc (h : X3dhHom dh encCtx kdfCtx enc pub) (b s o : W) :
    X3dh.create_bundle (enc b) (enc s) (enc o) =
      (enc (pub b), enc (pub s), enc (pub o), X3dh.sign (enc b) (enc (pub s))) := by
  simp only [X3dh.create_bundle, X3dh.X3dhPreKeyBundle, h.dh_pub]

/-- **Initiator key.** With the one-time prekey, the session key of `initiate` at the context
`encCtx c`, encoded private keys and a bundle of encoded public keys is the encoding of the
context KDF of the four Diffie-Hellman values. -/
theorem initiate_enc (h : X3dhHom dh encCtx kdfCtx enc pub) (c : X3dhCtx) (a e B S O : W)
    (sig : Array Int) :
    (X3dh.initiate (encCtx c) (enc a) (enc e) (enc B, enc S, enc O, sig) true).1 =
      enc (kdfCtx c (dh.ecdh a S) (dh.ecdh e B) (dh.ecdh e S) (dh.ecdh e O)) := by
  simp only [X3dh.initiate, X3dh.«.ik», X3dh.«.spk», X3dh.«.opk», ↓reduceIte,
    h.dh, h.kdf]

/-- The message of `initiate` at encoded private keys holds the encoded public keys and the
identifier of the one-time prekey. -/
theorem initiate_msg_enc (h : X3dhHom dh encCtx kdfCtx enc pub) (ctx : Array Int) (a e : W)
    (bundle : X3dh.X3dhPreKeyBundle_T) :
    (X3dh.initiate ctx (enc a) (enc e) bundle true).2.1 =
      (enc (pub a), enc (pub e), #[0, 0, 0, 1]) := by
  simp only [X3dh.initiate, X3dh.X3dhInitMessage, ↓reduceIte, h.dh_pub]

/-- **Responder key.** With the one-time prekey, the session key of `respond` at the context
`encCtx c`, encoded private keys and a message of encoded public keys is the encoding of the
context KDF of the four Diffie-Hellman values. -/
theorem respond_enc (h : X3dhHom dh encCtx kdfCtx enc pub) (c : X3dhCtx) (b s o A E : W)
    (opk_id : Array Int) :
    X3dh.respond (encCtx c) (enc b) (enc s) (enc o) (enc A, enc E, opk_id) true =
      enc (kdfCtx c (dh.ecdh s A) (dh.ecdh b E) (dh.ecdh s E) (dh.ecdh o E)) := by
  simp only [X3dh.respond, X3dh.«.ik_a», X3dh.«.ek_a», ↓reduceIte, h.dh,
    h.kdf]

/-- **Key agreement.** When `dh.ecdh` commutes on the public keys of `pub`, the responder's
key at the context `encCtx c` from the initiator's message is the initiator's key at the same
context. -/
theorem respond_agree (h : X3dhHom dh encCtx kdfCtx enc pub)
    (hc : ECDHSym.CommutesOnPub dh.ecdh pub) (c : X3dhCtx) (a e b s o : W) :
    X3dh.respond (encCtx c) (enc b) (enc s) (enc o)
        (X3dh.initiate (encCtx c) (enc a) (enc e)
          (X3dh.create_bundle (enc b) (enc s) (enc o)) true).2.1
        true =
      (X3dh.initiate (encCtx c) (enc a) (enc e)
        (X3dh.create_bundle (enc b) (enc s) (enc o)) true).1 := by
  rw [initiate_msg_enc h, create_bundle_enc h, initiate_enc h, respond_enc h,
    hc s a, hc b e, hc s e, hc o e]

/-- The extracted session at the context `ctx` and the flag `use_opk`: five key generations,
`create_bundle` and `initiate` at `ctx` and `use_opk` on the encoded private keys, the session
key and the transcript `(ik_A, ik_B, ek, spk_B, opk_B)` read from the message and the
bundle. -/
noncomputable def x3dh_extractedAt (dh : DDHDef W) (enc : W → Array Int) (ctx : Array Int)
    (use_opk : Bool) : SPComp (Array Int × X3DHTranscript (Array Int)) :=
  dh.keygen.bind fun ik_a => dh.keygen.bind fun ik_b =>
  dh.keygen.bind fun spk_b => dh.keygen.bind fun opk_b =>
  dh.keygen.bind fun ek =>
  SPComp.pure
    (let bundle := X3dh.create_bundle (enc ik_b.1) (enc spk_b.1) (enc opk_b.1)
     let r := X3dh.initiate ctx (enc ik_a.1) (enc ek.1) bundle use_opk
     (r.1, X3dh.«.ik_a» r.2.1, X3dh.«.ik» bundle, X3dh.«.ek_a» r.2.1, X3dh.«.spk» bundle,
       X3dh.«.opk» bundle))

/-- The extracted session at the context `ctx` with the one-time prekey. -/
noncomputable def x3dh_extracted (dh : DDHDef W) (enc : W → Array Int) (ctx : Array Int) :
    SPComp (Array Int × X3DHTranscript (Array Int)) :=
  x3dh_extractedAt dh enc ctx true

/-- **The extracted session is the encoded model session.** When key generation returns pairs
`(x, pub x)`, the extracted session at the context `encCtx (sid, a, b)` is the model session of
`ctxParams dh kdfCtx (sid, a, b)` followed by the encoding. -/
theorem x3dh_extracted_eq (h : X3dhHom dh encCtx kdfCtx enc pub)
    (hkg : dh.keygen = (SPComp.sample W).bind (fun x => SPComp.pure (x, pub x)))
    (sid : SessionId) (a b : PartyId) :
    x3dh_extracted dh enc (encCtx (sid, a, b)) =
      (x3dh_real (ctxParams dh kdfCtx (sid, a, b))).map (encOut enc) := by
  have hk : ∀ i b' s o e : W,
      (let bundle := X3dh.create_bundle (enc b') (enc s) (enc o)
       let r := X3dh.initiate (encCtx (sid, a, b)) (enc i) (enc e) bundle true
       (r.1, X3dh.«.ik_a» r.2.1, X3dh.«.ik» bundle, X3dh.«.ek_a» r.2.1, X3dh.«.spk» bundle,
         X3dh.«.opk» bundle)) =
      encOut enc (kdfCtx (sid, a, b) (dh.ecdh i (pub s)) (dh.ecdh e (pub b'))
        (dh.ecdh e (pub s)) (dh.ecdh e (pub o)), (pub i, pub b', pub e, pub s, pub o)) := by
    intro i b' s o e
    simp only [create_bundle_enc h, initiate_msg_enc h, initiate_enc h, encOut,
      X3dh.«.ik_a», X3dh.«.ik», X3dh.«.ek_a», X3dh.«.spk», X3dh.«.opk»]
  simp only [x3dh_extracted, x3dh_extractedAt, x3dh_real, x3dh_hyb, ctxParams, SPComp.map,
    ECDHSym.keygen_bind hkg, SPComp.bind_assoc, SPComp.pure_bind]
  simp only [hk]

/-- **Key indistinguishability of the extracted session.** When key generation returns pairs
`(x, pub x)` and `dh.ecdh` commutes on public keys, the advantage of every distinguisher `D`
between the extracted session at the context `encCtx (sid, a, b)` and the encoded ideal
session is at most `x3dhKIReductionBound` of `ctxParams dh kdfCtx (sid, a, b)` at the KI
adversary of `D ∘ encOut enc`. -/
theorem x3dh_extracted_advantage_le (h : X3dhHom dh encCtx kdfCtx enc pub)
    (hkg : dh.keygen = (SPComp.sample W).bind (fun x => SPComp.pure (x, pub x)))
    (hc : ECDHSym.CommutesOnPub dh.ecdh pub) (sid : SessionId) (a b : PartyId)
    (D : Array Int × X3DHTranscript (Array Int) → SPComp Bool) :
    AdvantageA (x3dh_extracted dh enc (encCtx (sid, a, b)))
        ((x3dh_ideal (ctxParams dh kdfCtx (sid, a, b))).map (encOut enc)) D ≤
      x3dhKIReductionBound (ctxParams dh kdfCtx (sid, a, b))
        (kiAdversaryOfDistinguisher (ctxParams dh kdfCtx (sid, a, b)) (D ∘ encOut enc)) := by
  rw [x3dh_extracted_eq h hkg, advantageA_map]
  exact x3dh_advantage_le (ctxParams dh kdfCtx (sid, a, b)) ⟨pub, hkg, hc⟩ (D ∘ encOut enc)

/-! ## The session without the one-time prekey

At `use_opk = false` the extraction computes three Diffie-Hellman values and applies `kdf3`
at the context. The extracted session at `false` and the context `encCtx c` equals the model
session of the parameters `noOpkParams (ctxParams dh kdfCtx c) (kdf3Ctx c)`, whose KDF applies
`kdf3Ctx c` to its first three arguments; the transcript still carries `opk_B`. -/

/-- The parameters `P` with the KDF `kdf3` of the first three Diffie-Hellman values. -/
def noOpkParams (P : X3DHParams W) (kdf3 : W → W → W → W) : X3DHParams W where
  dh := P.dh
  kdf a b c _ := kdf3 a b c

/-- The encodings `encCtx` and `enc` carry `kdf3` of the `X3dh.X3dhDeps` instance in scope at
the context `encCtx c` to `kdf3Ctx c`. -/
def X3dhKdf3Hom (encCtx : X3dhCtx → Array Int) (enc : W → Array Int)
    (kdf3Ctx : X3dhCtx → W → W → W → W) : Prop :=
  ∀ c a b d, X3dh.kdf3 (encCtx c) (enc a) (enc b) (enc d) = enc (kdf3Ctx c a b d)

variable {kdf3Ctx : X3dhCtx → W → W → W → W}

/-- **Initiator key without the one-time prekey.** The session key of `initiate` at the
context `encCtx c`, encoded private keys and a bundle of encoded public keys is the encoding of
`kdf3Ctx c` of the three Diffie-Hellman values. -/
theorem initiate_noOpk_enc (h : X3dhHom dh encCtx kdfCtx enc pub)
    (h3 : X3dhKdf3Hom encCtx enc kdf3Ctx) (c : X3dhCtx) (a e B S O : W) (sig : Array Int) :
    (X3dh.initiate (encCtx c) (enc a) (enc e) (enc B, enc S, enc O, sig) false).1 =
      enc (kdf3Ctx c (dh.ecdh a S) (dh.ecdh e B) (dh.ecdh e S)) := by
  simp only [X3dh.initiate, X3dh.«.ik», X3dh.«.spk», Bool.false_eq_true, ↓reduceIte, h.dh,
    h3 _ _ _ _]

/-- The message of `initiate` without the one-time prekey holds the encoded public keys and
the identifier `0`. -/
theorem initiate_msg_noOpk_enc (h : X3dhHom dh encCtx kdfCtx enc pub) (ctx : Array Int)
    (a e : W) (bundle : X3dh.X3dhPreKeyBundle_T) :
    (X3dh.initiate ctx (enc a) (enc e) bundle false).2.1 =
      (enc (pub a), enc (pub e), #[0, 0, 0, 0]) := by
  simp only [X3dh.initiate, X3dh.X3dhInitMessage, Bool.false_eq_true, ↓reduceIte, h.dh_pub]

/-- **Responder key without the one-time prekey.** The session key of `respond` at the context
`encCtx c`, encoded private keys and a message of encoded public keys is the encoding of
`kdf3Ctx c` of the three Diffie-Hellman values. -/
theorem respond_noOpk_enc (h : X3dhHom dh encCtx kdfCtx enc pub)
    (h3 : X3dhKdf3Hom encCtx enc kdf3Ctx) (c : X3dhCtx) (b s o A E : W) (opk_id : Array Int) :
    X3dh.respond (encCtx c) (enc b) (enc s) (enc o) (enc A, enc E, opk_id) false =
      enc (kdf3Ctx c (dh.ecdh s A) (dh.ecdh b E) (dh.ecdh s E)) := by
  simp only [X3dh.respond, X3dh.«.ik_a», X3dh.«.ek_a», Bool.false_eq_true, ↓reduceIte, h.dh,
    h3 _ _ _ _]

/-- **Key agreement without the one-time prekey.** When `dh.ecdh` commutes on the public keys
of `pub`, the responder's key at the context `encCtx c` from the initiator's message is the
initiator's key at the same context. -/
theorem respond_noOpk_agree (h : X3dhHom dh encCtx kdfCtx enc pub)
    (h3 : X3dhKdf3Hom encCtx enc kdf3Ctx) (hc : ECDHSym.CommutesOnPub dh.ecdh pub)
    (c : X3dhCtx) (a e b s o : W) :
    X3dh.respond (encCtx c) (enc b) (enc s) (enc o)
        (X3dh.initiate (encCtx c) (enc a) (enc e)
          (X3dh.create_bundle (enc b) (enc s) (enc o)) false).2.1
        false =
      (X3dh.initiate (encCtx c) (enc a) (enc e)
        (X3dh.create_bundle (enc b) (enc s) (enc o)) false).1 := by
  rw [initiate_msg_noOpk_enc h, create_bundle_enc h, initiate_noOpk_enc h h3,
    respond_noOpk_enc h h3, hc s a, hc b e, hc s e]

/-- **The extracted session without the one-time prekey is the encoded model session** of
`noOpkParams (ctxParams dh kdfCtx (sid, a, b)) (kdf3Ctx (sid, a, b))` at the context
`encCtx (sid, a, b)`, when key generation returns pairs `(x, pub x)`. -/
theorem x3dh_extracted_noOpk_eq (h : X3dhHom dh encCtx kdfCtx enc pub)
    (h3 : X3dhKdf3Hom encCtx enc kdf3Ctx)
    (hkg : dh.keygen = (SPComp.sample W).bind (fun x => SPComp.pure (x, pub x)))
    (sid : SessionId) (a b : PartyId) :
    x3dh_extractedAt dh enc (encCtx (sid, a, b)) false =
      (x3dh_real (noOpkParams (ctxParams dh kdfCtx (sid, a, b)) (kdf3Ctx (sid, a, b)))).map
        (encOut enc) := by
  have hk : ∀ i b' s o e : W,
      (let bundle := X3dh.create_bundle (enc b') (enc s) (enc o)
       let r := X3dh.initiate (encCtx (sid, a, b)) (enc i) (enc e) bundle false
       (r.1, X3dh.«.ik_a» r.2.1, X3dh.«.ik» bundle, X3dh.«.ek_a» r.2.1, X3dh.«.spk» bundle,
         X3dh.«.opk» bundle)) =
      encOut enc (kdf3Ctx (sid, a, b) (dh.ecdh i (pub s)) (dh.ecdh e (pub b'))
        (dh.ecdh e (pub s)), (pub i, pub b', pub e, pub s, pub o)) := by
    intro i b' s o e
    simp only [create_bundle_enc h, initiate_msg_noOpk_enc h, initiate_noOpk_enc h h3, encOut,
      X3dh.«.ik_a», X3dh.«.ik», X3dh.«.ek_a», X3dh.«.spk», X3dh.«.opk»]
  simp only [x3dh_extractedAt, x3dh_real, x3dh_hyb, noOpkParams, ctxParams, SPComp.map,
    ECDHSym.keygen_bind hkg, SPComp.bind_assoc, SPComp.pure_bind]
  simp only [hk]

/-- **Key indistinguishability of the extracted session without the one-time prekey.** When
key generation returns pairs `(x, pub x)` and `dh.ecdh` commutes on public keys, the advantage
of every distinguisher `D` between the extracted session at `use_opk = false` and the context
`encCtx (sid, a, b)` and the encoded ideal session is at most `x3dhKIReductionBound` of
`noOpkParams (ctxParams dh kdfCtx (sid, a, b)) (kdf3Ctx (sid, a, b))` at the KI adversary of
`D ∘ encOut enc`. -/
theorem x3dh_extracted_noOpk_advantage_le (h : X3dhHom dh encCtx kdfCtx enc pub)
    (h3 : X3dhKdf3Hom encCtx enc kdf3Ctx)
    (hkg : dh.keygen = (SPComp.sample W).bind (fun x => SPComp.pure (x, pub x)))
    (hc : ECDHSym.CommutesOnPub dh.ecdh pub) (sid : SessionId) (a b : PartyId)
    (D : Array Int × X3DHTranscript (Array Int) → SPComp Bool) :
    AdvantageA (x3dh_extractedAt dh enc (encCtx (sid, a, b)) false)
        ((x3dh_ideal (ctxParams dh kdfCtx (sid, a, b))).map (encOut enc)) D ≤
      x3dhKIReductionBound (noOpkParams (ctxParams dh kdfCtx (sid, a, b)) (kdf3Ctx (sid, a, b)))
        (kiAdversaryOfDistinguisher
          (noOpkParams (ctxParams dh kdfCtx (sid, a, b)) (kdf3Ctx (sid, a, b)))
          (D ∘ encOut enc)) := by
  rw [x3dh_extracted_noOpk_eq h h3 hkg, advantageA_map]
  exact x3dh_advantage_le (noOpkParams (ctxParams dh kdfCtx (sid, a, b)) (kdf3Ctx (sid, a, b)))
    ⟨pub, hkg, hc⟩ (D ∘ encOut enc)

end CatCrypt.Crypto.Signal.X3DH.ExtractedCorrespondence
