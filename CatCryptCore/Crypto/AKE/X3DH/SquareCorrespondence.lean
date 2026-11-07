/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DH.Extraction.X3dh_haxpipe
public import CatCryptCore.Crypto.AKE.X3DHSquare

/-!
# The extracted X3DH handshake and the key-derivation input of the square model

The square model `CatCryptCore.Crypto.AKE.X3DHSquare` derives the key of a session from an
input `Inp W`: the session, the initiator, the responder and the four Diffie-Hellman values over
a group `G : DHGroup S W`, computed by the initiator as `aliceInp` and by the responder as
`bobInp`. The extracted functions `X3dh.initiate` and `X3dh.respond` of the Rust crate
`x3dh-hax` take the session context `(sid, initiator, responder)` as their first argument and
pass it to the KDF. They apply the input check `valid_pub` to the peer public keys and return
`none` when one fails it, and otherwise `some` of `X3dh.initiate_checked` and
`X3dh.respond_checked`, which compute the key.

For a model key derivation `H : Inp W → K` and encodings of the context, the scalars `S`, the
group elements `W` and the keys `K` under which the operations of the `X3dh.X3dhDeps` instance
in scope are those of the model (`X3dhSquareHom`: `dh_pub` is `G.pub`, `dh` is `G.exp`, `kdf`
at an encoded context and encoded values is the encoding of `H` of the corresponding input,
and the encoding of every group element passes the check), `initiate` and `respond` return
`some` of the checked functions on encoded group elements, the session key of
`initiate_checked` is the encoding of `H` of `aliceInp`, the key of `respond_checked` the
encoding of `H` of `bobInp`, and the two agree on an unmodified exchange by
`aliceInp_eq_bobInp`.

The equations are stated with the one-time prekey (`use_opk = true`) only: the input `Inp W`
has the fourth Diffie-Hellman value as a field, and the branch without the one-time prekey,
whose KDF takes three values, has no counterpart in it.

## Main definitions

* `X3dhSquareHom G encCtx encS encW encK H` — the equations of `dh_pub`, `dh` and `kdf` on
  encoded arguments, and the check `valid_pub` on encoded group elements.

## Main results

* `initiate_square_eq_some`, `respond_square_eq_some` — on encoded group elements of the peer,
  `initiate` and `respond` return `some` of `initiate_checked` and `respond_checked`.
* `initiate_square_enc` — the session key of `initiate_checked` is the encoding of
  `H (aliceInp G sid a b ik ek IKB SPKB OPKB)`.
* `respond_square_enc` — the key of `respond_checked` is the encoding of
  `H (bobInp G sid a b IKA E ik spk opk)`.
* `respond_square_agree` — the responder's key from the initiator's message is the
  initiator's key; `initiate_respond_square_agree` states it for `initiate` and `respond`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DH.SquareCorrespondence

open CatCrypt.Crypto.PAKE.DHExtract (DHGroup)
open CatCrypt.Crypto.UCTransparent.FAKE (SessionId PartyId)
open CatCrypt.Crypto.AKE.X3DHSquare (Inp aliceInp bobInp aliceInp_eq_bobInp)

variable {S W K : Type} [Field S]

/-- Encodings of the session contexts, the scalars, the group elements and the keys that carry
the operations of the `X3dh.X3dhDeps` instance in scope to the square model: `dh_pub` to
`G.pub`, `dh` of a scalar and a group element to `G.exp`, and `kdf` at the context
`encCtx (sid, a, b)` to the key derivation `H` at the input of `(sid, a, b)` and the four
values; the input check `valid_pub` accepts the encoding of every group element. -/
structure X3dhSquareHom [X3dh.X3dhDeps] (G : DHGroup S W)
    (encCtx : SessionId × PartyId × PartyId → Array Int) (encS : S → Array Int)
    (encW : W → Array Int) (encK : K → Array Int) (H : Inp W → K) : Prop where
  dh_pub : ∀ x, X3dh.dh_pub (encS x) = encW (G.pub x)
  dh : ∀ x Y, X3dh.dh (encS x) (encW Y) = encW (G.exp Y x)
  kdf : ∀ sid a b d1 d2 d3 d4,
    X3dh.kdf (encCtx (sid, a, b)) (encW d1) (encW d2) (encW d3) (encW d4) =
      encK (H ⟨sid, a, b, d1, d2, d3, d4⟩)
  valid_pub : ∀ Y, X3dh.valid_pub (encW Y) = true

variable [X3dh.X3dhDeps] {G : DHGroup S W} {encCtx : SessionId × PartyId × PartyId → Array Int}
  {encS : S → Array Int} {encW : W → Array Int} {encK : K → Array Int} {H : Inp W → K}

/-- The extracted bundle of encoded secrets holds the encoded public keys. -/
theorem create_bundle_square_enc (h : X3dhSquareHom G encCtx encS encW encK H) (ik spk opk : S) :
    X3dh.create_bundle (encS ik) (encS spk) (encS opk) =
      (encW (G.pub ik), encW (G.pub spk), encW (G.pub opk),
        X3dh.sign (encS ik) (encW (G.pub spk))) := by
  simp only [X3dh.create_bundle, X3dh.X3dhPreKeyBundle, h.dh_pub]

/-- **The initiator's input check.** On a bundle of encoded group elements, `initiate` returns
`some` of `initiate_checked`. -/
theorem initiate_square_eq_some (h : X3dhSquareHom G encCtx encS encW encK H)
    (ctx ik ek : Array Int) (IKB SPKB OPKB : W) (sig : Array Int) (use_opk : Bool) :
    X3dh.initiate ctx ik ek (encW IKB, encW SPKB, encW OPKB, sig) use_opk =
      some (X3dh.initiate_checked ctx ik ek (encW IKB, encW SPKB, encW OPKB, sig) use_opk) := by
  simp only [X3dh.initiate, X3dh.«.ik», X3dh.«.spk», X3dh.«.opk», Hax.band, Hax.bor,
    h.valid_pub, Bool.true_and, Bool.or_true, ↓reduceIte]

/-- **The responder's input check.** On a message of encoded group elements, `respond` returns
`some` of `respond_checked`. -/
theorem respond_square_eq_some (h : X3dhSquareHom G encCtx encS encW encK H)
    (ctx ik spk opk : Array Int) (IKA E : W) (opk_id : Array Int) (use_opk : Bool) :
    X3dh.respond ctx ik spk opk (encW IKA, encW E, opk_id) use_opk =
      some (X3dh.respond_checked ctx ik spk opk (encW IKA, encW E, opk_id) use_opk) := by
  simp only [X3dh.respond, X3dh.«.ik_a», X3dh.«.ek_a», Hax.band, h.valid_pub, Bool.and_self,
    ↓reduceIte]

/-- The message of `initiate_checked` with the one-time prekey at encoded secrets holds the
encoded public keys and the identifier of the one-time prekey. -/
theorem initiate_msg_square_enc (h : X3dhSquareHom G encCtx encS encW encK H) (ctx : Array Int)
    (ik ek : S) (bundle : X3dh.X3dhPreKeyBundle_T) :
    (X3dh.initiate_checked ctx (encS ik) (encS ek) bundle true).2.1 =
      (encW (G.pub ik), encW (G.pub ek), #[0, 0, 0, 1]) := by
  simp only [X3dh.initiate_checked, X3dh.X3dhInitMessage, ↓reduceIte, h.dh_pub]

/-- **Initiator key.** The session key of `initiate_checked` with the one-time prekey, at the
context `encCtx (sid, a, b)`, the encoded identity and ephemeral secrets `ik`, `ek` and a bundle
of the encoded public keys `IKB`, `SPKB`, `OPKB`, is the encoding of the key derivation at the
initiator's input `aliceInp G sid a b ik ek IKB SPKB OPKB`. -/
theorem initiate_square_enc (h : X3dhSquareHom G encCtx encS encW encK H) (sid : SessionId)
    (a b : PartyId) (ik ek : S) (IKB SPKB OPKB : W) (sig : Array Int) :
    (X3dh.initiate_checked (encCtx (sid, a, b)) (encS ik) (encS ek)
        (encW IKB, encW SPKB, encW OPKB, sig) true).1 =
      encK (H (aliceInp G sid a b ik ek IKB SPKB OPKB)) := by
  simp only [X3dh.initiate_checked, X3dh.«.ik», X3dh.«.spk», X3dh.«.opk», ↓reduceIte, h.dh,
    h.kdf, aliceInp]

/-- **Responder key.** The session key of `respond_checked` with the one-time prekey, at the
context `encCtx (sid, a, b)`, the encoded secrets `ik`, `spk`, `opk` and a message of the
encoded public keys `IKA`, `E`, is the encoding of the key derivation at the responder's input
`bobInp G sid a b IKA E ik spk opk`. -/
theorem respond_square_enc (h : X3dhSquareHom G encCtx encS encW encK H) (sid : SessionId)
    (a b : PartyId) (IKA E : W) (ik spk opk : S) (opk_id : Array Int) :
    X3dh.respond_checked (encCtx (sid, a, b)) (encS ik) (encS spk) (encS opk)
        (encW IKA, encW E, opk_id) true =
      encK (H (bobInp G sid a b IKA E ik spk opk)) := by
  simp only [X3dh.respond_checked, X3dh.«.ik_a», X3dh.«.ek_a», ↓reduceIte, h.dh, h.kdf, bobInp]

/-- **Key agreement.** With the one-time prekey, the key of `respond_checked` of the responder
`b` on the message of `initiate_checked` of `a`, run on the bundle of `b`, is the initiator's
key: both are the encoding of `H` at the same input (`aliceInp_eq_bobInp`). -/
theorem respond_square_agree (h : X3dhSquareHom G encCtx encS encW encK H) (sid : SessionId)
    (a b : PartyId) (ikA ek ikB spkB opkB : S) :
    X3dh.respond_checked (encCtx (sid, a, b)) (encS ikB) (encS spkB) (encS opkB)
        (X3dh.initiate_checked (encCtx (sid, a, b)) (encS ikA) (encS ek)
          (X3dh.create_bundle (encS ikB) (encS spkB) (encS opkB)) true).2.1
        true =
      (X3dh.initiate_checked (encCtx (sid, a, b)) (encS ikA) (encS ek)
        (X3dh.create_bundle (encS ikB) (encS spkB) (encS opkB)) true).1 := by
  rw [initiate_msg_square_enc h, create_bundle_square_enc h, initiate_square_enc h,
    respond_square_enc h, aliceInp_eq_bobInp]

/-- **Key agreement of the checked exchange.** With the one-time prekey, `initiate` of `a` at the
context `encCtx (sid, a, b)` accepts the bundle of `b`, and `respond` of `b` accepts the message
it returns and derives the initiator's key. -/
theorem initiate_respond_square_agree (h : X3dhSquareHom G encCtx encS encW encK H)
    (sid : SessionId) (a b : PartyId) (ikA ek ikB spkB opkB : S) :
    ∃ k m v, X3dh.initiate (encCtx (sid, a, b)) (encS ikA) (encS ek)
        (X3dh.create_bundle (encS ikB) (encS spkB) (encS opkB)) true = some (k, m, v) ∧
      X3dh.respond (encCtx (sid, a, b)) (encS ikB) (encS spkB) (encS opkB) m true = some k := by
  let r := X3dh.initiate_checked (encCtx (sid, a, b)) (encS ikA) (encS ek)
    (X3dh.create_bundle (encS ikB) (encS spkB) (encS opkB)) true
  refine ⟨r.1, r.2.1, r.2.2, ?_, ?_⟩
  · rw [create_bundle_square_enc h, initiate_square_eq_some h, ← create_bundle_square_enc h]
  · have hk := respond_square_agree h sid a b ikA ek ikB spkB opkB
    rw [initiate_msg_square_enc h] at hk ⊢
    rw [respond_square_eq_some h, hk]

end CatCrypt.Crypto.AKE.X3DH.SquareCorrespondence
