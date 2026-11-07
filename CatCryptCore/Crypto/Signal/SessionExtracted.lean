/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DH.SquareCorrespondence
public import CatCryptCore.Crypto.Signal.DoubleRatchet.ExtractedScheme

/-!
# The extracted Signal session: X3DH, then the first epoch of the double ratchet

The initiator of a Signal session runs the X3DH handshake on the prekey bundle of the
responder and opens the double ratchet with the session key of X3DH as its first root key and
the responder's signed prekey as the remote public value of its first Diffie–Hellman step. In
the extracted code this is `X3dh.initiate` of `x3dh-hax` followed by `Uninitialized_establish`
of `doubleratchet-hax` on the key it returns, a fresh ratchet key pair and the signed prekey of
the bundle.

The correspondence is assembled from the two hom records of the extractions at shared
encodings: `X3dhSquareHom GX encCtx encS encG encR H` for X3DH, whose group elements are those
of the cyclic group `G` of the ratchet with the encoding `encG`, and whose session keys are the
root keys `RK` of the ratchet with the encoding `encR`; and `DrHom G R F D ptLen encR encG encSk
decE encSa encW encC` for the double ratchet. Under both, the initiator's session after
`establish` is the encoding of the root step `R` at the key derivation `H` of the initiator's
X3DH input `aliceInp`, on the key of the first send of the Diffie–Hellman CKA `dhCKAOf G decE`
from the state with the remote public value `SPKB`: the signed prekey is the first ratchet
public value of the CKA. The session holds the sending chain key of that step and no receiving
chain key.

The same session is the opening of an epoch (`drOpen`, the `ratchet` operation of the
extracted scheme `drExtractedSM`) from the initial session `drInitSession` whose root key is
the X3DH key and whose remote public value is the signed prekey
(`signal_session_extracted_drOpen`).

## Main definitions

* `initiatorStart` — the root key and the sending chain key of the initiator's first epoch in
  the model

## Main results

* `signal_session_extracted` — `X3dh.initiate`, then `Uninitialized_establish`, is the
  encoding of `initiatorStart`
* `signal_session_extracted_bundle` — the same on the bundle of the responder created by
  `X3dh.create_bundle` from encoded secrets
* `signal_session_extracted_drOpen` — the session is `drOpen` of the initial session at the
  X3DH key and the signed prekey
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.SessionExtracted

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Crypto.Messaging CatCrypt.Crypto.Assumptions
open CatCryptCore.Examples.CyclicGroupDDH
open CatCrypt.Crypto.PAKE.DHExtract (DHGroup)
open CatCrypt.Crypto.UCTransparent.FAKE (SessionId PartyId)
open CatCrypt.Crypto.AKE.X3DHSquare (Inp aliceInp)
open CatCrypt.Crypto.AKE.X3DH.SquareCorrespondence
open CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedCorrespondence
open CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedScheme

variable {S RK Sa W Ct Sk G : Type} [Field S] [SampleableType W] [CG : CyclicGroup G]
  [Fintype Sk] [Nonempty Sk]

/-- **The initiator's first epoch in the model**: the root step of `R` at the session key
`H (aliceInp GX sid a b ik ek IKB SPKB OPKB)` of X3DH, on the key of the first send with the
secret key `y` of the Diffie–Hellman CKA `dhCKAOf G decE` from the initiator's state `(SPKB, s)`,
whose remote public value is the responder's signed prekey `SPKB`. The result is the next root
key and the sending chain key. -/
noncomputable def initiatorStart (GX : DHGroup S G) (H : Inp G → RK)
    (R : PRGDef (RK × G) (RK × Sa)) (decE : Sk → CG.Exp) (sid : SessionId) (a b : PartyId)
    (ik ek : S) (IKB SPKB OPKB : G) (s y : Sk) : RK × Sa :=
  R.stretch (H (aliceInp GX sid a b ik ek IKB SPKB OPKB),
    (CKACoins.sendR (C := dhCKAOf G decE) (SPKB, s) y).2.2)

variable [X3dh.X3dhDeps] [Doubleratchet.DoubleratchetDeps] {GX : DHGroup S G}
  {encCtx : SessionId × PartyId × PartyId → Array Int} {encS : S → Array Int}
  {encG : G → Array Int} {encR : RK → Array Int} {H : Inp G → RK}
  {R : PRGDef (RK × G) (RK × Sa)} {F : PRGDef Sa (W × Sa)} {D : AEADDef W Ct} {ptLen : Int}
  {encSk : Sk → Array Int} {decE : Sk → CG.Exp} {encSa : Sa → Array Int}
  {encW : W → Array Int} {encC : Ct → Array Int}

/-- **The extracted Signal session of the initiator.** Under the hom records of X3DH and of the
double ratchet at shared encodings of group elements (`encG`) and of session and root keys
(`encR`), `X3dh.initiate` of the initiator `a` with the one-time prekey, at the context
`encCtx (sid, a, b)`, the encoded secrets `ik`, `ek` and a bundle of the encoded public keys
`IKB`, `SPKB`, `OPKB`, accepts the bundle; `Uninitialized_establish` on its session key, the
encoded secret key `y`, a public key `pk` and the encoded signed prekey `SPKB` gives the
session whose root key and sending chain key are the encodings of `initiatorStart`, with no
receiving chain key, the key pair `(encSk y, pk)` and the remote public value `encG SPKB`. -/
theorem signal_session_extracted (hX : X3dhSquareHom GX encCtx encS encG encR H)
    (hD : DrHom G R F D ptLen encR encG encSk decE encSa encW encC)
    (u : Doubleratchet.Uninitialized_T) (g : Array Int) (sid : SessionId) (a b : PartyId)
    (ik ek : S) (IKB SPKB OPKB : G) (sig : Array Int) (s y : Sk) (pk : Array Int) :
    (X3dh.initiate (encCtx (sid, a, b)) (encS ik) (encS ek) (encG IKB, encG SPKB, encG OPKB, sig)
        true).map (fun o => Doubleratchet.Uninitialized_establish u g o.1 (encSk y) pk
          (encG SPKB)) =
      some ((encR (initiatorStart GX H R decE sid a b ik ek IKB SPKB OPKB s y).1,
        some (encSa (initiatorStart GX H R decE sid a b ik ek IKB SPKB OPKB s y).2), none, 0, 0,
        encSk y, pk, encG SPKB, 0), Doubleratchet.event g 3 0) := by
  rw [initiate_square_eq_some hX, Option.map_some, initiate_square_enc hX, establish_enc hD]
  simp only [initiatorStart, CKACoins.sendR]

/-- **The extracted Signal session on the responder's bundle.** On the bundle that
`X3dh.create_bundle` computes from the encoded secrets `ikB`, `spkB`, `opkB` of the responder,
`X3dh.initiate` followed by `Uninitialized_establish` on the encoded signed prekey of the
bundle gives the encoding of `initiatorStart` at the public keys `GX.pub ikB`, `GX.pub spkB`,
`GX.pub opkB`. -/
theorem signal_session_extracted_bundle (hX : X3dhSquareHom GX encCtx encS encG encR H)
    (hD : DrHom G R F D ptLen encR encG encSk decE encSa encW encC)
    (u : Doubleratchet.Uninitialized_T) (g : Array Int) (sid : SessionId) (a b : PartyId)
    (ik ek ikB spkB opkB : S) (s y : Sk) (pk : Array Int) :
    (X3dh.initiate (encCtx (sid, a, b)) (encS ik) (encS ek)
        (X3dh.create_bundle (encS ikB) (encS spkB) (encS opkB)) true).map
        (fun o => Doubleratchet.Uninitialized_establish u g o.1 (encSk y) pk
          (encG (GX.pub spkB))) =
      some ((encR (initiatorStart GX H R decE sid a b ik ek (GX.pub ikB) (GX.pub spkB)
          (GX.pub opkB) s y).1,
        some (encSa (initiatorStart GX H R decE sid a b ik ek (GX.pub ikB) (GX.pub spkB)
          (GX.pub opkB) s y).2), none, 0, 0, encSk y, pk, encG (GX.pub spkB), 0),
        Doubleratchet.event g 3 0) := by
  rw [create_bundle_square_enc hX]
  exact signal_session_extracted hX hD u g sid a b ik ek _ _ _ _ s y pk

/-- **The extracted session is an epoch opening of the extracted scheme**, an unfolding of
`drOpen` at a session without a receiving chain key. The session that `Uninitialized_establish`
computes from the session key of `X3dh.initiate`, the new key pair `(sk, pk)` and the remote
public value `rpk` (the encoded signed prekey) is `drOpen` with that key pair of the initial
session `drInitSession` whose root key is the session key of X3DH and whose remote public value
is `rpk`, for any key pair `(sk₀, pk₀)` of the initial session. -/
theorem signal_session_extracted_drOpen (u : Doubleratchet.Uninitialized_T)
    (g ctx ik ek : Array Int) (bundle : X3dh.X3dhPreKeyBundle_T) (sk pk sk₀ pk₀ rpk : Array Int) :
    (Doubleratchet.Uninitialized_establish u g (X3dh.initiate_checked ctx ik ek bundle true).1 sk
        pk rpk).1 =
      drOpen (drInitSession (X3dh.initiate_checked ctx ik ek bundle true).1 sk₀ pk₀ rpk) sk pk := by
  simp only [drOpen, drInitSession, Doubleratchet.Session, Doubleratchet.«Session.recv_ck»,
    Doubleratchet.«Session.root_key», Doubleratchet.«Session.remote_pk»,
    Doubleratchet.Uninitialized_establish]

end CatCrypt.Crypto.Signal.SessionExtracted
