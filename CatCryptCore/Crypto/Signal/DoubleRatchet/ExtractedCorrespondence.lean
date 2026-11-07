/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signal.DoubleRatchet.Extraction.Doubleratchet_haxpipe
public import CatCryptCore.Crypto.Signal.DoubleRatchet_UC
public import CatCryptCore.Crypto.AdvantageMap
public import CatCryptCore.Crypto.SamplerCert

/-!
# The extracted double ratchet and the secure-messaging model

The haxpipeT extraction of `doubleratchet-hax` computes on byte arrays under an instance of
`Doubleratchet.DoubleratchetDeps`, whose fields are the primitives the crate calls
(`hmac_sha256`, `hkdf_extract`, `hkdf_expand`, `x25519`, `aead_encrypt`, `aead_decrypt`) and the
ghost hooks of its typestate machine (`send`, `recv`, `event`). The chain step `kdf_ck`, the root
step `kdf_rk` and the Diffie–Hellman function `dh` of the crate are extracted definitions over
these fields, and so are the session functions `Uninitialized_establish`, `Session_send`,
`Session_receive` and `Session_dh_ratchet`.

`DrHom` states equations of the primitives at encoded arguments: the Diffie–Hellman function at
the encoding `encSk s` of a secret key `s : Sk` is the exponentiation of a cyclic group `G` by
the exponent `decE s`, HKDF-Extract followed by HKDF-Expand under the two info blocks of
`kdf_rk` is the root KDF `R`, HMAC-SHA256 under the two chain constants is the generator `F`,
and `aead_encrypt` at the plaintext length `ptLen` is the AEAD `D`. Under these equations the
extracted `kdf_ck`, `kdf_rk` and `dh` compute the encodings of the model's steps, and the four
session functions the encodings of the model's sending, receiving, establishing and
Diffie–Hellman ratchet steps.

The game `sm_extracted` runs one session of the crate. It samples uniform secret keys in `Sk`
for the Diffie–Hellman CKA and a root key, establishes the session (`Uninitialized_establish`),
and runs the epochs in turn: the first epoch by `Session_send` per message, then per pair of
epochs one `Session_dh_ratchet` on the public value of the epoch and the session's new key
pair, the receiving epoch by `Session_receive` per message and the sending epoch by
`Session_send` per message. The chain keys of a session are optional:
`Uninitialized_establish` holds the chain key of its root step as the sending chain key and no
receiving chain key, `Session_dh_ratchet` sets both, and `Session_send` (`Session_receive`)
returns no session on a session without a sending (receiving) chain key (`session_send_none`,
`session_receive_none`). The runs of the game reach no refusal: the first receiving chain read
by `Session_receive` is the one `Session_dh_ratchet` sets. The session functions run with the
ghost hooks `keyGhost`, which
keep the message key the session hands to `send` or `recv`. The game encrypts each message
`(m, a)` of the model by the trait's `aead_encrypt` under that message key with the model's
associated data `a`; at the Signal instance (`signalMsgs`) the associated data of each message
is the plaintext itself. The view is the public values of the CKA and the ciphertexts of all
epochs; the message headers, the counters `send_n`, `recv_n` and `step` and the ghost trace are
not part of it. One session is run: the theorems state nothing about a second party running
the crate.

The extracted functions the game runs are `Uninitialized_establish`, `Session_send`,
`Session_receive` and `Session_dh_ratchet`, with `kdf_ck`, `kdf_rk`, `dh` and `ck_const`. The
theorems here state nothing about the other extracted functions: the accessors `Session_step`,
`Session_root_key`, `Session_send_ck`, `Session_recv_ck`, `Session_send_n`, `Session_recv_n`,
`Session_my_pk`, `Session_remote_pk`, the constants `MAX_MSG_LEN` and `MAX_PLAINTEXT_LEN`, and
the state-record functions `kdf_chain_step`, `kdf_chain_advance`, `ratchet_init_initiator`,
`ratchet_init_responder`, `ratchet_encrypt`, `ratchet_decrypt` and `dh_ratchet_step`.
`ratchet_encrypt` calls `aead_encrypt` with the sender's public key `my_pk` as associated
data.

The model game is presented as a game over an exponent sampler, `smSampled`: its real game
draws the `msgs.length + 1` exponents of the CKA from the sampler before anything else and is
`sm_real (dhCKA G)` at the uniform sampler; its ideal game is `sm_ideal (dhCKA G)` and draws
nothing from the sampler. `sm_extracted_realizes` proves that the game of the extracted session
and the encoded ideal game realize `smSampled` at the image of the uniform sampler on `Sk`
under `decE`, through `encView`. For a sampler certificate `c` from that image to the uniform
exponent sampler, `sm_extracted_advantage_le` bounds the advantage by the bound of
`sm_dh_advantage_le` plus `(msgs.length + 1) * c.δ`. When the image is uniform (for instance
`Sk = CG.Exp` and `decE = id`), `sm_extracted_eq` proves that the game is
`sm_real (dhCKA G) R F D` followed by the encoding of the views.

## Main definitions

* `keyGhost` — an instance of `DoubleratchetDeps` with the primitives of a given one and the
  ghost hooks that keep the message key
* `DrHom` — the equations of the primitives at encoded arguments
* `sendEpoch`, `recvEpoch` — the ciphertexts of an epoch under the message keys of
  `Session_send` (`Session_receive`)
* `ratchetCts`, `sessionCts` — the ciphertexts of the epochs of one session
* `encView` — the encoding of a view of the secure-messaging adversary
* `smSampled` — the secure-messaging game of the Diffie–Hellman CKA over an exponent sampler
* `sm_extracted` — the secure-messaging game of the extracted session

## Main results

* `kdf_ck_msg_enc`, `kdf_ck_chain_enc`, `kdf_rk_enc`, `dh_enc` — the extracted chain step,
  root step and Diffie–Hellman function at encoded arguments
* `session_send_enc`, `session_receive_enc`, `establish_enc`, `dh_ratchet_enc` — the session
  functions at encoded states
* `session_send_none`, `session_receive_none` — the refusals on an absent chain
* `sessionCts_eq` — the ciphertexts of the extracted session are the encoded ciphertexts of
  `smCts` over the root chain of the Diffie–Hellman CKA keys
* `smSampled_realAt_uniform`, `smSampled_idealAt` — the games of `smSampled` at the uniform
  sampler are `sm_real (dhCKA G)` and `sm_ideal (dhCKA G)`
* `sm_extracted_realizes` — `SampledRealizes (sm_extracted …) ((sm_ideal (dhCKA G) msgs).map
  (encView encG encC)) (smSampled R F D msgs) μ (encView encG encC)` at the image `μ` of the
  uniform sampler on `Sk` under `decE`
* `sm_extracted_eq` — at a uniform image,
  `sm_extracted = (sm_real (dhCKA G) R F D msgs).map (encView encG encC)`
* `sm_extracted_advantage_le_SM`, `sm_extracted_advantage_le` — the advantage of every
  distinguisher `A` between the extracted game and the encoded ideal game is at most the
  secure-messaging advantage (the bound of `sm_dh_advantage_le`) at `A ∘ encView encG encC`,
  plus `(msgs.length + 1) * c.δ`
* `sm_extracted_advantage_le_of_uniform` — the same without the charge at a uniform image
* `signalDR_extracted_advantage_le`, `signalDR_extracted_advantage_le_of_uniform` — the same at
  the Signal double ratchet, bounded by `signalDRBound`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedCorrespondence

open CatCrypt.Core CatCrypt.Prob CatCrypt.NonUniform CatCrypt.Crypto CatCrypt.Crypto.Messaging
open CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.Signal.DoubleRatchet_CKA CatCrypt.Crypto.Signal.DoubleRatchet_UC
open CatCryptCore.Examples.CyclicGroupDDH
open Doubleratchet
open scoped ENNReal

/-! ## Ghost hooks that keep the message key -/

/-- The instance with the primitives of `d` and the ghost hooks of a ghost that holds the last
message key: `send` and `recv` replace the ghost by the message key, `event` leaves it. The
session functions of the crate are generic in the ghost (`DoubleRatchetGhost`), and this is the
ghost the secure-messaging game runs them with. -/
@[reducible] def keyGhost (d : DoubleratchetDeps) : DoubleratchetDeps :=
  { d with
    event := fun g _ _ => g
    send := fun _ _ mk => mk
    recv := fun _ _ mk => mk }

variable [inst : DoubleratchetDeps]

/-! ## The primitives at encoded arguments -/

/-- Encodings of root keys (`encR`), group elements (`encG`), secret keys (`encSk`), FS-AEAD
states (`encS`), words (`encW`) and ciphertexts (`encC`), and the exponent `decE s` of a secret
key `s`, under which `x25519` at the secret key `s` is the exponentiation of `G` by `decE s`,
HKDF-Extract followed by HKDF-Expand under the info blocks of `kdf_rk` is the root KDF `R`,
HMAC-SHA256 under the chain constants `ck_const 2` and `ck_const 1` is the generator `F`, and
`aead_encrypt` at the plaintext length `ptLen` is the AEAD `D`. -/
structure DrHom {RK Sa W Ct Sk : Type} [SampleableType W] (G : Type) [CG : CyclicGroup G]
    (R : PRGDef (RK × G) (RK × Sa)) (F : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ptLen : Int) (encR : RK → Array Int) (encG : G → Array Int) (encSk : Sk → Array Int)
    (decE : Sk → CG.Exp) (encS : Sa → Array Int) (encW : W → Array Int)
    (encC : Ct → Array Int) : Prop where
  dh_eq : ∀ s T, x25519 (encSk s) (encG T) = encG (CyclicGroup.elemPow T (decE s))
  root_rk_eq : ∀ rk I, hkdf_expand (hkdf_extract (encR rk) (encG I)) (Hax.repeat_ 1 32) =
    encR (R.stretch (rk, I)).1
  root_ck_eq : ∀ rk I, hkdf_expand (hkdf_extract (encR rk) (encG I)) (Hax.repeat_ 2 32) =
    encS (R.stretch (rk, I)).2
  msg_key_eq : ∀ s, hmac_sha256 (encS s) (ck_const 2) = encW (F.stretch s).1
  chain_key_eq : ∀ s, hmac_sha256 (encS s) (ck_const 1) = encS (F.stretch s).2
  aead_eq : ∀ k m a, aead_encrypt (encW k) (encW m) ptLen (encW a) = encC (D.encrypt k m a)

section Model

variable {RK Sa W Ct Sk : Type} [SampleableType W] {G : Type} [CG : CyclicGroup G]
  {R : PRGDef (RK × G) (RK × Sa)} {F : PRGDef Sa (W × Sa)} {D : AEADDef W Ct} {ptLen : Int}
  {encR : RK → Array Int} {encG : G → Array Int} {encSk : Sk → Array Int}
  {decE : Sk → CG.Exp} {encS : Sa → Array Int} {encW : W → Array Int} {encC : Ct → Array Int}

/-- The equations of `DrHom` hold at `keyGhost`, which has the same primitives. -/
theorem DrHom.ghost (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC) :
    @DrHom (keyGhost inst) RK Sa W Ct Sk _ G CG R F D ptLen encR encG encSk decE encS encW encC :=
  @DrHom.mk (keyGhost inst) RK Sa W Ct Sk _ G CG R F D ptLen encR encG encSk decE encS encW encC
    h.dh_eq h.root_rk_eq h.root_ck_eq h.msg_key_eq h.chain_key_eq h.aead_eq

/-- The extracted chain step under the constant `2` at an encoded state is the encoded message
key of `F`. -/
theorem kdf_ck_msg_enc (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC) (s : Sa) :
    kdf_ck (encS s) 2 = encW (F.stretch s).1 := by
  grind [kdf_ck, h.msg_key_eq]

/-- The extracted chain step under the constant `1` at an encoded state is the encoded next
state of `F`. -/
theorem kdf_ck_chain_enc (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC) (s : Sa) :
    kdf_ck (encS s) 1 = encS (F.stretch s).2 := by
  grind [kdf_ck, h.chain_key_eq]

/-- The extracted root step at an encoded root key and an encoded group element is the
encoding of the root KDF `R`. -/
theorem kdf_rk_enc (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC) (rk : RK) (I : G) :
    kdf_rk (encR rk) (encG I) = (encR (R.stretch (rk, I)).1, encS (R.stretch (rk, I)).2) := by
  simp only [kdf_rk, h.root_rk_eq, h.root_ck_eq]

/-- The extracted Diffie–Hellman function at an encoded secret key and an encoded group element
is the encoded exponentiation by the exponent of the secret key. -/
theorem dh_enc (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC) (x : Sk) (T : G) :
    dh (encSk x) (encG T) = encG (CyclicGroup.elemPow T (decE x)) := by
  simp only [dh, h.dh_eq]

/-! ## The session functions at encoded states -/

/-- **Sending step.** `Session_send` at a session whose sending chain key is the encoding of
the state `s` returns the session with the encoding of the next state of `F` and hands the
encoded message key of `F` to the ghost hook `send`. -/
theorem session_send_enc (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC) (s : Sa)
    (rk : Array Int) (rc : Option (Array Int)) (sk pk rpk : Array Int) (sn rn st : Int)
    (g : Array Int) :
    Session_send (rk, some (encS s), rc, sn, rn, sk, pk, rpk, st) g =
      (some (rk, some (encS (F.stretch s).2), rc, sn + 1, rn, sk, pk, rpk, st + 1),
        event (send g st (encW (F.stretch s).1)) 0 (st + 1)) := by
  simp only [Session_send, Session, «Session.send_ck», «Session.root_key», «Session.recv_ck»,
    «Session.send_n», «Session.recv_n», «Session.my_sk», «Session.my_pk», «Session.remote_pk»,
    «.step», kdf_ck_msg_enc h, kdf_ck_chain_enc h, Hax.add]

/-- **Refused sending step.** `Session_send` at a session without a sending chain key returns
no session and leaves the ghost. -/
theorem session_send_none (rk : Array Int) (rc : Option (Array Int)) (sk pk rpk : Array Int)
    (sn rn st : Int) (g : Array Int) :
    Session_send (rk, none, rc, sn, rn, sk, pk, rpk, st) g = (none, g) := by
  simp only [Session_send, «Session.send_ck»]

/-- **Receiving step.** `Session_receive` at a session whose receiving chain key is the
encoding of the state `s` returns the session with the encoding of the next state of `F` and
hands the encoded message key of `F` to the ghost hook `recv`. -/
theorem session_receive_enc (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC) (s : Sa)
    (rk : Array Int) (sc : Option (Array Int)) (sk pk rpk : Array Int) (sn rn st : Int)
    (g : Array Int) :
    Session_receive (rk, sc, some (encS s), sn, rn, sk, pk, rpk, st) g =
      (some (rk, sc, some (encS (F.stretch s).2), sn, rn + 1, sk, pk, rpk, st + 1),
        event (recv g st (encW (F.stretch s).1)) 1 (st + 1)) := by
  simp only [Session_receive, Session, «Session.send_ck», «Session.root_key», «Session.recv_ck»,
    «Session.send_n», «Session.recv_n», «Session.my_sk», «Session.my_pk», «Session.remote_pk»,
    «.step», kdf_ck_msg_enc h, kdf_ck_chain_enc h, Hax.add]

/-- **Refused receiving step.** `Session_receive` at a session without a receiving chain key
returns no session and leaves the ghost. -/
theorem session_receive_none (rk : Array Int) (sc : Option (Array Int)) (sk pk rpk : Array Int)
    (sn rn st : Int) (g : Array Int) :
    Session_receive (rk, sc, none, sn, rn, sk, pk, rpk, st) g = (none, g) := by
  simp only [Session_receive, «Session.recv_ck»]

/-- **Establishing a session.** `Uninitialized_establish` at the encoded root key `rk`, the
encoded secret key `x` and the encoded remote element `T` holds the encodings of the root KDF
`R` at `rk` on the Diffie–Hellman key `T ^ decE x`, as root key and sending chain key, and no
receiving chain key. -/
theorem establish_enc (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC)
    (u : Uninitialized_T) (g : Array Int) (rk : RK) (x : Sk) (pk : Array Int) (T : G) :
    Uninitialized_establish u g (encR rk) (encSk x) pk (encG T) =
      ((encR (R.stretch (rk, CyclicGroup.elemPow T (decE x))).1,
        some (encS (R.stretch (rk, CyclicGroup.elemPow T (decE x))).2), none, 0, 0, encSk x, pk,
        encG T, 0),
        event g 3 0) := by
  simp only [Uninitialized_establish, Session, dh_enc h, kdf_rk_enc h]

/-- **The Diffie–Hellman ratchet.** `Session_dh_ratchet` at a session with the encoded root key
`rk` and the encoded secret key `x`, on the encoded remote element `T` and the new encoded
secret key `y`, holds the encodings of two root steps of `R`: at `rk` on `T ^ decE x` (the
receiving chain), then at the next root key on `T ^ decE y` (the sending chain). -/
theorem dh_ratchet_enc (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC)
    (rk : RK) (sc rc : Option (Array Int)) (pk : Array Int) (sn rn st : Int) (x y : Sk)
    (rpk pk' : Array Int) (T : G) (g : Array Int) :
    Session_dh_ratchet (encR rk, sc, rc, sn, rn, encSk x, pk, rpk, st) g (encG T) (encSk y) pk' =
      let r1 := R.stretch (rk, CyclicGroup.elemPow T (decE x))
      let r2 := R.stretch (r1.1, CyclicGroup.elemPow T (decE y))
      ((encR r2.1, some (encS r2.2), some (encS r1.2), 0, 0, encSk y, pk', encG T, st + 1),
        event g 2 (st + 1)) := by
  simp only [Session_dh_ratchet, Session, «Session.root_key», «Session.my_sk», «.step»,
    dh_enc h, kdf_rk_enc h, Hax.add]

/-! ## The ciphertexts of one extracted session -/

section Session

variable (ptLen) (encR) (encG) (encSk) (decE)

/-- The ciphertexts of a sending epoch from the session `x`: per message `(m, a)`, one
`Session_send` under the ghost hooks `keyGhost`, and `aead_encrypt` of `m` with associated data
`a` under the message key it hands to `send`; and the session after the epoch. The epoch ends
at a refusal of `Session_send`. -/
def sendEpoch (x : Session_T) : List (Array Int × Array Int) → List (Array Int) × Session_T
  | [] => ([], x)
  | m :: ms =>
    let r := @Session_send (keyGhost inst) x #[]
    match r.1 with
    | some y =>
      let p := sendEpoch y ms
      (aead_encrypt r.2 m.1 ptLen m.2 :: p.1, p.2)
    | none => ([], x)

/-- The ciphertexts of a receiving epoch at the session `x`: per message `(m, a)`, one
`Session_receive` under the ghost hooks `keyGhost`, and `aead_encrypt` of `m` with associated
data `a` under the message key it hands to `recv`; and the session after the epoch. The epoch
ends at a refusal of `Session_receive`. -/
def recvEpoch (x : Session_T) : List (Array Int × Array Int) → List (Array Int) × Session_T
  | [] => ([], x)
  | m :: ms =>
    let r := @Session_receive (keyGhost inst) x #[]
    match r.1 with
    | some y =>
      let p := recvEpoch y ms
      (aead_encrypt r.2 m.1 ptLen m.2 :: p.1, p.2)
    | none => ([], x)

/-- The ciphertexts of the epochs after the first from the session `x`, with the fresh CKA
secret keys `es` and the messages `mss` of the epochs. Per pair of epochs, one
`Session_dh_ratchet` on the peer's public value `g ^ decE a` with the new key pair
`(b, g ^ decE b)`, then the receiving epoch (`recvEpoch`) and the sending epoch (`sendEpoch`).
A last receiving epoch without a following sending epoch ratchets with the new key pair of the
next secret key if there is one and with empty arrays otherwise; its sending chain is not
used. -/
def ratchetCts (x : Session_T) : List Sk → List (List (Array Int × Array Int)) →
    List (List (Array Int))
  | [], _ => []
  | _ :: _, [] => []
  | [a], ms :: _ =>
    [(recvEpoch ptLen (@Session_dh_ratchet (keyGhost inst) x #[] (encG (CG.pow (decE a))) #[]
      #[]).1 ms).1]
  | a :: b :: _, [ms] =>
    [(recvEpoch ptLen (@Session_dh_ratchet (keyGhost inst) x #[] (encG (CG.pow (decE a)))
      (encSk b) (encG (CG.pow (decE b)))).1 ms).1]
  | a :: b :: es, ms₁ :: ms₂ :: mss =>
    let y := (@Session_dh_ratchet (keyGhost inst) x #[] (encG (CG.pow (decE a))) (encSk b)
      (encG (CG.pow (decE b)))).1
    let r := recvEpoch ptLen y ms₁
    let s := sendEpoch ptLen r.2 ms₂
    r.1 :: s.1 :: ratchetCts s.2 es mss

/-- The ciphertexts of the epochs of one extracted session from the root key `rk`, the
secret key `x₀` of the CKA initialisation and the fresh CKA secret keys `x₁ :: es`: the session
established by `Uninitialized_establish` on the encoded root key, the key pair
`(x₁, g ^ decE x₁)` and the remote public value `g ^ decE x₀`, its first epoch sent by
`sendEpoch`, the others by `ratchetCts`. -/
def sessionCts (rk : RK) (x₀ : Sk) : List Sk → List (List (Array Int × Array Int)) →
    List (List (Array Int))
  | [], _ => []
  | _ :: _, [] => []
  | x₁ :: es, ms :: mss =>
    let y := (@Uninitialized_establish (keyGhost inst) Uninitialized #[] (encR rk) (encSk x₁)
      (encG (CG.pow (decE x₁))) (encG (CG.pow (decE x₀)))).1
    let s := sendEpoch ptLen y ms
    s.1 :: ratchetCts ptLen encG encSk decE s.2 es mss

end Session

/-- The encoding of a message and its associated data. -/
def encPair (encW : W → Array Int) (m : W × W) : Array Int × Array Int := (encW m.1, encW m.2)

omit inst in
/-- The ciphertexts of one epoch from the state `s`: the head message under the first output
of `F`, the rest from the next state. -/
theorem encEpoch_cons (s : Sa) (m : W × W) (ms : List (W × W)) :
    encEpoch F D s (m :: ms) =
      D.encrypt (F.stretch s).1 m.1 m.2 :: encEpoch F D (F.stretch s).2 ms := by
  simp only [encEpoch, encAll, fsprgRun, List.length_cons, List.zipWith_cons_cons]

/-- The ciphertexts of a sending epoch from a session whose sending chain key is the encoding
of `s` are the encoded ciphertexts of `encEpoch F D s`. -/
theorem sendEpoch_cts (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC)
    (ms : List (W × W)) (x : Session_T) (s : Sa) (hs : «Session.send_ck» x = some (encS s)) :
    (sendEpoch ptLen x (ms.map (encPair encW))).1 = (encEpoch F D s ms).map encC := by
  induction ms generalizing x s with
  | nil => simp only [List.map_nil, sendEpoch, encEpoch, encAll, List.zipWith_nil_right]
  | cons m ms ih =>
    obtain ⟨a, b, c, d, e, f, g, i, j⟩ := x
    simp only [«Session.send_ck»] at hs
    subst hs
    simp only [List.map_cons, sendEpoch, encEpoch_cons, encPair]
    rw [session_send_enc (inst := keyGhost inst) h.ghost]
    exact congrArg₂ List.cons (h.aead_eq _ _ _) (ih _ _ rfl)

/-- The ciphertexts of a receiving epoch from a session whose receiving chain key is the
encoding of `s` are the encoded ciphertexts of `encEpoch F D s`. -/
theorem recvEpoch_cts (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC)
    (ms : List (W × W)) (x : Session_T) (s : Sa) (hs : «Session.recv_ck» x = some (encS s)) :
    (recvEpoch ptLen x (ms.map (encPair encW))).1 = (encEpoch F D s ms).map encC := by
  induction ms generalizing x s with
  | nil => simp only [List.map_nil, recvEpoch, encEpoch, encAll, List.zipWith_nil_right]
  | cons m ms ih =>
    obtain ⟨a, b, c, d, e, f, g, i, j⟩ := x
    simp only [«Session.recv_ck»] at hs
    subst hs
    simp only [List.map_cons, recvEpoch, encEpoch_cons, encPair]
    rw [session_receive_enc (inst := keyGhost inst) h.ghost]
    exact congrArg₂ List.cons (h.aead_eq _ _ _) (ih _ _ rfl)

/-- A sending epoch keeps the root key and the secret key of the session. -/
theorem sendEpoch_keys (ms : List (Array Int × Array Int)) (x : Session_T) :
    «Session.root_key» (sendEpoch ptLen x ms).2 = «Session.root_key» x ∧
      «Session.my_sk» (sendEpoch ptLen x ms).2 = «Session.my_sk» x := by
  induction ms generalizing x with
  | nil => exact ⟨rfl, rfl⟩
  | cons m ms ih =>
    obtain ⟨a, b, c, d, e, f, g, i, j⟩ := x
    cases b with
    | none => exact ⟨rfl, rfl⟩
    | some b => exact ih _

/-- A receiving epoch keeps the root key, the sending chain key and the secret key of the
session. -/
theorem recvEpoch_keys (ms : List (Array Int × Array Int)) (x : Session_T) :
    «Session.root_key» (recvEpoch ptLen x ms).2 = «Session.root_key» x ∧
      «Session.send_ck» (recvEpoch ptLen x ms).2 = «Session.send_ck» x ∧
      «Session.my_sk» (recvEpoch ptLen x ms).2 = «Session.my_sk» x := by
  induction ms generalizing x with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons m ms ih =>
    obtain ⟨a, b, c, d, e, f, g, i, j⟩ := x
    cases c with
    | none => exact ⟨rfl, rfl, rfl⟩
    | some c => exact ih _

omit inst in
/-- The ciphertexts of the epochs from the states `sa :: sas`: the epoch of `sa`, then the
others. -/
theorem smCts_cons (sa : Sa) (sas : List Sa) (ms : List (W × W)) (mss : List (List (W × W))) :
    smCts F D (sa :: sas) (ms :: mss) = encEpoch F D sa ms :: smCts F D sas mss := by
  simp only [smCts, List.zipWith_cons_cons]

/-- The receiving chain key after `Session_dh_ratchet` at a session with the encoded root key
`rk` and the encoded secret key `x`, on the encoded remote element `T`, is the encoded
FS-AEAD state of the root KDF `R` at `rk` on `T ^ decE x`, whatever the new key pair. -/
theorem dh_ratchet_recv_ck (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC)
    (rk : RK) (sc rc : Option (Array Int)) (pk : Array Int) (sn rn st : Int) (x : Sk)
    (rpk sk' pk' : Array Int) (T : G) (g : Array Int) :
    «Session.recv_ck» (Session_dh_ratchet (encR rk, sc, rc, sn, rn, encSk x, pk, rpk, st) g
      (encG T) sk' pk').1 = some (encS (R.stretch (rk, CyclicGroup.elemPow T (decE x))).2) := by
  simp only [Session_dh_ratchet, Session, «Session.root_key», «Session.my_sk», «Session.recv_ck»,
    dh_enc h, kdf_rk_enc h]

/-- **The epochs after the first.** From a session with the encoded root key `rk` and the
encoded secret key `y`, the ciphertexts of `ratchetCts` with the fresh secret keys `es` are the
encoded ciphertexts of `smCts` over the root chain from `rk` of the CKA keys of
`dhChain (g ^ decE y) (es.map decE)`. -/
theorem ratchetCts_eq (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC) :
    ∀ (es : List Sk) (mss : List (List (W × W))) (x : Session_T) (rk : RK) (y : Sk),
      «Session.root_key» x = encR rk → «Session.my_sk» x = encSk y →
      ratchetCts ptLen encG encSk decE x es (mss.map (List.map (encPair encW))) =
        (smCts F D (rootRun R rk ((dhChain (CG.pow (decE y)) (es.map decE)).map Prod.snd))
          mss).map (List.map encC)
  | [], mss, _, _, _, _, _ => by
    simp only [ratchetCts, dhChain, List.map_nil, rootRun, smCts, List.zipWith_nil_left]
  | _ :: _, [], _, _, _, _, _ => by
    simp only [ratchetCts, List.map_nil, smCts, List.zipWith_nil_right]
  | [a], ms :: _, x, rk, y, hr, hk => by
    obtain ⟨xr, xs, xrc, xsn, xrn, xsk, xpk, xrpk, xst⟩ := x
    simp only [«Session.root_key», «Session.my_sk»] at hr hk
    subst hr hk
    simp only [List.map_cons, ratchetCts, dhChain, rootRun, List.map_nil, smCts]
    refine congrArg₂ List.cons (recvEpoch_cts h ms _ _ ?_) rfl
    rw [dh_ratchet_recv_ck (inst := keyGhost inst) h.ghost, elemPow_pow_comm (decE a) (decE y)]
  | a :: b :: _, [ms], x, rk, y, hr, hk => by
    obtain ⟨xr, xs, xrc, xsn, xrn, xsk, xpk, xrpk, xst⟩ := x
    simp only [«Session.root_key», «Session.my_sk»] at hr hk
    subst hr hk
    simp only [List.map_cons, List.map_nil, ratchetCts, dhChain, rootRun, smCts]
    refine congrArg₂ List.cons (recvEpoch_cts h ms _ _ ?_) rfl
    rw [dh_ratchet_recv_ck (inst := keyGhost inst) h.ghost, elemPow_pow_comm (decE a) (decE y)]
  | a :: b :: es, ms₁ :: ms₂ :: mss, x, rk, y, hr, hk => by
    obtain ⟨xr, xs, xrc, xsn, xrn, xsk, xpk, xrpk, xst⟩ := x
    simp only [«Session.root_key», «Session.my_sk»] at hr hk
    subst hr hk
    simp only [List.map_cons, ratchetCts, dhChain, rootRun, smCts_cons,
      dh_ratchet_enc (inst := keyGhost inst) h.ghost, elemPow_pow_comm (decE a) (decE y)]
    refine congrArg₂ List.cons (recvEpoch_cts h ms₁ _ _ rfl)
      (congrArg₂ List.cons (sendEpoch_cts h ms₂ _ _ (recvEpoch_keys _ _).2.1)
        (ratchetCts_eq h es mss _ _ b ?_ ?_))
    · exact (sendEpoch_keys _ _).1.trans (recvEpoch_keys _ _).1
    · exact (sendEpoch_keys _ _).2.trans (recvEpoch_keys _ _).2.2

/-- **The epochs of one extracted session.** The ciphertexts of `sessionCts` from the root key
`rk`, the initial secret key `x₀` and the fresh secret keys `xs` are the encoded ciphertexts of
`smCts` over the root chain from `rk` of the CKA keys of
`dhChain (g ^ decE x₀) (xs.map decE)`. -/
theorem sessionCts_eq (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC) (rk : RK)
    (x₀ : Sk) (xs : List Sk) (msgs : List (List (W × W))) :
    sessionCts ptLen encR encG encSk decE rk x₀ xs (msgs.map (List.map (encPair encW))) =
      (smCts F D (rootRun R rk ((dhChain (CG.pow (decE x₀)) (xs.map decE)).map Prod.snd))
        msgs).map (List.map encC) := by
  match xs, msgs with
  | [], _ => simp only [sessionCts, dhChain, List.map_nil, rootRun, smCts, List.zipWith_nil_left]
  | _ :: _, [] => simp only [sessionCts, List.map_nil, smCts, List.zipWith_nil_right]
  | x₁ :: es, ms :: mss =>
    simp only [List.map_cons, sessionCts, dhChain, rootRun, smCts_cons,
      establish_enc (inst := keyGhost inst) h.ghost]
    exact congrArg₂ List.cons (sendEpoch_cts h ms _ _ rfl)
      (ratchetCts_eq h es mss _ _ x₁ (sendEpoch_keys _ _).1 (sendEpoch_keys _ _).2)

omit inst in
/-- The messages of `dhChain h xs` are the public values of the exponents `xs`. -/
theorem dhChain_map_fst (h : G) (xs : List CG.Exp) :
    (dhChain h xs).map Prod.fst = xs.map CG.pow := by
  induction xs generalizing h with
  | nil => rfl
  | cons x xs ih => simp only [dhChain, List.map_cons, ih]

/-! ## The model game over an exponent sampler -/

/-- The encoding of a view of the secure-messaging adversary: the CKA public value and messages
under `encM`, the ciphertexts under `encC`. -/
def encView {Msg : Type} (encM : Msg → Array Int) (encC : Ct → Array Int)
    (v : SMView Msg Ct) : SMView (Array Int) (Array Int) :=
  ((encM v.1.1, v.1.2.map encM), v.2.map (List.map encC))

variable [Fintype RK] [Nonempty RK] [Fintype Sa] [Nonempty Sa] [SampleableType Ct]

omit inst in
variable (R F D) in
/-- **The secure-messaging game of the Diffie–Hellman CKA over an exponent sampler.** The real
game draws the exponent `xs 0` of the CKA initialisation and the exponents `xs (i + 1)` of the
epochs, then a uniform root key, and shows the public values with the ciphertexts of `smCts`
over the root chain of the CKA keys of `dhChain`; the ideal game draws nothing from the sampler
and is `sm_ideal (dhCKA G)`. At the uniform sampler the real game is `sm_real (dhCKA G)`
(`smSampled_realAt_uniform`). -/
noncomputable def smSampled (msgs : List (List (W × W))) : SampledGame CG.Exp (SMView G Ct) where
  nR := msgs.length + 1
  nI := 0
  real xs := SPComp.bind (SPComp.sample RK) fun rk =>
    SPComp.pure ((CG.pow (xs 0), (List.ofFn (Fin.tail xs)).map CG.pow),
      smCts F D (rootRun R rk ((dhChain (CG.pow (xs 0)) (List.ofFn (Fin.tail xs))).map
        Prod.snd)) msgs)
  ideal _ := sm_ideal (dhCKA G) msgs

omit inst [Fintype Sa] [Nonempty Sa] in
/-- At the uniform exponent sampler the real game of `smSampled` is `sm_real (dhCKA G)`. -/
theorem smSampled_realAt_uniform (msgs : List (List (W × W))) :
    (smSampled R F D msgs).realAt (SDistr.uniform CG.Exp) = sm_real (dhCKA G) R F D msgs := by
  have hinit : (dhCKA G).init = SPComp.bind (SPComp.sample CG.Exp) fun x =>
      SPComp.pure (CG.pow x, (CG.pow x, x), (CG.pow x, x)) := rfl
  have hu : SDistr.uniform CG.Exp =
      (SDistr.uniform CG.Exp).bind fun x => SDistr.pure (id x) := (SDistr.bind_pure _).symm
  dsimp only [SampledGame.realAt, smSampled]
  rw [sampleFrom_replicateFin_succ_bind, sampleFrom_uniform, hu]
  simp only [sampleFrom_replicateFin_uniform_map_bind, sm_real, hinit, SPComp.bind_assoc,
    SPComp.pure_bind]
  congr 1
  funext x₀
  refine Eq.trans ?_ (ckaRun_dh_tail msgs.length _ _ fun l =>
    SPComp.bind (SPComp.sample RK) fun rk => SPComp.pure
      ((CG.pow x₀, l.map Prod.fst), smCts F D (rootRun R rk (l.map Prod.snd)) msgs)).symm
  simp only [Fin.cons_zero, Fin.tail_cons, Function.id_comp, dhChain_map_fst]

omit inst [Fintype Sa] [Nonempty Sa] in
/-- The ideal game of `smSampled` is `sm_ideal (dhCKA G)` at every sampler. -/
theorem smSampled_idealAt (msgs : List (List (W × W))) (μ : SDistr CG.Exp) :
    (smSampled R F D msgs).idealAt μ = sm_ideal (dhCKA G) msgs := by
  rw [SampledGame.idealAt]
  exact sampleFrom_replicateFin_zero_bind μ _

/-! ## The secure-messaging game of the extracted session -/

variable [Fintype Sk] [Nonempty Sk]

variable (G RK) in
/-- **The secure-messaging game of the extracted session.** It samples the secret key `x₀` of
the CKA initialisation, the fresh secret keys `v` of the epochs and a root key `rk`, uniformly,
and outputs the encoded public values `g ^ decE x₀` and `g ^ decE vᵢ` with the ciphertexts
`sessionCts` of one session of the crate: `Uninitialized_establish`, then `Session_send`,
`Session_dh_ratchet` and `Session_receive` over the epochs, which compute the message keys they
hand to the ghost. Each message `(m, a)` is encrypted by the trait's `aead_encrypt` under its
message key with the model's associated data `a`, not by the crate's `ratchet_encrypt`, whose
associated data is `my_pk`. -/
noncomputable def sm_extracted (ptLen : Int) (encR : RK → Array Int) (encG : G → Array Int)
    (encSk : Sk → Array Int) (decE : Sk → CG.Exp) (encW : W → Array Int)
    (msgs : List (List (W × W))) : SPComp (SMView (Array Int) (Array Int)) :=
  SPComp.bind (SPComp.sample Sk) fun x₀ =>
    SPComp.bind (SPComp.sample (Fin msgs.length → Sk)) fun v =>
      SPComp.bind (SPComp.sample RK) fun rk =>
        SPComp.pure ((encG (CG.pow (decE x₀)), (List.ofFn v).map (encG ∘ CG.pow ∘ decE)),
          sessionCts ptLen encR encG encSk decE rk x₀ (List.ofFn v)
            (msgs.map (List.map (encPair encW))))

omit [Fintype Sa] [Nonempty Sa] in
/-- **The extracted game realizes the model game at the exponent sampler of the secret keys.**
Under `DrHom`, the game of the extracted session and the encoded ideal game are `smSampled` at
the image of the uniform sampler on `Sk` under `decE`, with views encoded by
`encView encG encC`. -/
theorem sm_extracted_realizes (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC)
    (msgs : List (List (W × W))) :
    SampledRealizes (sm_extracted RK G ptLen encR encG encSk decE encW msgs)
      ((sm_ideal (dhCKA G) msgs).map (encView encG encC)) (smSampled R F D msgs)
      ((SDistr.uniform Sk).bind fun s => SDistr.pure (decE s)) (encView encG encC) where
  real := by
    dsimp only [SampledGame.realAt, smSampled]
    rw [sampleFrom_replicateFin_succ_bind, sampleFrom_uniform_map_bind]
    simp only [sampleFrom_replicateFin_uniform_map_bind, sm_extracted, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind, Fin.cons_zero, Fin.tail_cons, encView,
      ← List.map_ofFn, List.map_map, sessionCts_eq h]
  ideal := by rw [smSampled_idealAt]

omit [Fintype Sa] [Nonempty Sa] in
/-- **The extracted game is the encoded model game** when the exponent of a uniform secret key
is uniform: under `DrHom`, the secure-messaging game of the extracted session is `sm_real` of
the Diffie–Hellman CKA, the root KDF `R`, the generator `F` and the AEAD `D`, followed by the
encoding of the views. -/
theorem sm_extracted_eq (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC)
    (hU : ((SDistr.uniform Sk).bind fun s => SDistr.pure (decE s)) = SDistr.uniform CG.Exp)
    (msgs : List (List (W × W))) :
    sm_extracted RK G ptLen encR encG encSk decE encW msgs =
      (sm_real (dhCKA G) R F D msgs).map (encView encG encC) := by
  rw [(sm_extracted_realizes h msgs).real, hU, smSampled_realAt_uniform]

omit [Fintype Sa] [Nonempty Sa] in
/-- **The extracted game against the model game, at a certified exponent sampler.** Under
`DrHom`, for a certificate `c` from the image `c.μ` of the uniform sampler on `Sk` under `decE`
to the uniform exponent sampler `c.ν`, the advantage of every distinguisher `A` between the
game of the extracted session and the encoded ideal game is at most the secure-messaging
advantage of `A ∘ encView encG encC` against the Diffie–Hellman CKA, plus `c.δ` for each of the
`msgs.length + 1` exponent draws. -/
theorem sm_extracted_advantage_le_SM
    (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC) (c : SamplerCert CG.Exp)
    (hμ : c.μ = (SDistr.uniform Sk).bind fun s => SDistr.pure (decE s))
    (hν : c.ν = SDistr.uniform CG.Exp) (msgs : List (List (W × W)))
    (A : SMView (Array Int) (Array Int) → SPComp Bool) :
    AdvantageA (sm_extracted RK G ptLen encR encG encSk decE encW msgs)
        ((sm_ideal (dhCKA G) msgs).map (encView encG encC)) A ≤
      SM_Advantage (dhCKA G) R F D msgs (A ∘ encView encG encC) + (msgs.length + 1) * c.δ := by
  have hc := advantageA_le_of_realizes (smSampled R F D msgs) c (encView encG encC)
    (hμ ▸ sm_extracted_realizes h msgs) A
  have hn : ((smSampled R F D msgs).nR + (smSampled R F D msgs).nI : ℝ≥0∞) =
      msgs.length + 1 := by
    simp only [smSampled, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
  rw [hn, hν, SampledGame.advAt, smSampled_realAt_uniform, smSampled_idealAt] at hc
  exact hc

/-- **Confidentiality of the extracted double ratchet.** Under `DrHom`, for a certificate `c`
from the image `c.μ` of the uniform sampler on `Sk` under `decE` to the uniform exponent
sampler `c.ν`, the advantage of every distinguisher `A` between the game of the extracted
session and the encoded ideal game is at most the bound of `sm_dh_advantage_le` at the
distinguisher `A ∘ encView encG encC` (DDH advantages of `ckaDDHRed` at `smCKARed`, PRG
advantages of the root KDF at `smRootRed` and FS-AEAD advantages at `smAEADRed`), plus
`(msgs.length + 1) * c.δ`. -/
theorem sm_extracted_advantage_le (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC)
    (c : SamplerCert CG.Exp)
    (hμ : c.μ = (SDistr.uniform Sk).bind fun s => SDistr.pure (decE s))
    (hν : c.ν = SDistr.uniform CG.Exp) (msgs : List (List (W × W)))
    (A : SMView (Array Int) (Array Int) → SPComp Bool) :
    AdvantageA (sm_extracted RK G ptLen encR encG encSk decE encW msgs)
        ((sm_ideal (dhCKA G) msgs).map (encView encG encC)) A ≤
      ∑ t ∈ Finset.range msgs.length,
          DDH_Advantage G (ckaDDHRed t (msgs.length - (t + 1))
            (smCKARed R F D msgs t (A ∘ encView encG encC))) +
        ∑ t ∈ Finset.range msgs.length,
          PRG_Advantage R
            (smRootRed (dhCKA G) R F D msgs t (msgs.length - (t + 1)) (A ∘ encView encG encC)) +
        ∑ t ∈ Finset.range msgs.length,
          FSAEAD_Advantage F D (msgs.getD t [])
            (smAEADRed (dhCKA G) F D msgs t (msgs.length - (t + 1)) (A ∘ encView encG encC)) +
        (msgs.length + 1) * c.δ :=
  (sm_extracted_advantage_le_SM h c hμ hν msgs A).trans
    (add_le_add_left (sm_dh_advantage_le G R F D msgs (A ∘ encView encG encC)) _)

/-- **Confidentiality of the extracted double ratchet at uniform exponents.** Under `DrHom`,
when the exponent of a uniform secret key is uniform, the advantage of every distinguisher `A`
between the game of the extracted session and the encoded ideal game is at most the bound of
`sm_dh_advantage_le` at the distinguisher `A ∘ encView encG encC`. -/
theorem sm_extracted_advantage_le_of_uniform
    (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC)
    (hU : ((SDistr.uniform Sk).bind fun s => SDistr.pure (decE s)) = SDistr.uniform CG.Exp)
    (msgs : List (List (W × W))) (A : SMView (Array Int) (Array Int) → SPComp Bool) :
    AdvantageA (sm_extracted RK G ptLen encR encG encSk decE encW msgs)
        ((sm_ideal (dhCKA G) msgs).map (encView encG encC)) A ≤
      ∑ t ∈ Finset.range msgs.length,
          DDH_Advantage G (ckaDDHRed t (msgs.length - (t + 1))
            (smCKARed R F D msgs t (A ∘ encView encG encC))) +
        ∑ t ∈ Finset.range msgs.length,
          PRG_Advantage R
            (smRootRed (dhCKA G) R F D msgs t (msgs.length - (t + 1)) (A ∘ encView encG encC)) +
        ∑ t ∈ Finset.range msgs.length,
          FSAEAD_Advantage F D (msgs.getD t [])
            (smAEADRed (dhCKA G) F D msgs t (msgs.length - (t + 1)) (A ∘ encView encG encC)) := by
  rw [sm_extracted_eq h hU, advantageA_map]
  exact sm_dh_advantage_le G R F D msgs (A ∘ encView encG encC)

end Model

/-! ## The Signal double ratchet on the extracted session -/

section Signal

variable (RK G : Type) [CG : CyclicGroup G] {W Sk : Type} [Fintype RK] [Nonempty RK]
  [CryptoWord W] [Fintype Sk] [Nonempty Sk]

/-- The Signal double ratchet game of the extracted session: `sm_extracted` on the Signal
plaintexts, with root keys encoded by `encR`, group elements by `encG`, secret keys by `encSk`
with exponents `decE`, and words by `encW`. -/
noncomputable abbrev signalDRExtracted (ptLen : Int) (encR : RK → Array Int)
    (encG : G → Array Int) (encSk : Sk → Array Int) (decE : Sk → CG.Exp)
    (encW : W → Array Int) (msgs : List (List W)) :
    Unit → SPComp (SMView (Array Int) (Array Int)) :=
  fun _ => sm_extracted RK G ptLen encR encG encSk decE encW (signalMsgs msgs)

/-- The Signal ideal game with its views encoded by `encG` and `encW`. -/
noncomputable abbrev signalDRIdealEnc (encG : G → Array Int) (encW : W → Array Int)
    (msgs : List (List W)) : Unit → SPComp (SMView (Array Int) (Array Int)) :=
  fun _ => (signalDRIdeal G msgs ()).map (encView encG encW)

variable {RK G}

/-- **The extracted Signal double ratchet game is the encoded Signal game** when the exponent
of a uniform secret key is uniform. -/
theorem signalDRExtracted_eq {kdf : RK → G → RK × W} {cfg : Signal.FSAEAD.FSAEADConfig W}
    {ptLen : Int} {encR : RK → Array Int} {encG : G → Array Int} {encSk : Sk → Array Int}
    {decE : Sk → CG.Exp} {encW : W → Array Int}
    (h : DrHom G (hkdfRoot kdf) (Signal.FSAEAD.toPRG cfg) (Signal.FSAEAD.toAEAD cfg) ptLen encR
      encG encSk decE encW encW encW)
    (hU : ((SDistr.uniform Sk).bind fun s => SDistr.pure (decE s)) = SDistr.uniform CG.Exp)
    (msgs : List (List W)) :
    signalDRExtracted RK G ptLen encR encG encSk decE encW msgs () =
      (signalDRReal G kdf cfg msgs ()).map (encView encG encW) :=
  sm_extracted_eq h hU (signalMsgs msgs)

/-- **Confidentiality of the extracted Signal double ratchet.** Under `DrHom` at the HKDF root
step `hkdfRoot kdf` and the symmetric ratchet `cfg`, for a certificate `c` from the image `c.μ`
of the uniform sampler on `Sk` under `decE` to the uniform exponent sampler `c.ν`, the
advantage of every distinguisher `A` between the game of the extracted session and the encoded
ideal game is at most `signalDRBound` at `A ∘ encView encG encW` plus
`(msgs.length + 1) * c.δ`. -/
theorem signalDR_extracted_advantage_le {kdf : RK → G → RK × W}
    {cfg : Signal.FSAEAD.FSAEADConfig W} {ptLen : Int} {encR : RK → Array Int}
    {encG : G → Array Int} {encSk : Sk → Array Int} {decE : Sk → CG.Exp}
    {encW : W → Array Int}
    (h : DrHom G (hkdfRoot kdf) (Signal.FSAEAD.toPRG cfg) (Signal.FSAEAD.toAEAD cfg) ptLen encR
      encG encSk decE encW encW encW)
    (c : SamplerCert CG.Exp)
    (hμ : c.μ = (SDistr.uniform Sk).bind fun s => SDistr.pure (decE s))
    (hν : c.ν = SDistr.uniform CG.Exp)
    (msgs : List (List W)) (A : SMView (Array Int) (Array Int) → SPComp Bool) :
    AdvantageA (signalDRExtracted RK G ptLen encR encG encSk decE encW msgs ())
        (signalDRIdealEnc G encG encW msgs ()) A ≤
      signalDRBound G kdf cfg msgs (A ∘ encView encG encW) + (msgs.length + 1) * c.δ := by
  have hc := sm_extracted_advantage_le_SM h c hμ hν (signalMsgs msgs) A
  rw [signalMsgs, List.length_map, ← signalMsgs] at hc
  exact hc.trans
    (add_le_add_left (signal_dr_confidentiality G kdf cfg msgs (A ∘ encView encG encW)) _)

/-- **Confidentiality of the extracted Signal double ratchet at uniform exponents.** Under
`DrHom` at the HKDF root step `hkdfRoot kdf` and the symmetric ratchet `cfg`, when the exponent
of a uniform secret key is uniform, the advantage of every distinguisher `A` between the game
of the extracted session and the encoded ideal game is at most `signalDRBound` at
`A ∘ encView encG encW`. -/
theorem signalDR_extracted_advantage_le_of_uniform {kdf : RK → G → RK × W}
    {cfg : Signal.FSAEAD.FSAEADConfig W} {ptLen : Int} {encR : RK → Array Int}
    {encG : G → Array Int} {encSk : Sk → Array Int} {decE : Sk → CG.Exp}
    {encW : W → Array Int}
    (h : DrHom G (hkdfRoot kdf) (Signal.FSAEAD.toPRG cfg) (Signal.FSAEAD.toAEAD cfg) ptLen encR
      encG encSk decE encW encW encW)
    (hU : ((SDistr.uniform Sk).bind fun s => SDistr.pure (decE s)) = SDistr.uniform CG.Exp)
    (msgs : List (List W)) (A : SMView (Array Int) (Array Int) → SPComp Bool) :
    AdvantageA (signalDRExtracted RK G ptLen encR encG encSk decE encW msgs ())
        (signalDRIdealEnc G encG encW msgs ()) A ≤
      signalDRBound G kdf cfg msgs (A ∘ encView encG encW) := by
  rw [signalDRExtracted_eq h hU, advantageA_map]
  exact signal_dr_confidentiality G kdf cfg msgs (A ∘ encView encG encW)

end Signal

end CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedCorrespondence
