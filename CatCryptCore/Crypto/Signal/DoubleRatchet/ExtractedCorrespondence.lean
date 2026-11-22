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
`Doubleratchet.DoubleRatchetDeps Dp`, whose fields are the primitives the crate calls
(`hmac_sha256`, `hkdf_extract`, `hkdf_expand_64`, `x25519`, `aead_encrypt`, `aead_decrypt`).
The chain step `kdf_ck`, the root step `kdf_rk` and the Diffie–Hellman function `dh` of the
crate are extracted definitions over these fields, and so are the state functions
`ratchet_init_alice`, `ratchet_encrypt`, `dh_ratchet_recv_half` and `dh_ratchet_send_half`.
The ratchet state is a 13-component tuple (`RatchetState_T`): the sending key pair, the
optional remote ratchet key, the root key, the optional sending and receiving chain keys, the
counters `ns`, `nr`, `pn` and the four arrays of the store of skipped message keys.

`DrHom` states equations of the primitives at encoded arguments: `x25519` at the encoding
`encSk s` of a secret key `s : Sk` is the exponentiation of a cyclic group `G` by the exponent
`decE s`; HKDF-Extract, HKDF-Expand of 64 bytes under `KDF_RK_INFO` and the split into two
halves is the root KDF `R`; HMAC-SHA256 under the seeds `ck_const 1` and `ck_const 2` is the
generator `F` (message key and next chain key); `aead_encrypt` at the plaintext length `ptLen`
and the associated data `concat_ad (encAD a) (encH h)` is the encryption of the AEAD `D` at the
associated data `(a, h)`, and `aead_decrypt` at the ciphertext length `ct_len ptLen` is its
decryption. Under these equations the extracted `kdf_ck`, `kdf_rk` and `dh` compute the
encodings of the model's steps, `ratchet_encrypt` the encoded sending step and the two halves
of the Diffie–Hellman ratchet the encoded root steps.

The model game `smSampled` presents the secure-messaging game of the Diffie–Hellman CKA over
an exponent sampler: its real game draws the `msgs.length + 1` exponents of the CKA from the
sampler before anything else and is `sm_real (dhCKA G)` at the uniform sampler; its ideal game
is `sm_ideal (dhCKA G)` and draws nothing from the sampler.

## Main definitions

* `DrHom` — the equations of the primitives at encoded arguments
* `encView` — the encoding of a view of the secure-messaging adversary
* `smSampled` — the secure-messaging game of the Diffie–Hellman CKA over an exponent sampler

## Main results

* `kdf_ck_enc`, `kdf_rk_enc`, `dh_enc` — the extracted chain step, root step and
  Diffie–Hellman function at encoded arguments
* `ratchet_init_alice_enc` — the initial state of the initiator at encoded keys
* `ratchet_encrypt_enc`, `ratchet_encrypt_none` — the sending step at an encoded sending chain
  key, and its refusal without a sending chain key
* `dh_ratchet_recv_half_enc`, `dh_ratchet_send_half_enc`, `dh_ratchet_send_half_none` — the two
  halves of the Diffie–Hellman ratchet at encoded keys
* `smSampled_realAt_uniform`, `smSampled_idealAt` — the games of `smSampled` at the uniform
  sampler are `sm_real (dhCKA G)` and `sm_ideal (dhCKA G)`
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

/-! ## The primitives at encoded arguments -/

/-- Encodings of root keys (`encR`), group elements (`encG`), secret keys (`encSk`), chain
states (`encS`), message keys (`encW`), plaintexts (`encPt`), ciphertexts (`encC`), associated
data of the key agreement (`encAD`) and message headers (`encH`), and the exponent `decE s` of
a secret key `s`, under which the primitives of the instance `Dp` are the model's: `x25519` at
the secret key `s` is the exponentiation of `G` by `decE s`; HKDF-Extract, HKDF-Expand under
`KDF_RK_INFO` and `split64` are the root KDF `R`; HMAC-SHA256 under the seed `ck_const 1` is the
message key and under `ck_const 2` the next state of `F`; `aead_encrypt` at the plaintext
length `ptLen` and `aead_decrypt` at the ciphertext length `ct_len ptLen`, with the associated
data `concat_ad (encAD a) (encH h)`, are the encryption and decryption of `D` at `(a, h)`. -/
structure DrHom {RK Sa W Ct Sk A Hd : Type} [SampleableType W] (Dp : Type)
    [DoubleRatchetDeps Dp] (G : Type) [CG : CyclicGroup G]
    (R : PRGDef (RK × G) (RK × Sa)) (F : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (A × Hd))
    (ptLen : Int) (encR : RK → Array Int) (encG : G → Array Int) (encSk : Sk → Array Int)
    (decE : Sk → CG.Exp) (encS : Sa → Array Int) (encW : W → Array Int)
    (encPt : W → Array Int) (encC : Ct → Array Int) (encAD : A → Array Int)
    (encH : Hd → MessageHeader_T) : Prop where
  dh_eq : ∀ s T, DoubleRatchetDeps.x25519 (Self := Dp) (encSk s) (encG T) =
    encG (CyclicGroup.elemPow T (decE s))
  root_eq : ∀ rk I, split64 (DoubleRatchetDeps.hkdf_expand_64 (Self := Dp)
      (DoubleRatchetDeps.hkdf_extract (Self := Dp) (encR rk) (encG I)) KDF_RK_INFO) =
    (encR (R.stretch (rk, I)).1, encS (R.stretch (rk, I)).2)
  msg_key_eq : ∀ s, DoubleRatchetDeps.hmac_sha256 (Self := Dp) (encS s) (ck_const 1) =
    encW (F.stretch s).1
  chain_key_eq : ∀ s, DoubleRatchetDeps.hmac_sha256 (Self := Dp) (encS s) (ck_const 2) =
    encS (F.stretch s).2
  aead_eq : ∀ k m a h, DoubleRatchetDeps.aead_encrypt (Self := Dp) (encW k) (encPt m) ptLen
      (concat_ad (encAD a) (encH h)) = encC (D.encrypt k m (a, h))
  aead_dec_eq : ∀ k c a h, DoubleRatchetDeps.aead_decrypt (Self := Dp) (encW k) (encC c)
      (ct_len ptLen) (concat_ad (encAD a) (encH h)) =
    (D.decrypt k c (a, h)).map (fun m => (encPt m, ptLen))

section Primitives

variable {Dp : Type} [Inhabited Dp] [DoubleRatchetDeps Dp]
  {RK Sa W Ct Sk A Hd : Type} [SampleableType W] {G : Type} [CG : CyclicGroup G]
  {R : PRGDef (RK × G) (RK × Sa)} {F : PRGDef Sa (W × Sa)} {D : AEADDef W Ct (A × Hd)}
  {ptLen : Int} {encR : RK → Array Int} {encG : G → Array Int} {encSk : Sk → Array Int}
  {decE : Sk → CG.Exp} {encS : Sa → Array Int} {encW : W → Array Int}
  {encPt : W → Array Int} {encC : Ct → Array Int} {encAD : A → Array Int}
  {encH : Hd → MessageHeader_T}

/-- The extracted chain step at an encoded state is the encoded next state and the encoded
message key of `F`. -/
theorem kdf_ck_enc
    (h : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD encH) (s : Sa) :
    kdf_ck (D := Dp) (encS s) = (encS (F.stretch s).2, encW (F.stretch s).1) := by
  simp only [kdf_ck, h.chain_key_eq, h.msg_key_eq]

/-- The extracted root step at an encoded root key and an encoded group element is the
encoding of the root KDF `R`. -/
theorem kdf_rk_enc
    (h : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD encH)
    (rk : RK) (I : G) :
    kdf_rk (D := Dp) (encR rk) (encG I) =
      (encR (R.stretch (rk, I)).1, encS (R.stretch (rk, I)).2) := by
  simp only [kdf_rk, h.root_eq]

/-- The extracted Diffie–Hellman function at an encoded secret key and an encoded group element
is the encoded exponentiation by the exponent of the secret key. -/
theorem dh_enc
    (h : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD encH)
    (x : Sk) (T : G) :
    dh (D := Dp) (encSk x) (encG T) = encG (CyclicGroup.elemPow T (decE x)) := by
  simp only [dh, h.dh_eq]

/-! ## The state functions at encoded states -/

/-- **Initiator's initial state.** `ratchet_init_alice` at the encoded root key `rk`, the
encoded remote element `T` and the encoded secret key `x` holds the encodings of the root KDF
`R` at `rk` on `T ^ decE x` as root key and sending chain key, the remote ratchet key `T`, no
receiving chain key, zero counters and an empty store. -/
theorem ratchet_init_alice_enc
    (h : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD encH)
    (rk : RK) (T : G) (x : Sk) (pk : Array Int) :
    ratchet_init_alice (D := Dp) (encR rk) (encG T) (encSk x) pk =
      let r := R.stretch (rk, CyclicGroup.elemPow T (decE x))
      RatchetState (encSk x) pk (some (encG T)) (encR r.1) (some (encS r.2)) none 0 0 0
        (Hax.repeat_ false 32) (Hax.repeat_ (Hax.repeat_ 0 32) 32) (Hax.repeat_ 0 32)
        (Hax.repeat_ (Hax.repeat_ 0 32) 32) := by
  simp only [ratchet_init_alice, dh_enc h, kdf_rk_enc h]

/-- **Sending step.** `ratchet_encrypt` at a state whose sending chain key is the encoding of
the state `s` returns the state with the encoding of the next state of `F` and the sending
counter incremented, the header `(dhs_pk, pn, ns)`, the encryption of `D` under the message key
of `F` at the associated data `(a, hd)` for the header `hd` that encodes to it, and the
ciphertext length `ct_len ptLen`. -/
theorem ratchet_encrypt_enc
    (h : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD encH)
    (s : Sa) (m : W) (a : A) (hd : Hd) (sk pk rk : Array Int) (dhr ckr : Option (Array Int))
    (ns nr pn : Int) (u : Array Bool) (sd : Array (Array Int)) (sn : Array Int)
    (sm : Array (Array Int)) (hh : encH hd = (pk, pn, ns)) :
    ratchet_encrypt (D := Dp) (sk, pk, dhr, rk, some (encS s), ckr, ns, nr, pn, u, sd, sn, sm)
        (encPt m) ptLen (encAD a) =
      some ((sk, pk, dhr, rk, some (encS (F.stretch s).2), ckr, ns + 1, nr, pn, u, sd, sn, sm),
        encH hd, encC (D.encrypt (F.stretch s).1 m (a, hd)), ct_len ptLen) := by
  simp only [ratchet_encrypt, «.cks», «.dhs_sk», «.dhs_pk», «.dhr», «.rk», «.ckr», «.ns», «.nr»,
    «RatchetState.pn», «.sk_used», «.sk_dh», «.sk_n», «.sk_mk», RatchetState, MessageHeader,
    kdf_ck_enc h, Hax.add]
  rw [← hh, h.aead_eq]

/-- **Refused sending step.** `ratchet_encrypt` at a state without a sending chain key returns
nothing. -/
theorem ratchet_encrypt_none (sk pk rk : Array Int) (dhr ckr : Option (Array Int))
    (ns nr pn : Int) (u : Array Bool) (sd : Array (Array Int)) (sn : Array Int)
    (sm : Array (Array Int)) (pt : Array Int) (n : Int) (ad : Array Int) :
    ratchet_encrypt (D := Dp) (sk, pk, dhr, rk, none, ckr, ns, nr, pn, u, sd, sn, sm) pt n ad =
      none := by
  simp only [ratchet_encrypt, «.cks»]

/-- **Receiving half of the Diffie–Hellman ratchet.** `dh_ratchet_recv_half` at a state with
the encoded secret key `x` and the encoded root key `rk`, on the encoded remote element `T`,
holds `T` as remote ratchet key, the encodings of the root KDF `R` at `rk` on `T ^ decE x` as
root key and receiving chain key, `pn = ns` and zero counters `ns`, `nr`; the sending chain and
the store are kept. -/
theorem dh_ratchet_recv_half_enc
    (h : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD encH)
    (rk : RK) (x : Sk) (T : G) (pk : Array Int) (dhr cks ckr : Option (Array Int))
    (ns nr pn : Int) (u : Array Bool) (sd : Array (Array Int)) (sn : Array Int)
    (sm : Array (Array Int)) :
    dh_ratchet_recv_half (D := Dp)
        (encSk x, pk, dhr, encR rk, cks, ckr, ns, nr, pn, u, sd, sn, sm) (encG T) =
      let r := R.stretch (rk, CyclicGroup.elemPow T (decE x))
      (encSk x, pk, some (encG T), encR r.1, cks, some (encS r.2), 0, 0, ns, u, sd, sn, sm) := by
  simp only [dh_ratchet_recv_half, «.cks», «.dhs_sk», «.dhs_pk», «.rk», «.ns»,
    «.sk_used», «.sk_dh», «.sk_n», «.sk_mk», RatchetState, dh_enc h, kdf_rk_enc h]

/-- **Sending half of the Diffie–Hellman ratchet.** `dh_ratchet_send_half` at a state with
the encoded remote ratchet key `T` and the encoded root key `rk`, with the new key pair
`(encSk y, pk')`, holds the new key pair and the encodings of the root KDF `R` at `rk` on
`T ^ decE y` as root key and sending chain key; the receiving chain, the counters and the store
are kept. -/
theorem dh_ratchet_send_half_enc
    (h : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD encH)
    (rk : RK) (y : Sk) (T : G) (sk pk pk' : Array Int) (cks ckr : Option (Array Int))
    (ns nr pn : Int) (u : Array Bool) (sd : Array (Array Int)) (sn : Array Int)
    (sm : Array (Array Int)) :
    dh_ratchet_send_half (D := Dp)
        (sk, pk, some (encG T), encR rk, cks, ckr, ns, nr, pn, u, sd, sn, sm) (encSk y) pk' =
      let r := R.stretch (rk, CyclicGroup.elemPow T (decE y))
      (encSk y, pk', some (encG T), encR r.1, some (encS r.2), ckr, ns, nr, pn, u, sd, sn,
        sm) := by
  simp only [dh_ratchet_send_half, «.dhr», «.rk», «.ckr», «.ns», «.nr», «RatchetState.pn»,
    «.sk_used», «.sk_dh», «.sk_n», «.sk_mk», RatchetState, dh_enc h, kdf_rk_enc h]

/-- **Sending half without a remote ratchet key.** `dh_ratchet_send_half` at a state without a
remote ratchet key returns the state. -/
theorem dh_ratchet_send_half_none (sk pk rk : Array Int) (cks ckr : Option (Array Int))
    (ns nr pn : Int) (u : Array Bool) (sd : Array (Array Int)) (sn : Array Int)
    (sm : Array (Array Int)) (sk' pk' : Array Int) :
    dh_ratchet_send_half (D := Dp) (sk, pk, none, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm) sk'
        pk' = (sk, pk, none, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm) := by
  simp only [dh_ratchet_send_half, «.dhr»]

end Primitives

/-! ## The model game over an exponent sampler -/

section Model

variable {RK Sa W Ct : Type} [SampleableType W] {G : Type} [CG : CyclicGroup G]
  {R : PRGDef (RK × G) (RK × Sa)} {F : PRGDef Sa (W × Sa)} {D : AEADDef W Ct}

/-- The ciphertexts of one epoch from the state `s`: the head message under the first output
of `F`, the rest from the next state. -/
theorem encEpoch_cons (s : Sa) (m : W × W) (ms : List (W × W)) :
    encEpoch F D s (m :: ms) =
      D.encrypt (F.stretch s).1 m.1 m.2 :: encEpoch F D (F.stretch s).2 ms := by
  simp only [encEpoch, encAll, fsprgRun, List.length_cons, List.zipWith_cons_cons]

/-- The ciphertexts of the epochs from the states `sa :: sas`: the epoch of `sa`, then the
others. -/
theorem smCts_cons (sa : Sa) (sas : List Sa) (ms : List (W × W)) (mss : List (List (W × W))) :
    smCts F D (sa :: sas) (ms :: mss) = encEpoch F D sa ms :: smCts F D sas mss := by
  simp only [smCts, List.zipWith_cons_cons]

/-- The messages of `dhChain h xs` are the public values of the exponents `xs`. -/
theorem dhChain_map_fst (h : G) (xs : List CG.Exp) :
    (dhChain h xs).map Prod.fst = xs.map CG.pow := by
  induction xs generalizing h with
  | nil => rfl
  | cons x xs ih => simp only [dhChain, List.map_cons, ih]

/-- The encoding of a view of the secure-messaging adversary: the CKA public value and messages
under `encM`, the ciphertexts under `encC`. -/
def encView {Msg : Type} (encM : Msg → Array Int) (encC : Ct → Array Int)
    (v : SMView Msg Ct) : SMView (Array Int) (Array Int) :=
  ((encM v.1.1, v.1.2.map encM), v.2.map (List.map encC))

variable [Fintype RK] [Nonempty RK] [Fintype Sa] [Nonempty Sa] [SampleableType Ct]

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

omit [Fintype Sa] [Nonempty Sa] in
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

omit [Fintype Sa] [Nonempty Sa] in
/-- The ideal game of `smSampled` is `sm_ideal (dhCKA G)` at every sampler. -/
theorem smSampled_idealAt (msgs : List (List (W × W))) (μ : SDistr CG.Exp) :
    (smSampled R F D msgs).idealAt μ = sm_ideal (dhCKA G) msgs := by
  rw [SampledGame.idealAt]
  exact sampleFrom_replicateFin_zero_bind μ _

end Model

/- The passive game over the extracted functions is not part of this file: `encPair`,
`sendEpoch`, `recvEpoch`, `sendEpoch_cts`, `recvEpoch_cts`, `sendEpoch_keys`, `recvEpoch_keys`,
`dh_ratchet_recv_ck`, `ratchetCts`, `ratchetCts_eq`, `sessionCts`, `sessionCts_eq`,
`sm_extracted`, `sm_extracted_realizes`, `sm_extracted_eq`, `sm_extracted_advantage_le_SM`,
`sm_extracted_advantage_le`, `sm_extracted_advantage_le_of_uniform`, the section `Signal`
(`signalDRExtracted`, `signalDRExtracted_eq`, `signalDR_extracted_advantage_le`,
`signalDR_extracted_advantage_le_of_uniform`). They are restated over `ratchet_encrypt` and
`ratchet_receive_key`. -/

end CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedCorrespondence
