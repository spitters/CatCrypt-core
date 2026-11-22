/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signal.DoubleRatchet.Primitives
public import CatCryptCore.Crypto.Libcrux.Extraction.Libcrux_specs
public import CatCryptCore.Crypto.Libcrux.SignalKDFSpec
public import CatCryptCore.Crypto.Libcrux.ConcreteInstances
public import CatCryptCore.Hax.ReprBridge
public import CatCryptCore.Crypto.Signal.DoubleRatchet.Extraction.Doubleratchet_haxpipe

/-!
# The message encryption of the Signal double ratchet at the key schedule of libsignal

The message encryption below has the key schedule of libsignal without SPQR, its cipher and its
tag length, over the MAC input of `doubleratchet-hax`. It encrypts under a 32-byte message key
`mk` as follows (`MessageKeys::derive_keys` and `SignalMessage::compute_mac` of libsignal):

* HKDF-SHA256 with the zero salt and the info string `"WhisperMessageKeys"` expands `mk` into
  80 bytes: a 32-byte AES-256 key, a 32-byte HMAC-SHA256 key and a 16-byte IV;
* the plaintext, padded by PKCS#7 to whole blocks, is encrypted by AES-256-CBC under that key
  and IV;
* the tag is HMAC-SHA256 under the MAC key, truncated to its first 8 bytes. libsignal MACs the
  sender's and the receiver's identity keys followed by the serialized message (version byte,
  protobuf header and ciphertext); the crate passes an opaque 64-byte associated data, and this
  module MACs the associated data `concat_ad ad header` followed by the ciphertext blocks,
  without the protobuf framing.

`signalMsgCipher S ptLen` is this construction as a `MsgCipher` of `Primitives`, and
`aeadEncrypt` and `aeadDecrypt` are specification functions at the Lean signatures of the fields
`aead_encrypt` and `aead_decrypt` of `Doubleratchet.DoubleRatchetDeps`, defined as the encodings
of the encryption and decryption of `signalMsgAEAD (signalMsgCipher S ptLen)`. They do not model
the lengths of the crate.

The model fixes one plaintext length `ptLen` per instance: the ciphertexts of a core AEAD are
one type, and the ideal game of `Assumptions.AEAD_Advantage` samples its ciphertext uniformly
from that type, so the ciphertext length, and with it the plaintext length, is fixed.
`aeadEncrypt` and `aeadDecrypt` ignore their length arguments and read `ptLen` bytes of
plaintext and `16 (ptLen / 16 + 1) + 8` bytes of ciphertext, which is the extracted
`ct_len ptLen`.

`MsgCipher` takes message keys, plaintexts and associated data in one type. The type
`MsgWord ptLen` has three components: a 32-byte message key, 104 bytes of associated data (the
`concat_ad ad header` of the extracted `ratchet_encrypt`) and `ptLen` bytes of plaintext. A
message key is read from the first component, a plaintext from the third and associated data
from the second; the other components of each are not read.

The specification functions that `Libcrux_specs` and `SignalKDFSpec` lack (AES-256 and its
inverse, HKDF-Expand of 80 bytes under an 18-byte info string, HMAC-SHA256 on a message of any
length) are the fields of `MsgSpecFns`, a parameter of the construction. No implementation is
related to the fields and no property of them is assumed. The security bound
`deployed_aead_advantage_le` holds for every such parameter; its terms are the PRG advantage of
the key expansion, the PRP advantage of the block function and the PRF advantage of the
truncated tag, each at the explicit reduction of `aead_advantage_signalMsg_le`.

## Main definitions

* `MsgSpecFns` — the specification functions of AES-256, its inverse, HKDF-Expand of 80 bytes
  and HMAC-SHA256
* `MsgWord ptLen` — message key, associated data and plaintext of `ptLen` bytes
* `signalMsgCipher S ptLen` — the message encryption as a `MsgCipher`
* `aeadEncrypt`, `aeadDecrypt` — the specification functions on byte arrays

## Main results

* `aeadEncrypt_enc` — `aeadEncrypt` at encoded arguments is the encoded encryption
* `aeadDecrypt_enc` — `aeadDecrypt` at encoded arguments is the encoded decryption with the tag
  check
* `deployed_aead_advantage_le` — the one-time real-or-random advantage of the message
  encryption is at most a PRG, a PRP and a PRF advantage and `n(n-1) / 2^128`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.DoubleRatchet.DeployedAEAD

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.Signal.DoubleRatchet.Primitives
open CatCrypt.Crypto.Constructions.CBCINDCPA
open CatCrypt.Crypto.Libcrux.ConcreteInstances
open CatCrypt.Crypto.Libcrux.Extraction.Libcrux_specs
open CatCrypt.Hax.ReprBridge
open scoped ENNReal

/-! ## Specification functions and the message type -/

/-- The specification functions of the message encryption that `Libcrux_specs` and
`SignalKDFSpec` do not provide. No implementation is related to the fields and no property of
them is assumed. -/
structure MsgSpecFns where
  /-- AES-256 encryption of one 16-byte block under a 32-byte key. -/
  aes256Encrypt : Vector UInt8 32 → Vector UInt8 16 → Vector UInt8 16
  /-- AES-256 decryption of one 16-byte block under a 32-byte key. -/
  aes256Decrypt : Vector UInt8 32 → Vector UInt8 16 → Vector UInt8 16
  /-- HKDF-SHA256 Expand of 80 bytes from a 32-byte PRK under an 18-byte info string. -/
  hkdfExpand80 : Vector UInt8 32 → Vector UInt8 18 → Vector UInt8 80
  /-- HMAC-SHA256 under a 32-byte key on a message of any length. -/
  hmacSha256 : Vector UInt8 32 → Array UInt8 → Vector UInt8 32

/-- A message key, associated data and a plaintext of `ptLen` bytes: the one type of message
keys, plaintexts and associated data of `signalMsgCipher`. -/
structure MsgWord (ptLen : ℕ) where
  /-- The 32-byte message key. -/
  key : Vector UInt8 32
  /-- The 104 bytes of associated data (`concat_ad ad header`). -/
  ad : Vector UInt8 104
  /-- The plaintext of `ptLen` bytes. -/
  pt : Vector UInt8 ptLen
  deriving DecidableEq, Inhabited

/-- `MsgWord ptLen` is the product of its three components. -/
def MsgWord.equivProd (ptLen : ℕ) :
    MsgWord ptLen ≃ Vector UInt8 32 × Vector UInt8 104 × Vector UInt8 ptLen where
  toFun w := (w.key, w.ad, w.pt)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `MsgWord ptLen` is finite. -/
noncomputable instance (ptLen : ℕ) : Fintype (MsgWord ptLen) :=
  Fintype.ofEquiv _ (MsgWord.equivProd ptLen).symm

/-- `MsgWord ptLen` is a `CryptoWord` under componentwise XOR. -/
noncomputable instance instCryptoWordMsgWord (ptLen : ℕ) : CryptoWord (MsgWord ptLen) where
  toSampleableType := {}
  wxor a b := ⟨CryptoWord.wxor a.key b.key, CryptoWord.wxor a.ad b.ad,
    CryptoWord.wxor a.pt b.pt⟩
  wxor_cancel a b := by simp only [CryptoWord.wxor_cancel]
  wxor_comm a b := by simp only [MsgWord.mk.injEq]; exact ⟨CryptoWord.wxor_comm _ _,
    CryptoWord.wxor_comm _ _, CryptoWord.wxor_comm _ _⟩

/-- The message key `k` as a `MsgWord`, the other components zero. -/
def MsgWord.ofKey {ptLen : ℕ} (k : Vector UInt8 32) : MsgWord ptLen :=
  ⟨k, Vector.replicate 104 0, Vector.replicate ptLen 0⟩

/-- The associated data `a` as a `MsgWord`, the other components zero. -/
def MsgWord.ofAd {ptLen : ℕ} (a : Vector UInt8 104) : MsgWord ptLen :=
  ⟨Vector.replicate 32 0, a, Vector.replicate ptLen 0⟩

/-- The plaintext `p` as a `MsgWord`, the other components zero. -/
def MsgWord.ofPt {ptLen : ℕ} (p : Vector UInt8 ptLen) : MsgWord ptLen :=
  ⟨Vector.replicate 32 0, Vector.replicate 104 0, p⟩

/-! ## The construction -/

/-- The info string `"WhisperMessageKeys"` of the message-key expansion. -/
def msgKeysInfo : Vector UInt8 18 :=
  #v[87, 104, 105, 115, 112, 101, 114, 77, 101, 115, 115, 97, 103, 101, 75, 101, 121, 115]

/-- The number of CBC blocks of a plaintext of `ptLen` bytes under PKCS#7 padding. -/
abbrev nBlocks (ptLen : ℕ) : ℕ := ptLen / 16 + 1

/-- The plaintext `p` padded by PKCS#7 to `nBlocks ptLen` blocks: `16 - ptLen % 16` bytes of
value `16 - ptLen % 16` appended. -/
def pkcs7 {ptLen : ℕ} (p : Vector UInt8 ptLen) : Array UInt8 :=
  p.toArray ++ Array.replicate (16 - ptLen % 16) (16 - ptLen % 16).toUInt8

/-- The bytes of a list of blocks, in order. -/
def blockBytes (cs : List (Vector UInt8 16)) : Array UInt8 :=
  (cs.flatMap fun b => b.toList).toArray

/-- The key expansion of libsignal: HKDF-Extract with the zero salt on the message key, then
HKDF-Expand of 80 bytes under `"WhisperMessageKeys"`, split into the AES-256 key (bytes
`0..32`), the IV (bytes `64..80`) and the HMAC key (bytes `32..64`). -/
def deriveKeys (S : MsgSpecFns) (mk : Vector UInt8 32) :
    Vector UInt8 32 × Vector UInt8 16 × Vector UInt8 32 :=
  let okm := S.hkdfExpand80 (hkdf_extract_32 (Vector.replicate 32 0) mk) msgKeysInfo
  (Vector.ofFn fun i => okm[i.val], Vector.ofFn fun i => okm[64 + i.val],
    Vector.ofFn fun i => okm[32 + i.val])

/-- The tag of libsignal: HMAC-SHA256 under `km` of the associated data followed by the
ciphertext blocks, truncated to its first 8 bytes. -/
def msgTag (S : MsgSpecFns) (km : Vector UInt8 32) (ad : Vector UInt8 104)
    (cs : List (Vector UInt8 16)) : Vector UInt8 8 :=
  let t := S.hmacSha256 km (ad.toArray ++ blockBytes cs)
  Vector.ofFn fun i => t[i.val]

/-- AES-256-CBC decryption of `n` blocks under the key `ke` and the IV `iv`, then the check and
removal of the PKCS#7 padding of a plaintext of `ptLen` bytes; `none` on a wrong padding. -/
noncomputable def cbcDecPad (S : MsgSpecFns) (ptLen : ℕ) (ke : Vector UInt8 32)
    (iv : Vector UInt8 16) (c : Fin (nBlocks ptLen) → Vector UInt8 16) : Option (MsgWord ptLen) :=
  let p : Fin (nBlocks ptLen) → Vector UInt8 16 := fun j =>
    CryptoWord.wxor (S.aes256Decrypt ke (c j))
      (if h : j.val = 0 then iv else c ⟨j.val - 1, by omega⟩)
  let bytes := blockBytes (List.ofFn p)
  if bytes.extract ptLen bytes.size =
      Array.replicate (16 - ptLen % 16) (16 - ptLen % 16).toUInt8 then
    some (MsgWord.ofPt (Vector.ofFn fun i => bytes.getD i.val 0))
  else none

/-- **The message encryption** at plaintexts of `ptLen` bytes, over the specification
functions `S`: key expansion `deriveKeys` (HKDF with info `"WhisperMessageKeys"`), AES-256 as
the block function, PKCS#7 padding into `ptLen / 16 + 1` blocks, the tag `msgTag` (HMAC-SHA256
truncated to 8 bytes over the associated data and the ciphertext blocks) and the decryption
`cbcDecPad`. One plaintext length per instance. -/
noncomputable def signalMsgCipher (S : MsgSpecFns) (ptLen : ℕ) :
    MsgCipher (MsgWord ptLen) (Vector UInt8 16) (Vector UInt8 32) (Vector UInt8 32)
      (Vector UInt8 8) (nBlocks ptLen) where
  derive w := deriveKeys S w.key
  E := S.aes256Encrypt
  encode w j := Vector.ofFn fun i => (pkcs7 w.pt).getD (16 * j.val + i.val) 0
  T km x := msgTag S km x.1.ad x.2
  dec := cbcDecPad S ptLen

/-! ## The deployed functions on byte arrays -/

/-- A byte array read as a vector of `n` bytes: entry `i` truncated to a byte, `0` past the
end. -/
def readBytes (n : ℕ) (a : Array Int) : Vector UInt8 n :=
  Vector.ofFn fun i => (a.getD i 0).toNat.toUInt8

/-- `readBytes` is a left inverse of `vecToArrayInt`. -/
theorem readBytes_vecToArrayInt {n : ℕ} (v : Vector UInt8 n) :
    readBytes n (vecToArrayInt v) = v := by
  ext i hi
  simp [readBytes, vecToArrayInt]

/-- The encoding of a ciphertext as bytes: the `16 n` bytes of the blocks, then the 8 bytes of
the tag. -/
def encCt {n : ℕ} (c : (Fin n → Vector UInt8 16) × Vector UInt8 8) : Array Int :=
  Array.ofFn fun idx : Fin (16 * n + 8) =>
    if h : idx.val < 16 * n then ((c.1 ⟨idx.val / 16, by omega⟩)[idx.val % 16]'(by omega)).toNat
    else (c.2[idx.val - 16 * n]'(by omega)).toNat

/-- A byte array read as a ciphertext of `n` blocks and an 8-byte tag. -/
def decCt (n : ℕ) (a : Array Int) : (Fin n → Vector UInt8 16) × Vector UInt8 8 :=
  (fun j => Vector.ofFn fun i => (a.getD (16 * j.val + i.val) 0).toNat.toUInt8,
    Vector.ofFn fun i => (a.getD (16 * n + i.val) 0).toNat.toUInt8)

/-- `decCt` is a left inverse of `encCt`. -/
theorem decCt_encCt {n : ℕ} (c : (Fin n → Vector UInt8 16) × Vector UInt8 8) :
    decCt n (encCt c) = c := by
  obtain ⟨f, t⟩ := c
  refine Prod.ext (funext fun j => ?_) ?_
  · ext i hi
    have h1 : 16 * j.val + i < 16 * n + 8 := by omega
    have h2 : 16 * j.val + i < 16 * n := by omega
    have h3 : (16 * j.val + i) / 16 = j.val := by omega
    have h4 : (16 * j.val + i) % 16 = i := by omega
    simp [decCt, encCt, Array.getD_eq_getD_getElem?, h1, h2, h3, h4]
  · ext i hi
    simp [decCt, encCt, Array.getD_eq_getD_getElem?]

/-- **The encryption specification function** on byte arrays, at the Lean signature of
`aead_encrypt` of
`Doubleratchet.DoubleRatchetDeps`: the encoding `encCt` of the encryption of
`signalMsgAEAD (signalMsgCipher S ptLen)` under the 32-byte message key `mk` of the `ptLen`
bytes of `pt` with the 104 bytes of associated data `ad`. The length argument is not read:
one plaintext length per instance. -/
noncomputable def aeadEncrypt (S : MsgSpecFns) (ptLen : ℕ) (mk pt : Array Int) (_ptLen : Int)
    (ad : Array Int) : Array Int :=
  encCt ((signalMsgAEAD (signalMsgCipher S ptLen)).encrypt (MsgWord.ofKey (readBytes 32 mk))
    (MsgWord.ofPt (readBytes ptLen pt)) (MsgWord.ofAd (readBytes 104 ad)))

/-- **The decryption specification function** on byte arrays, at the Lean signature of
`aead_decrypt` of
`Doubleratchet.DoubleRatchetDeps`: the decryption of `signalMsgAEAD (signalMsgCipher S ptLen)`
under the 32-byte message key `mk` of the ciphertext `ct` (`16 (ptLen / 16 + 1)` bytes of blocks
and an 8-byte tag) with the 104 bytes of associated data `ad`, which is `none` on a wrong tag or
a wrong padding, and otherwise the `ptLen` bytes of the plaintext and the length `ptLen`. The
length argument is not read: one plaintext length per instance. -/
noncomputable def aeadDecrypt (S : MsgSpecFns) (ptLen : ℕ) (mk ct : Array Int) (_ctLen : Int)
    (ad : Array Int) : Option (Array Int × Int) :=
  ((signalMsgAEAD (signalMsgCipher S ptLen)).decrypt (MsgWord.ofKey (readBytes 32 mk))
    (decCt (nBlocks ptLen) ct) (MsgWord.ofAd (readBytes 104 ad))).map
    fun m => (vecToArrayInt m.pt, (ptLen : Int))

/-! ## The equations at encoded arguments -/

/-- **Encryption at encoded arguments.** `aeadEncrypt` at the bytes of the message key of `k`,
of the plaintext of `m`, at the plaintext length `ptLen` and the bytes of the associated data of
`ad` is the encoded encryption of `m` under `k` with associated data `ad`. -/
theorem aeadEncrypt_enc (S : MsgSpecFns) (ptLen : ℕ) (k m ad : MsgWord ptLen) :
    aeadEncrypt S ptLen (vecToArrayInt k.key) (vecToArrayInt m.pt) ptLen
        (vecToArrayInt ad.ad) =
      encCt ((signalMsgAEAD (signalMsgCipher S ptLen)).encrypt k m ad) := by
  simp only [aeadEncrypt, readBytes_vecToArrayInt]
  rfl

/-- **Decryption at encoded arguments.** `aeadDecrypt` at the bytes of the message key of `k`,
the encoded ciphertext `c`, the ciphertext length `ct_len ptLen` and the bytes of the
associated data of `ad` is the decryption of `c` under `k` with associated data `ad` (`none` on
a wrong tag), its plaintext encoded with the length `ptLen`. -/
theorem aeadDecrypt_enc (S : MsgSpecFns) (ptLen : ℕ) (k ad : MsgWord ptLen)
    (c : (Fin (nBlocks ptLen) → Vector UInt8 16) × Vector UInt8 8) :
    aeadDecrypt S ptLen (vecToArrayInt k.key) (encCt c) (Doubleratchet.ct_len ptLen)
        (vecToArrayInt ad.ad) =
      ((signalMsgAEAD (signalMsgCipher S ptLen)).decrypt k c ad).map
        fun m => (vecToArrayInt m.pt, (ptLen : Int)) := by
  simp only [aeadDecrypt, readBytes_vecToArrayInt, decCt_encCt]
  rfl

/-! ## Security -/

/-- **One-time security of the message encryption.** For the specification functions
`S`, plaintexts of `ptLen` bytes, every plaintext `pt`, associated data `ad` and adversary `A`,
the real-or-random advantage of the message encryption is at most the PRG advantage of
the key expansion `deriveKeys` against `msgKeyRed`, the PRP advantage of AES-256 against
`cbcRorAdv (msgCbcAdv …)` with `n(n-1) / 2^128` for `n = ptLen / 16 + 1` blocks, and the PRF
advantage of the truncated HMAC tag against `msgTagRed ad A`. -/
theorem deployed_aead_advantage_le (S : MsgSpecFns) (ptLen : ℕ) (pt ad : MsgWord ptLen)
    (A : Assumptions.AEAD_Adversary
      ((Fin (nBlocks ptLen) → Vector UInt8 16) × Vector UInt8 8)) :
    Assumptions.AEAD_Advantage (signalMsgAEAD (signalMsgCipher S ptLen)) pt ad A ≤
      Assumptions.PRG_Advantage (derivePRG (signalMsgCipher S ptLen))
          (msgKeyRed (signalMsgCipher S ptLen) pt ad A) +
        (PRP_q_Advantage S.aes256Encrypt
            (cbcRorAdv (msgCbcAdv (signalMsgCipher S ptLen) pt ad A)) +
          ((nBlocks ptLen * (nBlocks ptLen - 1) : ℕ) : ℝ≥0∞) /
            Fintype.card (Vector UInt8 16)) +
        PRF_q_Advantage (signalMsgCipher S ptLen).T (msgTagRed ad A) :=
  aead_advantage_signalMsg_le (signalMsgCipher S ptLen) pt ad A

end CatCrypt.Crypto.Signal.DoubleRatchet.DeployedAEAD
