/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.SymmRatchet
public import CatCryptCore.Crypto.Signal.DoubleRatchet.ExtractedCorrespondence
public import CatCryptCore.Hax.ReprBridge
public import CatCryptCore.Crypto.UCDSL
public import CatCryptCore.Crypto.Libcrux.Extraction.Libcrux_specs
public import CatCryptCore.Crypto.Libcrux.ConcreteInstances

/-!
# Signal Double Ratchet: Extraction to Security

Instantiates the hax-extracted `DoubleratchetDeps` of the crate `doubleratchet-hax`
(<https://github.com/spitters/signal-hax>) with libcrux-specs primitives and carries the game of
the extracted session to the Signal double ratchet of `Signal.DoubleRatchet_UC`.

```
doubleratchet-hax                        (Rust: the typestate session, generic in the
        |  haxpipeT --emit-certified       trait DoubleRatchetDeps)
Doubleratchet_haxpipe                    (DoubleratchetDeps: hmac_sha256, hkdf_extract,
        |                                  hkdf_expand, x25519, aead_encrypt, aead_decrypt)
        |  defaultDoubleratchetDeps        (libcrux-specs HMAC-SHA256, HKDF-SHA256, X25519)
        |  defaultDrHom                    (vecToArrayInt carries them to the model)
ExtractedCorrespondence                  (sm_extracted over Session_* = encoded sm_real)
        |  signalDR_extracted_advantage_le
Signal.DoubleRatchet_UC                  (DH CKA, HKDF root step, FS-AEAD)
```

The extraction computes on byte arrays and the model on `Vector UInt8 32`. The instance
`defaultDoubleratchetDeps` decodes its arguments (`decodeKey`, the inverse of
`vecToArrayInt`), applies the libcrux-specs operation and encodes the result: `hmac_sha256` is
`hmac_sha256_32`, `hkdf_extract` and `hkdf_expand` are `hkdf_extract_32` and `hkdf_expand_32`,
and `x25519` is `x25519_scalarmult`. Encryption is XOR: `aead_encrypt` and `aead_decrypt` are
`xorBytes`, the XOR of the decoded 32-byte key and the first 32 entries of the text (`wxorEnc`
on words). The trait's `aead_encrypt` takes texts of up to `MAX_PLAINTEXT_LEN = 256` bytes;
`xorBytes` reads 32 of them, and the theorems here use it at the 32-byte encodings
`vecToArrayInt` of words only.

The Diffie–Hellman CKA of the model is over a cyclic group `G` with byte encodings `encG` of its
elements and `encE` of its exponents; the hypothesis `hX` (a `Fact` for the instances) states
that `x25519_scalarmult` at the encodings is the exponentiation of `G`, for every exponent. No
`CyclicGroup` structure on X25519 byte vectors is instantiated here, and `hX` does not hold at
the X25519 group itself: RFC 7748 clamps every scalar to `2^254 + 8 j` with `j < 2^251`, so the
clamped scalars reach at most `2^251` residues modulo the order `ℓ > 2^252` of the prime-order
subgroup of Curve25519 and none of them is `0 mod ℓ`. Hence, for `G` that subgroup with
exponents `ZMod ℓ` and `encG` the u-coordinate, no `encE` satisfies `hX` at the exponent `0`.
The theorems below hold for every group and encodings that satisfy `hX`; the DDH terms of their
bounds are DDH advantages in such a group.

`signalDR_e2e_uc_secure`: the game of the extracted session at `defaultDoubleratchetDeps`
UC-emulates the encoded ideal game, through the class route (`PureGame`, `GameAdvBoundC`,
`UCFromGameC.uc`); the bound for adversary `A` and environment `Z` is `signalDRBound` at
`envReduction A Z` precomposed with the encoding of the views: the DDH advantages, the PRG
advantages of the HKDF root step and the FS-AEAD advantages of the libcrux symmetric ratchet
against explicit reductions, summed over the epochs.

## References

* J. Alwen, S. Coretti, Y. Dodis, "The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol", Eurocrypt 2019: the secure-messaging game and its
  decomposition into CKA, PRF-PRNG and FS-AEAD.
* R. Canetti, P. Jain, M. Swanberg, M. Varia, "Universally Composable End-to-End Secure
  Messaging", CRYPTO 2022 (ePrint 2022/376). The UC statement here is the lift of the
  secure-messaging game through `UCFromGameC`, not the functionality of that paper.
* T. Perrin, M. Marlinspike, "The Double Ratchet Algorithm", Signal specification, 2016.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.DoubleRatchet.SurfaceDeps

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Examples.SymmRatchet
open CatCrypt.Crypto.Messaging CatCrypt.Crypto.Signal.DoubleRatchet_CKA
open CatCrypt.Crypto.Signal.DoubleRatchet_UC
open CatCryptCore.Examples.CyclicGroupDDH
open CatCrypt.Crypto.UCDSL
open CatCrypt.Crypto.Libcrux.ConcreteInstances
open CatCrypt.Crypto.Libcrux.Extraction.Libcrux_specs
open CatCrypt.Hax.ReprBridge
open scoped ENNReal

/-- The ghost record of the typestate FSM (the trait `DoubleRatchetGhost` of the crate's module
`typestate_fsm`): the ghost state is the ordered trace of actions, and each hook appends
`kind`, its leading argument, the payload length and the payload, with `kind` `0` for
`send step msg_key`, `1` for `recv step msg_key` and `2` for `event tag step` (payload
`#[step]`). -/
def doubleratchetGhostRecord (kind : Int) (ghost : Array Int) (tag : Int)
    (payload : Array Int) : Array Int :=
  ghost ++ #[kind, tag, payload.size] ++ payload

/-- A byte array read as a 32-byte key: entry `i` truncated to a byte, `0` past the end. The
decoding is total and inverts `vecToArrayInt` (`decodeKey_vecToArrayInt`). -/
def decodeKey (a : Array Int) : Vector UInt8 32 :=
  Vector.ofFn fun i => (a.getD i 0).toNat.toUInt8

/-- `decodeKey` is a left inverse of `vecToArrayInt`: decoding the encoding of a 32-byte vector
returns the vector. -/
theorem decodeKey_vecToArrayInt (v : Vector UInt8 32) : decodeKey (vecToArrayInt v) = v := by
  ext i hi
  simp [decodeKey, vecToArrayInt]

/-! ## The libcrux primitives of the double ratchet

The chain step is HMAC-SHA256 of the chain key on a constant block (`ckConst`), as in the
crate (`kdf_ck ck 2` the message key, `kdf_ck ck 1` the next chain key); the root step is
HKDF-SHA256 with the root key as salt and the Diffie–Hellman output as input keying material,
expanded under two info blocks into the next root key and the chain key. The libcrux
primitives are opaque; the protocol composition is transparent. -/

/-- The HMAC message block of the chain-step constant `c`: 32 bytes `c`. -/
def ckConst (c : UInt8) : Vector UInt8 32 := Vector.replicate 32 c

/-- The block `Hax.repeat_ 1 32` of the extraction decodes to `ckConst 1`. -/
theorem decodeKey_repeat_one : decodeKey (Hax.repeat_ 1 32) = ckConst 1 := by
  decide

/-- The block `Hax.repeat_ 2 32` of the extraction decodes to `ckConst 2`. -/
theorem decodeKey_repeat_two : decodeKey (Hax.repeat_ 2 32) = ckConst 2 := by
  decide

/-- Libcrux-backed chain step: the message key `HMAC(ck, ckConst 2)` and the next chain key
`HMAC(ck, ckConst 1)`. -/
noncomputable def libcrux_prg : PRGDef (Vector UInt8 32) where
  stretch := fun ck => (hmac_sha256_32 ck (ckConst 2), hmac_sha256_32 ck (ckConst 1))

/-- The libcrux-backed symmetric ratchet: the chain step `libcrux_prg` and XOR encryption under
the message key. -/
noncomputable def libcrux_fsaeadConfig :
    Signal.FSAEAD.FSAEADConfig (Vector UInt8 32) :=
  ⟨libcrux_prg, wxorEnc⟩

/-- The HKDF info block of the next root key. -/
def rootInfoRk : Vector UInt8 32 := Vector.replicate 32 1

/-- The HKDF info block of the chain key of the root step. -/
def rootInfoCk : Vector UInt8 32 := Vector.replicate 32 2

/-- The libcrux root step on bytes: `HKDF-Extract(rk, dh)` expanded under `rootInfoRk` and
`rootInfoCk`. -/
noncomputable def libcruxKdfRk (rk dh : Vector UInt8 32) : Vector UInt8 32 × Vector UInt8 32 :=
  (hkdf_expand_32 (hkdf_extract_32 rk dh) rootInfoRk,
    hkdf_expand_32 (hkdf_extract_32 rk dh) rootInfoCk)

/-- The libcrux root step of the model: `libcruxKdfRk` at the encoding `encG` of the
Diffie–Hellman output. -/
noncomputable def libcruxRootKdf {G : Type} (encG : G → Vector UInt8 32) (rk : Vector UInt8 32)
    (I : G) : Vector UInt8 32 × Vector UInt8 32 :=
  libcruxKdfRk rk (encG I)

/-- The XOR of the decoded 32-byte key and the first 32 entries of the text, encoded back as a
32-entry array: the encryption and decryption of `defaultDoubleratchetDeps`. -/
noncomputable def xorBytes (k m : Array Int) : Array Int :=
  vecToArrayInt (CryptoWord.wxor (decodeKey k) (decodeKey m))

/-! ## Extraction instance -/

/-- The primitives of the extraction on byte arrays: `hmac_sha256_32`, `hkdf_extract_32`,
`hkdf_expand_32` and `x25519_scalarmult` of the decoded arguments, encoded back by
`vecToArrayInt`; `aead_encrypt` and `aead_decrypt` are `xorBytes` of the key and the text,
whatever the length and the associated data. The ghost hooks `send`, `recv`, `event` append to
the trace (`doubleratchetGhostRecord`). -/
noncomputable instance defaultDoubleratchetDeps : Doubleratchet.DoubleratchetDeps where
  event ghost tag step := doubleratchetGhostRecord 2 ghost tag #[step]
  send := doubleratchetGhostRecord 0
  recv := doubleratchetGhostRecord 1
  hmac_sha256 k m := vecToArrayInt (hmac_sha256_32 (decodeKey k) (decodeKey m))
  hkdf_extract s i := vecToArrayInt (hkdf_extract_32 (decodeKey s) (decodeKey i))
  hkdf_expand p i := vecToArrayInt (hkdf_expand_32 (decodeKey p) (decodeKey i))
  x25519 sk pk := vecToArrayInt (x25519_scalarmult (decodeKey sk) (decodeKey pk))
  aead_encrypt k m _ _ := xorBytes k m
  aead_decrypt k c _ _ := xorBytes k c

/-- `vecToArrayInt` carries the primitives of `defaultDoubleratchetDeps` to those of the Signal
double ratchet at the root step `libcruxRootKdf encG` and the symmetric ratchet
`libcrux_fsaeadConfig`, at the plaintext length `32`, when `x25519_scalarmult` at the encodings
`encE` and `encG` is the exponentiation of `G`. That hypothesis is not met at the X25519 group
itself (module docstring). -/
theorem defaultDrHom {G : Type} [CG : CyclicGroup G] (encG : G → Vector UInt8 32)
    (encE : CG.Exp → Vector UInt8 32)
    (hX : ∀ x T, x25519_scalarmult (encE x) (encG T) = encG (CyclicGroup.elemPow T x)) :
    ExtractedCorrespondence.DrHom G (hkdfRoot (libcruxRootKdf encG))
      (Signal.FSAEAD.toPRG libcrux_fsaeadConfig) (Signal.FSAEAD.toAEAD libcrux_fsaeadConfig) 32
      vecToArrayInt (vecToArrayInt ∘ encG) (vecToArrayInt ∘ encE) id vecToArrayInt vecToArrayInt
      vecToArrayInt where
  dh_eq x T := by
    simp only [Doubleratchet.x25519, Function.comp_apply, decodeKey_vecToArrayInt, hX, id_eq]
  root_rk_eq rk I := by
    simp only [Doubleratchet.hkdf_expand, Doubleratchet.hkdf_extract, decodeKey_vecToArrayInt,
      decodeKey_repeat_one, Function.comp_apply, hkdfRoot, libcruxRootKdf, libcruxKdfRk,
      rootInfoRk, ckConst]
  root_ck_eq rk I := by
    simp only [Doubleratchet.hkdf_expand, Doubleratchet.hkdf_extract, decodeKey_vecToArrayInt,
      decodeKey_repeat_two, Function.comp_apply, hkdfRoot, libcruxRootKdf, libcruxKdfRk,
      rootInfoCk, ckConst]
  msg_key_eq s := by
    simp only [Doubleratchet.hmac_sha256, Doubleratchet.ck_const, decodeKey_vecToArrayInt,
      decodeKey_repeat_two, Signal.FSAEAD.toPRG, libcrux_fsaeadConfig, libcrux_prg, PRGDef.core]
  chain_key_eq s := by
    simp only [Doubleratchet.hmac_sha256, Doubleratchet.ck_const, decodeKey_vecToArrayInt,
      decodeKey_repeat_one, Signal.FSAEAD.toPRG, libcrux_fsaeadConfig, libcrux_prg, PRGDef.core]
  aead_eq k m a := by
    simp only [Doubleratchet.aead_encrypt, xorBytes, decodeKey_vecToArrayInt,
      Signal.FSAEAD.toAEAD, libcrux_fsaeadConfig, EncDef.aead, wxorEnc]

/-! ## Security of the extracted double ratchet -/

section UC

open ExtractedCorrespondence UCConcrete

variable (G : Type) [CG : CyclicGroup G]

/-- The Signal double ratchet game of the extracted session at `defaultDoubleratchetDeps`:
`Uninitialized_establish`, `Session_send`, `Session_dh_ratchet` and `Session_receive` on the
libcrux primitives, the plaintext length `32`, group elements encoded by
`vecToArrayInt ∘ encG` and exponents by `vecToArrayInt ∘ encE`. -/
noncomputable abbrev signalDRLibcrux (encG : G → Vector UInt8 32)
    (encE : CG.Exp → Vector UInt8 32) (msgs : List (List (Vector UInt8 32))) :
    Unit → SPComp (SMView (Array Int) (Array Int)) :=
  signalDRExtracted (Vector UInt8 32) G 32 vecToArrayInt (vecToArrayInt ∘ encG)
    (vecToArrayInt ∘ encE) id vecToArrayInt msgs

/-- The encoded ideal game of `signalDRLibcrux`. -/
noncomputable abbrev signalDRLibcruxIdeal (encG : G → Vector UInt8 32)
    (msgs : List (List (Vector UInt8 32))) : Unit → SPComp (SMView (Array Int) (Array Int)) :=
  signalDRIdealEnc G (vecToArrayInt ∘ encG) vecToArrayInt msgs

variable {G} (encG : G → Vector UInt8 32) (encE : CG.Exp → Vector UInt8 32)
  [hX : Fact (∀ x T, x25519_scalarmult (encE x) (encG T) = encG (CyclicGroup.elemPow T x))]

/-- The game of the extracted session does not touch the heap. -/
instance signalDRLibcrux_pureGame (msgs : List (List (Vector UInt8 32))) :
    PureGame (signalDRLibcrux G encG encE msgs) :=
  ⟨fun u => by
    cases u
    change SPComp.IsPure (signalDRExtracted (Vector UInt8 32) G 32 vecToArrayInt
      (vecToArrayInt ∘ encG) (vecToArrayInt ∘ encE) id vecToArrayInt msgs ())
    rw [signalDRExtracted_eq (defaultDrHom encG encE hX.out) (SDistr.bind_pure _)]
    exact SPComp.bind_isPure (PureGame.isPure (G := signalDRReal G (libcruxRootKdf encG)
      libcrux_fsaeadConfig msgs) ()) fun _ => SPComp.pure_isPure _⟩

omit [hX : Fact (∀ x T, x25519_scalarmult (encE x) (encG T) = encG (CyclicGroup.elemPow T x))] in
/-- The encoded ideal game does not touch the heap. -/
instance signalDRLibcruxIdeal_pureGame (msgs : List (List (Vector UInt8 32))) :
    PureGame (signalDRLibcruxIdeal G encG msgs) :=
  ⟨fun _ => SPComp.bind_isPure (PureGame.isPure (G := signalDRIdeal (W := Vector UInt8 32) G
    msgs) ()) fun _ => SPComp.pure_isPure _⟩

/-- The per-adversary bound of the game of the extracted session: `signalDRBound` at the root
step `libcruxRootKdf encG` and the symmetric ratchet `libcrux_fsaeadConfig`, at the
distinguisher precomposed with the encoding of the views. -/
instance signalDRLibcrux_gameAdvBound (msgs : List (List (Vector UInt8 32))) :
    GameAdvBoundC (signalDRLibcrux G encG encE msgs) (signalDRLibcruxIdeal G encG msgs)
      (fun _ A => signalDRBound G (libcruxRootKdf encG) libcrux_fsaeadConfig msgs
        (A ∘ encView (vecToArrayInt ∘ encG) vecToArrayInt)) :=
  ⟨fun _ A => signalDR_extracted_advantage_le_of_uniform (defaultDrHom encG encE hX.out)
    (SDistr.bind_pure _) msgs A⟩

/-- **UC security of the extracted Signal double ratchet.** The secure-messaging game of one
session of `doubleratchet-hax` (`Uninitialized_establish`, `Session_send`, `Session_dh_ratchet`,
`Session_receive`) at `defaultDoubleratchetDeps` (libcrux HMAC-SHA256, HKDF-SHA256 and
X25519, XOR encryption), with the Diffie–Hellman CKA over a group `G` whose exponentiation is
`x25519_scalarmult` at the encodings `encG` and `encE` (`hX`), UC-emulates the encoded ideal
game; the bound for the adversary `A` and the environment `Z` is `signalDRBound` at the
distinguisher `envReduction A Z` precomposed with the encoding of the views. -/
theorem signalDR_e2e_uc_secure (msgs : List (List (Vector UInt8 32))) (V : Type) :
    UCConcrete.UCEmulatesCSim (UCSpec.ofGame Unit (SMView (Array Int) (Array Int)) V)
      (UCProtocol.ofGame (signalDRLibcrux G encG encE msgs))
      (UCProtocol.ofGame (signalDRLibcruxIdeal G encG msgs)) id
      (UCConcrete.gameUCBound fun _ A => signalDRBound G (libcruxRootKdf encG)
        libcrux_fsaeadConfig msgs (A ∘ encView (vecToArrayInt ∘ encG) vecToArrayInt)) :=
  UCFromGameC.uc

end UC

/-! ## Unfolding lemmas -/

/-- The chain step `libcrux_prg` at the chain key `ck` is the pair of the message key
`HMAC(ck, ckConst 2)` and the next chain key `HMAC(ck, ckConst 1)`. -/
theorem libcrux_prg_stretch (ck : Vector UInt8 32) :
    libcrux_prg.stretch ck = (hmac_sha256_32 ck (ckConst 2), hmac_sha256_32 ck (ckConst 1)) :=
  rfl

end CatCrypt.Crypto.Signal.DoubleRatchet.SurfaceDeps
