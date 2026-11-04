/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.List.Perm.Basic

/-!
# The Lizard encoding

Lizard is Signal's encoding of 16-byte messages as ristretto255 group elements, used in
zkgroup credential presentations (`RistrettoPoint::lizard_encode` and `lizard_decode` of
Signal's curve25519-dalek). It is stated here over an abstract hash `SHA256`, an abstract
point type and abstract Elligator directions:

1. The buffer of a message is `SHA256(msg)[0..8] ++ msg ++ SHA256(msg)[24..32]`.
2. The low bit of byte 0 and the two high bits of byte 31 are cleared, so that the buffer
   is a field element in the image used by Elligator.
3. Elligator maps the buffer to a point.

Decoding computes the Elligator preimage candidates of a point, keeps those that are the
canonical buffer of their middle 16 bytes (`checkValid`), and returns the middle bytes when
exactly one candidate passes. This is the semantics of dalek's `lizard_decode`, which counts
the passing candidates among the eight returned by `elligator_ristretto_flavor_inverse` and
returns `Some` only when the count is one.

## Main definitions

* `clearBits`, `buildBuffer`, `extractMsg`, `checkValid` — the byte-level steps.
* `lizardEncode`, `lizardDecode` — the encoding and the exactly-one decoding.
* `OnlyCanonical` — no decode candidate of an encoding but the canonical buffer is canonical.

## Main results

* `lizardRoundtrip` — `lizardDecode (lizardEncode msg) = some msg` for a 16-byte `msg`,
  when the canonical buffer of `msg` is among the decode candidates of its encoding and no
  other candidate passes `checkValid`. Neither condition is proved for SHA-256 and
  ristretto255's Elligator: the second is the event, for a uniformly random hash, that none
  of the other at most seven candidates is canonical.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.Zkgroup.Lizard

variable {Point : Type}
variable (SHA256 : List UInt8 → List UInt8)
variable (SHA256_length : ∀ msg, (SHA256 msg).length = 32)
variable (elligator2_encode : List UInt8 → Point)
variable (elligator2_decode_candidates : Point → List (List UInt8))

/-! ## Bytes and buffers -/

/-- Clear the low bit of a byte (mask with 0xFE). -/
def clearByte0 (b : UInt8) : UInt8 := b &&& 0xFE

/-- Clear the two high bits of a byte (mask with 0x3F). -/
def clearByte31 (b : UInt8) : UInt8 := b &&& 0x3F

theorem clearByte0_idem (b : UInt8) : clearByte0 (clearByte0 b) = clearByte0 b := by
  simp [clearByte0, UInt8.and_assoc]

theorem clearByte31_idem (b : UInt8) : clearByte31 (clearByte31 b) = clearByte31 b := by
  simp [clearByte31, UInt8.and_assoc]

/-- The 32-byte Lizard buffer of a 16-byte message:
`SHA256(msg)[0..8] ++ msg ++ SHA256(msg)[24..32]`. -/
def buildBuffer (msg : List UInt8) : List UInt8 :=
  (SHA256 msg).take 8 ++ msg ++ (SHA256 msg).drop 24

/-- The 16-byte message of a 32-byte buffer (bytes 8–23). -/
def extractMsg (buf : List UInt8) : List UInt8 :=
  (buf.drop 8).take 16

/-- Clear the bits reserved by Elligator: the low bit of byte 0 and the two high bits of
byte 31. -/
def clearBits (buf : List UInt8) : List UInt8 :=
  (buf.modify 0 clearByte0).modify 31 clearByte31

theorem clearBits_length (buf : List UInt8) : (clearBits buf).length = buf.length := by
  simp [clearBits]

theorem clearBits_idempotent (buf : List UInt8) : clearBits (clearBits buf) = clearBits buf := by
  refine List.ext_getElem (by simp [clearBits]) fun n _ _ => ?_
  simp only [clearBits, List.getElem_modify]
  grind [clearByte0_idem, clearByte31_idem]

/-- `clearBits` changes bytes 0 and 31 only, so it leaves the message bytes 8–23. -/
theorem clearBits_preserves_middle (buf : List UInt8) :
    extractMsg (clearBits buf) = extractMsg buf := by
  refine List.ext_getElem (by simp [extractMsg, clearBits]) fun n _ _ => ?_
  simp only [extractMsg, clearBits, List.getElem_take, List.getElem_drop, List.getElem_modify]
  grind [extractMsg, List.length_take]

/-! ## Encoding, validity check, decoding -/

/-- A buffer is canonical when it is the cleared buffer of its own message bytes. -/
def checkValid (buf : List UInt8) : Bool :=
  buf == clearBits (buildBuffer SHA256 (extractMsg buf))

/-- Encode a 16-byte message as a point. -/
def lizardEncode (msg : List UInt8) : Point :=
  elligator2_encode (clearBits (buildBuffer SHA256 msg))

/-- Decode a point: the message bytes of the canonical decode candidate when exactly one
candidate is canonical, `none` otherwise. -/
def lizardDecode (pt : Point) : Option (List UInt8) :=
  match (elligator2_decode_candidates pt).filter (checkValid SHA256) with
  | [buf] => some (extractMsg buf)
  | _ => none

/-! ## Roundtrip -/

include SHA256_length in
theorem extractMsg_buildBuffer (msg : List UInt8) (hlen : msg.length = 16) :
    extractMsg (buildBuffer SHA256 msg) = msg := by
  simp [extractMsg, buildBuffer, SHA256_length, hlen]

include SHA256_length in
theorem extractMsg_clearBits_buildBuffer (msg : List UInt8) (hlen : msg.length = 16) :
    extractMsg (clearBits (buildBuffer SHA256 msg)) = msg := by
  rw [clearBits_preserves_middle, extractMsg_buildBuffer SHA256 SHA256_length msg hlen]

include SHA256_length in
theorem checkValid_canonical (msg : List UInt8) (hlen : msg.length = 16) :
    checkValid SHA256 (clearBits (buildBuffer SHA256 msg)) = true := by
  rw [checkValid, extractMsg_clearBits_buildBuffer SHA256 SHA256_length msg hlen, beq_self_eq_true]

/-- No decode candidate of the encoding of `msg` other than its canonical buffer is
canonical: every candidate left after removing one occurrence of the canonical buffer fails
`checkValid`. -/
def OnlyCanonical (msg : List UInt8) : Prop :=
  ∀ buf ∈ (elligator2_decode_candidates (lizardEncode SHA256 elligator2_encode msg)).erase
    (clearBits (buildBuffer SHA256 msg)), checkValid SHA256 buf = false

include SHA256_length in
/-- **Roundtrip.** `lizardDecode (lizardEncode msg) = some msg` for a 16-byte message
`msg`, when the canonical buffer of `msg` is a decode candidate of its encoding and no other
candidate is canonical. -/
theorem lizardRoundtrip (msg : List UInt8) (hlen : msg.length = 16)
    (roundtrip : clearBits (buildBuffer SHA256 msg) ∈
      elligator2_decode_candidates (lizardEncode SHA256 elligator2_encode msg))
    (only : OnlyCanonical SHA256 elligator2_encode elligator2_decode_candidates msg) :
    lizardDecode SHA256 elligator2_decode_candidates (lizardEncode SHA256 elligator2_encode msg) =
      some msg := by
  have h0 : ((elligator2_decode_candidates (lizardEncode SHA256 elligator2_encode msg)).erase
      (clearBits (buildBuffer SHA256 msg))).filter (checkValid SHA256) = [] :=
    List.filter_eq_nil_iff.2 fun b hb => by simpa using only b hb
  have hp := (List.perm_cons_erase roundtrip).filter (checkValid SHA256)
  rw [List.filter_cons_of_pos (checkValid_canonical SHA256 SHA256_length msg hlen), h0] at hp
  rw [lizardDecode, List.perm_singleton.1 hp]
  exact congrArg some (extractMsg_clearBits_buildBuffer SHA256 SHA256_length msg hlen)

end CatCrypt.Crypto.Signal.Zkgroup.Lizard
