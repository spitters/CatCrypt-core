/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminTypes

/-!
# Jasmin x86 Operation Semantics

This file defines the semantics of x86 assembly operations used in the
Jasmin translation, focusing on the subset needed for the AES proof.

## Operations covered

- AES intrinsics: AESENC, AESENCLAST, AESDEC, AESDECLAST, AESIMC, AESKEYGENASSIST
- Bitwise SIMD: VPXOR, VPAND, VPOR, VPANDN
- Data movement: MOV, VMOVDQU
- Shuffle: VPSHUFD, VPSHUFB, VPSLLDQ, VPSRLDQ
- Arithmetic: ADD, SUB (for loop counters)

## Design

Operations are modeled as pure functions on `BitVec` values.
The AES S-Box is defined via concrete FIPS 197 lookup tables, with
involution properties proved by `native_decide` over all 256 inputs.

## References

- Intel x86 ISA reference
- `jasmin_translate.v`: `translate_exec_sopn`
- `aes_spec.v`: AES instruction wrappers
-/

namespace CatCrypt.Crypto.Jasmin

noncomputable section

/-! ## AES S-Box (FIPS 197 lookup tables) -/

/-- AES S-Box forward table (FIPS 197, Table 4). -/
private def sboxArray : Array (BitVec 8) := #[
  0x63, 0x7C, 0x77, 0x7B, 0xF2, 0x6B, 0x6F, 0xC5, 0x30, 0x01, 0x67, 0x2B, 0xFE, 0xD7, 0xAB, 0x76,
  0xCA, 0x82, 0xC9, 0x7D, 0xFA, 0x59, 0x47, 0xF0, 0xAD, 0xD4, 0xA2, 0xAF, 0x9C, 0xA4, 0x72, 0xC0,
  0xB7, 0xFD, 0x93, 0x26, 0x36, 0x3F, 0xF7, 0xCC, 0x34, 0xA5, 0xE5, 0xF1, 0x71, 0xD8, 0x31, 0x15,
  0x04, 0xC7, 0x23, 0xC3, 0x18, 0x96, 0x05, 0x9A, 0x07, 0x12, 0x80, 0xE2, 0xEB, 0x27, 0xB2, 0x75,
  0x09, 0x83, 0x2C, 0x1A, 0x1B, 0x6E, 0x5A, 0xA0, 0x52, 0x3B, 0xD6, 0xB3, 0x29, 0xE3, 0x2F, 0x84,
  0x53, 0xD1, 0x00, 0xED, 0x20, 0xFC, 0xB1, 0x5B, 0x6A, 0xCB, 0xBE, 0x39, 0x4A, 0x4C, 0x58, 0xCF,
  0xD0, 0xEF, 0xAA, 0xFB, 0x43, 0x4D, 0x33, 0x85, 0x45, 0xF9, 0x02, 0x7F, 0x50, 0x3C, 0x9F, 0xA8,
  0x51, 0xA3, 0x40, 0x8F, 0x92, 0x9D, 0x38, 0xF5, 0xBC, 0xB6, 0xDA, 0x21, 0x10, 0xFF, 0xF3, 0xD2,
  0xCD, 0x0C, 0x13, 0xEC, 0x5F, 0x97, 0x44, 0x17, 0xC4, 0xA7, 0x7E, 0x3D, 0x64, 0x5D, 0x19, 0x73,
  0x60, 0x81, 0x4F, 0xDC, 0x22, 0x2A, 0x90, 0x88, 0x46, 0xEE, 0xB8, 0x14, 0xDE, 0x5E, 0x0B, 0xDB,
  0xE0, 0x32, 0x3A, 0x0A, 0x49, 0x06, 0x24, 0x5C, 0xC2, 0xD3, 0xAC, 0x62, 0x91, 0x95, 0xE4, 0x79,
  0xE7, 0xC8, 0x37, 0x6D, 0x8D, 0xD5, 0x4E, 0xA9, 0x6C, 0x56, 0xF4, 0xEA, 0x65, 0x7A, 0xAE, 0x08,
  0xBA, 0x78, 0x25, 0x2E, 0x1C, 0xA6, 0xB4, 0xC6, 0xE8, 0xDD, 0x74, 0x1F, 0x4B, 0xBD, 0x8B, 0x8A,
  0x70, 0x3E, 0xB5, 0x66, 0x48, 0x03, 0xF6, 0x0E, 0x61, 0x35, 0x57, 0xB9, 0x86, 0xC1, 0x1D, 0x9E,
  0xE1, 0xF8, 0x98, 0x11, 0x69, 0xD9, 0x8E, 0x94, 0x9B, 0x1E, 0x87, 0xE9, 0xCE, 0x55, 0x28, 0xDF,
  0x8C, 0xA1, 0x89, 0x0D, 0xBF, 0xE6, 0x42, 0x68, 0x41, 0x99, 0x2D, 0x0F, 0xB0, 0x54, 0xBB, 0x16
]

/-- AES inverse S-Box table (FIPS 197, Table 5). -/
private def invSboxArray : Array (BitVec 8) := #[
  0x52, 0x09, 0x6A, 0xD5, 0x30, 0x36, 0xA5, 0x38, 0xBF, 0x40, 0xA3, 0x9E, 0x81, 0xF3, 0xD7, 0xFB,
  0x7C, 0xE3, 0x39, 0x82, 0x9B, 0x2F, 0xFF, 0x87, 0x34, 0x8E, 0x43, 0x44, 0xC4, 0xDE, 0xE9, 0xCB,
  0x54, 0x7B, 0x94, 0x32, 0xA6, 0xC2, 0x23, 0x3D, 0xEE, 0x4C, 0x95, 0x0B, 0x42, 0xFA, 0xC3, 0x4E,
  0x08, 0x2E, 0xA1, 0x66, 0x28, 0xD9, 0x24, 0xB2, 0x76, 0x5B, 0xA2, 0x49, 0x6D, 0x8B, 0xD1, 0x25,
  0x72, 0xF8, 0xF6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xD4, 0xA4, 0x5C, 0xCC, 0x5D, 0x65, 0xB6, 0x92,
  0x6C, 0x70, 0x48, 0x50, 0xFD, 0xED, 0xB9, 0xDA, 0x5E, 0x15, 0x46, 0x57, 0xA7, 0x8D, 0x9D, 0x84,
  0x90, 0xD8, 0xAB, 0x00, 0x8C, 0xBC, 0xD3, 0x0A, 0xF7, 0xE4, 0x58, 0x05, 0xB8, 0xB3, 0x45, 0x06,
  0xD0, 0x2C, 0x1E, 0x8F, 0xCA, 0x3F, 0x0F, 0x02, 0xC1, 0xAF, 0xBD, 0x03, 0x01, 0x13, 0x8A, 0x6B,
  0x3A, 0x91, 0x11, 0x41, 0x4F, 0x67, 0xDC, 0xEA, 0x97, 0xF2, 0xCF, 0xCE, 0xF0, 0xB4, 0xE6, 0x73,
  0x96, 0xAC, 0x74, 0x22, 0xE7, 0xAD, 0x35, 0x85, 0xE2, 0xF9, 0x37, 0xE8, 0x1C, 0x75, 0xDF, 0x6E,
  0x47, 0xF1, 0x1A, 0x71, 0x1D, 0x29, 0xC5, 0x89, 0x6F, 0xB7, 0x62, 0x0E, 0xAA, 0x18, 0xBE, 0x1B,
  0xFC, 0x56, 0x3E, 0x4B, 0xC6, 0xD2, 0x79, 0x20, 0x9A, 0xDB, 0xC0, 0xFE, 0x78, 0xCD, 0x5A, 0xF4,
  0x1F, 0xDD, 0xA8, 0x33, 0x88, 0x07, 0xC7, 0x31, 0xB1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xEC, 0x5F,
  0x60, 0x51, 0x7F, 0xA9, 0x19, 0xB5, 0x4A, 0x0D, 0x2D, 0xE5, 0x7A, 0x9F, 0x93, 0xC9, 0x9C, 0xEF,
  0xA0, 0xE0, 0x3B, 0x4D, 0xAE, 0x2A, 0xF5, 0xB0, 0xC8, 0xEB, 0xBB, 0x3C, 0x83, 0x53, 0x99, 0x61,
  0x17, 0x2B, 0x04, 0x7E, 0xBA, 0x77, 0xD6, 0x26, 0xE1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0C, 0x7D
]

@[simp] private theorem sboxArray_size : sboxArray.size = 256 := by native_decide
@[simp] private theorem invSboxArray_size : invSboxArray.size = 256 := by native_decide

/-- AES S-Box: SubBytes transformation on a single byte.
    Concrete FIPS 197 lookup table (GF(2^8) inversion + affine map). -/
def aesSBox (b : BitVec 8) : BitVec 8 :=
  sboxArray[b.toNat]'(sboxArray_size ▸ BitVec.isLt b)

/-- AES inverse S-Box. -/
def aesInvSBox (b : BitVec 8) : BitVec 8 :=
  invSboxArray[b.toNat]'(invSboxArray_size ▸ BitVec.isLt b)

/-- S-Box inverse property: InvSBox(SBox(b)) = b for all bytes. -/
theorem aesInvSBox_aesSBox : ∀ b, aesInvSBox (aesSBox b) = b := by native_decide

/-- S-Box inverse property: SBox(InvSBox(b)) = b for all bytes. -/
theorem aesSBox_aesInvSBox : ∀ b, aesSBox (aesInvSBox b) = b := by native_decide

/-! ## AES State Operations -/

/-- Extract byte `i` from a 128-bit state (little-endian). -/
def getByte128 (state : BitVec 128) (i : Nat) : BitVec 8 :=
  (state >>> (i * 8)).truncate 8

/-- Set byte `i` in a 128-bit state. -/
def setByte128 (state : BitVec 128) (i : Nat) (b : BitVec 8) : BitVec 128 :=
  let mask := ~~~((0xFF : BitVec 128) <<< (i * 8))
  (state &&& mask) ||| ((b.zeroExtend 128) <<< (i * 8))

/-- SubBytes: apply S-Box to each byte of the state. -/
def aesSubBytes (state : BitVec 128) : BitVec 128 :=
  (List.range 16).foldl (fun s i =>
    setByte128 s i (aesSBox (getByte128 state i))
  ) 0

/-- Inverse SubBytes. -/
def aesInvSubBytes (state : BitVec 128) : BitVec 128 :=
  (List.range 16).foldl (fun s i =>
    setByte128 s i (aesInvSBox (getByte128 state i))
  ) 0

/-- Extract 32-bit column `j` from the state (little-endian). -/
def getCol128 (state : BitVec 128) (j : Nat) : BitVec 32 :=
  (state >>> (j * 32)).truncate 32

/-- Set 32-bit column `j` in the state. -/
def setCol128 (state : BitVec 128) (j : Nat) (col : BitVec 32) : BitVec 128 :=
  let mask := ~~~((0xFFFFFFFF : BitVec 128) <<< (j * 32))
  (state &&& mask) ||| ((col.zeroExtend 128) <<< (j * 32))

/-- ShiftRows: rotate each row of the 4×4 byte matrix.
    Row 0: no shift, Row 1: left 1, Row 2: left 2, Row 3: left 3.
    The state is in column-major order. -/
def aesShiftRows (state : BitVec 128) : BitVec 128 :=
  let get (row col : Nat) := getByte128 state (col * 4 + row)
  let set' (s : BitVec 128) (row col : Nat) (b : BitVec 8) :=
    setByte128 s (col * 4 + row) b
  -- Row 0: stays, Row i: shift left by i
  let s := (0 : BitVec 128)
  let s := (List.range 4).foldl (fun s col => set' s 0 col (get 0 col)) s
  let s := (List.range 4).foldl (fun s col => set' s 1 col (get 1 ((col + 1) % 4))) s
  let s := (List.range 4).foldl (fun s col => set' s 2 col (get 2 ((col + 2) % 4))) s
  (List.range 4).foldl (fun s col => set' s 3 col (get 3 ((col + 3) % 4))) s

/-- Inverse ShiftRows. -/
def aesInvShiftRows (state : BitVec 128) : BitVec 128 :=
  let get (row col : Nat) := getByte128 state (col * 4 + row)
  let set' (s : BitVec 128) (row col : Nat) (b : BitVec 8) :=
    setByte128 s (col * 4 + row) b
  let s := (0 : BitVec 128)
  let s := (List.range 4).foldl (fun s col => set' s 0 col (get 0 col)) s
  let s := (List.range 4).foldl (fun s col => set' s 1 col (get 1 ((col + 3) % 4))) s
  let s := (List.range 4).foldl (fun s col => set' s 2 col (get 2 ((col + 2) % 4))) s
  (List.range 4).foldl (fun s col => set' s 3 col (get 3 ((col + 1) % 4))) s

/-! ## GF(2^8) Arithmetic for MixColumns -/

/-- Multiply by x (i.e., by 2) in GF(2^8) with irreducible polynomial x^8+x^4+x^3+x+1. -/
def gf256Xtime (b : BitVec 8) : BitVec 8 :=
  let shifted := b <<< 1
  if b &&& 0x80 != 0 then shifted ^^^ 0x1B else shifted

/-- Multiply two bytes in GF(2^8). -/
def gf256Mul (a b : BitVec 8) : BitVec 8 :=
  let b0 := if b &&& 0x01 != 0 then a else 0
  let b1 := if b &&& 0x02 != 0 then gf256Xtime a else 0
  let b2 := if b &&& 0x04 != 0 then gf256Xtime (gf256Xtime a) else 0
  let b3 := if b &&& 0x08 != 0 then gf256Xtime (gf256Xtime (gf256Xtime a)) else 0
  b0 ^^^ b1 ^^^ b2 ^^^ b3

/-- MixColumns: multiply each column by the MDS matrix in GF(2^8).
    Matrix: [[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]] -/
def aesMixColumns (state : BitVec 128) : BitVec 128 :=
  (List.range 4).foldl (fun result j =>
    let b0 := getByte128 state (j * 4 + 0)
    let b1 := getByte128 state (j * 4 + 1)
    let b2 := getByte128 state (j * 4 + 2)
    let b3 := getByte128 state (j * 4 + 3)
    let r0 := gf256Mul b0 2 ^^^ gf256Mul b1 3 ^^^ b2 ^^^ b3
    let r1 := b0 ^^^ gf256Mul b1 2 ^^^ gf256Mul b2 3 ^^^ b3
    let r2 := b0 ^^^ b1 ^^^ gf256Mul b2 2 ^^^ gf256Mul b3 3
    let r3 := gf256Mul b0 3 ^^^ b1 ^^^ b2 ^^^ gf256Mul b3 2
    let result := setByte128 result (j * 4 + 0) r0
    let result := setByte128 result (j * 4 + 1) r1
    let result := setByte128 result (j * 4 + 2) r2
    setByte128 result (j * 4 + 3) r3
  ) 0

/-- Inverse MixColumns: multiply by the inverse MDS matrix. -/
def aesInvMixColumns (state : BitVec 128) : BitVec 128 :=
  (List.range 4).foldl (fun result j =>
    let b0 := getByte128 state (j * 4 + 0)
    let b1 := getByte128 state (j * 4 + 1)
    let b2 := getByte128 state (j * 4 + 2)
    let b3 := getByte128 state (j * 4 + 3)
    let r0 := gf256Mul b0 14 ^^^ gf256Mul b1 11 ^^^ gf256Mul b2 13 ^^^ gf256Mul b3 9
    let r1 := gf256Mul b0 9  ^^^ gf256Mul b1 14 ^^^ gf256Mul b2 11 ^^^ gf256Mul b3 13
    let r2 := gf256Mul b0 13 ^^^ gf256Mul b1 9  ^^^ gf256Mul b2 14 ^^^ gf256Mul b3 11
    let r3 := gf256Mul b0 11 ^^^ gf256Mul b1 13 ^^^ gf256Mul b2 9  ^^^ gf256Mul b3 14
    let result := setByte128 result (j * 4 + 0) r0
    let result := setByte128 result (j * 4 + 1) r1
    let result := setByte128 result (j * 4 + 2) r2
    setByte128 result (j * 4 + 3) r3
  ) 0

/-! ## AES Round Instructions -/

/-- AESENC: one AES encryption round.
    `AESENC state key = MixColumns(ShiftRows(SubBytes(state))) ⊕ key` -/
def wAESENC (state key : BitVec 128) : BitVec 128 :=
  aesMixColumns (aesShiftRows (aesSubBytes state)) ^^^ key

/-- AESENCLAST: final AES encryption round (no MixColumns).
    `AESENCLAST state key = ShiftRows(SubBytes(state)) ⊕ key` -/
def wAESENCLAST (state key : BitVec 128) : BitVec 128 :=
  aesShiftRows (aesSubBytes state) ^^^ key

/-- AESDEC: one AES decryption round (FIPS 197 Section 5.3, direct inverse cipher).
    `AESDEC state key = InvMixColumns(InvShiftRows(InvSubBytes(state)) ⊕ key)` -/
def wAESDEC (state key : BitVec 128) : BitVec 128 :=
  aesInvMixColumns (aesInvShiftRows (aesInvSubBytes state) ^^^ key)

/-- AESDECLAST: final AES decryption round (no InvMixColumns). -/
def wAESDECLAST (state key : BitVec 128) : BitVec 128 :=
  aesInvShiftRows (aesInvSubBytes state) ^^^ key

/-- AESIMC: InverseMixColumns (for equivalent decryption key schedule). -/
def wAESIMC (state : BitVec 128) : BitVec 128 :=
  aesInvMixColumns state

/-! ## AES Key Generation -/

/-- RotWord: rotate a 32-bit word left by one byte. -/
def rotWord (w : BitVec 32) : BitVec 32 :=
  (w <<< 8) ||| (w >>> 24)

/-- SubWord: apply S-Box to each byte of a 32-bit word. -/
def subWord (w : BitVec 32) : BitVec 32 :=
  let b0 := aesSBox ((w >>> 0).truncate 8)
  let b1 := aesSBox ((w >>> 8).truncate 8)
  let b2 := aesSBox ((w >>> 16).truncate 8)
  let b3 := aesSBox ((w >>> 24).truncate 8)
  (b3.zeroExtend 32 <<< 24) ||| (b2.zeroExtend 32 <<< 16) |||
  (b1.zeroExtend 32 <<< 8)  ||| b0.zeroExtend 32

/-- VAESKEYGENASSIST: key generation assist.
    Applies SubWord and RotWord to the high dword, XORs with rcon. -/
def wAESKEYGENASSIST (src : BitVec 128) (rcon : BitVec 8) : BitVec 128 :=
  let w1 := getCol128 src 1
  let w3 := getCol128 src 3
  let x1 := subWord w1
  let x3 := subWord w3
  let r3 := rotWord x3 ^^^ (rcon.zeroExtend 32)
  setCol128 (setCol128 (setCol128 (setCol128 0 0 x1) 1 r3) 2 x1) 3 r3

/-! ## Bitwise SIMD Operations -/

/-- VPXOR: bitwise XOR of two 128-bit values. -/
def wVPXOR (a b : BitVec 128) : BitVec 128 := a ^^^ b

/-- VPAND: bitwise AND. -/
def wVPAND (a b : BitVec 128) : BitVec 128 := a &&& b

/-- VPOR: bitwise OR. -/
def wVPOR (a b : BitVec 128) : BitVec 128 := a ||| b

/-- VPANDN: bitwise AND-NOT (a AND (NOT b)). -/
def wVPANDN (a b : BitVec 128) : BitVec 128 := (~~~a) &&& b

/-! ## Shuffle Operations -/

/-- VPSHUFD: shuffle 32-bit dwords according to immediate control byte. -/
def wVPSHUFD (src : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  let sel (i : Nat) := (imm >>> (i * 2)).truncate 2 |>.toNat
  let d0 := getCol128 src (sel 0)
  let d1 := getCol128 src (sel 1)
  let d2 := getCol128 src (sel 2)
  let d3 := getCol128 src (sel 3)
  setCol128 (setCol128 (setCol128 (setCol128 0 0 d0) 1 d1) 2 d2) 3 d3

/-- VPSLLDQ: shift left by `n` bytes (with zero fill). -/
def wVPSLLDQ (src : BitVec 128) (n : Nat) : BitVec 128 :=
  src <<< (n * 8)

/-- VPSRLDQ: shift right by `n` bytes (with zero fill). -/
def wVPSRLDQ (src : BitVec 128) (n : Nat) : BitVec 128 :=
  src >>> (n * 8)

/-! ## Data Movement -/

/-- VMOVDQU: move unaligned (identity for our model). -/
def wVMOVDQU (src : BitVec 128) : BitVec 128 := src

/-! ## Operation Dispatch -/

/-- Result of executing an assembly operation.
    Returns a list of typed values (multiple outputs for flag-producing ops). -/
inductive OpResult where
  | ok (vals : List TypedValue) : OpResult
  | unsupported (name : String) : OpResult
  deriving Inhabited

/-- Known AES x86 operation names. -/
def aesOps : List String :=
  ["AESENC", "AESENCLAST", "AESDEC", "AESDECLAST", "AESIMC",
   "VAESKEYGENASSIST",
   "VPXOR", "VPAND", "VPOR", "VPANDN",
   "VPSHUFD", "VPSLLDQ", "VPSRLDQ", "VMOVDQU"]

/-- Execute a known assembly operation on typed value arguments. -/
def execSopn (op : AsmOp) (args : List TypedValue) : OpResult :=
  match op.name, args with
  -- AES round operations (2 args → 1 result)
  | "AESENC", [⟨.sword .U128, a⟩, ⟨.sword .U128, b⟩] =>
    .ok [⟨.sword .U128, wAESENC a b⟩]
  | "AESENCLAST", [⟨.sword .U128, a⟩, ⟨.sword .U128, b⟩] =>
    .ok [⟨.sword .U128, wAESENCLAST a b⟩]
  | "AESDEC", [⟨.sword .U128, a⟩, ⟨.sword .U128, b⟩] =>
    .ok [⟨.sword .U128, wAESDEC a b⟩]
  | "AESDECLAST", [⟨.sword .U128, a⟩, ⟨.sword .U128, b⟩] =>
    .ok [⟨.sword .U128, wAESDECLAST a b⟩]
  -- AESIMC (1 arg → 1 result)
  | "AESIMC", [⟨.sword .U128, a⟩] =>
    .ok [⟨.sword .U128, wAESIMC a⟩]
  -- VAESKEYGENASSIST (2 args: 128-bit src + 8-bit imm → 1 result)
  | "VAESKEYGENASSIST", [⟨.sword .U128, src⟩, ⟨.sword .U8, rcon⟩] =>
    .ok [⟨.sword .U128, wAESKEYGENASSIST src rcon⟩]
  -- Bitwise (2 args → 1 result)
  | "VPXOR", [⟨.sword .U128, a⟩, ⟨.sword .U128, b⟩] =>
    .ok [⟨.sword .U128, wVPXOR a b⟩]
  | "VPAND", [⟨.sword .U128, a⟩, ⟨.sword .U128, b⟩] =>
    .ok [⟨.sword .U128, wVPAND a b⟩]
  | "VPOR", [⟨.sword .U128, a⟩, ⟨.sword .U128, b⟩] =>
    .ok [⟨.sword .U128, wVPOR a b⟩]
  | "VPANDN", [⟨.sword .U128, a⟩, ⟨.sword .U128, b⟩] =>
    .ok [⟨.sword .U128, wVPANDN a b⟩]
  -- Shuffle
  | "VPSHUFD", [⟨.sword .U128, src⟩, ⟨.sword .U8, imm⟩] =>
    .ok [⟨.sword .U128, wVPSHUFD src imm⟩]
  -- Shift (128-bit src + byte count as immediate)
  | "VPSLLDQ", [⟨.sword .U128, src⟩, ⟨.sword .U8, n⟩] =>
    .ok [⟨.sword .U128, wVPSLLDQ src n.toNat⟩]
  | "VPSRLDQ", [⟨.sword .U128, src⟩, ⟨.sword .U8, n⟩] =>
    .ok [⟨.sword .U128, wVPSRLDQ src n.toNat⟩]
  -- Move
  | "VMOVDQU", [⟨.sword .U128, src⟩] =>
    .ok [⟨.sword .U128, wVMOVDQU src⟩]
  -- Unsupported
  | name, _ => .unsupported name

/-! ## AES Round-Trip Cancellation Proofs

These theorems prove the algebraic cancellation properties of AES round operations.
Proofs use three techniques:
- **bv_decide**: SAT solving for byte-level extraction and permutation identities
- **native_decide**: Exhaustive evaluation over all 256 byte values
- **GF(2)-linearity**: Decomposition into single-byte inputs via distributivity of gf256Mul -/

private theorem range_16' : List.range 16 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] := by
  native_decide
private theorem range_4' : List.range 4 = [0,1,2,3] := by native_decide

-- Byte extraction through SubBytes
set_option maxHeartbeats 4000000 in
private theorem getByte128_aesSubBytes (state : BitVec 128) (j : Nat) (hj : j < 16) :
    getByte128 (aesSubBytes state) j = aesSBox (getByte128 state j) := by
  unfold aesSubBytes; rw [range_16']
  simp only [List.foldl_cons, List.foldl_nil]
  interval_cases j <;> simp only [getByte128, setByte128, aesSBox] <;> bv_decide

-- Byte extraction through InvSubBytes
set_option maxHeartbeats 4000000 in
private theorem getByte128_aesInvSubBytes (state : BitVec 128) (j : Nat) (hj : j < 16) :
    getByte128 (aesInvSubBytes state) j = aesInvSBox (getByte128 state j) := by
  unfold aesInvSubBytes; rw [range_16']
  simp only [List.foldl_cons, List.foldl_nil]
  interval_cases j <;> simp only [getByte128, setByte128, aesInvSBox] <;> bv_decide

-- State reconstruction from bytes
set_option maxHeartbeats 4000000 in
private theorem state_from_bytes (s : BitVec 128) :
    (List.range 16).foldl (fun acc i => setByte128 acc i (getByte128 s i)) 0 = s := by
  rw [range_16']; simp only [List.foldl_cons, List.foldl_nil, getByte128, setByte128]; bv_decide

-- Foldl congr for setByte128
private theorem foldl_setByte_congr (f g : Nat → BitVec 8) (l : List Nat) (init : BitVec 128)
    (h : ∀ i ∈ l, f i = g i) :
    l.foldl (fun s i => setByte128 s i (f i)) init =
    l.foldl (fun s i => setByte128 s i (g i)) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    rw [h a (List.mem_cons_self ..)]
    exact ih _ (fun i hi => h i (List.mem_cons_of_mem a hi))

set_option maxHeartbeats 4000000 in
/-- InvSubBytes cancels SubBytes (S-Box involution applied per byte). -/
theorem aesInvSubBytes_aesSubBytes (state : BitVec 128) :
    aesInvSubBytes (aesSubBytes state) = state := by
  show (List.range 16).foldl
    (fun s i => setByte128 s i (aesInvSBox (getByte128 (aesSubBytes state) i))) 0 = state
  have key : ∀ i ∈ List.range 16,
      aesInvSBox (getByte128 (aesSubBytes state) i) = getByte128 state i := by
    intro i hi; rw [List.mem_range] at hi
    rw [getByte128_aesSubBytes state i hi, aesInvSBox_aesSBox]
  rw [foldl_setByte_congr _ _ _ _ key, state_from_bytes]

set_option maxHeartbeats 8000000 in
/-- InvShiftRows cancels ShiftRows (inverse byte permutation). -/
theorem aesInvShiftRows_aesShiftRows (state : BitVec 128) :
    aesInvShiftRows (aesShiftRows state) = state := by
  unfold aesInvShiftRows aesShiftRows
  rw [range_4']; simp only [List.foldl_cons, List.foldl_nil, getByte128, setByte128]
  bv_decide

/-! ### InvMixColumns cancels MixColumns

The proof uses GF(2)-linearity of the column operations. Since `gf256Mul` distributes
over XOR, the composition InvMixCol ∘ MixCol is GF(2)-linear on each 32-bit column.
We verify the identity on all 256 values of each byte position via `native_decide`,
then use linearity to extend to arbitrary 4-byte inputs. -/

-- Per-column MixColumns forward transform
private def mixColRow (b0 b1 b2 b3 : BitVec 8) (k : Fin 4) : BitVec 8 :=
  match k with
  | 0 => gf256Mul b0 2 ^^^ gf256Mul b1 3 ^^^ b2 ^^^ b3
  | 1 => b0 ^^^ gf256Mul b1 2 ^^^ gf256Mul b2 3 ^^^ b3
  | 2 => b0 ^^^ b1 ^^^ gf256Mul b2 2 ^^^ gf256Mul b3 3
  | 3 => gf256Mul b0 3 ^^^ b1 ^^^ b2 ^^^ gf256Mul b3 2

-- Per-column InvMixColumns transform
private def invMixColRow (r0 r1 r2 r3 : BitVec 8) (k : Fin 4) : BitVec 8 :=
  match k with
  | 0 => gf256Mul r0 14 ^^^ gf256Mul r1 11 ^^^ gf256Mul r2 13 ^^^ gf256Mul r3 9
  | 1 => gf256Mul r0 9  ^^^ gf256Mul r1 14 ^^^ gf256Mul r2 11 ^^^ gf256Mul r3 13
  | 2 => gf256Mul r0 13 ^^^ gf256Mul r1 9  ^^^ gf256Mul r2 14 ^^^ gf256Mul r3 11
  | 3 => gf256Mul r0 11 ^^^ gf256Mul r1 13 ^^^ gf256Mul r2 9  ^^^ gf256Mul r3 14

-- Per-column composition: byte k of InvMixCol(MixCol(b0,b1,b2,b3))
private def invMixMix_byte (b0 b1 b2 b3 : BitVec 8) (k : Fin 4) : BitVec 8 :=
  invMixColRow (mixColRow b0 b1 b2 b3 0) (mixColRow b0 b1 b2 b3 1)
               (mixColRow b0 b1 b2 b3 2) (mixColRow b0 b1 b2 b3 3) k

-- XOR left commutativity (not in Lean 4.28.0 stdlib)
private theorem BitVec.xor_left_comm' {w : Nat} (a b c : BitVec w) :
    a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

-- GF(2)-linearity of gf256Mul
set_option maxHeartbeats 8000000 in
private theorem gf256Mul_xor_left' (a b c : BitVec 8) :
    gf256Mul (a ^^^ b) c = gf256Mul a c ^^^ gf256Mul b c := by
  unfold gf256Mul gf256Xtime; bv_decide

-- Inner linearity (MixColumns)
set_option maxHeartbeats 8000000 in
private theorem mixColRow_xor (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 8) (k : Fin 4) :
    mixColRow (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3) k =
    mixColRow a0 a1 a2 a3 k ^^^ mixColRow b0 b1 b2 b3 k := by
  simp only [mixColRow, gf256Mul_xor_left']
  fin_cases k <;> simp only [BitVec.xor_assoc, BitVec.xor_comm, BitVec.xor_left_comm']

-- Outer linearity (InvMixColumns)
set_option maxHeartbeats 8000000 in
private theorem invMixColRow_xor (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 8) (k : Fin 4) :
    invMixColRow (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3) k =
    invMixColRow a0 a1 a2 a3 k ^^^ invMixColRow b0 b1 b2 b3 k := by
  simp only [invMixColRow, gf256Mul_xor_left']
  fin_cases k <;> simp only [BitVec.xor_assoc, BitVec.xor_left_comm']

-- Composed linearity
set_option maxHeartbeats 8000000 in
private theorem invMixMix_byte_xor (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 8) (k : Fin 4) :
    invMixMix_byte (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3) k =
    invMixMix_byte a0 a1 a2 a3 k ^^^ invMixMix_byte b0 b1 b2 b3 k := by
  simp only [invMixMix_byte, mixColRow_xor, invMixColRow_xor]

-- Basis checks: invMixMix is identity when only one byte is nonzero
private theorem invMixMix_b0_k0 : ∀ v : BitVec 8, invMixMix_byte v 0 0 0 0 = v := by native_decide
private theorem invMixMix_b0_k1 : ∀ v : BitVec 8, invMixMix_byte v 0 0 0 1 = 0 := by native_decide
private theorem invMixMix_b0_k2 : ∀ v : BitVec 8, invMixMix_byte v 0 0 0 2 = 0 := by native_decide
private theorem invMixMix_b0_k3 : ∀ v : BitVec 8, invMixMix_byte v 0 0 0 3 = 0 := by native_decide
private theorem invMixMix_b1_k0 : ∀ v : BitVec 8, invMixMix_byte 0 v 0 0 0 = 0 := by native_decide
private theorem invMixMix_b1_k1 : ∀ v : BitVec 8, invMixMix_byte 0 v 0 0 1 = v := by native_decide
private theorem invMixMix_b1_k2 : ∀ v : BitVec 8, invMixMix_byte 0 v 0 0 2 = 0 := by native_decide
private theorem invMixMix_b1_k3 : ∀ v : BitVec 8, invMixMix_byte 0 v 0 0 3 = 0 := by native_decide
private theorem invMixMix_b2_k0 : ∀ v : BitVec 8, invMixMix_byte 0 0 v 0 0 = 0 := by native_decide
private theorem invMixMix_b2_k1 : ∀ v : BitVec 8, invMixMix_byte 0 0 v 0 1 = 0 := by native_decide
private theorem invMixMix_b2_k2 : ∀ v : BitVec 8, invMixMix_byte 0 0 v 0 2 = v := by native_decide
private theorem invMixMix_b2_k3 : ∀ v : BitVec 8, invMixMix_byte 0 0 v 0 3 = 0 := by native_decide
private theorem invMixMix_b3_k0 : ∀ v : BitVec 8, invMixMix_byte 0 0 0 v 0 = 0 := by native_decide
private theorem invMixMix_b3_k1 : ∀ v : BitVec 8, invMixMix_byte 0 0 0 v 1 = 0 := by native_decide
private theorem invMixMix_b3_k2 : ∀ v : BitVec 8, invMixMix_byte 0 0 0 v 2 = 0 := by native_decide
private theorem invMixMix_b3_k3 : ∀ v : BitVec 8, invMixMix_byte 0 0 0 v 3 = v := by native_decide

-- XOR with zero helpers (OfNat form, avoids ofNat_eq_ofNat leaking into rw targets)
private theorem bv8_xor_zero (a : BitVec 8) : a ^^^ (0 : BitVec 8) = a := by
  simp [BitVec.ofNat_eq_ofNat, BitVec.xor_zero]
private theorem bv8_zero_xor (a : BitVec 8) : (0 : BitVec 8) ^^^ a = a := by
  simp [BitVec.ofNat_eq_ofNat, BitVec.zero_xor]

-- Decompose any 4-byte input using linearity
private theorem invMixMix_byte_decompose (b0 b1 b2 b3 : BitVec 8) (k : Fin 4) :
    invMixMix_byte b0 b1 b2 b3 k =
    invMixMix_byte b0 0 0 0 k ^^^ invMixMix_byte 0 b1 0 0 k ^^^
    invMixMix_byte 0 0 b2 0 k ^^^ invMixMix_byte 0 0 0 b3 k := by
  have h1 : invMixMix_byte b0 b1 b2 b3 k =
      invMixMix_byte b0 0 0 0 k ^^^ invMixMix_byte 0 b1 b2 b3 k := by
    have := invMixMix_byte_xor b0 0 0 0 0 b1 b2 b3 k
    simp only [bv8_xor_zero, bv8_zero_xor] at this; exact this
  have h2 : invMixMix_byte 0 b1 b2 b3 k =
      invMixMix_byte 0 b1 0 0 k ^^^ invMixMix_byte 0 0 b2 b3 k := by
    have := invMixMix_byte_xor 0 b1 0 0 0 0 b2 b3 k
    simp only [bv8_xor_zero, bv8_zero_xor] at this; exact this
  have h3 : invMixMix_byte 0 0 b2 b3 k =
      invMixMix_byte 0 0 b2 0 k ^^^ invMixMix_byte 0 0 0 b3 k := by
    have := invMixMix_byte_xor 0 0 b2 0 0 0 0 b3 k
    simp only [bv8_xor_zero, bv8_zero_xor] at this; exact this
  rw [h1, h2, h3]; simp only [BitVec.xor_assoc]

-- Per-k identity lemmas (k fixed at statement level avoids Fin matching issues)
private theorem invMixMix_byte_id_0 (b0 b1 b2 b3 : BitVec 8) :
    invMixMix_byte b0 b1 b2 b3 0 = b0 := by
  rw [invMixMix_byte_decompose]
  simp only [invMixMix_b0_k0, invMixMix_b1_k0, invMixMix_b2_k0, invMixMix_b3_k0, bv8_xor_zero]

private theorem invMixMix_byte_id_1 (b0 b1 b2 b3 : BitVec 8) :
    invMixMix_byte b0 b1 b2 b3 1 = b1 := by
  rw [invMixMix_byte_decompose]
  simp only [invMixMix_b0_k1, invMixMix_b1_k1, invMixMix_b2_k1, invMixMix_b3_k1,
             bv8_xor_zero, bv8_zero_xor]

private theorem invMixMix_byte_id_2 (b0 b1 b2 b3 : BitVec 8) :
    invMixMix_byte b0 b1 b2 b3 2 = b2 := by
  rw [invMixMix_byte_decompose]
  simp only [invMixMix_b0_k2, invMixMix_b1_k2, invMixMix_b2_k2, invMixMix_b3_k2,
             bv8_xor_zero, bv8_zero_xor]

private theorem invMixMix_byte_id_3 (b0 b1 b2 b3 : BitVec 8) :
    invMixMix_byte b0 b1 b2 b3 3 = b3 := by
  rw [invMixMix_byte_decompose]
  simp only [invMixMix_b0_k3, invMixMix_b1_k3, invMixMix_b2_k3, invMixMix_b3_k3,
             bv8_xor_zero, bv8_zero_xor]

-- Combined per-column identity
private theorem invMixMix_byte_id (b0 b1 b2 b3 : BitVec 8) (k : Fin 4) :
    invMixMix_byte b0 b1 b2 b3 k =
    match k with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 :=
  match k with
  | 0 => invMixMix_byte_id_0 b0 b1 b2 b3
  | 1 => invMixMix_byte_id_1 b0 b1 b2 b3
  | 2 => invMixMix_byte_id_2 b0 b1 b2 b3
  | 3 => invMixMix_byte_id_3 b0 b1 b2 b3

-- Byte extraction through MixColumns (Nat-indexed, explicit +0 for rw matching)
set_option maxHeartbeats 8000000 in
private theorem getByte128_aesMixColumns (state : BitVec 128)
    (col row : Nat) (hcol : col < 4) (hrow : row < 4) :
    getByte128 (aesMixColumns state) (col * 4 + row) =
    mixColRow (getByte128 state (col * 4 + 0)) (getByte128 state (col * 4 + 1))
              (getByte128 state (col * 4 + 2)) (getByte128 state (col * 4 + 3)) ⟨row, hrow⟩ := by
  unfold aesMixColumns; rw [range_4']
  simp only [List.foldl_cons, List.foldl_nil]
  interval_cases col <;> interval_cases row <;>
    simp only [getByte128, setByte128, mixColRow, gf256Mul] <;> bv_decide

-- Byte extraction through InvMixColumns (Nat-indexed, explicit +0)
set_option maxHeartbeats 8000000 in
private theorem getByte128_aesInvMixColumns (state : BitVec 128)
    (col row : Nat) (hcol : col < 4) (hrow : row < 4) :
    getByte128 (aesInvMixColumns state) (col * 4 + row) =
    invMixColRow (getByte128 state (col * 4 + 0)) (getByte128 state (col * 4 + 1))
                 (getByte128 state (col * 4 + 2)) (getByte128 state (col * 4 + 3)) ⟨row, hrow⟩ := by
  unfold aesInvMixColumns; rw [range_4']
  simp only [List.foldl_cons, List.foldl_nil]
  interval_cases col <;> interval_cases row <;>
    simp only [getByte128, setByte128, invMixColRow, gf256Mul] <;> bv_decide

-- Bridge: compose extraction lemmas to get invMixMix_byte
private theorem getByte128_composed (state : BitVec 128)
    (col row : Nat) (hcol : col < 4) (hrow : row < 4) :
    getByte128 (aesInvMixColumns (aesMixColumns state)) (col * 4 + row) =
    invMixMix_byte (getByte128 state (col * 4 + 0)) (getByte128 state (col * 4 + 1))
                   (getByte128 state (col * 4 + 2)) (getByte128 state (col * 4 + 3))
                   ⟨row, hrow⟩ := by
  rw [getByte128_aesInvMixColumns (aesMixColumns state) col row hcol hrow,
      getByte128_aesMixColumns state col 0 hcol (by omega),
      getByte128_aesMixColumns state col 1 hcol (by omega),
      getByte128_aesMixColumns state col 2 hcol (by omega),
      getByte128_aesMixColumns state col 3 hcol (by omega)]
  rfl

-- Per-byte identity via composition + linearity
private theorem key_byte (state : BitVec 128) (i : Nat) (hi : i < 16) :
    getByte128 (aesInvMixColumns (aesMixColumns state)) i = getByte128 state i := by
  have hcol : i / 4 < 4 := by omega
  have hrow : i % 4 < 4 := Nat.mod_lt i (by omega)
  have hi_eq : i / 4 * 4 + i % 4 = i := by omega
  rw [show i = i / 4 * 4 + i % 4 from hi_eq.symm,
      getByte128_composed state (i / 4) (i % 4) hcol hrow,
      invMixMix_byte_id]
  interval_cases i <;> rfl

set_option maxHeartbeats 8000000 in
/-- InvMixColumns cancels MixColumns (M_inv · M = I over GF(2^8)).
Proved via GF(2)-linearity + exhaustive byte evaluation. -/
theorem aesInvMixColumns_aesMixColumns (state : BitVec 128) :
    aesInvMixColumns (aesMixColumns state) = state := by
  have key : ∀ i ∈ List.range 16,
      getByte128 (aesInvMixColumns (aesMixColumns state)) i = getByte128 state i := by
    intro i hi; rw [List.mem_range] at hi; exact key_byte state i hi
  calc aesInvMixColumns (aesMixColumns state)
      _ = (List.range 16).foldl (fun acc i =>
            setByte128 acc i (getByte128 (aesInvMixColumns (aesMixColumns state)) i)) 0 :=
          (state_from_bytes _).symm
      _ = (List.range 16).foldl (fun acc i =>
            setByte128 acc i (getByte128 state i)) 0 :=
          foldl_setByte_congr _ _ _ _ key
      _ = state := state_from_bytes _

/-! ### InvSubBytes and ShiftRows commute -/

-- ShiftRows permutation: output byte j comes from input byte (shiftRowsPerm j)
private def shiftRowsPerm : Nat → Nat
  | 0 => 0 | 1 => 5 | 2 => 10 | 3 => 15
  | 4 => 4 | 5 => 9 | 6 => 14 | 7 => 3
  | 8 => 8 | 9 => 13 | 10 => 2 | 11 => 7
  | 12 => 12 | 13 => 1 | 14 => 6 | 15 => 11
  | _ => 0

private theorem shiftRowsPerm_lt (j : Nat) (hj : j < 16) : shiftRowsPerm j < 16 := by
  interval_cases j <;> simp [shiftRowsPerm]

set_option maxHeartbeats 8000000 in
private theorem getByte128_aesShiftRows_perm (state : BitVec 128) (j : Nat) (hj : j < 16) :
    getByte128 (aesShiftRows state) j = getByte128 state (shiftRowsPerm j) := by
  unfold aesShiftRows; rw [range_4']
  simp only [List.foldl_cons, List.foldl_nil]
  interval_cases j <;> simp only [getByte128, setByte128, shiftRowsPerm] <;> bv_decide

set_option maxHeartbeats 8000000 in
/-- InvSubBytes and ShiftRows commute (per-byte transform vs byte permutation).
Proved by showing both sides have the same byte at each position. -/
theorem aesInvSubBytes_aesShiftRows_comm (state : BitVec 128) :
    aesInvSubBytes (aesShiftRows state) = aesShiftRows (aesInvSubBytes state) := by
  calc aesInvSubBytes (aesShiftRows state)
      _ = (List.range 16).foldl (fun acc i =>
            setByte128 acc i (getByte128 (aesInvSubBytes (aesShiftRows state)) i)) 0 :=
          (state_from_bytes _).symm
      _ = (List.range 16).foldl (fun acc i =>
            setByte128 acc i (getByte128 (aesShiftRows (aesInvSubBytes state)) i)) 0 := by
          apply foldl_setByte_congr; intro i hi; rw [List.mem_range] at hi
          rw [getByte128_aesInvSubBytes _ i hi, getByte128_aesShiftRows_perm _ i hi,
              getByte128_aesShiftRows_perm _ i hi,
              getByte128_aesInvSubBytes _ _ (shiftRowsPerm_lt i hi)]
      _ = aesShiftRows (aesInvSubBytes state) := state_from_bytes _

/-- Composition identity: ISR(ISB(SR(SB(x)))) = x. -/
theorem aesInvShiftRows_aesInvSubBytes_aesShiftRows_aesSubBytes (state : BitVec 128) :
    aesInvShiftRows (aesInvSubBytes (aesShiftRows (aesSubBytes state))) = state := by
  rw [aesInvSubBytes_aesShiftRows_comm, aesInvShiftRows_aesShiftRows,
    aesInvSubBytes_aesSubBytes]

end

end CatCrypt.Crypto.Jasmin
