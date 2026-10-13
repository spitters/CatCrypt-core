/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Option

/-!
# CType: Closed Crypto Type Universe

A closed type universe mapping hax-extracted Rust types to concrete Lean types.
Eliminates per-protocol boilerplate for `Fintype`, `DecidableEq`, `Nonempty`,
and `Inhabited` instances that are currently duplicated across 19+ HaxBridge files.

## Main definitions

* `CType` — closed universe of crypto-relevant types
* `CType.denote` — interpretation function `CType → Type`
* `CType.instFintype` — `Fintype τ.denote` for all `τ : CType`
* `CType.instDecidableEq` — `DecidableEq τ.denote` for all `τ : CType`
* `CType.instInhabited` — `Inhabited τ.denote` for all `τ : CType`

## Design

Follows the Aeneas approach: a type universe provides a reflection layer
mapping hax-extracted types to concrete Lean types with all needed instances.
The key application is `CType.array .u8 16`, which denotes to
`Vector UInt8 16 = RustArray u8 16`, the standard hax block type.

## Type correspondences

| CType            | denote            | hax-lib alias      |
|------------------|-------------------|--------------------|
| `.u8`            | `UInt8`           | `u8`               |
| `.u16`           | `UInt16`          | `u16`              |
| `.u32`           | `UInt32`          | `u32`              |
| `.u64`           | `UInt64`          | `u64`              |
| `.u128`          | `BitVec 128`      | `u128`             |
| `.usize`         | `UInt64`          | `usize` (64-bit)   |
| `.array .u8 16`  | `Vector UInt8 16` | `RustArray u8 16`  |
| `.array .u8 32`  | `Vector UInt8 32` | `RustArray u8 32`  |
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax

/-- Closed universe of crypto-relevant types.

    Every type that appears in hax-extracted cryptographic code maps to a
    `CType` constructor. The `denote` function interprets each constructor
    as a concrete Lean type. -/
inductive CType where
  | u8 | u16 | u32 | u64 | u128 | usize
  | bool | unit
  | pair (a b : CType)
  | array (elem : CType) (n : Nat)
  | option (a : CType)
  | result (ok err : CType)
  deriving DecidableEq, Repr, Inhabited

namespace CType

/-! ## Interpretation -/

/-- Interpret a `CType` as a concrete Lean type.

    Integer types map to the corresponding Lean integer types (matching
    the hax `Rust_primitives.Num` abbreviations). Arrays map to `Vector`,
    which equals `RustArray` in hax-lib. -/
@[reducible] def denote : CType → Type
  | .u8 => UInt8
  | .u16 => UInt16
  | .u32 => UInt32
  | .u64 => UInt64
  | .u128 => BitVec 128
  | .usize => UInt64       -- 64-bit target (matching USize64.size)
  | .bool => Bool
  | .unit => Unit
  | .pair a b => a.denote × b.denote
  | .array elem n => Vector elem.denote n
  | .option a => Option a.denote
  | .result ok err => ok.denote ⊕ err.denote

/-! ## Foundational equivalences

These equivs are used to derive `Fintype` and other instances for the
integer types. Each UInt type is isomorphic to its underlying `BitVec`,
which is isomorphic to `Fin (2^w)`. -/

/-- `BitVec n ≃ Fin (2^n)` -/
noncomputable def bitVecEquivFin (n : Nat) : BitVec n ≃ Fin (2 ^ n) where
  toFun := BitVec.toFin
  invFun := BitVec.ofFin
  left_inv := fun x => by simp
  right_inv := fun x => by simp

/-- `UInt8 ≃ BitVec 8` -/
def uint8EquivBitVec : UInt8 ≃ BitVec 8 where
  toFun := UInt8.toBitVec
  invFun := UInt8.ofBitVec
  left_inv := fun u => by cases u; rfl
  right_inv := fun _ => rfl

/-- `UInt16 ≃ BitVec 16` -/
def uint16EquivBitVec : UInt16 ≃ BitVec 16 where
  toFun := UInt16.toBitVec
  invFun := UInt16.ofBitVec
  left_inv := fun u => by cases u; rfl
  right_inv := fun _ => rfl

/-- `UInt32 ≃ BitVec 32` -/
def uint32EquivBitVec : UInt32 ≃ BitVec 32 where
  toFun := UInt32.toBitVec
  invFun := UInt32.ofBitVec
  left_inv := fun u => by cases u; rfl
  right_inv := fun _ => rfl

/-- `UInt64 ≃ BitVec 64` -/
def uint64EquivBitVec : UInt64 ≃ BitVec 64 where
  toFun := UInt64.toBitVec
  invFun := UInt64.ofBitVec
  left_inv := fun u => by cases u; rfl
  right_inv := fun _ => rfl

/-- `Vector α n ≃ (Fin n → α)` via array indexing. -/
noncomputable def vectorEquivFin (α : Type) (n : Nat) : Vector α n ≃ (Fin n → α) where
  toFun v i := v[i]
  invFun f := Vector.ofFn f
  left_inv v := by ext i; simp [Vector.getElem_ofFn]
  right_inv f := by ext i; simp [Vector.getElem_ofFn]

/-! ## Fintype instances -/

noncomputable instance fintypeBitVec (n : Nat) : Fintype (BitVec n) :=
  Fintype.ofEquiv (Fin (2 ^ n)) (bitVecEquivFin n).symm

noncomputable instance fintypeUInt8 : Fintype UInt8 :=
  Fintype.ofEquiv (BitVec 8) uint8EquivBitVec.symm

noncomputable instance fintypeUInt16 : Fintype UInt16 :=
  Fintype.ofEquiv (BitVec 16) uint16EquivBitVec.symm

noncomputable instance fintypeUInt32 : Fintype UInt32 :=
  Fintype.ofEquiv (BitVec 32) uint32EquivBitVec.symm

noncomputable instance fintypeUInt64 : Fintype UInt64 :=
  Fintype.ofEquiv (BitVec 64) uint64EquivBitVec.symm

noncomputable instance fintypeVector (α : Type) [Fintype α] (n : Nat) :
    Fintype (Vector α n) :=
  Fintype.ofEquiv (Fin n → α) (vectorEquivFin α n).symm

/-- `Fintype τ.denote` for any `τ : CType`, by structural recursion. -/
noncomputable def instFintype : (τ : CType) → Fintype τ.denote
  | .u8 => fintypeUInt8
  | .u16 => fintypeUInt16
  | .u32 => fintypeUInt32
  | .u64 => fintypeUInt64
  | .u128 => fintypeBitVec 128
  | .usize => fintypeUInt64
  | .bool => inferInstance
  | .unit => inferInstance
  | .pair a b =>
    haveI : Fintype a.denote := instFintype a
    haveI : Fintype b.denote := instFintype b
    inferInstance
  | .array elem n => @fintypeVector _ (instFintype elem) n
  | .option a =>
    haveI : Fintype a.denote := instFintype a
    inferInstance
  | .result ok err =>
    haveI : Fintype ok.denote := instFintype ok
    haveI : Fintype err.denote := instFintype err
    inferInstance

/-! ## DecidableEq instances -/

/-- `DecidableEq τ.denote` for any `τ : CType`, by structural recursion. -/
def instDecidableEq : (τ : CType) → DecidableEq τ.denote
  | .u8 => inferInstance
  | .u16 => inferInstance
  | .u32 => inferInstance
  | .u64 => inferInstance
  | .u128 => inferInstance
  | .usize => inferInstance
  | .bool => inferInstance
  | .unit => inferInstance
  | .pair a b =>
    haveI : DecidableEq a.denote := instDecidableEq a
    haveI : DecidableEq b.denote := instDecidableEq b
    inferInstance
  | .array elem _n =>
    haveI : DecidableEq elem.denote := instDecidableEq elem
    inferInstance
  | .option a =>
    haveI : DecidableEq a.denote := instDecidableEq a
    inferInstance
  | .result ok err =>
    haveI : DecidableEq ok.denote := instDecidableEq ok
    haveI : DecidableEq err.denote := instDecidableEq err
    inferInstance

/-! ## Inhabited / Nonempty instances -/

/-- `Inhabited τ.denote` for any `τ : CType`, by structural recursion. -/
def instInhabited : (τ : CType) → Inhabited τ.denote
  | .u8 => ⟨0⟩
  | .u16 => ⟨0⟩
  | .u32 => ⟨0⟩
  | .u64 => ⟨0⟩
  | .u128 => ⟨0⟩
  | .usize => ⟨0⟩
  | .bool => ⟨false⟩
  | .unit => ⟨()⟩
  | .pair a b =>
    haveI : Inhabited a.denote := instInhabited a
    haveI : Inhabited b.denote := instInhabited b
    inferInstance
  | .array elem n => ⟨Vector.replicate n (instInhabited elem).default⟩
  | .option _ => ⟨none⟩
  | .result ok _ => ⟨Sum.inl (instInhabited ok).default⟩

/-- `Nonempty τ.denote` for any `τ : CType`. -/
def instNonempty (τ : CType) : Nonempty τ.denote :=
  ⟨(instInhabited τ).default⟩

/-! ## Common crypto types

Abbreviations for frequently-used crypto type patterns, matching
the type aliases found in HaxBridge files. -/

/-- 128-bit block: `Vector UInt8 16` = `RustArray u8 16`. -/
abbrev block128 : CType := .array .u8 16

/-- 256-bit block: `Vector UInt8 32` = `RustArray u8 32`. -/
abbrev block256 : CType := .array .u8 32

/-- 512-bit block: `Vector UInt8 64` = `RustArray u8 64`. -/
abbrev block512 : CType := .array .u8 64

/-- AES-SIV key (32 bytes). -/
abbrev key256 : CType := .array .u8 32

/-! ## Sanity checks -/

example : block128.denote = Vector UInt8 16 := rfl
example : block256.denote = Vector UInt8 32 := rfl
example : (CType.pair .u8 .bool).denote = (UInt8 × Bool) := rfl
example : (CType.option .u64).denote = Option UInt64 := rfl

/-! ## Global instances for common crypto types

Global `Fintype` instances for the fixed-width unsigned integer types and for byte
vectors, derived from `CType.instFintype`. -/

noncomputable instance instGlobalFintypeUInt8 : Fintype UInt8 := instFintype .u8
noncomputable instance instGlobalFintypeUInt16 : Fintype UInt16 := instFintype .u16
noncomputable instance instGlobalFintypeUInt32 : Fintype UInt32 := instFintype .u32

noncomputable instance instGlobalFintypeUInt64 : Fintype UInt64 := instFintype .u64

/-- `Fintype (Vector UInt8 n)` for any `n`, from `CType.instFintype (.array .u8 n)`. -/
noncomputable instance instGlobalFintypeVectorUInt8 (n : Nat) : Fintype (Vector UInt8 n) :=
  instFintype (.array .u8 n)

/-- `Fintype (Vector UInt32 n)` for any `n`. -/
noncomputable instance instGlobalFintypeVectorUInt32 (n : Nat) : Fintype (Vector UInt32 n) :=
  instFintype (.array .u32 n)

/-- `Fintype (Vector UInt64 n)` for any `n`. -/
noncomputable instance instGlobalFintypeVectorUInt64 (n : Nat) : Fintype (Vector UInt64 n) :=
  instFintype (.array .u64 n)

/-- `Nonempty (Vector UInt8 n)` for any `n`. -/
instance instGlobalNonemptyVectorUInt8 (n : Nat) : Nonempty (Vector UInt8 n) :=
  instNonempty (.array .u8 n)

/-- `Nonempty (Vector UInt32 n)` for any `n`. -/
instance instGlobalNonemptyVectorUInt32 (n : Nat) : Nonempty (Vector UInt32 n) :=
  instNonempty (.array .u32 n)

/-- `Nonempty (Vector UInt64 n)` for any `n`. -/
instance instGlobalNonemptyVectorUInt64 (n : Nat) : Nonempty (Vector UInt64 n) :=
  instNonempty (.array .u64 n)

/-- `Nonempty UInt32`. -/
instance instGlobalNonemptyUInt32 : Nonempty UInt32 := instNonempty .u32

/-- `Nonempty UInt64`. -/
instance instGlobalNonemptyUInt64 : Nonempty UInt64 := instNonempty .u64

end CType

end CatCrypt.Hax
