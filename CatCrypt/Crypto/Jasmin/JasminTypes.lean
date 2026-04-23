/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminAST
import CatCrypt.Crypto.CryptoWord
import Mathlib.Data.Fintype.Pi

/-!
# Jasmin Type Encoding

Maps Jasmin types (`SType`) to Lean types that can be stored in CatCrypt locations.
Following the Rocq `encode` function from `jasmin_translate.v`.

## Encoding

| Jasmin type  | Lean type         | Notes                                |
|-------------|-------------------|--------------------------------------|
| `sbool`     | `Bool`            | Boolean values                       |
| `sint`      | `Int`             | Arbitrary-precision integers         |
| `sarr n`    | `JArray n`        | Byte arrays of fixed size            |
| `sword ws`  | `BitVec ws.bits`  | Machine words                        |

## Design decisions

- Arrays are modeled as `Fin n → BitVec 8` (functions from index to byte),
  which provides `Fintype` and `Inhabited` instances automatically.
  The Rocq version uses `chMap Int (word U8)` (finite maps), but functional
  arrays are simpler and sufficient for non-aliasing Jasmin programs.

- `sint` (arbitrary-precision integers) does NOT have `Fintype`. For locations
  that need to store integers, we truncate to a bounded range in practice.
  In the translation, integer expressions are typically used as array indices
  and loop bounds, not stored in heap locations.
-/

namespace CatCrypt.Crypto.Jasmin

/-! ## Byte Arrays -/

/-- Jasmin array: `n` bytes indexed by `Fin n`.
    Models `sarr n` from Jasmin where `n` is the number of bytes. -/
def JArray (n : Nat) := Fin n → BitVec 8

namespace JArray

instance (n : Nat) : Inhabited (JArray n) :=
  ⟨fun _ => 0⟩

noncomputable instance instFintypeJArray (n : Nat) : Fintype (JArray n) := by
  unfold JArray
  haveI : Fintype (BitVec 8) := instFintypeBitVec 8
  exact inferInstance

noncomputable instance (n : Nat) : DecidableEq (JArray n) :=
  Classical.decEq _

/-- Empty array (zero bytes). -/
def empty : JArray 0 := Fin.elim0

/-- Get a byte from the array. -/
def get {n : Nat} (a : JArray n) (i : Fin n) : BitVec 8 := a i

/-- Set a byte in the array. -/
def set {n : Nat} (a : JArray n) (i : Fin n) (v : BitVec 8) : JArray n :=
  Function.update a i v

/-- Get a word of size `ws` starting at byte index `i` (little-endian). -/
noncomputable def getWord {n : Nat} (a : JArray n) (ws : WSize) (i : Nat) : BitVec ws.bits :=
  -- Assemble bytes in little-endian order
  (List.range ws.bytes).foldl (fun (acc : BitVec ws.bits) (j : Nat) =>
    let byte : BitVec 8 := if h : i + j < n then a ⟨i + j, h⟩ else 0
    acc ||| ((byte.zeroExtend ws.bits) <<< (j * 8))
  ) 0

/-- Set a word of size `ws` starting at byte index `i` (little-endian). -/
def setWord {n : Nat} (a : JArray n) (ws : WSize) (i : Nat) (v : BitVec ws.bits) : JArray n :=
  (List.range ws.bytes).foldl (fun arr j =>
    if h : i + j < n then
      arr.set ⟨i + j, h⟩ (v >>> (j * 8) |>.truncate 8)
    else arr
  ) a

end JArray

/-! ## Type Encoding -/

/-- The Lean type corresponding to a Jasmin type.
    This is the `encode` function from the Rocq jasmin branch. -/
@[reducible]
def SType.encode : SType → Type
  | .sbool    => Bool
  | .sint     => Int
  | .sarr n   => JArray n
  | .sword ws => BitVec ws.bits

/-- `Inhabited` instance for encoded types. -/
instance SType.instInhabitedEncode (t : SType) : Inhabited t.encode := by
  cases t <;> simp [SType.encode] <;> infer_instance

/-- `DecidableEq` for encoded types. -/
noncomputable instance SType.instDecidableEqEncode (t : SType) : DecidableEq t.encode := by
  cases t <;> simp [SType.encode] <;> infer_instance

/-! ## Word Operations -/

/-- Truncate a word to a smaller size (keep lower bits). -/
def truncateWord (wsi wso : WSize) (v : BitVec wsi.bits) : BitVec wso.bits :=
  v.truncate wso.bits

/-- Zero-extend a word to a larger size. -/
def zeroExtendWord (wsi wso : WSize) (v : BitVec wsi.bits) : BitVec wso.bits :=
  v.zeroExtend wso.bits

/-- Sign-extend a word to a larger size. -/
def signExtendWord (wsi wso : WSize) (v : BitVec wsi.bits) : BitVec wso.bits :=
  v.signExtend wso.bits

/-! ## Typed Values -/

/-- A dynamically-typed Jasmin value: pairs a type tag with a value. -/
structure TypedValue where
  ty : SType
  val : ty.encode

/-- Create a typed value. -/
def TypedValue.mk' (t : SType) (v : t.encode) : TypedValue := ⟨t, v⟩

/-- Default value for any Jasmin type. -/
def SType.default : (t : SType) → t.encode
  | .sbool    => (false : Bool)
  | .sint     => (0 : Int)
  | .sarr _   => (fun _ => 0 : JArray _)
  | .sword _  => (0 : BitVec _)

/-! ## Conversion Utilities -/

/-- Convert an integer to a word (truncating). -/
def intToWord (ws : WSize) (z : Int) : BitVec ws.bits :=
  BitVec.ofInt ws.bits z

/-- Convert a word to an unsigned integer. -/
def wordToInt (_ws : WSize) (w : BitVec _ws.bits) : Int :=
  (w.toNat : Int)

/-- Coerce a value to a target type (identity if types match, default otherwise). -/
noncomputable def coerceValue (src tgt : SType) (v : src.encode) : tgt.encode :=
  if h : src = tgt then h ▸ v else tgt.default

end CatCrypt.Crypto.Jasmin
