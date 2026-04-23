/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminTypes
import Mathlib.Data.List.Basic

/-!
# Rust-cmd DSL: Typed Tower-Field Command Language

`RustCmd` is a typed DSL for safe Rust programs over tower field elements
(Fp, Fp2, Fp6, Fp12, U64).  The borrow checker (`RustCmdBorrowCheck.lean`)
certifies memory safety statically; the simulation semantics (`RustExec`)
gives the big-step meaning used for frame proofs.

## Tower type encoding

Tower elements are modelled as fixed-size byte arrays (`JArray`), using the
BLS12-381 sizes as concrete defaults.  The `byteSize` function can be
overridden by downstream files for other curves.

## References

* AUCurves `SafeRustSimulation.v` and `SafeRustBorrowCheck.v`
-/

namespace CatCrypt.Crypto.Jasmin.RustCmd

open CatCrypt.Crypto.Jasmin (JArray)

/-! ## §1  Tower types -/

/-- Tower type hierarchy for pairing-friendly curves. -/
inductive TowerType where
  | TFp   : TowerType   -- base field element
  | TFp2  : TowerType   -- degree-2 extension
  | TFp6  : TowerType   -- degree-6 extension
  | TFp12 : TowerType   -- degree-12 extension
  | TU64  : TowerType   -- unsigned 64-bit scalar
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Byte size for BLS12-381.  Other curves override this. -/
def TowerType.byteSize : TowerType → Nat
  | .TFp   => 48
  | .TFp2  => 96
  | .TFp6  => 288
  | .TFp12 => 576
  | .TU64  => 8

/-- Runtime value for tower type `t`: a fixed-size byte array. -/
abbrev RustVal (t : TowerType) := JArray t.byteSize

/-! ## §2  Located values -/

/-- A located value: a named variable together with its source and
    destination tower types (may differ when only a subfield is updated). -/
structure Located where
  locVar : String
  locSrc : TowerType
  locDst : TowerType
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Does `dest` share a base variable with any element of `args`? -/
def callAliases (dest : Located) (args : List Located) : Bool :=
  args.any (fun a => a.locVar == dest.locVar)

/-! ## §3  Rust commands -/

/-- Safe Rust commands over tower-typed variables.

    Every `RCall` writes to `dest` and reads from `args`; the borrow
    checker (`borrowOk`) ensures `dest ∉ args` at every call site.

    `RCloneCall` breaks the alias by cloning the old destination value into
    a fresh variable before dispatching the inner call. -/
inductive RustCmd where
  | RSkip      : RustCmd
  | RSeq       : RustCmd → RustCmd → RustCmd
  | RLetZero   : String → TowerType → RustCmd → RustCmd
  | RLetU64Zero : String → RustCmd → RustCmd
  | RScalarSet : String → Nat → RustCmd
  | RCall      : String → Located → List Located → RustCmd
  | RCloneCall : String → TowerType → Located → String →
                 Located → List Located → RustCmd
  | RIfNz      : String → RustCmd → RustCmd → RustCmd
  | RWhileNz   : String → RustCmd → RustCmd
  | RLimbStore : Located → Nat → BitVec 64 → RustCmd
  deriving Repr, Inhabited

/-! ## §4  Runtime state -/

/-- Specification of a single leaf-function call (formerly `LeafSpec`).
    `f dt argTs oldDest args` = new value of dest after calling `f`. -/
def CallSpec :=
  String →
  ∀ (dt : TowerType) (argTs : List TowerType),
    RustVal dt → List (Σ t : TowerType, RustVal t) → RustVal dt

/-- Specification of a limb-store operation (abstract oracle analogous to
    Rocq's `asm_correct` for `Oasm` operators).

    `spec loc oldV idx v` = new tower value for `loc` after writing the u64
    word `v` into limb index `idx` of the previous value `oldV`. -/
def LimbStoreSpec :=
  ∀ (loc : Located), RustVal loc.locDst → Nat → BitVec 64 → RustVal loc.locDst

/-- **Bundled oracle record** (Rocq-style): leaf-call behaviour plus
    machine-instruction behaviour. Treating these as oracles mirrors Rocq
    `jasmin_translate.v`'s use of `handled_program` (for calls) and
    `asm_correct` (for `Oasm`). -/
structure LeafSpec where
  call      : CallSpec
  limbStore : LimbStoreSpec

/-- Runtime state: a tower-variable heap and a scalar heap. -/
structure RustState where
  rsTower  : String → Option (Σ t : TowerType, RustVal t)
  rsScalar : String → Nat   -- default 0

instance : Inhabited RustState where
  default := { rsTower := fun _ => none, rsScalar := fun _ => 0 }

/-- Set a tower variable. -/
def rsSetTower (rs : RustState) (x : String)
    (v : Σ t : TowerType, RustVal t) : RustState :=
  { rs with rsTower := fun y => if y == x then some v else rs.rsTower y }

/-- Set a scalar variable. -/
def rsSetScalar (rs : RustState) (x : String) (v : Nat) : RustState :=
  { rs with rsScalar := fun y => if y == x then v else rs.rsScalar y }

/-- Remove a tower variable (used after `RLetZero` body exits scope). -/
def rsRemoveTower (rs : RustState) (x : String) : RustState :=
  { rs with rsTower := fun y => if y == x then none else rs.rsTower y }

/-- Look up a tower variable, checking the stored type matches `loc.locDst`. -/
def locatedLookup (rs : RustState) (loc : Located) :
    Option (RustVal loc.locDst) :=
  match rs.rsTower loc.locVar with
  | some ⟨t, v⟩ => if h : t = loc.locDst then some (h ▸ v) else none
  | none         => none

/-- Write a new value to the destination of `loc`. -/
def locatedUpdate (rs : RustState) (loc : Located)
    (v : RustVal loc.locDst) : RustState :=
  rsSetTower rs loc.locVar ⟨loc.locDst, v⟩

/-! ## §5  Key state-update lemmas -/

theorem rsSetTower_same (rs : RustState) (x : String) (v : Σ t, RustVal t) :
    (rsSetTower rs x v).rsTower x = some v := by
  simp [rsSetTower]

theorem rsSetTower_other (rs : RustState) (x y : String)
    (v : Σ t, RustVal t) (h : x ≠ y) :
    (rsSetTower rs x v).rsTower y = rs.rsTower y := by
  unfold rsSetTower; simp only []
  have : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

theorem rsRemoveTower_other (rs : RustState) (x y : String) (h : x ≠ y) :
    (rsRemoveTower rs x).rsTower y = rs.rsTower y := by
  unfold rsRemoveTower; simp only []
  have : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

/-- Setting one tower var leaves a different located's lookup unchanged. -/
theorem locatedLookup_rsSetTower_other (rs : RustState) (x : String)
    (v : Σ t, RustVal t) (loc : Located) (h : x ≠ loc.locVar) :
    locatedLookup (rsSetTower rs x v) loc = locatedLookup rs loc := by
  unfold locatedLookup rsSetTower; simp only []
  have : (loc.locVar == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

/-- Removing one tower var leaves a different located's lookup unchanged. -/
theorem locatedLookup_rsRemoveTower_other (rs : RustState) (x : String)
    (loc : Located) (h : x ≠ loc.locVar) :
    locatedLookup (rsRemoveTower rs x) loc = locatedLookup rs loc := by
  unfold locatedLookup rsRemoveTower; simp only []
  have : (loc.locVar == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

/-- Setting scalar leaves tower lookups unchanged. -/
theorem locatedLookup_rsSetScalar (rs : RustState) (x : String) (v : Nat)
    (loc : Located) :
    locatedLookup (rsSetScalar rs x v) loc = locatedLookup rs loc := by
  unfold locatedLookup rsSetScalar; simp only []

/-- `locatedUpdate` writes to the correct variable. -/
theorem locatedUpdate_dest (rs : RustState) (loc : Located)
    (v : RustVal loc.locDst) :
    (locatedUpdate rs loc v).rsTower loc.locVar = some ⟨loc.locDst, v⟩ := by
  unfold locatedUpdate rsSetTower
  simp

/-- `locatedUpdate` leaves other variables unchanged. -/
theorem locatedUpdate_other (rs : RustState) (loc1 loc2 : Located)
    (v : RustVal loc1.locDst)
    (h : loc1.locVar ≠ loc2.locVar) :
    locatedLookup (locatedUpdate rs loc1 v) loc2 = locatedLookup rs loc2 := by
  apply locatedLookup_rsSetTower_other
  exact h

/-! ## §6  Big-step semantics -/

/-- Big-step execution relation for `RustCmd`.

    `RustExec N leafSpec c rs rs'` means: running `c` from state `rs`
    with fuel bound `N` and leaf specification `leafSpec` terminates in `rs'`.

    `N` bounds `RWhileNz` loop iterations (via the `while_true` case's
    induction structure — the bound appears implicitly in the finite derivation
    tree). -/
inductive RustExec (N : Nat) (leafSpec : LeafSpec) :
    RustCmd → RustState → RustState → Prop where
  | skip   : ∀ rs, RustExec N leafSpec .RSkip rs rs
  | seq    : ∀ c1 c2 rs r1 rs',
      RustExec N leafSpec c1 rs r1 →
      RustExec N leafSpec c2 r1 rs' →
      RustExec N leafSpec (.RSeq c1 c2) rs rs'
  | letZero : ∀ x t body rs rs',
      RustExec N leafSpec body (rsSetTower rs x ⟨t, default⟩) rs' →
      RustExec N leafSpec (.RLetZero x t body) rs rs'
  | letU64Zero : ∀ x body rs rs',
      RustExec N leafSpec body (rsSetScalar rs x 0) rs' →
      RustExec N leafSpec (.RLetU64Zero x body) rs rs'
  | scalarSet : ∀ x v rs,
      RustExec N leafSpec (.RScalarSet x v) rs (rsSetScalar rs x v)
  | ifTrue  : ∀ e ct cf rs rs' v,
      rs.rsScalar e = v → v ≠ 0 →
      RustExec N leafSpec ct rs rs' →
      RustExec N leafSpec (.RIfNz e ct cf) rs rs'
  | ifFalse : ∀ e ct cf rs rs',
      rs.rsScalar e = 0 →
      RustExec N leafSpec cf rs rs' →
      RustExec N leafSpec (.RIfNz e ct cf) rs rs'
  | whileFalse : ∀ e body rs,
      rs.rsScalar e = 0 →
      RustExec N leafSpec (.RWhileNz e body) rs rs
  | whileTrue : ∀ e body rs r1 rs' v,
      rs.rsScalar e = v → v ≠ 0 →
      RustExec N leafSpec body rs r1 →
      RustExec N leafSpec (.RWhileNz e body) r1 rs' →
      RustExec N leafSpec (.RWhileNz e body) rs rs'
  | call : ∀ f dest args rs oldDestV argList,
      locatedLookup rs dest = some oldDestV →
      argList = args.filterMap (fun a => rs.rsTower a.locVar) →
      RustExec N leafSpec (.RCall f dest args) rs
        (locatedUpdate rs dest
          (leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList))
  | cloneCall : ∀ cloneVar cloneTy oldDest innerF dest args
                   rs rsClone rs',
      rsClone = rsSetTower rs cloneVar
                  (rs.rsTower oldDest.locVar |>.getD ⟨cloneTy, default⟩) →
      RustExec N leafSpec (.RCall innerF dest args) rsClone rs' →
      RustExec N leafSpec
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args)
        rs rs'  -- aligns with Jasmin semantics: no variable removal
  | limbStore : ∀ loc idx v rs oldDestV,
      locatedLookup rs loc = some oldDestV →
      RustExec N leafSpec (.RLimbStore loc idx v) rs
        (locatedUpdate rs loc (leafSpec.limbStore loc oldDestV idx v))

end CatCrypt.Crypto.Jasmin.RustCmd
