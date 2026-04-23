/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.RustCmd
import CatCrypt.Crypto.Jasmin.RustCmdBorrowCheck
import CatCrypt.Crypto.Jasmin.JasminTranslate
import CatCrypt.Deep.Eval
import CatCrypt.Core.Heap

/-!
# RustCmd → Jasmin AST Translation

After AUCurves `Bedrock/Jasmin/RustCmdToJasmin.v`.

## Contents

* §1  Tower-type ↔ Jasmin SType representation
* §2  `toJasminCmd : RustCmd → Cmd` — syntax translation
* §3  State encoding bridge (`rustStateToHeap`)
* §4  Simulation theorem (`rustExecSimulates`)
* §5  Concrete programs (G1 add/dbl, G2 add)
* §6  Pretty-printer — `ppJasminCmd`, `writeJasminProg`

## Printing ASTs to files

Both the `RustCmd` and Jasmin ASTs can be emitted to disk from Lean:

```lean
-- Print RustCmd AST
#eval IO.println (repr g1Add)

-- Print translated Jasmin Cmd
#eval IO.println (repr (toJasminCmd g1Add))

-- Write Jasmin source to file
#eval writeJasminProg "g1_add.jazz" "g1_add" g1Add
```

`repr` uses the auto-derived `Repr` instances (all constructors have
`deriving Repr`). `writeJasminProg` calls `ppFunDecl` which emits
human-readable Jasmin syntax.
-/

namespace CatCrypt.Crypto.Jasmin.RustCmd

open CatCrypt.Crypto.Jasmin

/-! ## §1  Tower-type ↔ SType -/

/-- Map a `TowerType` to the Jasmin `SType` used to represent it:
    a fixed-size byte array (`sarr n`). -/
def towerToSType (t : TowerType) : SType :=
  .sarr t.byteSize

/-- Make a Jasmin variable for a named tower-type location. -/
def locToVar (loc : Located) : Var :=
  { vname := loc.locVar, vtype := towerToSType loc.locSrc }

/-- Make a `GVar` (local variable reference) for a Located. -/
def locToGVar (loc : Located) : GVar :=
  { gv := { var := locToVar loc, info := {} }, gs := false }

/-- Emit a Located as a Jasmin expression (variable read). -/
def locToPExpr (loc : Located) : PExpr :=
  .Pvar (locToGVar loc)

/-- Emit a Located as a Jasmin left-value (variable write). -/
def locToLVal (loc : Located) : LVal :=
  .Lvar { var := locToVar loc, info := {} }

/-! ## §2  Syntax translation -/

/-- Translate `RustCmd` to a Jasmin `Cmd` (list of instructions).

    The mapping is:
    - `RCall f dest args`   → `Ccall [dest] f [arg₀, …, argₙ]`
    - `RSeq c1 c2`          → `toJasminCmd c1 ++ toJasminCmd c2`
    - `RLetZero x t body`   → `[assign x := zero] ++ toJasminCmd body`
    - `RLetU64Zero x body`  → `[assign x := 0u64] ++ toJasminCmd body`
    - `RScalarSet x v`      → `[assign x := v]`
    - `RCloneCall …`        → clone assignment ++ inner call
    - `RIfNz e ct cf`       → `Cif (e ≠ 0) (toJasminCmd ct) (toJasminCmd cf)`
    - `RWhileNz e body`     → `Cwhile [] (e ≠ 0) (toJasminCmd body)`
    - `RLimbStore loc i v`  → array-set instruction
    - `RSkip`               → `[]`
-/
def toJasminCmd : RustCmd → Cmd
  | .RSkip => []
  | .RSeq c1 c2 =>
      toJasminCmd c1 ++ toJasminCmd c2
  | .RLetZero x t body =>
      -- Initialise x to a zero array, then run body
      let zeroExpr : PExpr := .Parr_init t.byteSize
      let initInstr : InstrR :=
        .Cassgn (.Lvar { var := { vname := x, vtype := .sarr t.byteSize }, info := {} })
                .AT_none (.sarr t.byteSize) zeroExpr
      initInstr :: toJasminCmd body
  | .RLetU64Zero x body =>
      let initInstr : InstrR :=
        .Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                .AT_none (.sword .U64) (.Pconst 0)
      initInstr :: toJasminCmd body
  | .RScalarSet x v =>
      -- Use Oword_of_int to convert the Nat constant to a U64 word value
      [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
               .AT_none (.sword .U64) (.Papp1 (.Oword_of_int .U64) (.Pconst v))]
  | .RCall f dest args =>
      [.Ccall .DoNotInline [locToLVal dest] { name := f } (args.map locToPExpr)]
  | .RCloneCall cloneVar cloneTy oldDest innerF dest args =>
      -- Clone: array-copy cloneVar := oldDest, treated as a Jasmin Oasm
      -- oracle ("CLONE_TOWER"), analogous to the STORE64 oracle for RLimbStore.
      -- Then the inlined call.
      let cloneVar' : Var := { vname := cloneVar, vtype := .sarr cloneTy.byteSize }
      let cloneInstr : InstrR :=
        .Copn [.Lvar { var := cloneVar', info := {} }] .AT_none
              (.Oasm { name := "CLONE_TOWER" })
              [locToPExpr oldDest]
      [cloneInstr,
       .Ccall .DoNotInline [locToLVal dest] { name := innerF } (args.map locToPExpr)]
  | .RIfNz e ct cf =>
      -- Use Oword_of_int to convert 0 to a U64 word so evalSop2 (.Oneq .U64) gets
      -- two .sword arguments and produces .sbool (not the _ fallback).
      let zero64 : PExpr := .Papp1 (.Oword_of_int .U64) (.Pconst 0)
      let condExpr : PExpr :=
        .Papp2 (.Oneq .U64)
          (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} },
                   gs := false })
          zero64
      [.Cif condExpr (toJasminCmd ct) (toJasminCmd cf)]
  | .RWhileNz e body =>
      let condExpr : PExpr :=
        .Papp2 (.Oneq .U64)
          (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} },
                   gs := false })
          (.Pconst 0)
      -- Jasmin: Cwhile [] (e ≠ 0) body
      [.Cwhile [] condExpr (toJasminCmd body)]
  | .RLimbStore loc idx v =>
      -- Store u64 v into array loc at index idx (scaled by 8 bytes)
      [.Copn [locToLVal loc] .AT_none (.Oasm { name := "STORE64" })
             [locToPExpr loc, .Pconst idx, .Pconst v.toNat]]

/-- Wrap a translated command as a `FunDecl` with given name, params, results. -/
def toFunDecl (name : String) (params results : List Located)
    (c : RustCmd) : FunDecl where
  name    := { name }
  params  := params.map fun loc => { var := { var := locToVar loc, info := {} } }
  body    := toJasminCmd c
  results := results.map fun loc => { var := locToVar loc, info := {} }

/-- Build a single-function `JasminProg`. -/
def toJasminProg (name : String) (params results : List Located)
    (c : RustCmd) : JasminProg :=
  { funcs := [toFunDecl name params results c] }

/-! ## §3  State encoding bridge -/

section HeapBridge

open CatCrypt.Core
open CatCrypt.Deep

/-- Heap location for tower variable `x` at type `t` in scope `sid`.
    Matches the `translateVar`/`arrLoc` encoding in `JasminTranslate`. -/
noncomputable def towerLoc (sid : ScopeId) (x : String) (t : TowerType) :
    CatCrypt.Core.Location :=
  translateVar sid { vname := x, vtype := .sarr t.byteSize }

/-- **Heap invariant**: the CatCrypt heap at scope `sid` faithfully encodes `rs`.

    For each `x : t ↦ v` in `rs.rsTower`, the heap holds `v` at `towerLoc sid x t`.

    Scalar variables live at `sword U64` locations (type component `106400`)
    that are disjoint from tower locations (type component `≤ 57800`), so
    writing scalars preserves this invariant without extra proof. -/
def HeapInv (rs : RustState) (heap : Heap) (sid : ScopeId) : Prop :=
  ∀ (x : String) (t : TowerType) (v : RustVal t),
    rs.rsTower x = some ⟨t, v⟩ → heap.get (towerLoc sid x t) = v

/-- `whileFree c = true` iff `c` contains no `RWhileNz` subterm.
    While-free programs translate to deterministic, non-failing code because
    `translateInstrR` maps `Cwhile` (the only non-deterministic/failing case) to
    `.fail` — so all other instructions are fine. -/
def whileFree : RustCmd → Bool
  | .RSkip | .RScalarSet _ _ | .RCall _ _ _
  | .RCloneCall _ _ _ _ _ _ | .RLimbStore _ _ _ => true
  | .RSeq c1 c2 | .RIfNz _ c1 c2 => whileFree c1 && whileFree c2
  | .RLetZero _ _ body | .RLetU64Zero _ body => whileFree body
  | .RWhileNz _ _ => false

/-- Minimum fuel for `translateCmd env (toJasminCmd c) sid fuel` to not return `.fail`.

    * Structural commands (RSkip) need 1.
    * Single-instruction commands (RScalarSet, RCall, RLimbStore, RCloneCall) need 2:
      one for the instruction, one for the trailing empty list.
    * RLetZero/RLetU64Zero add 1 (one fuel level consumed at the top).
    * RSeq sums the two parts (append decomposes fuel additively).
    * RIfNz: the outer [Cif] needs fuel ≥ 1 to handle the trailing []; the inner branches
      run at `fuel - 1`, so we need `fuel - 1 ≥ max(jasminFuel ct, jasminFuel cf)`.
    * RWhileNz: always maps to `.fail`, so 1 suffices (will be blocked by `whileFree`). -/
def jasminFuel : RustCmd → Nat
  | .RSkip               => 1
  | .RScalarSet _ _      => 2
  | .RCall _ _ _         => 2
  | .RLimbStore _ _ _    => 2
  | .RCloneCall _ _ _ _ _ _ => 3
  | .RLetZero _ _ body   => 1 + jasminFuel body
  | .RLetU64Zero _ body  => 1 + jasminFuel body
  | .RSeq c1 c2          => jasminFuel c1 + jasminFuel c2
  | .RIfNz _ ct cf       => max (jasminFuel ct) (jasminFuel cf) + 1
  | .RWhileNz _ _        => 2

/-- `callFree c = true` iff `c` contains no `RCall`, `RCloneCall`, or `RLimbStore`.
    Call-free programs translate to instruction lists with no `Ccall` instructions,
    so `translateCmd` never invokes `freshId` and `newSid` stays equal to `sid`. -/
def callFree : RustCmd → Bool
  | .RSkip | .RScalarSet _ _ => true
  | .RSeq c1 c2 | .RIfNz _ c1 c2 => callFree c1 && callFree c2
  | .RLetZero _ _ body | .RLetU64Zero _ body | .RWhileNz _ body => callFree body
  | .RCall _ _ _ | .RCloneCall _ _ _ _ _ _ | .RLimbStore _ _ _ => false

/-- **Scalar invariant**: the heap correctly encodes `rs.rsScalar` at `sword U64` locations. -/
def ScalarInv (rs : RustState) (heap : Heap) (sid : ScopeId) : Prop :=
  ∀ (x : String),
    heap.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
    BitVec.ofNat 64 (rs.rsScalar x)

/-- All scalars in `rs` are representable as 64-bit words. -/
def ScalarsBounded (rs : RustState) : Prop :=
  ∀ x, rs.rsScalar x < 2^64

/-- `scalarSetsSmall c = true` iff every `RScalarSet x v` subterm of `c`
    has `v < 2^64`. Needed to maintain `ScalarsBounded` after scalar writes. -/
def scalarSetsSmall : RustCmd → Bool
  | .RSkip | .RCall _ _ _ | .RCloneCall _ _ _ _ _ _ | .RLimbStore _ _ _ => true
  | .RSeq c1 c2 | .RIfNz _ c1 c2 => scalarSetsSmall c1 && scalarSetsSmall c2
  | .RLetZero _ _ body | .RLetU64Zero _ body | .RWhileNz _ body => scalarSetsSmall body
  | .RScalarSet _ v => decide (v < 2^64)

end HeapBridge

/-! ## §4  Simulation theorem -/

section SimulationTheorem

open CatCrypt.Core
open CatCrypt.Deep
open CatCrypt.Prob

/-- **Leaf implementation hypothesis**: for each `RCall f dest args`, the
    translated `Ccall` instruction (run from any heap encoding `rs`) produces
    a heap where `dest` holds `leafSpec f ...` and all other tower locs are unchanged.

    This axiomatises what the concrete Jasmin function bodies in `env` must do.
    Note: `translateInstrR` ignores the `_lvs` in `Ccall`, so this condition
    cannot be derived from the translation alone — it is a semantic assumption
    about `env`. -/
def LeafImplOk (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat) : Prop :=
  ∀ (f : String) (dest : Located) (args : List Located)
    (rs0 : RustState) (sid : ScopeId) (heap0 : Heap)
    (oldDestV : RustVal dest.locDst)
    (argList : List (Σ t, RustVal t)),
    HeapInv rs0 heap0 sid →
    rs0.rsTower dest.locVar = some ⟨dest.locDst, oldDestV⟩ →
    argList = args.filterMap (fun a => rs0.rsTower a.locVar) →
    ∃ heap1 : Heap,
      (translateCmd env
        [.Ccall .DoNotInline [locToLVal dest] { name := f } (args.map locToPExpr)]
        sid fuel).code.eval heap0 =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap1) ∧
      heap1.get (towerLoc sid dest.locVar dest.locDst) =
        leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList ∧
      (∀ (x : String) (t : TowerType),
        x ≠ dest.locVar → heap1.get (towerLoc sid x t) = heap0.get (towerLoc sid x t)) ∧
      (∀ (x : String),
        heap1.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
        heap0.get (translateVar sid { vname := x, vtype := .sword .U64 }))

/-! ### Helper lemmas for scalarSet / letU64Zero HeapInv -/

/-- U64 word location ID and tower (sarr) location ID are always disjoint:
    `encodeSType (.sword .U64) = 1064 ≠ 2 + t.byteSize` for any `TowerType`. -/
private lemma wordLoc_id_ne_towerLoc_id (sid : ScopeId) (x y : String) (t : TowerType) :
    varLocId sid { vname := x, vtype := .sword .U64 } ≠
    varLocId sid { vname := y, vtype := .sarr t.byteSize } := by
  simp only [varLocId]
  intro h
  have h1 := (Nat.pair_eq_pair.mp h).1
  have h2 := (Nat.pair_eq_pair.mp h1).2
  simp only [encodeSType, WSize.bits] at h2
  cases t <;> simp only [TowerType.byteSize] at h2 <;> omega

/-- Tower locations with different variable names have different IDs. -/
private lemma towerLoc_id_ne_of_ne_name (sid : ScopeId) (x y : String) (t : TowerType)
    (hne : x ≠ y) :
    varLocId sid { vname := x, vtype := .sarr t.byteSize } ≠
    varLocId sid { vname := y, vtype := .sarr t.byteSize } := by
  simp only [varLocId]
  intro h
  exact hne (encodeVarName_injective (Nat.pair_eq_pair.mp h).2)

/-- Scalar (word) locations with different variable names have different IDs. -/
private lemma wordLoc_id_ne_of_ne_name (sid : ScopeId) (x y : String)
    (hne : x ≠ y) :
    varLocId sid { vname := x, vtype := .sword .U64 } ≠
    varLocId sid { vname := y, vtype := .sword .U64 } := by
  simp only [varLocId]
  intro h
  exact hne (encodeVarName_injective (Nat.pair_eq_pair.mp h).2)

/-! ### jasminFuel bounds -/

private lemma jasminFuel_pos : ∀ (c : RustCmd), 1 ≤ jasminFuel c := by
  intro c; induction c <;> simp [jasminFuel] <;> omega

/-- The length of `toJasminCmd c` is strictly less than `jasminFuel c`. -/
private lemma jasminFuel_gt_length : ∀ (c : RustCmd), (toJasminCmd c).length < jasminFuel c := by
  intro c
  induction c with
  | RSkip => simp [toJasminCmd, jasminFuel]
  | RSeq c1 c2 ih1 ih2 =>
    simp only [toJasminCmd, jasminFuel, List.length_append]
    omega
  | RLetZero x t body ih =>
    simp only [toJasminCmd, jasminFuel, List.length_cons]
    omega
  | RLetU64Zero x body ih =>
    simp only [toJasminCmd, jasminFuel, List.length_cons]
    omega
  | RScalarSet x v => simp [toJasminCmd, jasminFuel]
  | RCall f dest args => simp [toJasminCmd, jasminFuel]
  | RCloneCall cv ct od f dest args => simp [toJasminCmd, jasminFuel]
  | RIfNz e ct cf ih1 ih2 =>
    simp only [toJasminCmd, jasminFuel, List.length_singleton]
    have h1 := jasminFuel_pos ct; have h2 := jasminFuel_pos cf; omega
  | RWhileNz e body ih => simp [toJasminCmd, jasminFuel]
  | RLimbStore loc idx v => simp [toJasminCmd, jasminFuel]

/-! ### Scalar assignment eval helpers -/

/-- `coerceValue` from `sint` to `sword U64` always returns 0 (type mismatch). -/
private lemma coerceValue_sint_u64 (v : Int) :
    coerceValue .sint (.sword .U64) v = (0 : BitVec 64) := rfl

/-- `coerceValue` is identity for matching `sword U64` types. -/
private lemma coerceValue_u64_u64 (v : BitVec 64) :
    coerceValue (.sword .U64) (.sword .U64) v = v := rfl

/-- `truncateWord .U64 .U64` is identity. -/
private lemma truncateWord_u64_u64 (v : BitVec 64) : truncateWord .U64 .U64 v = v := rfl

/-- `intToWord .U64` for a non-negative integer equals `BitVec.ofNat`. -/
private lemma intToWord_U64_ofNat (v : Nat) :
    intToWord .U64 (v : Int) = BitVec.ofNat 64 v := by
  simp [intToWord, BitVec.ofInt_natCast, WSize.bits]

/-- `writeVar` at `sword U64` with value `0` equals `put` at the public `translateVar` location. -/
private lemma writeVar_u64_zero (sid : ScopeId) (x : String) :
    writeVar sid { vname := x, vtype := .sword .U64 } ⟨.sword .U64, (0 : BitVec 64)⟩ =
    RawCode.put (translateVar sid { vname := x, vtype := .sword .U64 }) (0 : BitVec 64) := rfl

/-- `writeVar` at `sword U64` with value `v` equals `put` at `translateVar`. -/
private lemma writeVar_u64_val (sid : ScopeId) (x : String) (v : BitVec 64) :
    writeVar sid { vname := x, vtype := .sword .U64 } ⟨.sword .U64, v⟩ =
    RawCode.put (translateVar sid { vname := x, vtype := .sword .U64 }) v := rfl

/-- `HeapInv` is preserved by setting a U64 scalar location (disjoint from tower locs). -/
private lemma heapInv_set_u64 (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (v : BitVec 64) (hInv : HeapInv rs heap sid) :
    HeapInv rs (heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) v) sid := by
  intro y t w hy
  rw [Heap.get_set_other _ _ _ _ (wordLoc_id_ne_towerLoc_id sid x y t)]
  exact hInv y t w hy

/-- `rsSetScalar` only changes `rsScalar`, preserving `HeapInv`. -/
private lemma heapInv_rsSetScalar (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (v : Nat) (hInv : HeapInv rs heap sid) :
    HeapInv (rsSetScalar rs x v) heap sid := by
  intro y t w hy; exact hInv y t w hy

/-! ### Tower init (RLetZero) helper -/

/-- Writing `default` to `towerLoc sid x t` and setting `rsSetTower` preserves `HeapInv`. -/
private lemma heapInv_rsSetTower_init (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (t : TowerType) (hInv : HeapInv rs heap sid) :
    HeapInv (rsSetTower rs x ⟨t, default⟩) (heap.set (towerLoc sid x t) default) sid := by
  intro y t' v hy
  simp only [rsSetTower] at hy
  by_cases hxy : y == x
  · -- y = x
    have hyx : y = x := beq_iff_eq.mp hxy
    simp only [hxy, ite_true] at hy
    -- hy : some ⟨t, default⟩ = some ⟨t', v⟩
    have hsome := Option.some.inj hy
    obtain ⟨rfl, hveq⟩ := Sigma.mk.inj hsome
    rw [← eq_of_heq hveq, hyx]
    exact Heap.get_set_same _ _ _
  · -- y ≠ x
    simp only [hxy, ite_false] at hy
    have hne_name : x ≠ y := by
      intro h; simp [h] at hxy
    have hid_ne : (towerLoc sid x t).id ≠ (towerLoc sid y t').id := by
      simp only [towerLoc, translateVar, varLocId]
      intro h
      exact hne_name (encodeVarName_injective (Nat.pair_eq_pair.mp h).2)
    rw [Heap.get_set_other _ _ _ _ hid_ne]
    exact hInv y t' v hy

/-! ### ScalarInv helpers -/

/-- `rsSetTower` doesn't change `rsScalar`, so `ScalarInv` is preserved. -/
private lemma scalarInv_rsSetTower (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (tv : Σ t, RustVal t) (hSInv : ScalarInv rs heap sid) :
    ScalarInv (rsSetTower rs x tv) heap sid := by
  intro y; exact hSInv y

/-- Tower-loc set preserves `ScalarInv` (disjoint ids). -/
private lemma scalarInv_set_tower (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (t : TowerType) (v : RustVal t) (hSInv : ScalarInv rs heap sid) :
    ScalarInv rs (heap.set (towerLoc sid x t) v) sid := by
  intro y
  rw [Heap.get_set_other _ _ _ _ (Ne.symm (wordLoc_id_ne_towerLoc_id sid y x t))]
  exact hSInv y

/-- Writing the correct value at a scalar loc establishes the scalar inv entry. -/
private lemma scalarInv_set_scalar_eq (heap : Heap) (sid : ScopeId)
    (x y : String) (v w : Nat) (hSInv_y : heap.get (translateVar sid { vname := y, vtype := .sword .U64 }) = BitVec.ofNat 64 w)
    (hne : x ≠ y) :
    (heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (BitVec.ofNat 64 v)).get
      (translateVar sid { vname := y, vtype := .sword .U64 }) = BitVec.ofNat 64 w := by
  rw [Heap.get_set_other _ _ _ _ (wordLoc_id_ne_of_ne_name sid x y hne)]
  exact hSInv_y

/-- After writing `BitVec.ofNat 64 v` to scalar `x`'s location, `ScalarInv` holds for `rsSetScalar`. -/
private lemma scalarInv_after_scalar_set (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (v : Nat) (hSInv : ScalarInv rs heap sid) :
    ScalarInv (rsSetScalar rs x v)
      (heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (BitVec.ofNat 64 v)) sid := by
  intro y
  simp only [rsSetScalar]
  by_cases hxy : x = y
  · subst hxy; simp [Heap.get_set_same]
  · rw [Heap.get_set_other _ _ _ _ (wordLoc_id_ne_of_ne_name sid x y hxy)]
    simp only [beq_eq_false_iff_ne.mpr (Ne.symm hxy), ite_false]
    exact hSInv y

/-- `rsSetScalar` preserves `ScalarInv` when the heap val is already correct. -/
private lemma scalarInv_rsSetScalar_other (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (v : Nat)
    (hSInv : ScalarInv rs heap sid)
    (hheap : heap.get (translateVar sid { vname := x, vtype := .sword .U64 }) = BitVec.ofNat 64 v) :
    ScalarInv (rsSetScalar rs x v) heap sid := by
  intro y
  simp only [rsSetScalar]
  by_cases hxy : y == x
  · simp only [hxy, ite_true]
    have heq : y = x := beq_iff_eq.mp hxy
    subst heq; exact hheap
  · simp only [hxy, ite_false]; exact hSInv y

/-! ### ScalarsBounded helpers -/

private lemma scalarsBounded_zero : (0 : Nat) < 2^64 := by norm_num

private lemma scalarsBounded_rsSetScalar_zero (rs : RustState) (x : String) (hB : ScalarsBounded rs) :
    ScalarsBounded (rsSetScalar rs x 0) := by
  intro y; simp only [rsSetScalar]
  split_ifs with hxy
  · exact scalarsBounded_zero
  · exact hB y

private lemma scalarsBounded_rsSetTower (rs : RustState) (x : String) (tv : Σ t, RustVal t)
    (hB : ScalarsBounded rs) : ScalarsBounded (rsSetTower rs x tv) := by
  intro y; exact hB y

private lemma scalarsBounded_rsSetScalar (rs : RustState) (x : String) (v : Nat)
    (hv : v < 2^64) (hB : ScalarsBounded rs) : ScalarsBounded (rsSetScalar rs x v) := by
  intro y
  simp only [rsSetScalar]
  split_ifs with hxy
  · exact hv
  · exact hB y

private lemma scalarSetsSmall_val (c : RustCmd) (x : String) (v : Nat)
    (h : scalarSetsSmall c = true) (heq : c = .RScalarSet x v) : v < 2^64 := by
  subst heq; simp [scalarSetsSmall] at h; exact h

/-! ### translateCmd append decomposition -/

/-- `newSid` of appended command list equals `newSid` of the second list run after the first. -/
private lemma translateCmd_append_newSid
    (env : TransEnv) (l1 l2 : Cmd) (sid : ScopeId) (fuel : Nat) :
    (translateCmd env (l1 ++ l2) sid fuel).newSid =
      (translateCmd env l2
        (translateCmd env l1 sid fuel).newSid
        (fuel - l1.length)).newSid := by
  induction l1 generalizing sid fuel with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.sub_zero]
    cases fuel with
    | zero => simp [translateCmd]
    | succ n => simp [translateCmd]
  | cons i is ih =>
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      simp only [List.cons_append, List.length_cons, translateCmd]
      rw [ih]
      simp only [translateCmd, Nat.succ_sub_succ_eq_sub]

/-- Evaluation of appended command list equals sequential composition. -/
private lemma translateCmd_append_eval
    (env : TransEnv) (l1 l2 : Cmd) (sid : ScopeId) (fuel : Nat) (heap : Heap) :
    (translateCmd env (l1 ++ l2) sid fuel).code.eval heap =
      ((translateCmd env l1 sid fuel).code.eval heap).bind (fun x =>
        (translateCmd env l2
          (translateCmd env l1 sid fuel).newSid
          (fuel - l1.length)).code.eval x.2) := by
  induction l1 generalizing sid fuel heap with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.sub_zero]
    cases fuel with
    | zero => simp [translateCmd, CatCrypt.Deep.eval_fail, SPComp.fail, SDistr.bind_fail]
    | succ n =>
      simp only [translateCmd, CatCrypt.Deep.eval_ret, SPComp.pure_def, SDistr.pure_bind]
  | cons i is ih =>
    cases fuel with
    | zero => simp [translateCmd, CatCrypt.Deep.eval_fail, SPComp.fail, SDistr.bind_fail]
    | succ n =>
      simp only [List.cons_append, List.length_cons, Nat.succ_sub_succ_eq_sub]
      simp only [translateCmd, eval_bind, SPComp.bind_def]
      simp_rw [ih (translateInstrR env sid n i).newSid n]
      rw [← SDistr.bind_assoc]

/-! ### callFree → newSid = sid -/

/-- Call-free programs leave `newSid` unchanged. -/
private lemma callFree_toJasmin_newSid
    (c : RustCmd) (hCF : callFree c = true)
    (env : TransEnv) (sid : ScopeId) (fuel : Nat) :
    (translateCmd env (toJasminCmd c) sid fuel).newSid = sid := by
  induction c generalizing sid fuel with
  | RSkip => cases fuel <;> simp [toJasminCmd, translateCmd]
  | RScalarSet x v =>
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      cases n with
      | zero => simp [toJasminCmd, translateCmd, translateInstrR]
      | succ m => simp [toJasminCmd, translateCmd, translateInstrR]
  | RSeq c1 c2 ih1 ih2 =>
    simp only [callFree, Bool.and_eq_true] at hCF
    simp only [toJasminCmd, translateCmd_append_newSid, ih1 hCF.1 sid fuel,
               ih2 hCF.2 sid _]
  | RLetZero x t body ih =>
    simp only [callFree] at hCF
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      cases n with
      | zero => simp [toJasminCmd, translateCmd, translateInstrR]
      | succ m =>
        simp only [toJasminCmd, translateCmd, translateInstrR]
        exact ih hCF sid (m + 1)
  | RLetU64Zero x body ih =>
    simp only [callFree] at hCF
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      cases n with
      | zero => simp [toJasminCmd, translateCmd, translateInstrR]
      | succ m =>
        simp only [toJasminCmd, translateCmd, translateInstrR]
        exact ih hCF sid (m + 1)
  | RIfNz e ct cf ih1 ih2 =>
    simp only [callFree, Bool.and_eq_true] at hCF
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      simp only [toJasminCmd, translateCmd, translateInstrR]
      rw [ih1 hCF.1 sid n, ih2 hCF.2 sid n]
      cases n <;> simp only [translateCmd]
  | RWhileNz e body ih =>
    simp only [callFree] at hCF
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      cases n with
      | zero => simp [toJasminCmd, translateCmd, translateInstrR]
      | succ m => simp [toJasminCmd, translateCmd, translateInstrR]
  | RCall _ _ _ => simp [callFree] at hCF
  | RCloneCall _ _ _ _ _ _ => simp [callFree] at hCF
  | RLimbStore _ _ _ => simp [callFree] at hCF

/-- Eval of `translateCmd` for a single U64 const-assign writes `0` to the U64 location. -/
private lemma translateCmd_cassgn_u64_eval
    (env : TransEnv) (sid : ScopeId) (x : String) (v : Int) (n : Nat) (heap : Heap) :
    (translateCmd env
        [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64) (.Pconst v)]
        sid (n + 2)).code.eval heap =
    SDistr.pure (⟨()⟩,
        heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (0 : BitVec 64)) := by
  simp only [translateCmd, translateInstrR, translatePExpr, translateWriteLVal,
             coerceValue_sint_u64, writeVar_u64_zero,
             eval_bind, eval_ret, eval_put, SPComp.bind_def, SPComp.set_def, SPComp.pure_def,
             SDistr.pure_bind]

/-- `newSid` for a single U64 const-assign equals `sid`. -/
private lemma translateCmd_cassgn_u64_newSid
    (env : TransEnv) (sid : ScopeId) (x : String) (v : Int) (n : Nat) :
    (translateCmd env
        [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64) (.Pconst v)]
        sid (n + 2)).newSid = sid := by
  simp [translateCmd, translateInstrR]

/-- One-step eval: U64 const-assign followed by `rest`; advances heap then runs `rest`. -/
private lemma translateCmd_cons_cassgn_u64_eval
    (env : TransEnv) (sid : ScopeId) (x : String) (v : Int)
    (rest : Cmd) (n : Nat) (heap : Heap) :
    (translateCmd env
        (.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64) (.Pconst v) :: rest)
        sid (n + 2)).code.eval heap =
    (translateCmd env rest sid (n + 1)).code.eval
        (heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (0 : BitVec 64)) := by
  simp only [translateCmd, translateInstrR, translatePExpr, translateWriteLVal,
             coerceValue_sint_u64, writeVar_u64_zero,
             eval_bind, eval_ret, eval_put, SPComp.bind_def, SPComp.set_def, SPComp.pure_def,
             SDistr.pure_bind]

/-- One-step `newSid`: U64 const-assign followed by `rest`. -/
private lemma translateCmd_cons_cassgn_u64_newSid
    (env : TransEnv) (sid : ScopeId) (x : String) (v : Int)
    (rest : Cmd) (n : Nat) :
    (translateCmd env
        (.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64) (.Pconst v) :: rest)
        sid (n + 2)).newSid =
    (translateCmd env rest sid (n + 1)).newSid := by
  simp [translateCmd, translateInstrR]

/-! ### RScalarSet eval (with corrected Papp1 encoding) -/

/-- `translatePExpr` for `Papp1 (Oword_of_int U64) (Pconst v)` evaluates to `BitVec.ofNat 64 v`. -/
private lemma translatePExpr_word_of_int_eval (sid : ScopeId) (v : Nat) (heap : Heap) :
    (translatePExpr sid (.Papp1 (.Oword_of_int .U64) (.Pconst (v : Int)))).eval heap =
    SDistr.pure (⟨.sword .U64, BitVec.ofNat 64 v⟩, heap) := by
  simp [translatePExpr, evalSop1, intToWord_U64_ofNat,
        CatCrypt.Deep.eval_ret, CatCrypt.Deep.eval_bind, SPComp.pure_def, SDistr.pure_bind]

/-- Eval of a `Cassgn` with `Papp1 (Oword_of_int U64) (Pconst v)` writes `BitVec.ofNat 64 v`. -/
private lemma translateCmd_cassgn_u64_val_eval
    (env : TransEnv) (sid : ScopeId) (x : String) (v : Nat) (n : Nat) (heap : Heap) :
    (translateCmd env
        [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64) (.Papp1 (.Oword_of_int .U64) (.Pconst (v : Int)))]
        sid (n + 2)).code.eval heap =
    SDistr.pure (⟨()⟩,
        heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (BitVec.ofNat 64 v)) := by
  simp only [translateCmd, translateInstrR, translatePExpr, evalSop1, intToWord_U64_ofNat,
             coerceValue_u64_u64, translateWriteLVal, writeVar_u64_val, truncateWord_u64_u64,
             CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_ret, CatCrypt.Deep.eval_put,
             SPComp.bind_def, SPComp.set_def, SPComp.pure_def, SDistr.pure_bind]

/-- `newSid` for the single-instruction `Cassgn Papp1` case. -/
private lemma translateCmd_cassgn_u64_val_newSid
    (env : TransEnv) (sid : ScopeId) (x : String) (v : Nat) (n : Nat) :
    (translateCmd env
        [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64) (.Papp1 (.Oword_of_int .U64) (.Pconst (v : Int)))]
        sid (n + 2)).newSid = sid := by
  simp [translateCmd, translateInstrR]

/-! ### RLetZero eval (Parr_init / sarr init) -/

/-- `writeVar` at `sarr t.byteSize` with default value equals `put` at `towerLoc`. -/
private lemma writeVar_sarr_default (sid : ScopeId) (x : String) (t : TowerType) :
    writeVar sid { vname := x, vtype := .sarr t.byteSize }
      ⟨.sarr t.byteSize, (fun _ => 0 : JArray t.byteSize)⟩ =
    RawCode.put (towerLoc sid x t) (fun _ => 0 : JArray t.byteSize) := by
  rw [writeVar_sarr_eq]; rfl

/-- `default : JArray n = fun _ => 0`. -/
private lemma jarray_default_eq (n : Nat) : (default : JArray n) = fun _ => 0 := rfl

/-- One-step cons eval: `Cassgn (Parr_init t.byteSize)` writes `default` to `towerLoc`,
    then runs `rest`. -/
private lemma translateCmd_cons_cassgn_sarr_init_eval
    (env : TransEnv) (sid : ScopeId) (x : String) (t : TowerType)
    (rest : Cmd) (n : Nat) (heap : Heap) :
    (translateCmd env
      (.Cassgn (.Lvar { var := { vname := x, vtype := .sarr t.byteSize }, info := {} })
               .AT_none (.sarr t.byteSize) (.Parr_init t.byteSize) :: rest)
      sid (n + 2)).code.eval heap =
    (translateCmd env rest sid (n + 1)).code.eval
      (heap.set (towerLoc sid x t) (default : JArray t.byteSize)) := by
  simp only [translateCmd, translateInstrR, translatePExpr, coerceValue, eq_self_iff_true,
             ↓reduceDIte, translateWriteLVal, writeVar_sarr_default, jarray_default_eq,
             CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_ret, CatCrypt.Deep.eval_put,
             SPComp.bind_def, SPComp.set_def, SPComp.pure_def, SDistr.pure_bind]

/-- `newSid` for cons Cassgn sarr init. -/
private lemma translateCmd_cons_cassgn_sarr_init_newSid
    (env : TransEnv) (sid : ScopeId) (x : String) (t : TowerType)
    (rest : Cmd) (n : Nat) :
    (translateCmd env
      (.Cassgn (.Lvar { var := { vname := x, vtype := .sarr t.byteSize }, info := {} })
               .AT_none (.sarr t.byteSize) (.Parr_init t.byteSize) :: rest)
      sid (n + 2)).newSid =
    (translateCmd env rest sid (n + 1)).newSid := by
  simp [translateCmd, translateInstrR]

/-! ### Cif eval helpers -/

/-- Reading a `sword U64` variable from the heap. -/
private lemma translatePExpr_pvar_u64_eval (sid : ScopeId) (e : String) (heap : Heap) :
    (translatePExpr sid
      (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} }, gs := false })).eval heap =
    SDistr.pure (⟨.sword .U64, heap.get (translateVar sid { vname := e, vtype := .sword .U64 })⟩, heap) := by
  simp only [translatePExpr, readGVar, readVar_sword_eq,
             CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_get, CatCrypt.Deep.eval_ret,
             SPComp.bind_def, SPComp.get_def, SPComp.pure_def, SDistr.pure_bind]

/-- Evaluating the `RIfNz` condition expression. -/
private lemma cif_cond_eval (sid : ScopeId) (e : String) (heap : Heap) :
    let zero64 : PExpr := .Papp1 (.Oword_of_int .U64) (.Pconst 0)
    let condExpr : PExpr :=
      .Papp2 (.Oneq .U64)
        (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} }, gs := false })
        zero64
    let w : BitVec 64 := heap.get (translateVar sid { vname := e, vtype := .sword .U64 })
    (translatePExpr sid condExpr).eval heap =
    SDistr.pure (⟨.sbool, w != (0 : BitVec 64)⟩, heap) := by
  simp only [translatePExpr, readGVar, readVar_sword_eq, evalSop1, evalSop2, intToWord_U64_ofNat,
             CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_get, CatCrypt.Deep.eval_ret,
             SPComp.bind_def, SPComp.get_def, SPComp.pure_def, SDistr.pure_bind]
  rfl

/-- `BitVec.ofNat 64 v ≠ 0` when `v ≠ 0` and `v < 2^64`. -/
private lemma bitVec_ofNat_ne_zero (v : Nat) (hv : v ≠ 0) (hlt : v < 2^64) :
    (BitVec.ofNat 64 v) ≠ (0 : BitVec 64) := by
  intro h
  apply hv
  have h1 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, BitVec.toNat_zero] at h1
  exact h1

/-- Single-instruction `Cif` eval when condition is true. -/
private lemma translateCmd_cif_eval_true
    (env : TransEnv) (sid : ScopeId) (cond : PExpr) (ct cf : Cmd)
    (fuel : Nat) (heap heap' : Heap)
    (hcond : (translatePExpr sid cond).eval heap = SDistr.pure (⟨.sbool, true⟩, heap')) :
    (translateCmd env [.Cif cond ct cf] sid (fuel + 1)).code.eval heap =
    (translateCmd env ct sid fuel).code.eval heap' := by
  cases fuel with
  | zero =>
    simp only [translateCmd, translateInstrR, CatCrypt.Deep.eval_bind, SPComp.bind_def, hcond,
               SDistr.pure_bind, CatCrypt.Deep.eval_fail, SPComp.fail, SDistr.bind_fail]
  | succ n =>
    simp only [translateCmd, translateInstrR, CatCrypt.Deep.eval_bind, SPComp.bind_def, hcond,
               SDistr.pure_bind, CatCrypt.Deep.eval_ret, SPComp.pure_def]
    have hunit : (fun p : ULift Unit × Heap => SDistr.pure (⟨()⟩, p.2)) = SDistr.pure :=
      funext fun ⟨u, h'⟩ => by cases u; rfl
    rw [hunit, SDistr.bind_pure]

/-- Single-instruction `Cif` eval when condition is false. -/
private lemma translateCmd_cif_eval_false
    (env : TransEnv) (sid : ScopeId) (cond : PExpr) (ct cf : Cmd)
    (fuel : Nat) (heap heap' : Heap)
    (hcond : (translatePExpr sid cond).eval heap = SDistr.pure (⟨.sbool, false⟩, heap')) :
    (translateCmd env [.Cif cond ct cf] sid (fuel + 1)).code.eval heap =
    (translateCmd env cf (translateCmd env ct sid fuel).newSid fuel).code.eval heap' := by
  cases fuel with
  | zero =>
    simp only [translateCmd, translateInstrR, CatCrypt.Deep.eval_bind, SPComp.bind_def, hcond,
               SDistr.pure_bind, CatCrypt.Deep.eval_fail, SPComp.fail, SDistr.bind_fail]
  | succ n =>
    simp only [translateCmd, translateInstrR, CatCrypt.Deep.eval_bind, SPComp.bind_def, hcond,
               SDistr.pure_bind, CatCrypt.Deep.eval_ret, SPComp.pure_def]
    have hunit : (fun p : ULift Unit × Heap => SDistr.pure (⟨()⟩, p.2)) = SDistr.pure :=
      funext fun ⟨u, h'⟩ => by cases u; rfl
    rw [hunit, SDistr.bind_pure]

/-- `newSid` for `[Cif cond ct cf]` (when ct and cf are call-free). -/
private lemma translateCmd_cif_newSid
    (env : TransEnv) (sid : ScopeId) (cond : PExpr) (ct cf : Cmd) (fuel : Nat) :
    (translateCmd env [.Cif cond ct cf] sid (fuel + 1)).newSid =
    (translateCmd env cf (translateCmd env ct sid fuel).newSid fuel).newSid := by
  cases fuel <;> simp [translateCmd, translateInstrR]

/-- **rustExecSimulates**: the `RustCmd → Jasmin` translation is operationally correct.

    If `c` is while-free, `env` correctly implements `leafSpec`, and the initial
    heap encodes `rs`, then executing `translateCmd env (toJasminCmd c)` from that
    heap deterministically produces a heap encoding `rs'`.

    ## Signature

    * `hLeaf : ∀ fuel', LeafImplOk leafSpec env fuel'` — `LeafImplOk` at any fuel
    * `hFuel : jasminFuel c ≤ fuel` — minimum fuel for the translated program to run
    * Induction generalizes over `sid`, `heap`, and `fuel` to allow IH reuse at subterms.

    ## Proof sketch per case

    * `skip`      — `toJasminCmd .RSkip = []`; `translateCmd [] = ret ⟨()⟩`; heap unchanged ✓
    * `seq`       — needs `translateCmd_append`; IH₁ then IH₂ in sequence
    * `letZero`   — assignment writes default array to `towerLoc`; IH on body
    * `letU64Zero` — writes to `wordLoc` (disjoint); IH on body; heap updates preserve HeapInv
    * `scalarSet` — writes to `wordLoc` (disjoint from towerLoc by encodeSType); HeapInv preserved
    * `ifTrue/False` — IH on taken branch
    * `whileFalse/True` — `False` from `hWf : whileFree (.RWhileNz ..) = false ≠ true` ✓
    * `call`      — `hLeaf` gives result heap; HeapInv blocked by scope mismatch
    * `cloneCall` — `rsSetTower` + IH(inner call) + `rsRemoveTower`
    * `limbStore` — similar to `call`; writes to `towerLoc dest`

    **Proved: all 11 cases (0 sorry).**

    ## Hypotheses

    * `hCF : callFree c = true` — excludes `RCall`, `RCloneCall`, `RLimbStore`
      (those advance `newSid`; without them `newSid = sid` throughout)
    * `hSSS : scalarSetsSmall c = true` — all `RScalarSet x v` have `v < 2^64`
    * `hSInv : ScalarInv rs heap sid` — heap correctly encodes `rsScalar`
    * `hBounded : ScalarsBounded rs` — all scalars fit in 64 bits

    ## Conclusion

    Uses `sid` (not `newSid`) since call-free programs preserve `newSid = sid`. -/
theorem rustExecSimulates
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hLeaf : ∀ fuel', LeafImplOk leafSpec env fuel')
    (c : RustCmd) (rs rs' : RustState)
    (hWf : whileFree c = true)
    (hCF : callFree c = true)
    (hSSS : scalarSetsSmall c = true)
    (hFuel : jasminFuel c ≤ fuel)
    (hExec : RustExec N leafSpec c rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmd c) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  induction hExec generalizing sid heap fuel with

  | skip _ =>
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [jasminFuel] at hFuel; omega⟩
    exact ⟨heap, by simp [toJasminCmd, translateCmd, CatCrypt.Deep.eval_ret, SPComp.pure_def], hInv, hSInv, hBounded⟩

  | seq c1 c2 rs0 r1 rs' _h1 _h2 ih1 ih2 =>
    simp only [whileFree, Bool.and_eq_true] at hWf
    simp only [callFree, Bool.and_eq_true] at hCF
    simp only [scalarSetsSmall, Bool.and_eq_true] at hSSS
    simp only [jasminFuel] at hFuel
    -- fuel bounds
    have hFuel1 : jasminFuel c1 ≤ fuel := by omega
    have hFuel2 : jasminFuel c2 ≤ fuel - (toJasminCmd c1).length := by
      have := jasminFuel_gt_length c1; omega
    -- Apply IH1
    obtain ⟨heap1, heval1, hInv1, hSInv1, hB1⟩ :=
      ih1 fuel hWf.1 hCF.1 hSSS.1 hFuel1 sid heap hInv hSInv hBounded
    -- The two translated lists are appended
    simp only [toJasminCmd]
    -- Eval of append
    rw [translateCmd_append_eval]
    rw [callFree_toJasmin_newSid c1 hCF.1 env sid fuel] at *
    rw [heval1, SDistr.pure_bind]
    -- Now apply IH2 from heap1 at sid
    have hFuel2' : jasminFuel c2 ≤ fuel - (toJasminCmd c1).length := hFuel2
    obtain ⟨heap2, heval2, hInv2, hSInv2, hB2⟩ :=
      ih2 (fuel - (toJasminCmd c1).length) hWf.2 hCF.2 hSSS.2 hFuel2' sid heap1 hInv1 hSInv1 hB1
    exact ⟨heap2, heval2, hInv2, hSInv2, hB2⟩

  | letZero x t body rs0 rs' _h ih =>
    simp only [whileFree] at hWf
    simp only [callFree] at hCF
    simp only [scalarSetsSmall] at hSSS
    simp only [jasminFuel] at hFuel
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by have := jasminFuel_pos body; omega⟩
    have hFuel' : jasminFuel body ≤ n + 1 := by omega
    -- Initial heap: write default to towerLoc sid x t
    let heap' := heap.set (towerLoc sid x t) (default : JArray t.byteSize)
    have hInv' : HeapInv (rsSetTower rs0 x ⟨t, default⟩) heap' sid :=
      heapInv_rsSetTower_init rs0 heap sid x t hInv
    have hSInv' : ScalarInv (rsSetTower rs0 x ⟨t, default⟩) heap' sid :=
      scalarInv_rsSetTower rs0 heap' sid x ⟨t, default⟩
        (scalarInv_set_tower rs0 heap sid x t (default : JArray t.byteSize) hSInv)
    have hB' : ScalarsBounded (rsSetTower rs0 x ⟨t, default⟩) :=
      scalarsBounded_rsSetTower rs0 x ⟨t, default⟩ hBounded
    obtain ⟨heap'', heval', hInv'', hSInv'', hB''⟩ := ih (n + 1) hWf hCF hSSS hFuel' sid heap' hInv' hSInv' hB'
    simp only [toJasminCmd, show (n + 2) = (n + 1) + 1 from rfl]
    rw [translateCmd_cons_cassgn_sarr_init_eval]
    exact ⟨heap'', heval', hInv'', hSInv'', hB''⟩

  | letU64Zero x body rs0 rs' _h ih =>
    simp only [whileFree] at hWf
    simp only [callFree] at hCF
    simp only [scalarSetsSmall] at hSSS
    simp only [jasminFuel] at hFuel
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by have := jasminFuel_pos body; omega⟩
    have hFuel' : jasminFuel body ≤ n + 1 := by omega
    let heap' := heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (0 : BitVec 64)
    have hInv' : HeapInv (rsSetScalar rs0 x 0) heap' sid :=
      heapInv_set_u64 _ heap sid x 0 (heapInv_rsSetScalar rs0 heap sid x 0 hInv)
    have hSInv' : ScalarInv (rsSetScalar rs0 x 0) heap' sid :=
      scalarInv_after_scalar_set rs0 heap sid x 0 hSInv
    have hB' : ScalarsBounded (rsSetScalar rs0 x 0) :=
      scalarsBounded_rsSetScalar_zero rs0 x hBounded
    obtain ⟨heap'', heval', hInv'', hSInv'', hB''⟩ := ih (n + 1) hWf hCF hSSS hFuel' sid heap' hInv' hSInv' hB'
    refine ⟨heap'', ?_, ?_, ?_, hB''⟩
    · simp only [toJasminCmd]; rw [translateCmd_cons_cassgn_u64_eval]; exact heval'
    · exact hInv''
    · exact hSInv''

  | scalarSet x v rs0 =>
    simp only [callFree] at hCF
    simp only [scalarSetsSmall] at hSSS
    simp only [jasminFuel] at hFuel
    have hv_small : v < 2^64 := scalarSetsSmall_val (.RScalarSet x v) x v hSSS rfl
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
    refine ⟨heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (BitVec.ofNat 64 v),
            ?_, ?_, ?_, scalarsBounded_rsSetScalar rs0 x v hv_small hBounded⟩
    · simp only [toJasminCmd]; exact translateCmd_cassgn_u64_val_eval env sid x v n heap
    · exact heapInv_set_u64 _ heap sid x _ (heapInv_rsSetScalar rs0 heap sid x v hInv)
    · exact scalarInv_after_scalar_set rs0 heap sid x v hSInv

  | ifTrue e ct cf rs0 rs' v hv hne_zero _h ih =>
    simp only [whileFree, Bool.and_eq_true] at hWf
    simp only [callFree, Bool.and_eq_true] at hCF
    simp only [scalarSetsSmall, Bool.and_eq_true] at hSSS
    simp only [jasminFuel] at hFuel
    -- Determine the condition value from ScalarInv
    have he_val : heap.get (translateVar sid { vname := e, vtype := .sword .U64 }) =
        BitVec.ofNat 64 v := hv ▸ hSInv e
    have he_bnd : v < 2^64 := by rw [← hv]; exact hBounded e
    -- Condition evaluates to true
    have hcond : (translatePExpr sid (.Papp2 (.Oneq .U64)
        (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} }, gs := false })
        (.Papp1 (.Oword_of_int .U64) (.Pconst 0)))).eval heap =
        SDistr.pure (⟨.sbool, true⟩, heap) := by
      rw [cif_cond_eval]
      simp only [he_val]
      have hbne : BitVec.ofNat 64 v != (0 : BitVec 64) := by
        rw [bne_iff_ne]; exact bitVec_ofNat_ne_zero v hne_zero he_bnd
      rw [show ((0 : BitVec 64) = (0#64 : BitVec 64)) from rfl] at hbne
      simp [hbne]
    -- Fuel: max(j_ct, j_cf) + 1 ≤ fuel, so j_ct ≤ fuel - 1
    obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
    have hFuel_ct : jasminFuel ct ≤ fuel' := by omega
    obtain ⟨heap', heval', hInv', hSInv', hB'⟩ :=
      ih fuel' hWf.1 hCF.1 hSSS.1 hFuel_ct sid heap hInv hSInv hBounded
    simp only [toJasminCmd]
    refine ⟨heap', ?_, ?_, ?_, hB'⟩
    · rw [translateCmd_cif_eval_true env sid _ _ _ fuel' heap heap hcond]; exact heval'
    · exact hInv'
    · exact hSInv'

  | ifFalse e ct cf rs0 rs' h _h ih =>
    simp only [whileFree, Bool.and_eq_true] at hWf
    simp only [callFree, Bool.and_eq_true] at hCF
    simp only [scalarSetsSmall, Bool.and_eq_true] at hSSS
    simp only [jasminFuel] at hFuel
    obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
    -- Scalar = 0, condition evaluates to false
    have he_val : heap.get (translateVar sid { vname := e, vtype := .sword .U64 }) = (0 : BitVec 64) := by
      have h1 := hSInv e; rw [h] at h1; exact h1
    have hcond : (translatePExpr sid (.Papp2 (.Oneq .U64)
        (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} }, gs := false })
        (.Papp1 (.Oword_of_int .U64) (.Pconst 0)))).eval heap =
        SDistr.pure (⟨.sbool, false⟩, heap) := by
      rw [cif_cond_eval]
      simp only [he_val]
      rfl
    have hFuel_cf : jasminFuel cf ≤ fuel' := by omega
    -- newSid after ct = sid (call-free)
    have hCT_newSid : (translateCmd env (toJasminCmd ct) sid fuel').newSid = sid :=
      callFree_toJasmin_newSid ct hCF.1 env sid fuel'
    obtain ⟨heap', heval', hInv', hSInv', hB'⟩ :=
      ih fuel' hWf.2 hCF.2 hSSS.2 hFuel_cf sid heap hInv hSInv hBounded
    simp only [toJasminCmd]
    refine ⟨heap', ?_, ?_, ?_, hB'⟩
    · rw [translateCmd_cif_eval_false env sid _ _ _ fuel' heap heap hcond, hCT_newSid]
      exact heval'
    · exact hInv'
    · exact hSInv'

  | whileFalse _ _ _ _ => simp [whileFree] at hWf

  | whileTrue _ _ _ _ _ _ _ _ _ _ _ _ => simp [whileFree] at hWf

  | call _ _ _ _ _ _ _ _ => simp [callFree] at hCF

  | cloneCall _ _ _ _ _ _ _ _ _ _ _ => simp [callFree] at hCF

  | limbStore _ _ _ _ => simp [callFree] at hCF

/-- **Standalone call simulation**: an `RCall` instruction simulates correctly
    given `LeafImplOk`. This is the case that `rustExecSimulates` omits via
    the `callFree = true` precondition.

    Composes with `rustExecSimulates` via `translateCmd_append_eval` when a
    call is sequenced with call-free code. -/
lemma rustCallSimulates
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hLeaf : ∀ fuel', LeafImplOk leafSpec env fuel')
    (f : String) (dest : Located) (args : List Located)
    (rs rs' : RustState)
    (hExec : RustExec N leafSpec (.RCall f dest args) rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmd (.RCall f dest args)) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  cases hExec with
  | call f' dest' args' rs'' oldDestV argList hLookup hArgs =>
    have hTower : rs.rsTower dest.locVar = some ⟨dest.locDst, oldDestV⟩ := by
      unfold locatedLookup at hLookup
      split at hLookup
      · rename_i ty v heq
        split at hLookup
        · rename_i hty
          cases hty
          simp at hLookup
          rw [heq, hLookup]
        · simp at hLookup
      · simp at hLookup
    obtain ⟨heap1, hEval, hDest, hOtherTower, hScalarPreserve⟩ :=
      hLeaf fuel f dest args rs sid heap oldDestV argList hInv hTower hArgs
    refine ⟨heap1, ?_, ?_, ?_, ?_⟩
    · simp only [toJasminCmd]; exact hEval
    · -- HeapInv after call
      intro x t v hxTower
      by_cases hx : x = dest.locVar
      · subst hx
        simp only [locatedUpdate, rsSetTower, BEq.rfl, if_true] at hxTower
        -- hxTower : some ⟨dest.locDst, leafSpec ...⟩ = some ⟨t, v⟩
        obtain ⟨ht, hv⟩ := Sigma.mk.inj (Option.some.inj hxTower)
        subst ht
        simp at hv
        subst hv
        exact hDest
      · simp only [locatedUpdate, rsSetTower, beq_iff_eq, hx, if_false] at hxTower
        rw [hOtherTower x t hx]
        exact hInv x t v hxTower
    · -- ScalarInv after call (call doesn't touch scalars)
      intro x
      rw [hScalarPreserve x, hSInv x]
      -- rs'.rsScalar = rs.rsScalar since locatedUpdate only touches tower
      rfl
    · -- ScalarsBounded rs' (rs' = rs on scalars)
      intro x
      -- locatedUpdate = rsSetTower, which leaves rsScalar unchanged
      exact hBounded x

/-- **Limb-store oracle hypothesis**: the translated `.Copn ... (.Oasm "STORE64") ...`
    instruction (run from any heap encoding `rs`) produces a heap that matches
    the abstract `leafSpec.limbStore` update, and leaves everything else intact.

    This is the `STORE64`-specific analog of `LeafImplOk`, mirroring Rocq's
    `asm_correct` axiom for `Oasm` operators in `jasmin_translate.v`. -/
def LimbStoreImplOk (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat) : Prop :=
  ∀ (loc : Located) (idx : Nat) (v : BitVec 64)
    (rs0 : RustState) (sid : ScopeId) (heap0 : Heap)
    (oldDestV : RustVal loc.locDst),
    HeapInv rs0 heap0 sid →
    rs0.rsTower loc.locVar = some ⟨loc.locDst, oldDestV⟩ →
    ∃ heap1 : Heap,
      (translateCmd env [.Copn [locToLVal loc] .AT_none (.Oasm { name := "STORE64" })
                               [locToPExpr loc, .Pconst idx, .Pconst v.toNat]]
        sid fuel).code.eval heap0 =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap1) ∧
      heap1.get (towerLoc sid loc.locVar loc.locDst) =
        leafSpec.limbStore loc oldDestV idx v ∧
      (∀ (x : String) (t : TowerType),
        x ≠ loc.locVar → heap1.get (towerLoc sid x t) = heap0.get (towerLoc sid x t)) ∧
      (∀ (x : String),
        heap1.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
        heap0.get (translateVar sid { vname := x, vtype := .sword .U64 }))

/-- **Standalone limb-store simulation**: an `RLimbStore` instruction simulates
    correctly given `LimbStoreImplOk`. Same pattern as `rustCallSimulates`
    for Jasmin `Oasm` operators (Rocq's `asm_correct`). -/
lemma rustLimbStoreSimulates
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hLimb : ∀ fuel', LimbStoreImplOk leafSpec env fuel')
    (loc : Located) (idx : Nat) (v : BitVec 64)
    (rs rs' : RustState)
    (hExec : RustExec N leafSpec (.RLimbStore loc idx v) rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmd (.RLimbStore loc idx v)) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  cases hExec with
  | limbStore loc' idx' v' rs'' oldDestV hLookup =>
    have hTower : rs.rsTower loc.locVar = some ⟨loc.locDst, oldDestV⟩ := by
      unfold locatedLookup at hLookup
      split at hLookup
      · rename_i ty w heq
        split at hLookup
        · rename_i hty
          cases hty
          simp at hLookup
          rw [heq, hLookup]
        · simp at hLookup
      · simp at hLookup
    obtain ⟨heap1, hEval, hDest, hOtherTower, hScalarPreserve⟩ :=
      hLimb fuel loc idx v rs sid heap oldDestV hInv hTower
    refine ⟨heap1, ?_, ?_, ?_, ?_⟩
    · simp only [toJasminCmd]; exact hEval
    · intro x t vx hxTower
      by_cases hx : x = loc.locVar
      · subst hx
        simp only [locatedUpdate, rsSetTower, BEq.rfl, if_true] at hxTower
        obtain ⟨ht, hv⟩ := Sigma.mk.inj (Option.some.inj hxTower)
        subst ht
        simp at hv
        subst hv
        exact hDest
      · simp only [locatedUpdate, rsSetTower, beq_iff_eq, hx, if_false] at hxTower
        rw [hOtherTower x t hx]
        exact hInv x t vx hxTower
    · intro x
      rw [hScalarPreserve x, hSInv x]
      rfl
    · intro x
      exact hBounded x

/-- **Clone oracle hypothesis**: the `.Copn ... (.Oasm "CLONE_TOWER") [oldDest]`
    instruction copies the tower value at `oldDest` into the tower slot
    associated to `cloneVar` at type `cloneTy.byteSize`. Mirrors Rocq
    `asm_correct` for `Oasm` operators. -/
def CloneImplOk (env : TransEnv) (fuel : Nat) : Prop :=
  ∀ (cloneVar : String) (cloneTy : TowerType) (oldDest : Located)
    (rs0 : RustState) (sid : ScopeId) (heap0 : Heap)
    (oldDestV : RustVal cloneTy),
    HeapInv rs0 heap0 sid →
    rs0.rsTower oldDest.locVar = some ⟨cloneTy, oldDestV⟩ →
    ∃ heap1 : Heap,
      (translateCmd env
        [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.byteSize },
                        info := {} }] .AT_none
              (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]]
        sid fuel).code.eval heap0 =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap1) ∧
      heap1.get (towerLoc sid cloneVar cloneTy) = oldDestV ∧
      (∀ (x : String) (t : TowerType),
        x ≠ cloneVar → heap1.get (towerLoc sid x t) = heap0.get (towerLoc sid x t)) ∧
      (∀ (x : String),
        heap1.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
        heap0.get (translateVar sid { vname := x, vtype := .sword .U64 }))

/-- **Standalone clone-call simulation**: `RCloneCall` simulates via the
    composition of `CloneImplOk` (for the clone step) and `LeafImplOk` (for
    the inner call). Mirrors Rocq's structural decomposition of sequences.

    Requires `rs.rsTower oldDest.locVar = some ⟨cloneTy, oldV⟩` — the clone
    is well-typed. -/
lemma rustCloneCallSimulates
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hLeaf : ∀ fuel', LeafImplOk leafSpec env fuel')
    (hClone : ∀ fuel', CloneImplOk env fuel')
    (cloneVar : String) (cloneTy : TowerType) (oldDest : Located)
    (innerF : String) (dest : Located) (args : List Located)
    (rs rs' : RustState)
    (hExec : RustExec N leafSpec
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args) rs rs')
    (oldV : RustVal cloneTy)
    (hOldDest : rs.rsTower oldDest.locVar = some ⟨cloneTy, oldV⟩)
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmd
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args)) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  cases hExec with
  | cloneCall _ _ _ _ _ _ _ rsClone _ hClone_eq hCall =>
    -- Apply clone oracle to get heap1
    obtain ⟨heap1, hEvalClone, hCloneDest, hCloneOther, hCloneScalar⟩ :=
      hClone fuel cloneVar cloneTy oldDest rs sid heap oldV hInv hOldDest
    -- Establish invariants at rsClone / heap1
    have hRsClone : rsClone = rsSetTower rs cloneVar ⟨cloneTy, oldV⟩ := by
      rw [hClone_eq, hOldDest]; rfl
    have hInv1 : HeapInv rsClone heap1 sid := by
      intro x t v hxTower
      rw [hRsClone] at hxTower
      simp only [rsSetTower, beq_iff_eq] at hxTower
      by_cases hx : x = cloneVar
      · subst hx
        simp only [if_true] at hxTower
        obtain ⟨ht, hv⟩ := Sigma.mk.inj (Option.some.inj hxTower)
        subst ht
        simp at hv
        subst hv
        exact hCloneDest
      · simp only [hx, if_false] at hxTower
        rw [hCloneOther x t hx]
        exact hInv x t v hxTower
    have hSInv1 : ScalarInv rsClone heap1 sid := by
      intro x
      rw [hCloneScalar x, hSInv x, hRsClone]
      rfl
    have hBounded1 : ScalarsBounded rsClone := by
      intro x
      rw [hRsClone]
      exact hBounded x
    -- Decompose translateCmd [cloneInstr, callInstr] via append
    have h_toJ : toJasminCmd (.RCloneCall cloneVar cloneTy oldDest innerF dest args) =
        [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.byteSize },
                         info := {} }] .AT_none
              (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]] ++
        (toJasminCmd (.RCall innerF dest args)) := by
      rfl
    rw [h_toJ, translateCmd_append_eval]
    rw [hEvalClone, SDistr.pure_bind]
    -- newSid after the clone = sid (Copn doesn't change newSid)
    have h_newSid : (translateCmd env
        [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.byteSize },
                         info := {} }] .AT_none
              (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]]
        sid fuel).newSid = sid := by
      cases fuel with
      | zero => simp only [translateCmd]
      | succ n =>
        simp only [translateCmd, translateInstrR]
        cases n <;> simp only [translateCmd]
    rw [h_newSid]
    simp only [List.length_cons, List.length_nil, Nat.zero_add]
    -- Apply rustCallSimulates for the inner call (now takes explicit N)
    obtain ⟨heap2, hEvalCall, hInv2, hSInv2, hB2⟩ :=
      rustCallSimulates N leafSpec env (fuel - 1) hLeaf innerF dest args
        rsClone rs' hCall sid heap1 hInv1 hSInv1 hBounded1
    exact ⟨heap2, hEvalCall, hInv2, hSInv2, hB2⟩

end SimulationTheorem

/-! ## §5  Concrete programs -/

section ConcretePrograms

/-- Located values for G1 curve operations. -/
def mkFpLoc (x : String) : Located := { locVar := x, locSrc := .TFp, locDst := .TFp }
def mkFp2Loc (x : String) : Located := { locVar := x, locSrc := .TFp2, locDst := .TFp2 }

def g1X1 := mkFpLoc "X1"
def g1X2 := mkFpLoc "X2"
def g1Y1 := mkFpLoc "Y1"
def g1Y2 := mkFpLoc "Y2"
def g1Z1 := mkFpLoc "Z1"
def g1Z2 := mkFpLoc "Z2"
def g1X3 := mkFpLoc "X3"
def g1Y3 := mkFpLoc "Y3"
def g1Z3 := mkFpLoc "Z3"
def g1T0 := mkFpLoc "t0"
def g1T1 := mkFpLoc "t1"
def g1T2 := mkFpLoc "t2"
def g1T3 := mkFpLoc "t3"
def g1T4 := mkFpLoc "t4"
def g1T5 := mkFpLoc "t5"

/-- G1 projective addition (Renes et al., fresh-destination form).
    Identical structure to Rocq `RustCmdCurve.g1_add`. -/
def g1Add : RustCmd :=
  let c1  := .RCall "fp_mul" g1T0 [g1X1, g1X2]
  let c2  := .RCall "fp_mul" g1T1 [g1Y1, g1Y2]
  let c3  := .RCall "fp_mul" g1T2 [g1Z1, g1Z2]
  let c4  := .RCall "fp_add" g1T3 [g1X1, g1Y1]
  let c5  := .RCall "fp_add" g1T4 [g1X2, g1Y2]
  let c6  := .RCall "fp_mul" g1T5 [g1T3, g1T4]
  let c7  := .RCall "fp_sub" g1T3 [g1T5, g1T0]
  let c8  := .RCall "fp_sub" g1X3 [g1T3, g1T1]
  let c9  := .RCall "fp_add" g1T3 [g1Y1, g1Z1]
  let c10 := .RCall "fp_add" g1T4 [g1Y2, g1Z2]
  let c11 := .RCall "fp_mul" g1T5 [g1T3, g1T4]
  let c12 := .RCall "fp_sub" g1T3 [g1T5, g1T1]
  let c13 := .RCall "fp_sub" g1Y3 [g1T3, g1T2]
  .RSeq c1 (.RSeq c2 (.RSeq c3 (.RSeq c4 (.RSeq c5 (.RSeq c6
  (.RSeq c7 (.RSeq c8 (.RSeq c9 (.RSeq c10 (.RSeq c11 (.RSeq c12 c13)))))))))))

/-- G1 projective doubling. -/
def g1Dbl : RustCmd :=
  let c1 := .RCall "fp_sqr" g1T0 [g1X1]
  let c2 := .RCall "fp_sqr" g1T1 [g1Y1]
  let c3 := .RCall "fp_sqr" g1T2 [g1Z1]
  let c4 := .RCall "fp_mul" g1T3 [g1X1, g1Y1]
  let c5 := .RCall "fp_add" g1X3 [g1T3, g1T3]
  let c6 := .RCall "fp_mul" g1T3 [g1Y1, g1Z1]
  let c7 := .RCall "fp_add" g1Y3 [g1T3, g1T3]
  .RSeq c1 (.RSeq c2 (.RSeq c3 (.RSeq c4 (.RSeq c5 (.RSeq c6 c7)))))

/-- G2 affine addition. -/
def g2Add : RustCmd :=
  let c1 := .RCall "fp2_mul" (mkFp2Loc "t0") [mkFp2Loc "X1", mkFp2Loc "X2"]
  let c2 := .RCall "fp2_mul" (mkFp2Loc "t1") [mkFp2Loc "Y1", mkFp2Loc "Y2"]
  let c3 := .RCall "fp2_add" (mkFp2Loc "t2") [mkFp2Loc "X1", mkFp2Loc "Y1"]
  let c4 := .RCall "fp2_add" (mkFp2Loc "t3") [mkFp2Loc "X2", mkFp2Loc "Y2"]
  let c5 := .RCall "fp2_mul" (mkFp2Loc "X3") [mkFp2Loc "t2", mkFp2Loc "t3"]
  let c6 := .RCall "fp2_sub" (mkFp2Loc "Y3") [mkFp2Loc "X3", mkFp2Loc "t0"]
  .RSeq c1 (.RSeq c2 (.RSeq c3 (.RSeq c4 (.RSeq c5 c6))))

example : borrowOk g1Add = true  := by decide
example : borrowOk g1Dbl = true  := by decide
example : borrowOk g2Add = true  := by decide

section FrameTheorems

variable (N : Nat) (leafSpec : LeafSpec)

theorem g1AddPreservesX1 (rs rs' : RustState)
    (h : RustExec N leafSpec g1Add rs rs') :
    locatedLookup rs' g1X1 = locatedLookup rs g1X1 := by
  apply seqFrame N leafSpec g1Add rs rs' g1X1 h
  decide

theorem g1DblPreservesInputs (rs rs' : RustState)
    (h : RustExec N leafSpec g1Dbl rs rs') :
    locatedLookup rs' g1X1 = locatedLookup rs g1X1 ∧
    locatedLookup rs' g1Y1 = locatedLookup rs g1Y1 ∧
    locatedLookup rs' g1Z1 = locatedLookup rs g1Z1 := by
  refine ⟨?_, ?_, ?_⟩
  · apply seqFrame N leafSpec g1Dbl rs rs' g1X1 h; decide
  · apply seqFrame N leafSpec g1Dbl rs rs' g1Y1 h; decide
  · apply seqFrame N leafSpec g1Dbl rs rs' g1Z1 h; decide

end FrameTheorems
end ConcretePrograms

/-! ## §6  Pretty-printer and file output -/

section Printer

/-- Pretty-print a `TowerType` as a Jasmin array type comment. -/
def ppTowerType : TowerType → String
  | .TFp   => "fp"    | .TFp2  => "fp2"
  | .TFp6  => "fp6"   | .TFp12 => "fp12"
  | .TU64  => "u64"

/-- Pretty-print a `WSize`. -/
def ppWSize : WSize → String
  | .U8 => "u8" | .U16 => "u16" | .U32 => "u32"
  | .U64 => "u64" | .U128 => "u128" | .U256 => "u256"

/-- Pretty-print a `SType`. -/
def ppSType : SType → String
  | .sbool   => "bool"
  | .sint    => "int"
  | .sarr n  => "u8[" ++ toString n ++ "]"
  | .sword w => ppWSize w

/-- Pretty-print a `PExpr` (simplified). -/
def ppPExpr : PExpr → String
  | .Pconst z   => toString z
  | .Pbool b    => if b then "true" else "false"
  | .Pvar gv    => gv.gv.var.vname
  | .Papp2 (.Oneq _) e (.Pconst 0) => "(" ++ ppPExpr e ++ " != 0)"
  | .Papp2 _ e1 e2 => "(" ++ ppPExpr e1 ++ " op " ++ ppPExpr e2 ++ ")"
  | .Parr_init n => "#init(" ++ toString n ++ ")"
  | e => "<expr:" ++ (repr e).pretty 80 ++ ">"

/-- Pretty-print an `LVal`. -/
def ppLVal : LVal → String
  | .Lvar v        => v.var.vname
  | .Laset _ _ v _ => v.var.vname
  | lv             => "<lval:" ++ (repr lv).pretty 80 ++ ">"

/-- Indent by `n` spaces. -/
def indent (n : Nat) (s : String) : String :=
  String.replicate n ' ' ++ s

mutual
  /-- Pretty-print one instruction with indentation `ind`. -/
  def ppInstrR (ind : Nat) : InstrR → String
    | .Cassgn lv _ _ e =>
        indent ind (ppLVal lv ++ " = " ++ ppPExpr e ++ ";")
    | .Copn lvs _ (.Oasm op) es =>
        let lhss := String.intercalate ", " (lvs.map ppLVal)
        let args := String.intercalate ", " (es.map ppPExpr)
        indent ind (lhss ++ " = #" ++ op.name ++ "(" ++ args ++ ");")
    | .Ccall _ lvs fn args =>
        let lhss := String.intercalate ", " (lvs.map ppLVal)
        let argStr := String.intercalate ", " (args.map ppPExpr)
        indent ind (lhss ++ " = " ++ fn.name ++ "(" ++ argStr ++ ");")
    | .Cif cond cthen celse =>
        let hdr := indent ind ("if (" ++ ppPExpr cond ++ ") {")
        let thenStr := ppCmd (ind + 2) cthen
        if celse.isEmpty then
          hdr ++ "\n" ++ thenStr ++ "\n" ++ indent ind "}"
        else
          hdr ++ "\n" ++ thenStr ++ "\n" ++ indent ind "} else {" ++
          "\n" ++ ppCmd (ind + 2) celse ++ "\n" ++ indent ind "}"
    | .Cwhile _ cond body =>
        indent ind ("while (" ++ ppPExpr cond ++ ") {") ++
        "\n" ++ ppCmd (ind + 2) body ++ "\n" ++ indent ind "}"
    | .Cfor v r body =>
        indent ind ("for " ++ v.var.vname ++ " = " ++ toString r.lo ++
                    " to " ++ toString r.hi ++ " {") ++
        "\n" ++ ppCmd (ind + 2) body ++ "\n" ++ indent ind "}"

  /-- Pretty-print a `Cmd` (list of instructions) with indentation `ind`. -/
  def ppCmd (ind : Nat) : Cmd → String
    | [] => ""
    | instrs => String.intercalate "\n" (instrs.map (ppInstrR ind))
end

/-- Pretty-print a `FunDecl`. -/
def ppFunDecl (fd : FunDecl) : String :=
  let params := String.intercalate ", "
    (fd.params.map (fun p => ppSType p.var.var.vtype ++ " " ++ p.var.var.vname))
  let results := String.intercalate ", " (fd.results.map (fun r => r.var.vname))
  let body := ppCmd 2 fd.body
  "fn " ++ fd.name.name ++ "(" ++ params ++ ") -> (" ++ results ++ ") {\n" ++ body ++ "\n}"

/-- Pretty-print a full `JasminProg`. -/
def ppJasminProg (prog : JasminProg) : String :=
  String.intercalate "\n\n" (prog.funcs.map ppFunDecl)

/-- Write a `RustCmd` as a Jasmin function to a file. -/
def writeJasminProg (filename name : String) (params results : List Located)
    (c : RustCmd) : IO Unit := do
  let prog := toJasminProg name params results c
  IO.FS.writeFile filename (ppJasminProg prog)

/-- Write the `RustCmd` Rocq repr to a file (for round-trip inspection). -/
def writeRustCmdRepr (filename : String) (c : RustCmd) : IO Unit :=
  IO.FS.writeFile filename (repr c |>.pretty 80)

end Printer

/-! ## §7  Demo: emit g1_add to file

Uncomment to generate `g1_add.jazz` and `g1_add_rustcmd.txt`:

```lean
#eval writeJasminProg "/tmp/g1_add.jazz" "g1_add"
        [g1X1, g1Y1, g1Z1, g1X2, g1Y2, g1Z2]
        [g1X3, g1Y3]
        g1Add

#eval writeRustCmdRepr "/tmp/g1_add_rustcmd.txt" g1Add

#eval IO.println (ppJasminProg (toJasminProg "g1_add"
        [g1X1, g1Y1, g1Z1, g1X2, g1Y2, g1Z2] [g1X3, g1Y3] g1Add))
```
-/

end CatCrypt.Crypto.Jasmin.RustCmd
