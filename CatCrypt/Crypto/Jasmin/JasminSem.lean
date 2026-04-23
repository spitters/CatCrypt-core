/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminAST
import CatCrypt.Crypto.Jasmin.JasminVar
import CatCrypt.Crypto.Jasmin.RustCmd
import CatCrypt.Crypto.Jasmin.RustCmdToJasmin
import CatCrypt.Core.Heap

/-!
# Jasmin Operational Semantics Bridge (Item 1)

Port of Jasmin's `sem.sem_call` from `theories/lang/sem.v`, restricted to
the `handled_instr_r` subset (what `toJasminCmd` can emit).

## Scope

**Supported** (matches Rocq `handled_instr_r = true`):
- `Cassgn` with `Parr_init` (for RLetZero)
- `Cassgn` with `Pconst 0` of u64 (for RLetU64Zero)
- `Cassgn` with `Papp1 (Oword_of_int U64) (Pconst v)` (for RScalarSet)
- `Cif` with the RIfNz canonical condition
- `Ccall` (for RCall)
- `Copn (Oasm "STORE64")` (for RLimbStore)
- `Copn (Oasm "CLONE_TOWER")` (for RCloneCall)

**Not supported** (Rocq also: `handled_instr_r = false`):
- `Cwhile`, `Cfor`

## Design choice

Jasmin sem acts directly on `RustState` rather than a new `estate` type.
The `translateVar`-indexed encoding already relates Lean `Heap` to
`RustState` (via `HeapInv`/`ScalarInv`), so building a separate
intermediate state buys nothing.
-/

namespace CatCrypt.Crypto.Jasmin.SemBridge

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.RustCmd

/-- Big-step operational semantics of a Jasmin command list, acting on
    `RustState`. Only covers the InstrR variants in the image of
    `toJasminCmd`. -/
inductive jasminSem (leafSpec : LeafSpec) : Cmd → RustState → RustState → Prop where
  | nil : ∀ rs, jasminSem leafSpec [] rs rs
  | cons : ∀ i is rs rs1 rs',
      jasminSem leafSpec [i] rs rs1 →
      jasminSem leafSpec is rs1 rs' →
      jasminSem leafSpec (i :: is) rs rs'
  /-- `Cassgn` of `Parr_init` to an sarr variable → zero-init the tower slot. -/
  | assgn_parr_init : ∀ x t rs,
      jasminSem leafSpec
        [.Cassgn (.Lvar { var := { vname := x, vtype := .sarr t.byteSize },
                           info := {} })
                 .AT_none (.sarr t.byteSize) (.Parr_init t.byteSize)]
        rs (rsSetTower rs x ⟨t, default⟩)
  /-- `Cassgn` of `Pconst 0` to a u64 scalar → set rsScalar to 0. -/
  | assgn_u64_zero : ∀ x rs,
      jasminSem leafSpec
        [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                 .AT_none (.sword .U64) (.Pconst 0)]
        rs (rsSetScalar rs x 0)
  /-- `Cassgn` of `Papp1 (Oword_of_int U64) (Pconst v)` → set rsScalar to v. -/
  | assgn_u64_val : ∀ x (v : Nat) rs,
      jasminSem leafSpec
        [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                 .AT_none (.sword .U64)
                 (.Papp1 (.Oword_of_int .U64) (.Pconst (v : Int)))]
        rs (rsSetScalar rs x v)
  /-- `Cif` true branch (scalar nonzero). -/
  | if_true : ∀ (e : String) (ct cf : Cmd) (rs rs' : RustState) (v : Nat),
      rs.rsScalar e = v → v ≠ 0 →
      jasminSem leafSpec ct rs rs' →
      jasminSem leafSpec
        [.Cif (.Papp2 (.Oneq .U64)
               (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 },
                                 info := {} }, gs := false })
               (.Papp1 (.Oword_of_int .U64) (.Pconst 0))) ct cf]
        rs rs'
  /-- `Cif` false branch (scalar zero). -/
  | if_false : ∀ (e : String) (ct cf : Cmd) (rs rs' : RustState),
      rs.rsScalar e = 0 →
      jasminSem leafSpec cf rs rs' →
      jasminSem leafSpec
        [.Cif (.Papp2 (.Oneq .U64)
               (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 },
                                 info := {} }, gs := false })
               (.Papp1 (.Oword_of_int .U64) (.Pconst 0))) ct cf]
        rs rs'
  /-- `Ccall` via the leaf oracle. -/
  | call_oracle : ∀ (f : String) (dest : Located) (args : List Located)
                    (rs : RustState) (oldDestV : RustVal dest.locDst)
                    (argList : List (Σ t, RustVal t)),
      locatedLookup rs dest = some oldDestV →
      argList = args.filterMap (fun a => rs.rsTower a.locVar) →
      jasminSem leafSpec
        [.Ccall .DoNotInline [locToLVal dest] { name := f } (args.map locToPExpr)]
        rs (locatedUpdate rs dest
              (leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList))
  /-- `Copn (Oasm "STORE64")` via the limb-store oracle. -/
  | limb_store_oracle : ∀ (loc : Located) (idx : Nat) (v : BitVec 64)
                         (rs : RustState) (oldDestV : RustVal loc.locDst),
      locatedLookup rs loc = some oldDestV →
      jasminSem leafSpec
        [.Copn [locToLVal loc] .AT_none (.Oasm { name := "STORE64" })
               [locToPExpr loc, .Pconst idx, .Pconst v.toNat]]
        rs (locatedUpdate rs loc (leafSpec.limbStore loc oldDestV idx v))
  /-- `Copn (Oasm "CLONE_TOWER")` — tower copy, matching `RustExec.cloneCall`
      semantics: if `oldDest.locVar` has a tower value, copy it; otherwise
      write `⟨cloneTy, default⟩` (the `|>.getD` case). -/
  | clone_tower : ∀ (cloneVar : String) (cloneTy : TowerType) (oldDest : Located)
                    (rs : RustState),
      jasminSem leafSpec
        [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.byteSize },
                         info := {} }] .AT_none
              (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]]
        rs (rsSetTower rs cloneVar
             ((rs.rsTower oldDest.locVar).getD ⟨cloneTy, default⟩))

/-! ## Sequential composition helper -/

/-- Concatenation law: `jasminSem l1 rs r1 ∧ jasminSem l2 r1 rs' ⟹
    jasminSem (l1 ++ l2) rs rs'`. Proved by induction on the first derivation. -/
theorem jasminSem_seq_compose
    (leafSpec : LeafSpec) (l1 l2 : Cmd) (rs r1 rs' : RustState)
    (h1 : jasminSem leafSpec l1 rs r1)
    (h2 : jasminSem leafSpec l2 r1 rs') :
    jasminSem leafSpec (l1 ++ l2) rs rs' := by
  induction h1 generalizing l2 rs' with
  | nil rs0 => exact h2
  | cons i is rs0 rs1 r1' hi his _ih1 ih2 =>
    exact jasminSem.cons i (is ++ l2) rs0 rs1 rs' hi (ih2 l2 rs' h2)
  | assgn_parr_init x t rs0 =>
    exact jasminSem.cons _ l2 rs0 _ rs' (jasminSem.assgn_parr_init x t rs0) h2
  | assgn_u64_zero x rs0 =>
    exact jasminSem.cons _ l2 rs0 _ rs' (jasminSem.assgn_u64_zero x rs0) h2
  | assgn_u64_val x v rs0 =>
    exact jasminSem.cons _ l2 rs0 _ rs' (jasminSem.assgn_u64_val x v rs0) h2
  | if_true e ct cf rs0 r1' v hv hne hct =>
    exact jasminSem.cons _ l2 rs0 r1' rs'
            (jasminSem.if_true e ct cf rs0 r1' v hv hne hct) h2
  | if_false e ct cf rs0 r1' h0 hcf =>
    exact jasminSem.cons _ l2 rs0 r1' rs'
            (jasminSem.if_false e ct cf rs0 r1' h0 hcf) h2
  | call_oracle f dest args rs0 oldDestV argList hLk hArgs =>
    exact jasminSem.cons _ l2 rs0 _ rs'
            (jasminSem.call_oracle f dest args rs0 oldDestV argList hLk hArgs) h2
  | limb_store_oracle loc idx v rs0 oldDestV hLk =>
    exact jasminSem.cons _ l2 rs0 _ rs'
            (jasminSem.limb_store_oracle loc idx v rs0 oldDestV hLk) h2
  | clone_tower cv ct oldDest rs0 =>
    exact jasminSem.cons _ l2 rs0 _ rs'
            (jasminSem.clone_tower cv ct oldDest rs0) h2

/-! ## Bridge: `RustExec c rs rs' → jasminSem (toJasminCmd c) rs rs'` -/

/-- `RSkip` case: `toJasminCmd .RSkip = []`, closed by `jasminSem.nil`. -/
theorem jasminSem_of_rustSkip
    (leafSpec : LeafSpec) (rs rs' : RustState)
    (h : ∃ N, RustExec N leafSpec .RSkip rs rs') :
    jasminSem leafSpec (toJasminCmd .RSkip) rs rs' := by
  obtain ⟨_, h⟩ := h
  cases h
  exact jasminSem.nil rs

/-- `RScalarSet` case: direct application of `jasminSem.assgn_u64_val`.
    `toJasminCmd (.RScalarSet x v)` emits a single `Cassgn (Papp1 ...)`. -/
theorem jasminSem_of_rustScalarSet
    (leafSpec : LeafSpec) (x : String) (v : Nat) (rs rs' : RustState)
    (h : ∃ N, RustExec N leafSpec (.RScalarSet x v) rs rs') :
    jasminSem leafSpec (toJasminCmd (.RScalarSet x v)) rs rs' := by
  obtain ⟨_, h⟩ := h
  cases h
  simp only [toJasminCmd]
  exact jasminSem.assgn_u64_val x v rs

/-- **Main bridge theorem**: `RustExec c rs rs' → jasminSem (toJasminCmd c)
    rs rs'` for while-free programs. Structural induction on `hExec`;
    each case uses the matching `jasminSem` constructor, with
    `jasminSem_seq_compose` handling sequencing. -/
theorem rustExecSoundInJasmin
    (N : Nat) (leafSpec : LeafSpec) (c : RustCmd) (rs rs' : RustState)
    (hWf : whileFree c = true)
    (hExec : RustExec N leafSpec c rs rs') :
    jasminSem leafSpec (toJasminCmd c) rs rs' := by
  induction hExec with
  | skip rs0 => grind [toJasminCmd, jasminSem.nil]
  | seq c1 c2 rs0 r1 rs0' _h1 _h2 ih1 ih2 =>
    simp only [whileFree, Bool.and_eq_true] at hWf
    exact jasminSem_seq_compose leafSpec _ _ rs0 r1 rs0' (ih1 hWf.1) (ih2 hWf.2)
  | letZero x t body rs0 rs0' _h ih =>
    simp only [whileFree] at hWf
    simp only [toJasminCmd]
    exact jasminSem.cons _ _ rs0 _ rs0'
      (jasminSem.assgn_parr_init x t rs0)
      (ih hWf)
  | letU64Zero x body rs0 rs0' _h ih =>
    simp only [whileFree] at hWf
    simp only [toJasminCmd]
    exact jasminSem.cons _ _ rs0 _ rs0'
      (jasminSem.assgn_u64_zero x rs0)
      (ih hWf)
  | scalarSet x v rs0 => grind [toJasminCmd, jasminSem.assgn_u64_val]
  | ifTrue e ct cf rs0 rs0' v hv hne_zero _h ih =>
    simp only [whileFree, Bool.and_eq_true] at hWf
    simp only [toJasminCmd]
    exact jasminSem.if_true e (toJasminCmd ct) (toJasminCmd cf) rs0 rs0' v
      hv hne_zero (ih hWf.1)
  | ifFalse e ct cf rs0 rs0' h _h ih =>
    simp only [whileFree, Bool.and_eq_true] at hWf
    simp only [toJasminCmd]
    exact jasminSem.if_false e (toJasminCmd ct) (toJasminCmd cf) rs0 rs0'
      h (ih hWf.2)
  | whileFalse _ _ _ _ => simp [whileFree] at hWf
  | whileTrue _ _ _ _ _ _ _ _ _ _ _ _ => simp [whileFree] at hWf
  | call f dest args rs0 oldDestV argList hLk hArgs =>
    grind [toJasminCmd, jasminSem.call_oracle]
  | cloneCall cloneVar cloneTy oldDest innerF dest args
                rs0 rsClone rs0' hClone_eq _hCall ih =>
    simp only [whileFree] at hWf
    simp only [toJasminCmd]
    -- Two-step: (1) the clone via jasminSem.clone_tower, (2) the inner call
    -- via ih (after whileFree).
    have h1 : jasminSem leafSpec
        [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.byteSize },
                         info := {} }] .AT_none
              (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]]
        rs0 rsClone := by
      rw [hClone_eq]
      exact jasminSem.clone_tower cloneVar cloneTy oldDest rs0
    have h2 : jasminSem leafSpec (toJasminCmd (.RCall innerF dest args))
        rsClone rs0' := ih rfl
    exact jasminSem.cons _ _ rs0 rsClone rs0' h1 h2
  | limbStore loc idx v rs0 oldDestV hLk =>
    simp only [toJasminCmd]
    exact jasminSem.limb_store_oracle loc idx v rs0 oldDestV hLk

end CatCrypt.Crypto.Jasmin.SemBridge
