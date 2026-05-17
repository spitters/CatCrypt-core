/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.RustCmd

/-!
# Borrow Checker and Frame Theorems for RustCmd

Port of `AUCurves/src/Bedrock/SafeRustBorrowCheck.v`.

## Contents

* §1  `borrowOk`: static alias checker (one `decide` per program)
* §2  `destsOf`: write-set of a program
* §3  `seqFrame`: if `loc ∉ destsOf c`, then `c` preserves `locatedLookup rs loc`
* §4  `callFrame`: convenience wrappers

## Design note

`seqFrame` is proved by induction on the `RustExec` derivation, matching
every constructor.  The `cloneCall` case is closed cleanly by including
`cloneVar` in `destsOf`: the precondition `loc.locVar ∉ destsOf c` then
directly yields both `loc.locVar ≠ cloneVar` and `loc.locVar ≠ dest.locVar`,
making the three-step chain `RemoveTower → inner ih → SetTower` trivial.

**0 admits, 0 sorry.**
-/

namespace CatCrypt.Crypto.Jasmin.RustCmd

open List

/-! ## §1  Borrow checker -/

-- RCloneCall : cloneVar cloneTy oldDest innerF dest args
/-- `borrowOk c` holds iff every `RCall` (and the inner call of every
    `RCloneCall`) has its destination variable distinct from all arguments.

    For `RCallSwap f dest1 dest2 args`, the borrow check additionally
    requires `dest1.locVar ≠ dest2.locVar` (the two destinations don't
    alias each other) and that neither destination appears in `args`. -/
def borrowOk : RustCmd → Bool
  | .RSkip                      => true
  | .RSeq c1 c2                 => borrowOk c1 && borrowOk c2
  | .RLetZero _ _ body          => borrowOk body
  | .RLetU64Zero _ body         => borrowOk body
  | .RScalarSet _ _             => true
  | .RCall _ dest args          => !callAliases dest args
  | .RCallSwap _ dest1 dest2 args =>
      (dest1.locVar != dest2.locVar)
        && !callAliases dest1 args
        && !callAliases dest2 args
  | .RCloneCall _ _ _ _ dest args => !callAliases dest args
  | .RIfNz _ ct cf              => borrowOk ct && borrowOk cf
  | .RWhileNz _ body            => borrowOk body
  | .RFor _ _ body              => borrowOk body
  | .RLimbStore _ _ _           => true
  -- Phase F: dests must be mutually distinct and disjoint from args.
  | .RAsmOp _ dests args        =>
      dests.Nodup && dests.all (fun d => !callAliases d args)
  -- Phase G: same as F.
  | .RCallN _ dests args        =>
      dests.Nodup && dests.all (fun d => !callAliases d args)
  -- Phase H: dst, src0, src1 base vars distinct (for the simple
  -- discipline; cmov-with-aliased-src is a future refinement).
  | .RSelect dst _ src0 src1    =>
      (dst.locVar != src0.locVar) && (dst.locVar != src1.locVar)
  -- Phase L: assertion has no destination, no args.
  | .RAssert _                  => true
  -- Phase M: scoped block lifts to its body.
  | .RBlock body                => borrowOk body
  -- Phase C: function-def borrow-OK iff body and continuation are.
  -- Param/return aliasing rules are checked at the FnSpec layer.
  | .RFnDef _ _ _ body cont     => borrowOk body && borrowOk cont
  -- Phase C: function-call same shape as RCallN.
  | .RFnCall _ dests args       =>
      dests.Nodup && dests.all (fun d => !callAliases d args)
  -- Phase I: tuple component store/load — single destination, no aliasing concern.
  | .RTupleStore dst _ src      => dst.locVar != src.locVar
  | .RTupleLoad dst src _       => dst.locVar != src.locVar
  -- Phase Ext (2026-05-12): runtime array load/store + scalar expression assign.
  -- Conservative defaults: array load/store require dst.locVar ≠ src.locVar
  -- (the scalar `idxVar` is read-only, no aliasing concern with tower locs).
  -- RScalarSetExpr is always borrowOk (writes only a scalar; reads scalars).
  | .RArrStore arr _ src        => arr.locVar != src.locVar
  | .RArrLoad dst src _         => dst.locVar != src.locVar
  | .RScalarSetExpr _ _         => true
  -- Phase Ext2 (2026-05-13): byte-slice copy.  Dst and src must be
  -- distinct base variables (slice copy with overlapping memory is
  -- UB at the Rust level; copy_from_slice panics on overlap).
  | .RBytesSlice dst src _ _    => dst.locVar != src.locVar

/-! ## §2  Write-set -/

/-- `destsOf c` is the list of base variable names that `c` may write. -/
def destsOf : RustCmd → List String
  | .RSkip                       => []
  | .RSeq c1 c2                  => destsOf c1 ++ destsOf c2
  | .RLetZero x _ body           => x :: destsOf body
  | .RLetU64Zero _ body          => destsOf body
  | .RScalarSet _ _              => []
  | .RCall _ dest _              => [dest.locVar]
  | .RCallSwap _ dest1 dest2 _   => [dest1.locVar, dest2.locVar]
  | .RCloneCall cloneVar _ _ _ dest _   => [cloneVar, dest.locVar]
  | .RIfNz _ ct cf               => destsOf ct ++ destsOf cf
  | .RWhileNz _ body             => destsOf body
  | .RFor _ _ body               => destsOf body
  | .RLimbStore loc _ _          => [loc.locVar]
  | .RAsmOp _ dests _            => dests.map (·.locVar)
  | .RCallN _ dests _            => dests.map (·.locVar)
  | .RSelect dst _ _ _           => [dst.locVar]
  | .RAssert _                   => []
  | .RBlock body                 => destsOf body
  -- Phase C: function-def's writes are body ∪ cont (under static analysis).
  | .RFnDef _ _ _ body cont      => destsOf body ++ destsOf cont
  | .RFnCall _ dests _           => dests.map (·.locVar)
  -- Phase I: tuple component store/load — single destination.
  | .RTupleStore dst _ _         => [dst.locVar]
  | .RTupleLoad dst _ _          => [dst.locVar]
  -- Phase Ext (2026-05-12): runtime array load/store + scalar expression assign.
  | .RArrStore arr _ _           => [arr.locVar]  -- mutates the array variable
  | .RArrLoad dst _ _            => [dst.locVar]
  | .RScalarSetExpr _ _          => []           -- writes a scalar, not in destsOf
  -- Phase Ext2 (2026-05-13): byte-slice copy mutates dst.
  | .RBytesSlice dst _ _ _       => [dst.locVar]

/-! ## §3  callAliases ↔ ∉ lemma -/

/-- If `callAliases dest args = false`, then every arg has a different
    base variable from `dest`. -/
lemma callAliases_false_ne (dest : Located) (args : List Located)
    (h : callAliases dest args = false) (arg : Located) (hmem : arg ∈ args) :
    dest.locVar ≠ arg.locVar := by
  intro heq
  have htrue : callAliases dest args = true := by
    simp only [callAliases, List.any_eq_true]
    exact ⟨arg, hmem, by simp [heq]⟩
  simp [htrue] at h

/-! ## §4  seqFrame -/

/-- **seqFrame**: if `loc.locVar ∉ destsOf c`, then any execution of `c`
    preserves `locatedLookup rs loc`.

    This replaces ~400 lines of per-function separation-logic frame proofs
    with a single structural induction, proved once here. -/
theorem seqFrame (N : Nat) (leafSpec : LeafSpec)
    (c : RustCmd) (rs rs' : RustState) (loc : Located)
    (hExec : RustExec N leafSpec c rs rs')
    (hNotIn : loc.locVar ∉ destsOf c) :
    locatedLookup rs' loc = locatedLookup rs loc := by
  induction hExec with

  | skip _ => rfl

  | seq _ _ _ _ _ _ _ ih1 ih2 =>
    simp only [destsOf, List.mem_append, not_or] at hNotIn
    rw [ih2 hNotIn.2, ih1 hNotIn.1]

  | letZero x _ _ _ _ _ ih =>
    simp only [destsOf, List.mem_cons, not_or] at hNotIn
    rw [ih hNotIn.2]
    exact locatedLookup_rsSetTower_other _ _ _ _ (Ne.symm hNotIn.1)

  | letU64Zero _ _ _ _ _ ih =>
    simp only [destsOf] at hNotIn
    rw [ih hNotIn]
    exact locatedLookup_rsSetScalar _ _ _ _

  | scalarSet _ _ _ =>
    exact locatedLookup_rsSetScalar _ _ _ _

  | ifTrue _ _ _ _ _ _ _ _ _ ih =>
    simp only [destsOf, List.mem_append, not_or] at hNotIn
    exact ih hNotIn.1

  | ifFalse _ _ _ _ _ _ _ ih =>
    simp only [destsOf, List.mem_append, not_or] at hNotIn
    exact ih hNotIn.2

  | whileFalse _ _ _ _ => rfl

  -- whileTrue: 10 constructor args (e body rs r1 rs' v h1 h2 hBody hWhile) + 2 IHs
  | whileTrue _ _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    simp only [destsOf] at hNotIn
    rw [ih2 hNotIn, ih1 hNotIn]

  | forZero _ _ _ => rfl

  -- forSucc: x n body rs r1 rs' + 2 IHs (one for the inner RFor, one for the body run).
  -- Setting the scalar counter doesn't touch the tower heap, so the body run preserves
  -- locatedLookup; the inner RFor preservation follows by IH.
  | forSucc _ n _ _ _ _ _ _ ih1 ih2 =>
    simp only [destsOf] at hNotIn
    -- After ih2, the body run preserves loc; before that, scalarSet preserves loc;
    -- before that, ih1 (the inner RFor) preserves loc.
    rw [ih2 hNotIn]
    rw [locatedLookup_rsSetScalar]
    rw [ih1 hNotIn]

  | call _ dest _ _ _ _ _ _ =>
    simp only [destsOf] at hNotIn
    rw [List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)

  | cloneCall cloneVar cloneTy oldDest innerF dest args rs0 rsClone rsInner hClone _ ih =>
    simp only [destsOf, List.mem_cons, List.mem_singleton, not_or] at hNotIn
    obtain ⟨hne_clone, hne_dest⟩ := hNotIn
    have hne : cloneVar ≠ loc.locVar := Ne.symm hne_clone
    have hDestsRCall : destsOf (.RCall innerF dest args) = [dest.locVar] := rfl
    have hInner : loc.locVar ∉ destsOf (.RCall innerF dest args) := by
      rw [hDestsRCall]; simp [hne_dest]
    -- two-step chain: inner call → initial SetTower (no Remove now)
    exact (ih hInner).trans (hClone ▸ locatedLookup_rsSetTower_other _ _ _ _ hne)

  | callSwap f dest1 dest2 args rs0 rs1 rs2 _h1 _h2 ih1 ih2 =>
    simp only [destsOf, List.mem_cons, List.mem_singleton, not_or] at hNotIn
    obtain ⟨hne_dest1, hne_dest2⟩ := hNotIn
    have hDests1 : destsOf (.RCall f dest1 args) = [dest1.locVar] := rfl
    have hDests2 : destsOf (.RCall f dest2 args) = [dest2.locVar] := rfl
    have hIn1 : loc.locVar ∉ destsOf (.RCall f dest1 args) := by
      rw [hDests1]; simp [hne_dest1]
    have hIn2 : loc.locVar ∉ destsOf (.RCall f dest2 args) := by
      rw [hDests2]; simp [hne_dest2]
    exact (ih2 hIn2).trans (ih1 hIn1)

  | limbStore _ _ _ _ =>
    simp only [destsOf] at hNotIn
    rw [List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)

  -- Phase F: identity-stub semantics → state unchanged.
  | asmOp _ _ _ _ => rfl

  -- Phase G: identity-stub semantics → state unchanged.
  | callN _ _ _ _ => rfl

  -- Phase H — selectFalse: dst gets updated, others untouched.
  | selectFalse dst _ _ _ _ _ _ _ _ =>
    simp only [destsOf] at hNotIn
    rw [List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)

  -- Phase H — selectTrue: same as selectFalse.
  | selectTrue dst _ _ _ _ _ _ _ _ _ _ =>
    simp only [destsOf] at hNotIn
    rw [List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)

  -- Phase L: assertion is a state no-op.
  | assert _ _ => rfl

  -- Phase M: scope wraps body identity-fully; lift via the body IH.
  | block _ _ _ _ ih =>
    simp only [destsOf] at hNotIn
    exact ih hNotIn

  -- Phase C: fnDef is identity at the runtime level (cont runs); IH
  -- on cont covers the post-state.
  | fnDef _ _ _ _ _ _ _ _ ih =>
    simp only [destsOf, List.mem_append, not_or] at hNotIn
    exact ih hNotIn.2

  -- Phase C: fnCall is identity-stub semantics → state unchanged.
  | fnCall _ _ _ _ => rfl

  -- Phase I.1 (2026-05-04): tuple store writes to dst → use
  -- locatedUpdate_other to preserve other locations' lookups.
  | tupleStore dst _ _ _ _ _ _ _ =>
    simp only [destsOf, List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)

  -- Phase I.1: same as tupleStore.
  | tupleLoad dst _ _ _ _ _ _ _ =>
    simp only [destsOf, List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)

  -- Phase Ext (2026-05-12): array store/load update a single dst → use locatedUpdate_other.
  | arrStore arr _ _ _ _ _ _ _ _ _ =>
    simp only [destsOf, List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)
  | arrLoad dst _ _ _ _ _ _ _ _ _ =>
    simp only [destsOf, List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)
  | scalarSetExpr _ _ _ =>
    -- RScalarSetExpr writes to rsScalar only (not rsTower); leaves tower lookups intact.
    exact locatedLookup_rsSetScalar _ _ _ _

  -- Phase Ext2 (2026-05-13): RBytesSlice updates dst → locatedUpdate_other for others.
  | bytesSlice dst _ _ _ _ _ _ _ _ =>
    simp only [destsOf, List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)

/-! ## §5  Call frame theorems -/

/-- **borrowOkCallFrame**: for a borrow-checked `RCall`, every argument
    variable is preserved by the call. -/
theorem borrowOkCallFrame (N : Nat) (leafSpec : LeafSpec)
    (f : String) (dest : Located) (args : List Located)
    (rs rs' : RustState)
    (hBok : borrowOk (.RCall f dest args) = true)
    (hExec : RustExec N leafSpec (.RCall f dest args) rs rs')
    (arg : Located) (hArg : arg ∈ args) :
    locatedLookup rs' arg = locatedLookup rs arg := by
  have hca : callAliases dest args = false := by simpa [borrowOk] using hBok
  apply seqFrame N leafSpec _ _ _ _ hExec
  simp only [destsOf]
  rw [List.mem_singleton]
  exact Ne.symm (callAliases_false_ne dest args hca arg hArg)

/-- **callFrameNonDest**: any variable whose base name differs from `dest`
    is preserved by an `RCall`, regardless of `borrowOk`. -/
theorem callFrameNonDest (N : Nat) (leafSpec : LeafSpec)
    (f : String) (dest : Located) (args : List Located)
    (rs rs' : RustState) (loc : Located)
    (hExec : RustExec N leafSpec (.RCall f dest args) rs rs')
    (hne : dest.locVar ≠ loc.locVar) :
    locatedLookup rs' loc = locatedLookup rs loc := by
  apply seqFrame N leafSpec _ _ _ _ hExec
  simp only [destsOf]
  rw [List.mem_singleton]
  exact Ne.symm hne

/-! ## §6  seqFrame corollaries -/

lemma borrowOk_seq_l {c1 c2 : RustCmd} (h : borrowOk (.RSeq c1 c2) = true) :
    borrowOk c1 = true := by simp [borrowOk] at h; exact h.1

lemma borrowOk_seq_r {c1 c2 : RustCmd} (h : borrowOk (.RSeq c1 c2) = true) :
    borrowOk c2 = true := by simp [borrowOk] at h; exact h.2

/-! ## §7  RCallSwap smoke tests

Sanity-check `borrowOk` and `destsOf` on the new 2-destination call. -/

/-- Two distinct destinations, neither in args: borrow-checks. -/
example :
    borrowOk
      (.RCallSwap "cswap"
        { locVar := "x2", locSrc := .TFp25519 }
        { locVar := "x3", locSrc := .TFp25519 }
        [{ locVar := "swap", locSrc := .TU64 }]) = true := by
  decide

/-- Same destination twice: borrow-check fails (`dest1 = dest2`). -/
example :
    borrowOk
      (.RCallSwap "cswap"
        { locVar := "x2", locSrc := .TFp25519 }
        { locVar := "x2", locSrc := .TFp25519 }
        [{ locVar := "swap", locSrc := .TU64 }]) = false := by
  decide

/-- Destination aliases an arg: borrow-check fails. -/
example :
    borrowOk
      (.RCallSwap "cswap"
        { locVar := "x2", locSrc := .TFp25519 }
        { locVar := "x3", locSrc := .TFp25519 }
        [{ locVar := "x2", locSrc := .TFp25519 }]) = false := by
  decide

/-- `destsOf` on `RCallSwap` lists both destination variables. -/
example :
    destsOf
      (.RCallSwap "cswap"
        { locVar := "x2", locSrc := .TFp25519 }
        { locVar := "x3", locSrc := .TFp25519 }
        []) = ["x2", "x3"] := by
  decide

end CatCrypt.Crypto.Jasmin.RustCmd
