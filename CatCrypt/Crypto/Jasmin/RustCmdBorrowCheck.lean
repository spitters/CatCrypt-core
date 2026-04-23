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
    `RCloneCall`) has its destination variable distinct from all arguments. -/
def borrowOk : RustCmd → Bool
  | .RSkip                      => true
  | .RSeq c1 c2                 => borrowOk c1 && borrowOk c2
  | .RLetZero _ _ body          => borrowOk body
  | .RLetU64Zero _ body         => borrowOk body
  | .RScalarSet _ _             => true
  | .RCall _ dest args          => !callAliases dest args
  | .RCloneCall _ _ _ _ dest args => !callAliases dest args
  | .RIfNz _ ct cf              => borrowOk ct && borrowOk cf
  | .RWhileNz _ body            => borrowOk body
  | .RLimbStore _ _ _           => true

/-! ## §2  Write-set -/

/-- `destsOf c` is the list of base variable names that `c` may write. -/
def destsOf : RustCmd → List String
  | .RSkip                       => []
  | .RSeq c1 c2                  => destsOf c1 ++ destsOf c2
  | .RLetZero x _ body           => x :: destsOf body
  | .RLetU64Zero _ body          => destsOf body
  | .RScalarSet _ _              => []
  | .RCall _ dest _              => [dest.locVar]
  | .RCloneCall cloneVar _ _ _ dest _   => [cloneVar, dest.locVar]
  | .RIfNz _ ct cf               => destsOf ct ++ destsOf cf
  | .RWhileNz _ body             => destsOf body
  | .RLimbStore loc _ _          => [loc.locVar]

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

  | limbStore _ _ _ _ =>
    simp only [destsOf] at hNotIn
    rw [List.mem_singleton] at hNotIn
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

end CatCrypt.Crypto.Jasmin.RustCmd
