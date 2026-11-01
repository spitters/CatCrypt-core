/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveFreeSig
public import CatCryptCore.Core.SPTreeFree
public import CatCryptCore.Core.SPTreeTimed
public import CatCryptCore.Crypto.Party.ProgE

/-!
# Tests of `derive_free_sig`

`derive_free_sig` run on three program-tree types:

* `SPTree`, compared with the hand-written signature of `CatCryptCore.Core.SPTreeFree`: the
  generated operations are equivalent to `SPTree.SPOp` with the same directions
  (`spOpEquiv`, `dir_spOpEquiv`, `spSigEquiv`), and along this equivalence the generated
  `toFreeM` is `SPTree.toFreeM` (`mapLens_toFreeM`, `ofFreeM_mapLens_toFreeM`);
* `Party.ProgE Op E O`, whose parameters precede the result type, with its bind;
* `SPTree.Timed`, a type in `Type 1` declared in a `meta section`.

Search words: polynomial functor, signature, free monad, deriving, tests.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Tactics.DeriveFreeSigTest

open CatCrypt.Core

/-! ## `SPTree` against the hand-written signature `SPTree.SPSig` -/

derive_free_sig SPTree (namespace := SPTreeGen) (bind := SPTree.bind)

/-- The generated operations of `SPTree` are the hand-written operations `SPTree.SPOp`. -/
def spOpEquiv : SPTreeGen.Op ≃ SPTree.SPOp where
  toFun
    | .sample β f n => .sample β f n
    | .sampleDist β μ => .sampleDist β μ
    | .get l => .get l
    | .set l v => .set l v
    | .fail => .fail
    | .load h => .load h
  invFun
    | .sample β f n => .sample β f n
    | .sampleDist β μ => .sampleDist β μ
    | .get l => .get l
    | .set l v => .set l v
    | .fail => .fail
    | .load h => .load h
  left_inv o := by cases o <;> rfl
  right_inv o := by cases o <;> rfl

/-- `spOpEquiv` preserves directions. -/
theorem dir_spOpEquiv (o : SPTreeGen.Op) :
    SPTree.SPOp.dir (spOpEquiv o) = SPTreeGen.Op.dir o := by
  cases o <;> rfl

/-- The generated signature of `SPTree` is equivalent to `SPTree.SPSig`, with identical
directions. -/
def spSigEquiv : PFunctor.Equiv SPTreeGen.Sig SPTree.SPSig where
  equivA := spOpEquiv
  equivB o := by cases o <;> exact Equiv.refl _

/-- Along `spSigEquiv`, the generated `toFreeM` is the hand-written `SPTree.toFreeM`. -/
theorem mapLens_toFreeM {α : Type} (s : SPTree α) :
    (SPTreeGen.toFreeM s).mapLens (PFunctor.Equiv.toLensEquiv spSigEquiv).toLens =
      SPTree.toFreeM s := by
  induction s with
  | ret a => rfl
  | _ =>
    simp only [SPTreeGen.toFreeM, SPTree.toFreeM]
    refine (PFunctor.FreeM.mapLens_liftBind _ _ _).trans (congrArg _ (funext fun d => ?_))
    first | exact d.elim | (rename_i ih; exact ih _) | (rename_i ih; exact ih)

/-- Along `spSigEquiv`, the hand-written `SPTree.ofFreeM` inverts the generated `toFreeM`. -/
theorem ofFreeM_mapLens_toFreeM {α : Type} (s : SPTree α) :
    SPTree.ofFreeM ((SPTreeGen.toFreeM s).mapLens (PFunctor.Equiv.toLensEquiv spSigEquiv).toLens) =
      s := by
  rw [mapLens_toFreeM, SPTree.ofFreeM_toFreeM]

/-! ## `Party.ProgE`: parameters before the result type -/

derive_free_sig CatCrypt.Crypto.Party.ProgE (namespace := ProgEGen)
  (bind := CatCrypt.Crypto.Party.ProgE.bind)

/-- The generated equivalence of `ProgE` with the free monad over its signature. -/
example (Op E O α : Type) :
    CatCrypt.Crypto.Party.ProgE Op E O α ≃ PFunctor.FreeM (ProgEGen.Sig Op E O) α :=
  ProgEGen.equivFreeM

/-- The generated signature of `ProgE` is the sum of its four summands. -/
example (Op E O : Type) : PFunctor.Equiv (ProgEGen.Sig Op E O)
    (ProgEGen.Sig.recv Op E O + (ProgEGen.Sig.send Op E O +
      (ProgEGen.Sig.opN Op E O + ProgEGen.Sig.fail Op E O))) :=
  ProgEGen.sigEquivSum Op E O

/-! ## `SPTree.Timed`: a tree type in `Type 1` -/

derive_free_sig SPTree.Timed (namespace := TimedGen)

/-- The generated signature of `SPTree.Timed` has positions in `Type 1`. -/
example : PFunctor.{1, 0} := TimedGen.Sig

/-- The generated equivalence of `SPTree.Timed` with the free monad over its signature. -/
noncomputable example (α : Type) : SPTree.Timed α ≃ PFunctor.FreeM TimedGen.Sig α :=
  TimedGen.equivFreeM

end CatCrypt.Tactics.DeriveFreeSigTest

end
